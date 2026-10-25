package DSL.flare_v

import DSL.fl._
import DSL.flex.{FlexResult, FlexOk, FlexErr}
import DSL.flare.{
    T, TS, TVar, TSClosed, TSGeneric, TArrow, Unify, Fresh, TEPrim, FlarePrim,
    FlarePgm, FlareKernelProgram, FlareSugarProgram, freeIdsTE
}

// Type reconstruction for FLARE/V (Section 17.2.2 of the book): FLARE's
// reconstruction (Figures 13.14, 13.20, 13.26) extended with the mutable
// variable assignment `set!` and the soundness restriction of Section 13.5.2
// (consequences 1 and 2) / Exercise 13.11.
//
// New rules, relative to FLARE:
//
//   [set!R]  (set! I E)  — I must be bound to a CLOSED (monomorphic) type in
//        the environment; the value E must have exactly I's type; the result
//        is unit. Assignment to a generic (polymorphic) binding is rejected
//        (defensive: with the restriction below, every binding that a set!
//        can target is already closed, so this branch only fires for a
//        binding that is generic and NOT assigned in its scope — e.g. a
//        sibling let definition's name).
//
//   Soundness restriction (Section 13.5.2, consequence 1; Exercise 13.11b/c/e):
//        it is unsound to generalize a definition whose associated name is
//        assigned via set! in its scope. rgenPureV therefore keeps a
//        definition monomorphic when (a) it is impure (FLARE's value
//        restriction, Figure 13.25) OR (b) its name is assigned (via
//        findAssigned, a scope-respecting walk) in the scope of the binding.
//        This is exactly what rejects the Exercise 13.11b counterexample:
//            (let ((f (abs (x) x)))
//              (begin (set! f (abs (y) (prim + y 1)))
//                     (if (f #t) 1 (f 2))))
//        where `f` must stay monomorphic, so (f #t) : int and the if's test
//        is not a bool.
//
//   Purity (Section 13.5.2, consequence 2; Figure 13.25): FLARE's syntactic
//        purity test is reused as-is, with SetBang impure. (The book notes
//        that a variable reference is impure in a stateful language — it
//        reads the mutable store — and Exercise 13.11f/h explores the
//        consequence for generalization under a naive vs. a set-tracking
//        purity. The reference FLARE/V system keeps FLARE's syntactic
//        purity: assignment mutates bindings, not values, so an aliased
//        value (a let definition that is a variable reference) keeps its
//        value, and generalizing it remains sound. The Exercise 13.11f
//        program — which a naive purity would reject — is therefore accepted
//        here, as it is in FLARE.)
//
// Theorem: a program WITHOUT set! is typable in FLARE if and only if it is
// typable in FLARE/V (the accept/reject decision is identical; the
// restriction and the set! rule are inactive, and the displayed types are
// FLARE's). A cross-check test against DSL.flare.flareRecon locks this in.
// FLARE/V additionally accepts set! programs.
//
// As in FLARE, the constraints are solved once, at the top, by the lazy
// left-to-right unifier (Figure 13.11), and the program's type is displayed
// as (=> (Targ*) Tresult) (or just the body type when there are no formals),
// with free type identifiers canonicalized to T1, T2, ... in first-appearance
// order.

object FlareVRecon {

    // The result of reconstructing an expression: its type and the type
    // constraints collected along the way.
    private type Recon = (T, List[(T, T)])

    def recon(e: Exp, te: Map[String, TS]): Either[String, Recon] = e match {
        // [unitR] / [intR] / [boolR] / [symR]
        case _: UnitLit => Right((T.unit, Nil))
        case _: BoolLit => Right((T.bool, Nil))
        case _: IntLit  => Right((T.int, Nil))
        case _: Sym     => Right((T.symb, Nil))

        // [errorR]: a fresh type identifier is introduced for the error.
        case _: ErrorExpr => Right((TVar(Fresh.next()), Nil))

        // [varLPR] (closed schema) / [genvarLPR] (generic schema: freshen).
        case Var(name) => te.get(name) match {
            case None => Left(s"unbound variable: $name")
            case Some(TSClosed(t)) => Right((t, Nil))
            case Some(TSGeneric(bound, body)) =>
                val fresh = bound.map(b => b -> TVar(Fresh.next())).toMap
                Right((T.subst(fresh, body), Nil))
        }

        // [ifR]: result type is the then-branch's type; constrain the test to
        // bool and the two branches to be equal.
        case If(test, thenExp, elseExp) =>
            recon(test, te).flatMap { case (tTest, cTest) =>
                recon(thenExp, te).flatMap { case (tThen, cThen) =>
                    recon(elseExp, te).map { case (tElse, cElse) =>
                        (tThen, cTest ++ cThen ++ cElse ++ List(T.bool -> tTest, tThen -> tElse))
                    }
                }
            }

        // [→-introR]: a fresh type identifier per formal; multi-parameter
        // abstractions are kernel forms (Abs), so this handles them directly.
        case Abs(formals, body) =>
            val freshFormals = formals.map(_ => TVar(Fresh.next()))
            val teF = te ++ formals.zip(freshFormals).map { case (n, t) => n -> TSClosed(t) }.toMap
            recon(body, teF).map { case (tBody, cBody) =>
                (T.arrow(freshFormals, tBody), cBody)
            }

        // [→-elimR]: a fresh result type; constrain the rator to be an arrow
        // from the argument types to that result. Multi-argument applications
        // are kernel forms (MultiApp).
        case MultiApp(rator, rands) =>
            recon(rator, te).flatMap { case (tRator, cRator) =>
                reconAll(rands, te).map { case (tArgs, cArgs) =>
                    val tRes = TVar(Fresh.next())
                    (tRes, cRator ++ cArgs ++ List(tRator -> T.arrow(tArgs, tRes)))
                }
            }

        // Robustness: FL's single-parameter forms (never produced by the
        // FLARE/V parser, which uses Abs / MultiApp) are handled by
        // delegation.
        case Lam(f, b) => recon(Abs(List(f), b), te)
        case App(r, a) => recon(MultiApp(r, List(a)), te)

        // [primR]: the operator type is looked up in TEprim and instantiated
        // with fresh identifiers; constrain it to an arrow over the actual
        // argument types.
        case FlarePrim(op, args) =>
            reconAll(args, te).map { case (tArgs, cArgs) =>
                val top = freshenSchema(TEPrim.schema(op))
                val tRes = TVar(Fresh.next())
                (tRes, cArgs ++ List(top -> T.arrow(tArgs, tRes)))
            }

        // [set!R] (FLARE/V): the target must be bound to a closed type; the
        // value must have exactly that type; the result is unit.
        case SetBang(name, e) => te.get(name) match {
            case None => Left(s"unbound variable: $name")
            case Some(TSClosed(t)) =>
                recon(e, te).map { case (tE, cE) =>
                    (T.unit, cE ++ List(tE -> t))
                }
            case Some(TSGeneric(_, _)) =>
                Left(s"cannot assign to a polymorphic variable: $name")
        }

        // [letLPR]: each definition is typed in the OUTER environment (let is
        // parallel: a definition cannot refer to the let-bound names), and its
        // schema is generalized with only its own constraints — UNLESS the
        // name is assigned via set! in the body, in which case it is kept
        // monomorphic (Section 13.5.2). A definition cannot assign to a name
        // bound by this let (parallel let: definitions see the outer
        // environment), so only the body is inspected.
        case Let(binds, body) =>
            processBinds(binds, te, body).flatMap { case (teBinds, cDefs) =>
                recon(body, teBinds).map { case (tBody, cBody) =>
                    (tBody, cBody ++ cDefs)
                }
            }

        // [letrecLPR]: a fresh type identifier per name; each definition is
        // typed with ALL the names (including its own) bound to their fresh
        // identifiers (monomorphic inside the definitions). A set! in ANY
        // definition (or in the body) targets the letrec's own bindings, so
        // any of them assigns to a name and keeps it monomorphic. The
        // constraint set is the union of the definitions' constraints plus
        // the equations tau_i = T_i; each schema is generalized over the full
        // constraint set and the OUTER environment.
        case LetRec(binds, body) =>
            val taus = binds.map { case (name, _) => name -> TVar(Fresh.next()) }
            val teTau = te ++ taus.map { case (n, t) => n -> TSClosed(t) }.toMap
            binds.foldLeft[Either[String, List[(String, Exp, T, List[(T, T)])]]](Right(Nil)) {
                case (acc, (name, defn)) => acc match {
                    case Left(m) => Left(m)
                    case Right(accL) =>
                        recon(defn, teTau).map { case (tDef, cDef) =>
                            accL :+ (name, defn, tDef, cDef)
                        }
                }
            }.flatMap { defnResults =>
                val cUnion = defnResults.flatMap(_._4)
                val cEqs = defnResults.map { case (name, _, tDef, _) =>
                    (taus.find(_._1 == name).get._2, tDef)
                }
                val tcsDefns = cUnion ++ cEqs
                val schemas: List[(String, TS)] = defnResults.map {
                    case (name, defn, tDef, _) =>
                        val assigned = findAssigned(body, name) ||
                            binds.exists { case (_, d) => findAssigned(d, name) }
                        (name, rgenPureV(defn, tDef, te, tcsDefns, assigned))
                }
                val teBinds = te ++ schemas.toMap
                recon(body, teBinds).map { case (tBody, cBody) =>
                    (tBody, cBody ++ tcsDefns)
                }
            }

        case _ => Left("internal error: unexpected expression node in reconstruction")
    }

    // Type each definition in the OUTER environment (parallel let) and build
    // the extended environment and the accumulated definition constraints.
    // `body` is needed for the soundness restriction: a name assigned via
    // set! in the body is not generalized.
    private def processBinds(binds: List[(String, Exp)], te: Map[String, TS], body: Exp):
        Either[String, (Map[String, TS], List[(T, T)])] =
        binds.foldLeft[Either[String, (Map[String, TS], List[(T, T)])]](Right((te, Nil))) {
            case (acc, (name, defn)) => acc match {
                case Left(m) => Left(m)
                case Right((teAcc, cAcc)) =>
                    recon(defn, te).map { case (tDef, cDef) =>
                        (teAcc + (name -> rgenPureV(defn, tDef, te, cDef, findAssigned(body, name))), cAcc ++ cDef)
                    }
            }
        }

    // Reconstruct a list of expressions in the same environment.
    private def reconAll(es: List[Exp], te: Map[String, TS]): Either[String, (List[T], List[(T, T)])] =
        es.foldLeft[Either[String, (List[T], List[(T, T)])]](Right((Nil, Nil))) {
            case (acc, e) => acc match {
                case Left(m) => Left(m)
                case Right((ts, cs)) => recon(e, te).map { case (t, c) => (ts :+ t, cs ++ c) }
            }
        }

    // Instantiate the generic-bound identifiers of a primitive's type schema
    // with fresh type identifiers.
    private def freshenSchema(ts: TS): T = ts match {
        case TSClosed(t) => t
        case TSGeneric(bound, body) =>
            T.subst(bound.map(b => b -> TVar(Fresh.next())).toMap, body)
    }

    // rgenPureV (Figure 13.26 + Section 13.5.2): generalize a definition's
    // type only if it is pure AND its name is never assigned via set! in the
    // binding's scope; otherwise keep it monomorphic (closed).
    private def rgenPureV(e: Exp, t: T, te: Map[String, TS], tcs: List[(T, T)], assigned: Boolean): TS =
        if (FlareVPurity.pure(e) && !assigned) rgen(t, te, tcs) else TSClosed(t)

    // rgen (Figure 13.20): solve the constraint set, apply the resulting
    // substitution to the type, and generalize over the identifiers that are
    // free in the type but not in the (substituted) environment.
    private def rgen(t: T, te: Map[String, TS], tcs: List[(T, T)]): TS =
        Unify.solveTCS(tcs) match {
            case Unify.Solved(σ) =>
                val t2 = T.subst(σ, t)
                val gen = T.freeIds(t2) -- freeIdsTE(σ, te)
                if (gen.isEmpty) TSClosed(t2)
                else TSGeneric(gen.toList.sortBy(Fresh.order), t2)
            case Unify.Unsolvable(_) =>
                // The local constraints do not unify; the top-level solve will
                // report the failure. Fall back to a closed type.
                TSClosed(t)
        }

    // findAssigned (cf. the MutIds function, Figure 17.10): does a `set!` in
    // `e` target the binding of `name` that is in scope at the head of `e`?
    // The walk is scope-respecting: a set! targets the INNERMOST binding of
    // its name, so a binder that rebinds `name` shadows it.
    //
    //   - SetBang(n, e): true iff n == name, or the value assigns name.
    //   - Abs/Lam: a formal that rebinds name shadows it (false); otherwise
    //     recurse into the body.
    //   - Let: definitions see the OUTER environment (parallel let), so a
    //     set! name in ANY definition (including name's own) targets the
    //     enclosing binding; the body is shadowed if this let binds name.
    //   - LetRec: definitions see ALL the letrec names (including their own),
    //     so a set! name anywhere inside the letrec (defs or body) targets the
    //     letrec's own name, not an enclosing one — false when this letrec
    //     binds name; otherwise recurse into defs and body.
    def findAssigned(e: Exp, name: String): Boolean = e match {
        case SetBang(n, ee) => n == name || findAssigned(ee, name)
        case Var(_) => false
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: ErrorExpr => false
        case If(t, th, el) =>
            findAssigned(t, name) || findAssigned(th, name) || findAssigned(el, name)
        case Abs(fs, body) => !fs.contains(name) && findAssigned(body, name)
        case Lam(f, b) => f != name && findAssigned(b, name)
        case MultiApp(rator, rands) =>
            findAssigned(rator, name) || rands.exists(findAssigned(_, name))
        case App(r, a) => findAssigned(r, name) || findAssigned(a, name)
        case FlarePrim(_, args) => args.exists(findAssigned(_, name))
        case Let(bs, body) =>
            bs.exists { case (_, defn) => findAssigned(defn, name) } ||
                (!bs.exists(_._1 == name) && findAssigned(body, name))
        case LetRec(bs, body) =>
            !bs.exists(_._1 == name) &&
                (bs.exists { case (_, defn) => findAssigned(defn, name) } || findAssigned(body, name))
        case _ => false
    }

    // Reconstruct the type of a whole program.
    def reconProgram(p: FlarePgm): FlexResult = {
        Fresh.reset()
        val (formals, bodyExpr) = p match {
            case k: FlareKernelProgram => (k.formals, FlareVDesugar(k.body))
            case s: FlareSugarProgram => (s.formals, FlareVDesugar.program(s.body, s.defs))
        }
        // A fresh type identifier per formal, bound in the initial environment.
        val tauFormals = formals.map(_ => TVar(Fresh.next()))
        val te0 = formals.zip(tauFormals).map { case (n, t) => n -> TSClosed(t) }.toMap
        recon(bodyExpr, te0) match {
            case Left(m) => FlexErr(m)
            case Right((tBody, cBody)) =>
                Unify.solveTCS(cBody) match {
                    case Unify.Solved(σ) =>
                        val f2 = tauFormals.map(t => T.subst(σ, t))
                        val b2 = T.subst(σ, tBody)
                        FlexOk(showProgramType(f2, b2))
                    case Unify.Unsolvable(failed) => FlexErr(Unify.failureMessage(failed))
                }
        }
    }

    // Display the program type, canonicalizing any remaining free type
    // identifiers to T1, T2, ... in first-appearance order. As in FLARE, a
    // program with no formals is displayed as just its body type; a program
    // with formals is displayed as (=> (Targ*) Tresult).
    private def showProgramType(formals: List[T], body: T): String = {
        T.canonicalize(T.arrow(formals, body)) match {
            case TArrow(ps, r) =>
                if (ps.isEmpty) T.show(r)
                else "(=> (" + ps.map(T.show).mkString(" ") + ") " + T.show(r) + ")"
        }
    }
}

// Purity for FLARE/V: FLARE's syntactic purity test (Figure 13.25) with
// SetBang impure. A literal, a variable reference, or an error expression is
// pure; an abstraction is always pure (creating a procedure does not touch
// the store, even if invoking it might — and assignment changes bindings,
// not values); an if is pure iff all three subexpressions are pure; a
// let/letrec is pure iff all of its definition expressions are pure (the
// body is not required); a primitive application is pure iff the operator is
// not one of {cell, ^, :=} and all of its arguments are pure; a procedure
// application is always impure; an assignment is always impure.
object FlareVPurity {
    private val storeOps = Set("cell", "^", ":=")

    def pure(e: Exp): Boolean = e match {
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: Var | _: ErrorExpr => true
        case _: Abs => true
        case If(t, th, el) => pure(t) && pure(th) && pure(el)
        case Let(bs, _) => bs.forall { case (_, e) => pure(e) }
        case LetRec(bs, _) => bs.forall { case (_, e) => pure(e) }
        case FlarePrim(op, args) => !storeOps.contains(op) && args.forall(pure)
        case _: SetBang | _: MultiApp | _: App | _: Lam => false
        case _ => false
    }
}

// Parse and reconstruct the type of a full-FLARE/V program.
def flareVRecon(input: String): FlexResult =
    FlareVProgram(input) match {
        case Some(p) => FlareVRecon.reconProgram(p)
        case None => FlexErr("parse error")
    }

// Test helpers:  "(flare ...)" shouldFlareVReconTo (FlexOk("(=> (int) int)"))
extension (input: String)
    def shouldFlareVReconTo(expected: FlexResult): Unit = {
        val got = flareVRecon(input)
        assert(got == expected, s"expected $expected but got $got for: $input")
    }

// "(flare ...)" shouldFlareVReconFail("unbound")
extension (input: String)
    def shouldFlareVReconFail(prefix: String): Unit = {
        val got = flareVRecon(input)
        got match {
            case FlexErr(m) =>
                assert(m.startsWith(prefix), s"expected an error starting with '$prefix' but got '$m' for: $input")
            case FlexOk(t) =>
                throw new AssertionError(s"expected a type error but got FlexOk($t) for: $input")
        }
    }
