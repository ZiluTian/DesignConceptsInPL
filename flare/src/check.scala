package DSL.flare

import DSL.fl._
import DSL.flex.{FlexResult, FlexOk, FlexErr}

// Type reconstruction for the full FLARE language (Figures 13.14, 13.20, and
// 13.26 of the book).
//
// The reconstruction algorithm walks the (desugared) kernel expression,
// assigning each subexpression a type and accumulating a set of type
// constraints. Type environments map identifiers to type schemas; a reference
// to a name bound to (generic (tau*) T) is instantiated with fresh type
// identifiers (one per tau) at each use ([genvarLPR]). Let and letrec
// introduce schemas, generalized by rgenPure, which restricts generalization
// to pure definition expressions (the value restriction, Figure 13.25).
//
// The collected constraints are solved once, at the top, by the lazy
// left-to-right unifier (Figure 13.11). The program's type is then displayed
// as (=> (Targ*) Tresult), with any remaining free type identifiers
// canonicalized to T1, T2, ... in order of first appearance.

object FlareRecon {

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
        // FLARE parser, which uses Abs / MultiApp) are handled by delegation.
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

        // [letLPR]: each definition is typed in the OUTER environment (let is
        // parallel: a definition cannot refer to the let-bound names), and its
        // schema is generalized with only its own constraints.
        case Let(binds, body) =>
            processBinds(binds, te).flatMap { case (teBinds, cDefs) =>
                recon(body, teBinds).map { case (tBody, cBody) =>
                    (tBody, cBody ++ cDefs)
                }
            }

        // [letrecLPR]: a fresh type identifier per name; each definition is
        // typed with ALL the names (including its own) bound to their fresh
        // identifiers (monomorphic inside the definitions). The constraint set
        // is the union of the definitions' constraints plus the equations
        // tau_i = T_i; each schema is generalized over the full constraint set
        // and the OUTER environment.
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
                    case (name, defn, tDef, _) => (name, rgenPure(defn, tDef, te, tcsDefns))
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
    private def processBinds(binds: List[(String, Exp)], te: Map[String, TS]):
        Either[String, (Map[String, TS], List[(T, T)])] =
        binds.foldLeft[Either[String, (Map[String, TS], List[(T, T)])]](Right((te, Nil))) {
            case (acc, (name, defn)) => acc match {
                case Left(m) => Left(m)
                case Right((teAcc, cAcc)) =>
                    recon(defn, te).map { case (tDef, cDef) =>
                        (teAcc + (name -> rgenPure(defn, tDef, te, cDef)), cAcc ++ cDef)
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

    // rgenPure (Figure 13.26): generalize a definition's type, but only if the
    // definition expression is pure; otherwise keep it monomorphic (closed).
    private def rgenPure(e: Exp, t: T, te: Map[String, TS], tcs: List[(T, T)]): TS =
        if (Purity.pure(e)) rgen(t, te, tcs) else TSClosed(t)

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

    // Reconstruct the type of a whole program.
    def reconProgram(p: FlarePgm): FlexResult = {
        Fresh.reset()
        val (formals, bodyExpr) = p match {
            case FlareKernelProgram(formals, body) => (formals, DSL.flare.Desugar(body))
            case FlareSugarProgram(formals, body, defs) => (formals, DSL.flare.Desugar.program(body, defs))
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
    // identifiers to T1, T2, ... in first-appearance order. As in FLEX, a
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

// Purity (Figure 13.25): a conservative approximation of "does not touch the
// store". Literals, variable references, and error expressions are pure. An
// abstraction is always pure (creating a procedure does not touch the store,
// even if invoking it might). An if is pure iff all three subexpressions are
// pure. A let/letrec is pure iff all of its definition expressions are pure
// (the body is not required). A primitive application is pure iff the operator
// is not one of {cell, ^, :=} and all of its arguments are pure. Procedure
// applications are always impure (the invoked body might touch the store).
object Purity {
    private val storeOps = Set("cell", "^", ":=")

    def pure(e: Exp): Boolean = e match {
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: Var | _: ErrorExpr => true
        case _: Abs => true
        case If(t, th, el) => pure(t) && pure(th) && pure(el)
        case Let(bs, _) => bs.forall { case (_, e) => pure(e) }
        case LetRec(bs, _) => bs.forall { case (_, e) => pure(e) }
        case FlarePrim(op, args) => !storeOps.contains(op) && args.forall(pure)
        case _: MultiApp | _: App | _: Lam => false
        case _ => false
    }
}

// Parse and reconstruct the type of a full-FLARE program.
def flareRecon(input: String): FlexResult =
    FlareProgram(input) match {
        case Some(p) => FlareRecon.reconProgram(p)
        case None => FlexErr("parse error")
    }

// Test helpers:  "(flare ...)" shouldFlareReconTo (FlexOk("(=> (int) int)"))
extension (input: String)
    def shouldFlareReconTo(expected: FlexResult): Unit = {
        val got = flareRecon(input)
        assert(got == expected, s"expected $expected but got $got for: $input")
    }

// "(flare ...)" shouldFlareReconFail("unbound")
extension (input: String)
    def shouldFlareReconFail(prefix: String): Unit = {
        val got = flareRecon(input)
        got match {
            case FlexErr(m) =>
                assert(m.startsWith(prefix), s"expected an error starting with '$prefix' but got '$m' for: $input")
            case FlexOk(t) =>
                throw new AssertionError(s"expected a type error but got FlexOk($t) for: $input")
        }
    }
