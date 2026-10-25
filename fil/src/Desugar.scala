package DSL.fil

import DSL.fl._

// Desugaring and AST-construction simplifications for FIL.
//
// Desugaring (Figure 17.14, syntactic sugar):
//   DS[[(@O E*)]]               = (prim O E*)         (base and indexed operators)
//   DS[[(let* () E)]]           = E
//   DS[[(let* ((I E) rest*) E)]] = (let ((I E)) (let* (rest*) E))
//
// Simplifications (Figure 17.15) — performed when FIL ASTs are constructed
// (that is, by the parser and by Translate), not by a separate transforming
// stage:
//
//   (let () E)                 -> E                    [empty-let]
//   (app (abs (I*) E) Ei*)     -> (let ((Ii Ei)*) E)   [implicit-let]
//   (abs (I*) (app Erator I*)) -> Erator               [eta]
//       where Erator is a variable or abstraction and
//       FrIds[Erator] ∩ {I1, ..., In} = {}
//   (let ((I I')) E)           -> [I'/I]E              [copy-prop]
//
// The rules are not confluent: the book's Eambig example (page 1034),
// (app (abs (I) (app Irator I)) E) with I ≠ Irator, can simplify either to
// (let ((I E)) (app Irator I)) (via [implicit-let] on the outer app) or to
// (app Irator E) (via [eta] on the rator), and the two results do not in
// general simplify to a common expression. The book resolves the ambiguity
// by requiring a BOTTOM-UP application: a rule may be applied to an
// expression only if no rule applies to any of its subexpressions — so
// Eambig unambiguously simplifies to (app Irator E) (the rator is
// simplified first; the [implicit-let] rule on the outer app is blocked
// because its rator can be simplified). `simp` implements exactly that:
// simplify the children (to fixpoint), then try the rules at this node,
// then re-simplify the result (which may expose a new opportunity higher
// up). The process terminates: every rule application removes a let, an
// abs, or an app ([copy-prop] shrinks the tree), so no infinite
// simplification chain exists.
//
// [copy-prop] is safe in FIL precisely because FIL has no mutable variables
// (page 1033; Exercise 17.7 shows it is unsafe in FLARE, where assignments
// to I or I' can alias). The substitution [I'/I]E is capture-free: bound
// variables are renamed as necessary to prevent variable capture.

object Desugar {

    private var counter = 0
    /** A fresh, unreferenced identifier (capture-avoiding renames; also
      * used by Translate for the letrec translation's mset! bindings). */
    def freshName(): String = {
        counter += 1
        s"@@fil_fresh_$counter"
    }

    // Entry point for parsed (possibly sugared) FIL expressions and for
    // Translate's output: desugar the sugar, then apply the Figure 17.15
    // simplifications to fixpoint.
    def apply(e: Exp): Exp = simp(desugar(e))

    // ------------------------------------------------------------------
    // Desugaring of the syntactic sugar (Figure 17.14)
    // ------------------------------------------------------------------

    private def desugar(e: Exp): Exp = e match {
        case e: UnitLit    => e
        case e: BoolLit    => e
        case e: IntLit     => e
        case e: Sym        => e
        case e: Var        => e
        case e: ErrorExpr  => e
        case If(t, th, el) => If(desugar(t), desugar(th), desugar(el))
        case FilPrim(op, args) => FilPrim(op, args.map(desugar))
        case FilApp(r, rands) => FilApp(desugar(r), rands.map(desugar))
        case Abs(fs, b)     => Abs(fs, desugar(b))
        case Let(bs, b)     =>
            Let(bs.map { case (n, e) => (n, desugar(e)) }, desugar(b))

        // (@O E*) -> (prim O E*)  (the parser already validated the name,
        // including the literal index of the indexed operators).
        case SugaredPrimOp(op, args) =>
            if (FilPrimop.valid(op)) FilPrim(op, args.map(desugar))
            else ErrorExpr(s"unknown FIL primitive operator: $op")

        // (let* ((I E) rest*) E) -> (let ((I E)) (let* rest* E))
        case LetStar(binds, body) =>
            binds match {
                case Nil => desugar(body)
                case (n, e) :: rest =>
                    Let(List((n, desugar(e))), desugar(LetStar(rest, body)))
            }

        case _ => ErrorExpr("internal error: non-FIL expression node")
    }

    // ------------------------------------------------------------------
    // The Figure 17.15 simplifications, applied bottom-up to fixpoint
    // ------------------------------------------------------------------

    def simp(e: Exp): Exp = e match {
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: Var | _: ErrorExpr => e
        case If(t, th, el) => If(simp(t), simp(th), simp(el))
        case FilPrim(op, args) => FilPrim(op, args.map(simp))

        // [eta]: (abs (I*) (app Erator I*)) -> Erator, where Erator is a
        // variable or an abstraction (a syntactic purity guarantee) and
        // FrIds[Erator] is disjoint from the formals.
        case Abs(formals, body) =>
            val sb = simp(body)
            sb match {
                case FilApp(rator, rands)
                      if rands.size == formals.size &&
                         rands.zip(formals).forall { case (Var(x), f) => x == f } &&
                         isEtaRator(rator) &&
                         frIds(rator).intersect(formals.toSet).isEmpty =>
                    simp(rator)
                case _ => Abs(formals, sb)
            }

        // [implicit-let]: (app (abs (I*) E) E*) -> (let ((Ii Ei)*) E).
        // The rator was simplified first (bottom-up), so it is reached only
        // when it is an abs that could NOT be eta-reduced — this is what
        // resolves the Eambig ambiguity.
        case FilApp(rator, rands) =>
            val sr = simp(rator)
            val ss = rands.map(simp)
            sr match {
                case Abs(formals, body) if formals.size == ss.size =>
                    simp(Let(formals.zip(ss).toList, body))
                case _ => FilApp(sr, ss)
            }

        // [empty-let] and [copy-prop].
        case Let(binds, body) =>
            val sb = binds.map { case (n, e) => (n, simp(e)) }
            val sbd = simp(body)
            (sb, sbd) match {
                case (Nil, b) => simp(b)
                case (List((n, Var(m))), b) => simp(subst(n, Var(m))(b))
                case _ => Let(sb, sbd)
            }

        // let* never appears in desugared output, but the translation's
        // letrec encoding builds it mid-pipeline; desugar and simplify.
        case LetStar(binds, body) => simp(desugar(LetStar(binds, body)))

        case _ => ErrorExpr("internal error: non-FIL expression node in simplification")
    }

    // [eta] requires Erator to be a variable or an abstraction (page 1033).
    private def isEtaRator(r: Exp): Boolean = r match {
        case _: Var | _: Abs => true
        case _ => false
    }

    // ------------------------------------------------------------------
    // Free identifiers (needed by [eta] and by the capture analysis)
    // ------------------------------------------------------------------

    def frIds(e: Exp): Set[String] = e match {
        case Var(n) => Set(n)
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: ErrorExpr => Set.empty
        case If(t, th, el) => frIds(t) ++ frIds(th) ++ frIds(el)
        case FilPrim(_, args) =>
            args.foldLeft(Set.empty[String])((s, a) => s ++ frIds(a))
        case Abs(fs, b) => frIds(b) -- fs.toSet
        case FilApp(r, rands) =>
            frIds(r) ++ rands.foldLeft(Set.empty[String])((s, a) => s ++ frIds(a))
        case Let(bs, b) =>
            val defs = bs.foldLeft(Set.empty[String])((s, be) => s ++ frIds(be._2))
            defs ++ (frIds(b) -- bs.map(_._1).toSet)
        // let* desugars to NESTED single-binding lets, so its bindings are
        // sequential (each definition sees the earlier ones), unlike the
        // parallel Let.
        case LetStar(binds, b) =>
            binds.foldRight(frIds(b)) { case ((n, e), acc) => frIds(e) ++ (acc - n) }
    }

    // ------------------------------------------------------------------
    // Capture-free substitution  [E'/I]E
    // ------------------------------------------------------------------
    // Used by [copy-prop] (with E' a variable) and by Translate's msubst
    // (with E' = (prim (mget 1) I)). A binder that binds a name in
    // FrIds(E') while I is still free would capture the replacement, so it
    // is renamed to a fresh name before the substitution proceeds.

    def subst(old: String, repl: Exp)(e: Exp): Exp =
        sub(old, repl, active = true)(e)

    private def sub(old: String, repl: Exp, active: Boolean)(e: Exp): Exp = e match {
        case Var(o) => if (active && o == old) repl else e
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: ErrorExpr => e
        case If(t, th, el) =>
            If(sub(old, repl, active)(t), sub(old, repl, active)(th), sub(old, repl, active)(el))
        case FilPrim(op, args) =>
            FilPrim(op, args.map(sub(old, repl, active)))
        case FilApp(r, rands) =>
            FilApp(sub(old, repl, active)(r), rands.map(sub(old, repl, active)))
        case Abs(fs, b) =>
            val oldShadowed = fs.contains(old)
            val capture =
                if (active && !oldShadowed) frIds(repl) intersect fs.toSet
                else Set.empty[String]
            if (capture.nonEmpty) {
                // Rename this abs's bindings of the captured names, then
                // substitute (the replacement names are now free here).
                val ren = fs.map(f => f -> (if (capture.contains(f)) freshName() else f)).toMap
                Abs(fs.map(f => ren(f)), sub(old, repl, active)(renameSet(capture, ren)(b)))
            } else {
                Abs(fs, sub(old, repl, if (oldShadowed) false else active)(b))
            }
        case Let(bs, b) =>
            val oldShadowed = bs.exists(_._1 == old)
            // A parallel let's definitions see the OUTER environment, so
            // they are substituted with the outer `active`.
            val bs2 = bs.map { case (nm, e) => (nm, sub(old, repl, active)(e)) }
            val capture =
                if (active && !oldShadowed) frIds(repl) intersect bs.map(_._1).toSet
                else Set.empty[String]
            if (capture.nonEmpty) {
                val ren = bs.map { case (n, _) => n -> (if (capture.contains(n)) freshName() else n) }.toMap
                val bs3 = bs2.map { case (nm, e) => (ren(nm), e) }
                Let(bs3, sub(old, repl, active)(renameSet(capture, ren)(b)))
            } else {
                Let(bs2, sub(old, repl, if (oldShadowed) false else active)(b))
            }
        // let* is nested lets; substitute in the desugared form.
        case LetStar(binds, b) => sub(old, repl, active)(desugar(LetStar(binds, b)))
    }

    // Rename the occurrences of the names in `names` that are bound by the
    // enclosing binder (renaming each per `ren`) to fresh names, within its
    // scope. A binder that rebinds one of the names SHADOWS it: its binder
    // names and its body are left untouched. In a parallel let the
    // definitions see the outer environment, so name occurrences there still
    // belong to the enclosing binder and are renamed; the body sees this
    // let's bindings, so it does not.
    private def renameSet(names: Set[String], ren: Map[String, String])(e: Exp): Exp =
        renameWS(names, ren, names)(e)

    private def renameWS(names: Set[String], ren: Map[String, String], active: Set[String])(e: Exp): Exp = e match {
        case Var(o) => ren.get(o).filter(_ => active.contains(o)).map(Var(_)).getOrElse(e)
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: ErrorExpr => e
        case If(t, th, el) =>
            If(renameWS(names, ren, active)(t), renameWS(names, ren, active)(th),
               renameWS(names, ren, active)(el))
        case FilPrim(op, args) =>
            FilPrim(op, args.map(renameWS(names, ren, active)))
        case FilApp(r, rands) =>
            FilApp(renameWS(names, ren, active)(r), rands.map(renameWS(names, ren, active)))
        case Abs(fs2, b2) =>
            Abs(fs2, renameWS(names, ren, active -- fs2.toSet)(b2))
        case Let(bs2, b2) =>
            val act2 = active -- bs2.map(_._1).toSet
            Let(bs2.map { case (nm, e) => (nm, renameWS(names, ren, active)(e)) },
                renameWS(names, ren, act2)(b2))
        case LetStar(binds, b) => renameWS(names, ren, active)(desugar(LetStar(binds, b)))
    }
}
