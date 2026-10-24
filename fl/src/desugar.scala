package DSL.fl

// The desugaring function DS (Figure 6.4 of the book): it maps FL expressions
// (kernel + sugar) to FLK kernel expressions by removing the syntactic sugar.
// It is the identity on kernel expressions.
//
//   DS[[(@O E*)]]            = (prim O E*)
//   DS[[(abs () E)]]         = (lam Ifresh E)
//   DS[[(abs (I) E)]]        = (lam I E)
//   DS[[(abs (I Irest+) E)]] = (lam I (abs Irest+ E))
//   DS[[(E)]]                = (app E #u)
//   DS[[(E1 E2)]]            = (app E1 E2)
//   DS[[(E1 E2 Erest+)]]     = ((app E1 E2) Erest+)
//   DS[[(list)]]             = #u
//   DS[[(list E Erest+)]]    = (pair E (list Erest+))
//   DS[[(quote #u/B/N/Y/(SX*))] ...
//   DS[[(cond (else D)]]     = D
//   DS[[(cond (T E) ...]]    = (if T E (cond ...))
//   DS[[(scand E*)]]         = short-circuit conjunction
//   DS[[(scor E*)]]          = short-circuit disjunction
//   DS[[(let ((I E)*) B)]]   = ((abs (I*) B) E*)
//   DS[[(letrec ((I E)*) B)]] = kept native (mutual recursion)
//   DS[[(recur P ((I E)*) B)]] = (letrec ((P (abs (I*) B))) (P E*))
//
// Note: `letrec` is left as a kernel-level construct that the evaluator
// supports natively (with true mutual recursion) rather than being desugared
// to the book's Church-tuple encoding, for clarity in the reference evaluator.
object Desugar {

    private var counter = 0
    private def fresh(): String = { counter += 1; s"@@fl_fresh_$counter" }

    def apply(e: Exp): Exp = e match {
        // Kernel forms: recurse into subexpressions.
        case e: UnitLit    => e
        case e: BoolLit    => e
        case e: IntLit     => e
        case e: Sym        => e
        case e: Var        => e
        case ErrorExpr(msg) => ErrorExpr(msg)
        case If(t, th, el) => If(apply(t), apply(th), apply(el))
        case PrimOp(op, args) => PrimOp(op, args.map(apply))
        case Lam(f, b)     => Lam(f, apply(b))
        case App(r, a)     => App(apply(r), apply(a))
        case Pair(f, s)    => Pair(apply(f), apply(s))
        case Rec(n, b)     => Rec(n, apply(b))

        // Sugar forms.
        case SugaredPrimOp(op, args) =>
            PrimOpTag.fromName(op) match {
                case Some(tag) => PrimOp(tag, args.map(apply))
                case None      => ErrorExpr(s"unknown primitive operator: $op")
            }
        case Abs(Nil, b)          => Lam(fresh(), apply(b))
        case Abs(List(f), b)      => Lam(f, apply(b))
        case Abs(f :: rest, b)    => Lam(f, apply(Abs(rest, b)))

        case MultiApp(r, Nil)       => App(apply(r), UnitLit())
        case MultiApp(r, a :: Nil)  => App(apply(r), apply(a))
        case MultiApp(r, a1 :: a2 :: rest) =>
            apply(MultiApp(App(apply(r), apply(a1)), a2 :: rest))

        case ListExpr(Nil)           => UnitLit()
        case ListExpr(e :: rest)     => Pair(apply(e), apply(ListExpr(rest)))

        case Quote(sx) => apply(quoteSExp(sx))

        case Cond(Nil, Some(d)) => apply(d)
        case Cond((t, th) :: rest, d) => If(apply(t), apply(th), apply(Cond(rest, d)))
        case Cond(Nil, None) => ErrorExpr("cond: no branches and no else")

        case Scand(Nil)      => BoolLit(true)
        case Scand(e :: rest) => If(apply(e), apply(Scand(rest)), BoolLit(false))
        case Scor(Nil)       => BoolLit(false)
        case Scor(e :: rest)  => If(apply(e), BoolLit(true), apply(Scor(rest)))

        case Let(binds, body) =>
            apply(MultiApp(Abs(binds.map(_._1), body), binds.map(_._2)))
        case LetRec(binds, body) =>
            LetRec(binds.map { case (n, e) => (n, apply(e)) }, apply(body))
        case Recur(proc, binds, body) =>
            // (letrec ((proc (abs (I*) body))) (proc E*)) — run through `apply`
            // so the `abs` binding is desugared to a kernel `lam`.
            apply(LetRec(List((proc, Abs(binds.map(_._1), body))),
                         MultiApp(Var(proc), binds.map(_._2))))

        // Should not occur inside an expression; handled by the program runner.
        case _: UnsugaredProgram | _: SugaredProgram => ErrorExpr("internal: program in expression position")
    }

    // DS[[quote SX]] — a quoted s-expression becomes a value.
    private def quoteSExp(sx: SExp): Exp = sx match {
        case SExpUnit()       => UnitLit()
        case SExpBool(b)      => BoolLit(b)
        case SExpInt(n)       => IntLit(n)
        case SExpSym(s)       => Sym(s)
        case SExpList(elems)  => ListExpr(elems.map(Quote(_)))
    }
}
