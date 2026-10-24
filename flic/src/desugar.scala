package DSL.flic

import DSL.fl._

// The desugaring function for FLIC (Figure 8.9 of the book). It maps FLIC
// expressions (FLICK kernel + FL sugar + FLIC sugar) to FLICK kernel
// expressions:
//
//   (begin)                        -> #u
//   (begin E)                      -> E
//   (begin E1 E2 Erest*)           -> (begin E1 (begin E2 Erest*))
//   (if Etest Ethen)               -> (if Etest Ethen #u)
//   (while Etest Ebody)            -> (letrec ((Iloop (abs ()
//                                                (if Etest (begin Ebody Iloop) #u)))))
//                                             Iloop)         {Iloop is fresh}
//   (@^ E) / (@:= E1 E2) /
//   (@cell=? E1 E2) / (@cell? E)   -> the FLICK kernel cell primops
//
// The desugarings of the constructs inherited from FL (and FLK) are exactly
// those of Figure 6.4 (see DSL.fl.Desugar).
object Desugar {

    private var counter = 0
    private def fresh(): String = { counter += 1; s"@@flic_fresh_$counter" }

    def apply(e: Exp): Exp = e match {
        // FLICK kernel forms: recurse into subexpressions.
        case e: UnitLit      => e
        case e: BoolLit      => e
        case e: IntLit       => e
        case e: Sym          => e
        case e: Var          => e
        case ErrorExpr(msg)  => ErrorExpr(msg)
        case If(t, th, el)   => If(apply(t), apply(th), apply(el))
        case PrimOp(op, args) => PrimOp(op, args.map(apply))
        case Lam(f, b)       => Lam(f, apply(b))
        case App(r, a)       => App(apply(r), apply(a))
        case Pair(f, s)      => Pair(apply(f), apply(s))
        case Rec(n, b)       => Rec(n, apply(b))
        case CellExp(x)      => CellExp(apply(x))
        case BeginExp(a, b)  => BeginExp(apply(a), apply(b))
        case CellFetchExp(x) => CellFetchExp(apply(x))
        case CellStoreExp(c, v) => CellStoreExp(apply(c), apply(v))
        case CellEqExp(a, b) => CellEqExp(apply(a), apply(b))
        case CellPredExp(x)  => CellPredExp(apply(x))

        // FLIC sugar forms.
        case BeginListExp(Nil)        => UnitLit()
        case BeginListExp(List(e))    => apply(e)
        case BeginListExp(e1 :: es)   =>
            BeginExp(apply(e1), apply(BeginListExp(es)))
        case ElselessIfExp(t, th)     => If(apply(t), apply(th), UnitLit())
        case WhileExp(t, b) =>
            // (letrec ((Iloop (abs () (if Etest (begin Ebody (Iloop)) #u)))) (Iloop))
            // — Iloop is fresh. The body is an *application* of Iloop; re-enter
            // apply so the Abs/MultiApp sugar inside the built LetRec becomes
            // kernel Lam/App (evalLetRec's pass 1 only binds kernel Lams).
            val loop = fresh()
            apply(LetRec(
                List((loop, Abs(Nil, If(apply(t), BeginExp(apply(b), MultiApp(Var(loop), Nil)), UnitLit())))),
                MultiApp(Var(loop), Nil)))

        // @-sugar: the four cell primops become FLICK kernel nodes; the rest
        // are FL primops.
        case SugaredPrimOp(op, args) => op match {
            case "^" => args.map(apply) match {
                case List(x) => CellFetchExp(x)
                case _ => ErrorExpr(s"arity mismatch: expected 1 argument for ^, got ${args.size}")
            }
            case ":=" => args.map(apply) match {
                case List(c, v) => CellStoreExp(c, v)
                case _ => ErrorExpr(s"arity mismatch: expected 2 arguments for :=, got ${args.size}")
            }
            case "cell=?" => args.map(apply) match {
                case List(a, b) => CellEqExp(a, b)
                case _ => ErrorExpr(s"arity mismatch: expected 2 arguments for cell=?, got ${args.size}")
            }
            case "cell?" => args.map(apply) match {
                case List(x) => CellPredExp(x)
                case _ => ErrorExpr(s"arity mismatch: expected 1 argument for cell?, got ${args.size}")
            }
            case _ => PrimOpTag.fromName(op) match {
                case Some(tag) => PrimOp(tag, args.map(apply))
                case None      => ErrorExpr(s"unknown primitive operator: $op")
            }
        }

        // FL sugar forms (Figure 6.4).
        case Abs(Nil, b)          => Lam(fresh(), apply(b))
        case Abs(List(f), b)      => Lam(f, apply(b))
        case Abs(f :: rest, b)    => Lam(f, apply(Abs(rest, b)))

        case MultiApp(r, Nil)       => App(apply(r), UnitLit())
        case MultiApp(r, a :: Nil)  => App(apply(r), apply(a))
        case MultiApp(r, a1 :: a2 :: rest) =>
            apply(MultiApp(App(apply(r), apply(a1)), a2 :: rest))

        case ListExpr(Nil)          => UnitLit()
        case ListExpr(e :: rest)    => Pair(apply(e), apply(ListExpr(rest)))

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
            // (letrec ((proc (abs (I*) body))) (proc E*))
            apply(LetRec(List((proc, Abs(binds.map(_._1), body))),
                         MultiApp(Var(proc), binds.map(_._2))))

        // Should not occur inside an expression; handled by the program runner.
        case _: UnsugaredProgram | _: SugaredProgram =>
            ErrorExpr("internal: program in expression position")
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
