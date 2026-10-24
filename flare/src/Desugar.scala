package DSL.flare

import DSL.fl._

// The desugaring of the full FLARE language (Figure 13.23 of the book): it
// maps FLARE expressions (kernel + sugar) to kernel expressions. It is the
// identity on kernel expressions and removes the sugar:
//
//   DS[[(@O E*)]]                 = (prim O E*)
//   DS[[(cond (T E) ... )]]       = nested if          (as in FL)
//   DS[[(scand E*)]]             = short-circuit conjunction (as in FL)
//   DS[[(scor E*)]]              = short-circuit disjunction (as in FL)
//   DS[[(recur P ((I E)*) B)]]   = (letrec ((P (abs (I*) B))) (P E*))
//   DS[[(begin E1 E2)]]          = (let ((_ E1)) E2), _ fresh and unreferenced
//   DS[[(list)]]                 = (prim null)
//   DS[[(list E1 Erest*)]]       = (prim cons E1 (list Erest*))
//
// Unlike FL, multi-parameter abstractions (abs) and multi-argument
// applications are KERNEL forms in FLARE, so Abs / MultiApp pass through
// unchanged, and let / letrec are kernel forms as well.
//
// The full-FLARE program desugaring (Figure 13.23) is
//
//   (flare (I*) Ebody (def I E)*)
//     -> (flarek (I*) (letrec {Standard library bindings}
//                       (letrec ((I E)*) Ebody)))
//
// where the standard library binds a wrapper procedure for every FLARE
// primop plus true / false.

object Desugar {

    private var counter = 0
    private def fresh(): String = {
        counter += 1
        s"@@flare_fresh_$counter"
    }

    def apply(e: Exp): Exp = e match {
        // Leaves and kernel forms: unchanged / recurse.
        case e: UnitLit    => e
        case e: BoolLit    => e
        case e: IntLit     => e
        case e: Sym        => e
        case e: Var        => e
        case e: ErrorExpr  => e
        case If(t, th, el) => If(apply(t), apply(th), apply(el))
        case p: FlarePrim  => FlarePrim(p.op, p.args.map(apply))
        case Lam(f, b)     => Lam(f, apply(b))
        case App(r, a)     => App(apply(r), apply(a))
        case Abs(fs, b)    => Abs(fs, apply(b))
        case MultiApp(r, as) => MultiApp(apply(r), as.map(apply))
        case Let(bs, b)    => Let(bs.map { case (n, e) => (n, apply(e)) }, apply(b))
        case LetRec(bs, b) => LetRec(bs.map { case (n, e) => (n, apply(e)) }, apply(b))

        // Sugar forms.
        case SugaredPrimOp(op, args) => FlarePrim(op, args.map(apply))

        case Cond(Nil, Some(d)) => apply(d)
        case Cond((t, th) :: rest, d) => If(apply(t), apply(th), apply(Cond(rest, d)))
        case Cond(Nil, None) => ErrorExpr("cond: no branches and no else")

        case Scand(Nil)     => BoolLit(true)
        case Scand(e :: rest) => If(apply(e), apply(Scand(rest)), BoolLit(false))
        case Scor(Nil)      => BoolLit(false)
        case Scor(e :: rest) => If(apply(e), BoolLit(true), apply(Scor(rest)))

        case Recur(proc, binds, body) =>
            // (letrec ((proc (abs (I*) body))) (proc E*))
            apply(LetRec(List((proc, Abs(binds.map(_._1), body))),
                         MultiApp(Var(proc), binds.map(_._2))))

        case BeginExp(e1, e2) =>
            // (begin E1 E2) -> (let ((_ E1)) E2)
            Let(List((fresh(), apply(e1))), apply(e2))

        case ListExpr(es) =>
            es match {
                case Nil => FlarePrim("null", Nil)
                case e :: rest =>
                    FlarePrim("cons", List(apply(e), apply(ListExpr(rest))))
            }

        // Unreachable via the FLARE parser (pair is a primop, not a
        // keyword), but desugar it for completeness.
        case Pair(f, s) => FlarePrim("pair", List(apply(f), apply(s)))

        case _ => ErrorExpr("internal error: non-FLARE expression node")
    }

    // ------------------------------------------------------------------
    // Program desugaring (Figure 13.23)
    // ------------------------------------------------------------------

    def program(body: Exp, defs: List[(String, Exp)]): Exp =
        LetRec(stdlib, LetRec(defs.map { case (n, e) => (n, apply(e)) }, apply(body)))

    // The standard library bindings (Figures 13.1 / 13.23): a wrapper
    // procedure for every FLARE primitive operator, plus true / false as
    // synonyms for the boolean literals. None of these bindings is
    // recursive.
    val stdlib: List[(String, Exp)] = {
        def wrap1(op: String): (String, Exp) =
            (op, Abs(List("x"), FlarePrim(op, List(Var("x")))))
        def wrap2(op: String): (String, Exp) =
            (op, Abs(List("x", "y"), FlarePrim(op, List(Var("x"), Var("y")))))
        List(
            wrap1("not"), wrap2("and"), wrap2("or"), wrap2("bool=?"),
            wrap2("="), wrap2("!="), wrap2("<"), wrap2("<="), wrap2(">"), wrap2(">="),
            wrap2("+"), wrap2("-"), wrap2("*"), wrap2("/"), wrap2("%"), wrap2("sym=?"),
            wrap2("pair"), wrap1("fst"), wrap1("snd"),
            wrap2("cons"), wrap1("car"), wrap1("cdr"),
            ("null", Abs(Nil, FlarePrim("null", Nil))),
            wrap1("null?"),
            wrap1("cell"), wrap1("^"), wrap2(":="), wrap2("cell=?"),
            ("true", BoolLit(true)),
            ("false", BoolLit(false))
        )
    }
}
