package DSL.flare_v

import DSL.fl._
import DSL.flare.{FlarePrim, BeginExp, Desugar => FlareDesugar}

// The desugaring of the full-FLARE/V language (Figures 17.2 / 17.3 of the
// book): it maps FLARE/V expressions (kernel + sugar) to kernel expressions.
//
// It is FLARE's desugaring (Figure 13.23) with one addition: `set!` is a
// **kernel** form in FLARE/V (Figure 17.2), so a SetBang node passes through
// unchanged (exactly like `let` / `letrec` / `abs` / multi-application).
//
//   DS[[(@O E*)]]                 = (prim O E*)
//   DS[[(cond (T E) ... )]]       = nested if          (as in FL)
//   DS[[(scand E*)]]             = short-circuit conjunction (as in FL)
//   DS[[(scor E*)]]              = short-circuit disjunction (as in FL)
//   DS[[(recur P ((I E)*) B)]]   = (letrec ((P (abs (I*) B))) (P E*))
//   DS[[(begin E1 E2)]]          = (let ((_ E1)) E2), _ fresh and unreferenced
//   DS[[(list)]]                 = (prim null)
//   DS[[(list E1 Erest*)]]       = (prim cons E1 (list Erest*))
//   DS[[set! I E]]               = (set! I DS[[E]])     (kernel form)
//
// The full-FLARE/V program desugaring (Figure 17.3) is
//
//   (flare (I*) Ebody (def I E)*)
//     -> (flarek (I*) (letrec ((I E)*) Ebody))
//
// and, as in FLARE, the standard library is opened around that so that the
// primitive names (`+`, `cons`, `cell`, ...) resolve to global procedures.
//
// NOTE (book vs. this module): the book says FLARE/V's *desugaring* does not
// introduce the standard-identifier bindings — those are handled by the
// **globalization** compiler transformation (Section 17.4) instead. For the
// *type checker* (the reference static semantics of this module) it is
// equivalent to open the standard library up front, so we do that here (reusing
// FLARE's stdlib), folding the globalization step into the checker's initial
// environment. This keeps the type system identical to FLARE's for every
// program that does not use `set!`.

object FlareVDesugar {

    private var counter = 0
    private def fresh(): String = {
        counter += 1
        s"@@flare_v_fresh_$counter"
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

        // The FLARE/V mutable-variable assignment is a kernel form: recurse
        // into the assigned value only.
        case s: SetBang    => SetBang(s.name, apply(s.e))

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

        // Unreachable via the FLARE/V parser (pair is a primop, not a
        // keyword), but desugar it for completeness.
        case Pair(f, s) => FlarePrim("pair", List(apply(f), apply(s)))

        case _ => ErrorExpr("internal error: non-FLARE/V expression node")
    }

    // ------------------------------------------------------------------
    // Program desugaring (Figure 17.3)
    // ------------------------------------------------------------------

    def program(body: Exp, defs: List[(String, Exp)]): Exp =
        LetRec(FlareDesugar.stdlib, LetRec(defs.map { case (n, e) => (n, apply(e)) }, apply(body)))
}
