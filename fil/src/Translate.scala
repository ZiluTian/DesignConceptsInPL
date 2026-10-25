package DSL.fil

import DSL.fl._
import DSL.flare.{
    FlarePrim, FlareKernelProgram, FlareSugarProgram,
    FlareProgram, Desugar => FlareDesugar
}

// The Translation stage (Section 17.7.2 of the book, Figure 17.16): Tprog
// and Texp translate a kernel FLARE program into a FIL program.
//
// Preconditions (Tprog): the input is a valid, CLOSED, ASSIGNMENT-FREE
// kernel FLARE program — a FLARE expression built from the literals, Var,
// ErrorExpr, If, Abs, MultiApp, Let, LetRec, and FlarePrim (i.e. the
// output of the desugaring stage, after globalization has eliminated free
// standard-library identifiers). All valid FIL programs are necessarily
// closed, so the postcondition need not restate it. (Assignment-free: the
// assignment-conversion stage — which turns every name assigned via set!
// into a cell — must have run before the Translation; set! has no Texp
// case.)
//
// The translation is purely structural except that:
//
//   1. Tprog changes the program tag from flarek to fil;
//   2. Texp adds the explicit app keyword to applications:
//          (Erator E*)  ->  (app Texp[Erator] (Texp[Ei])*)
//   3. Texp transforms each letrec into a let that binds each name to a
//      one-slot mutable product (a cell) and rewrites every reference to a
//      letrec-bound name I through (mget 1) I:
//
//        (letrec ((I1 E1) ... (In En)) Ebody)
//          -> (let ((I1 (prim mprod #u)) ... (In (prim mprod #u)))
//                 (let* (($_i (prim (mset! 1) Ii (msubst Texp[Ei])))ni=1)
//                    (msubst Texp[Ebody])))
//             where msubst E = ([(prim (mget 1) Ii)/Ii]ni=1)E
//
//      One rule that performs three conceptually distinct steps (page 1037):
//      (1) the FLAVAR letrec desugaring (bind each name to #u and set! the
//      definition expression into it), (2) the assignment conversion (turn
//      the mutable names into cells), and (3) the representation of those
//      cells as one-slot mutable products. The first step is not
//      well-typedness-preserving as a FLARE/V-to-FLARE/V transformation (a
//      variable holding #u cannot be assigned an arbitrary value) — one
//      of several cases that is simpler to express in FIL, without a formal
//      type system, which is the main reason the compiler uses FIL.
//   4. Texp translates FLARE's cells and immutable pairs to FIL mutable
//      products:
//
//        (prim cell E)      -> (prim mprod Texp[E])
//        (prim ^ E)         -> (prim (mget 1) Texp[E])
//        (prim := E Enew)   -> (prim (mset! 1) Texp[E] Texp[Enew])
//        (prim cell=? E E)  -> (prim mprod=? Texp[E1] Texp[E2])
//        (prim pair E E)    -> (prim mprod Texp[E1] Texp[E2])
//        (prim fst E)       -> (prim (mget 1) Texp[E])
//        (prim snd E)       -> (prim (mget 2) Texp[E])
//
// The output is run through Desugar (the Figure 17.15 simplifications are
// performed when FIL ASTs are constructed), so the result never contains
// the trivial lets / eta-expandable abstractions the translation can
// introduce.
object Translate {

    // Texp: ExpFLARE -> ExpFIL
    def Texp(e: Exp): Exp = DSL.fil.Desugar(texp(e))

    private def texp(e: Exp): Exp = e match {
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: Var | _: ErrorExpr => e
        case If(t, th, el) => If(texp(t), texp(th), texp(el))
        case Abs(fs, b) => Abs(fs, texp(b))
        // (Erator E*) -> (app Texp[Erator] (Texp[Ei])*)
        case MultiApp(rator, rands) =>
            FilApp(texp(rator), rands.map(texp))
        // let is structural (a multibinding let is a kernel form in both
        // languages; in both it is a parallel binding).
        case Let(bs, b) =>
            Let(bs.map { case (n, e) => (n, texp(e)) }, texp(b))
        // The letrec -> mutable-product encoding (Figure 17.16).
        case LetRec(bs, b) =>
            val msubst = (x: Exp) => bs.foldLeft(x) { case (acc, (n, _)) =>
                DSL.fil.Desugar.subst(n, FilPrim("mget 1", List(Var(n))))(acc)
            }
            val freshNames = bs.map(_ => DSL.fil.Desugar.freshName())
            Let(
                bs.map { case (n, _) => (n, FilPrim("mprod", List(UnitLit()))) },
                LetStar(
                    bs.zip(freshNames).map { case ((n, e), fn) =>
                        (fn, FilPrim("mset! 1", List(Var(n), msubst(texp(e)))))
                    },
                    msubst(texp(b)))
            )
        // Cell / pair operators -> mutable products (Figure 17.16).
        case FlarePrim(op, args) => op match {
            case "cell"   => FilPrim("mprod", args.map(texp))
            case "^"      => FilPrim("mget 1", args.map(texp))
            case ":="     => FilPrim("mset! 1", args.map(texp))
            case "cell=?" => FilPrim("mprod=?", args.map(texp))
            case "pair"   => FilPrim("mprod", args.map(texp))
            case "fst"    => FilPrim("mget 1", args.map(texp))
            case "snd"    => FilPrim("mget 2", args.map(texp))
            case other    => FilPrim(other, args.map(texp))
        }
        // FL forms that are not kernel FLARE but have a well-defined
        // translation (robustness for hand-built ASTs).
        case Lam(f, b)  => Abs(List(f), texp(b))
        case App(r, a)  => FilApp(texp(r), List(texp(a)))
        case Pair(f, s) => FilPrim("mprod", List(texp(f), texp(s)))
        case _ => ErrorExpr("internal error: non-FLARE expression in translation")
    }

    // Tprog: ProgFLARE -> ProgFIL
    //   (flarek (I*) Ebody)  ->  (fil (I*) (Texp[Ebody]))
    def Tprog(p: FlareKernelProgram): FilProgram =
        FilProgram(p.formals, Texp(p.body))

    // Parse a FLARE program (kernel or sugar tag) and translate it.
    //
    //   - a `flarek` program: its body is desugared (the kernel desugaring
    //     is the identity on a pure kernel body) and translated;
    //   - a `flare` program: the full-FLARE program desugaring (Figure
    //     13.23) is applied first — the standard-library wrapper and the
    //     top-level defs become explicit letrecs, exactly as the book's
    //     desugaring + globalization produce before the Translation.
    def translate(input: String): Option[FilProgram] =
        FlareProgram(input) match {
            case Some(k: FlareKernelProgram) =>
                Some(Tprog(FlareKernelProgram(k.formals, FlareDesugar(k.body))))
            case Some(s: FlareSugarProgram) =>
                Some(Tprog(FlareKernelProgram(s.formals,
                    FlareDesugar.program(s.body, s.defs))))
            case _ => None
        }
}
