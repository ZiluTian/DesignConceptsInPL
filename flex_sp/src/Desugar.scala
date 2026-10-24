package DSL.flex_sp

import DSL.fl._
import DSL.flex._

// The desugaring function for FLEX/SP: the FLEX desugaring (Figures 11.2,
// 11.21, and 11.24 of the book) extended with the two FLEX/SP kernel forms
// (Figure 12.9), which are already in kernel form:
//
//   DS[[(pabs (τ*) E)]]  = (pabs (τ*) DS[[E]])
//   DS[[(pcall E T*)]]   = (pcall DS[[E]] T*)
//
// The let-type / let-type* sugar of FLEX desugars to a type substitution.
// In FLEX/SP that substitution must also descend into pabs bodies and pcall
// type arguments (DSL.flex.Subst does not know those forms), so this module
// carries the FLEX/SP substitution walkers (substTypeDefsExp and
// substSimTypeDefsExp below). They are binder-aware: a pabs-bound type
// identifier shadows the substituted identifier in the pabs body.
//
// (The flex/SP program sugar — def, def-type, def-datatype, and the
// standard-library let — is handled by the program checker, per Figure 11.2.)
object Desugar {

    // The primitive operators available in FLEX: the usual FL primops except
    // the type predicates and the pair operators (Figure 11.1: "no type
    // predicates or pair operators"; fst/snd are separate kernel forms in
    // full FLEX, Figure 11.15).
    val legalPrimops: Set[String] =
        Set("not", "and", "or", "bool=?", "=", "!=", "<", "<=", ">", ">=",
            "+", "-", "*", "/", "%", "sym=?")

    private var counter = 0
    private def fresh(): String = {
        counter += 1
        s"@@flexsp_fresh_$counter"
    }

    def apply(e: Exp): Exp = e match {
        // Leaves: unchanged.
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions.
        case FlexError(m, t) => FlexError(m, t)
        case If(t1, t2, t3) => If(apply(t1), apply(t2), apply(t3))
        case PrimOp(op, args) => PrimOp(op, args.map(apply))
        case AbsExp(params, body) => AbsExp(params, apply(body))
        case AppExp(r, args) => AppExp(apply(r), args.map(apply))
        case Let(binds, body) =>
            Let(binds.map { case (n, e2) => (n, apply(e2)) }, apply(body))
        case LetRecExp(bs, body) =>
            LetRecExp(bs.map { case (n, t, e2) => (n, t, apply(e2)) }, apply(body))
        case TheExp(t, e2) => TheExp(t, apply(e2))
        case Pair(f, s) => Pair(apply(f), apply(s))
        case FstExp(e2) => FstExp(apply(e2))
        case SndExp(e2) => SndExp(apply(e2))
        case ProdExp(cs) => ProdExp(cs.map(apply))
        case GetExp(n, e2) => GetExp(n, apply(e2))
        case SeqExp(cs) => SeqExp(cs.map(apply))
        case SeqGetExp(i, s) => SeqGetExp(apply(i), apply(s))
        case SeqSizeExp(e2) => SeqSizeExp(apply(e2))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, apply(e2)) })
        case SelectExp(n, e2) => SelectExp(n, apply(e2))
        case WithExp(r, b) => WithExp(apply(r), apply(b))
        case OneExp(t, tag, p) => OneExp(t, tag, apply(p))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(apply(d), pn, cs.map { case (n, e2) => (n, apply(e2)) }, el.map(apply))
        case ConsExp(h, t2) => ConsExp(apply(h), apply(t2))
        case CarExp(e2) => CarExp(apply(e2))
        case CdrExp(e2) => CdrExp(apply(e2))
        case NullExp(t) => NullExp(t)
        case NullQExp(e2) => NullQExp(apply(e2))
        case SetExp(n, e2) => SetExp(n, apply(e2))
        case CellExp(e2) => CellExp(apply(e2))
        case DerefExp(e2) => DerefExp(apply(e2))
        case CellSetExp(c, e2) => CellSetExp(apply(c), apply(e2))
        case CellEqExp(e1, e2) => CellEqExp(apply(e1), apply(e2))

        // FLEX/SP kernel forms (Figure 12.9).
        case PabsExp(vs, body) => PabsExp(vs, apply(body))
        case PcallExp(e2, ts) => PcallExp(apply(e2), ts)

        // Sugar forms (Figures 11.2, 11.21, 11.24).
        case SugaredPrimOp(op, args) =>
            if (legalPrimops.contains(op))
                PrimOp(PrimOpTag.fromName(op).get, args.map(apply))
            else
                FlexError(s"$op is not a FLEX primitive operator", TBase("unit"))

        case Cond(branches, d) =>
            branches match {
                case Nil => d map (apply(_)) getOrElse FlexError("cond: no branches and no else", TBase("unit"))
                case (t, th) :: rest => If(apply(t), apply(th), apply(Cond(rest, d)))
            }

        case Scand(es) =>
            es match {
                case Nil => BoolLit(true)
                case e :: rest => If(apply(e), apply(Scand(rest)), BoolLit(false))
            }

        case Scor(es) =>
            es match {
                case Nil => BoolLit(false)
                case e :: rest => If(apply(e), BoolLit(true), apply(Scor(rest)))
            }

        case LetTypeExp(binds, body) => substSimTypeDefsExp(binds, body)

        case LetTypeStarExp(binds, body) =>
            binds match {
                case Nil => apply(body)
                case (tau, td) :: rest =>
                    // The substitution applies to the remaining definitions as
                    // well as the body (let-type* desugars to nested let-type).
                    apply(LetTypeStarExp(
                        rest.map { case (n, d) => (n, Subst.substType(td, tau, d)) },
                        substTypeDefsExp(td, tau, body)))
            }

        case BeginExp(e1, e2) =>
            // (begin E1 E2) -> (let ((Ifresh E1)) E2)
            Let(List((fresh(), apply(e1))), apply(e2))

        case ListExp(t, es) =>
            es match {
                case Nil => NullExp(t)
                case e :: rest => ConsExp(apply(e), apply(ListExp(t, rest)))
            }

        // Should not occur inside a FLEX/SP expression.
        case _ => FlexError("internal error: non-FLEX/SP expression node", TBase("unit"))
    }

    // ------------------------------------------------------------------
    // Type substitution for FLEX/SP expressions (the FLEX/SP version of
    // DSL.flex.Subst's expression substitution, which does not know the
    // pabs / pcall forms). A pabs binding shadows the substituted
    // identifier in the pabs body.
    // ------------------------------------------------------------------

    // [T/tau]E (Figure 11.5), the FLEX/SP expression version.
    def substTypeDefsExp(repl: T, tau: String, e: Exp): Exp =
        goExp(repl, tau, e, Set.empty)

    private def goExp(repl: T, tau: String, e: Exp, shadowed: Set[String]): Exp = e match {
        // Leaves: unchanged (types cannot harbor value identifiers, and
        // literals carry no types).
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions and type annotations.
        case FlexError(m, t) => FlexError(m, Subst.substType(repl, tau, t, shadowed))
        case If(t1, t2, t3) => If(goExp(repl, tau, t1, shadowed), goExp(repl, tau, t2, shadowed), goExp(repl, tau, t3, shadowed))
        case PrimOp(op, args) => PrimOp(op, args.map(goExp(repl, tau, _, shadowed)))
        case AbsExp(params, body) =>
            AbsExp(params.map { case (n, t) => (n, Subst.substType(repl, tau, t, shadowed)) },
                   goExp(repl, tau, body, shadowed))
        case AppExp(r, args) => AppExp(goExp(repl, tau, r, shadowed), args.map(goExp(repl, tau, _, shadowed)))
        case Let(binds, body) =>
            Let(binds.map { case (n, e2) => (n, goExp(repl, tau, e2, shadowed)) },
                goExp(repl, tau, body, shadowed))
        case LetRecExp(bs, body) =>
            LetRecExp(bs.map { case (n, t, e2) => (n, Subst.substType(repl, tau, t, shadowed), goExp(repl, tau, e2, shadowed)) },
                      goExp(repl, tau, body, shadowed))
        case TheExp(t, e2) => TheExp(Subst.substType(repl, tau, t, shadowed), goExp(repl, tau, e2, shadowed))
        case Pair(f, s) => Pair(goExp(repl, tau, f, shadowed), goExp(repl, tau, s, shadowed))
        case FstExp(e2) => FstExp(goExp(repl, tau, e2, shadowed))
        case SndExp(e2) => SndExp(goExp(repl, tau, e2, shadowed))
        case ProdExp(cs) => ProdExp(cs.map(goExp(repl, tau, _, shadowed)))
        case GetExp(n, e2) => GetExp(n, goExp(repl, tau, e2, shadowed))
        case SeqExp(cs) => SeqExp(cs.map(goExp(repl, tau, _, shadowed)))
        case SeqGetExp(i, s) => SeqGetExp(goExp(repl, tau, i, shadowed), goExp(repl, tau, s, shadowed))
        case SeqSizeExp(e2) => SeqSizeExp(goExp(repl, tau, e2, shadowed))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, goExp(repl, tau, e2, shadowed)) })
        case SelectExp(n, e2) => SelectExp(n, goExp(repl, tau, e2, shadowed))
        case WithExp(r, b) => WithExp(goExp(repl, tau, r, shadowed), goExp(repl, tau, b, shadowed))
        case OneExp(t, tag, p) => OneExp(Subst.substType(repl, tau, t, shadowed), tag, goExp(repl, tau, p, shadowed))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(goExp(repl, tau, d, shadowed), pn,
                       cs.map { case (n, e2) => (n, goExp(repl, tau, e2, shadowed)) },
                       el.map(goExp(repl, tau, _, shadowed)))
        case ConsExp(h, t2) => ConsExp(goExp(repl, tau, h, shadowed), goExp(repl, tau, t2, shadowed))
        case CarExp(e2) => CarExp(goExp(repl, tau, e2, shadowed))
        case CdrExp(e2) => CdrExp(goExp(repl, tau, e2, shadowed))
        case NullExp(t) => NullExp(Subst.substType(repl, tau, t, shadowed))
        case NullQExp(e2) => NullQExp(goExp(repl, tau, e2, shadowed))
        case SetExp(n, e2) => SetExp(n, goExp(repl, tau, e2, shadowed))
        case CellExp(e2) => CellExp(goExp(repl, tau, e2, shadowed))
        case DerefExp(e2) => DerefExp(goExp(repl, tau, e2, shadowed))
        case CellSetExp(c, e2) => CellSetExp(goExp(repl, tau, c, shadowed), goExp(repl, tau, e2, shadowed))
        case CellEqExp(e1, e2) => CellEqExp(goExp(repl, tau, e1, shadowed), goExp(repl, tau, e2, shadowed))

        // FLEX/SP forms (Figure 12.9): the pabs variables shadow tau in the
        // pabs body; the pcall type arguments are ordinary type positions.
        case PabsExp(vs, body) => PabsExp(vs, goExp(repl, tau, body, shadowed ++ vs.toSet))
        case PcallExp(e2, ts) =>
            PcallExp(goExp(repl, tau, e2, shadowed),
                     ts.map(t => Subst.substType(repl, tau, t, shadowed)))

        // Sugar forms: recurse (and into their type annotations / bindings).
        case SugaredPrimOp(op, args) => SugaredPrimOp(op, args.map(goExp(repl, tau, _, shadowed)))
        case Cond(branches, d) =>
            Cond(branches.map { case (t1, th) => (goExp(repl, tau, t1, shadowed), goExp(repl, tau, th, shadowed)) },
                 d.map(goExp(repl, tau, _, shadowed)))
        case Scand(es) => Scand(es.map(goExp(repl, tau, _, shadowed)))
        case Scor(es) => Scor(es.map(goExp(repl, tau, _, shadowed)))
        case BeginExp(e1, e2) => BeginExp(goExp(repl, tau, e1, shadowed), goExp(repl, tau, e2, shadowed))
        case ListExp(t, es) => ListExp(Subst.substType(repl, tau, t, shadowed), es.map(goExp(repl, tau, _, shadowed)))
        case LetTypeExp(binds, body) =>
            LetTypeExp(binds.map { case (n, d) => (n, Subst.substType(repl, tau, d, shadowed)) },
                       goExp(repl, tau, body, shadowed))
        case LetTypeStarExp(binds, body) =>
            LetTypeStarExp(binds.map { case (n, d) => (n, Subst.substType(repl, tau, d, shadowed)) },
                           goExp(repl, tau, body, shadowed))

        // Non-FLEX nodes (e.g. FL kernel forms built by hand): types cannot
        // harbor value identifiers, so they are returned unchanged.
        case e => e
    }

    // [T1/tau1, ..., Tn/taun]E (Figure 11.2), the FLEX/SP expression
    // version, applied simultaneously.
    def substSimTypeDefsExp(binds: List[(String, T)], e: Exp): Exp =
        goSimExp(binds, e, Set.empty)

    private def goSimExp(binds: List[(String, T)], e: Exp, shadowed: Set[String]): Exp = e match {
        // Leaves: unchanged.
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions and type annotations.
        case FlexError(m, t) => FlexError(m, Subst.substSim(binds, t, shadowed))
        case If(t1, t2, t3) => If(goSimExp(binds, t1, shadowed), goSimExp(binds, t2, shadowed), goSimExp(binds, t3, shadowed))
        case PrimOp(op, args) => PrimOp(op, args.map(goSimExp(binds, _, shadowed)))
        case AbsExp(params, body) =>
            AbsExp(params.map { case (n, t) => (n, Subst.substSim(binds, t, shadowed)) },
                   goSimExp(binds, body, shadowed))
        case AppExp(r, args) => AppExp(goSimExp(binds, r, shadowed), args.map(goSimExp(binds, _, shadowed)))
        case Let(binds2, body) =>
            Let(binds2.map { case (n, e2) => (n, goSimExp(binds, e2, shadowed)) },
                goSimExp(binds, body, shadowed))
        case LetRecExp(bs, body) =>
            LetRecExp(bs.map { case (n, t, e2) => (n, Subst.substSim(binds, t, shadowed), goSimExp(binds, e2, shadowed)) },
                      goSimExp(binds, body, shadowed))
        case TheExp(t, e2) => TheExp(Subst.substSim(binds, t, shadowed), goSimExp(binds, e2, shadowed))
        case Pair(f, s) => Pair(goSimExp(binds, f, shadowed), goSimExp(binds, s, shadowed))
        case FstExp(e2) => FstExp(goSimExp(binds, e2, shadowed))
        case SndExp(e2) => SndExp(goSimExp(binds, e2, shadowed))
        case ProdExp(cs) => ProdExp(cs.map(goSimExp(binds, _, shadowed)))
        case GetExp(n, e2) => GetExp(n, goSimExp(binds, e2, shadowed))
        case SeqExp(cs) => SeqExp(cs.map(goSimExp(binds, _, shadowed)))
        case SeqGetExp(i, s) => SeqGetExp(goSimExp(binds, i, shadowed), goSimExp(binds, s, shadowed))
        case SeqSizeExp(e2) => SeqSizeExp(goSimExp(binds, e2, shadowed))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, goSimExp(binds, e2, shadowed)) })
        case SelectExp(n, e2) => SelectExp(n, goSimExp(binds, e2, shadowed))
        case WithExp(r, b) => WithExp(goSimExp(binds, r, shadowed), goSimExp(binds, b, shadowed))
        case OneExp(t, tag, p) => OneExp(Subst.substSim(binds, t, shadowed), tag, goSimExp(binds, p, shadowed))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(goSimExp(binds, d, shadowed), pn,
                       cs.map { case (n, e2) => (n, goSimExp(binds, e2, shadowed)) },
                       el.map(goSimExp(binds, _, shadowed)))
        case ConsExp(h, t2) => ConsExp(goSimExp(binds, h, shadowed), goSimExp(binds, t2, shadowed))
        case CarExp(e2) => CarExp(goSimExp(binds, e2, shadowed))
        case CdrExp(e2) => CdrExp(goSimExp(binds, e2, shadowed))
        case NullExp(t) => NullExp(Subst.substSim(binds, t, shadowed))
        case NullQExp(e2) => NullQExp(goSimExp(binds, e2, shadowed))
        case SetExp(n, e2) => SetExp(n, goSimExp(binds, e2, shadowed))
        case CellExp(e2) => CellExp(goSimExp(binds, e2, shadowed))
        case DerefExp(e2) => DerefExp(goSimExp(binds, e2, shadowed))
        case CellSetExp(c, e2) => CellSetExp(goSimExp(binds, c, shadowed), goSimExp(binds, e2, shadowed))
        case CellEqExp(e1, e2) => CellEqExp(goSimExp(binds, e1, shadowed), goSimExp(binds, e2, shadowed))

        // FLEX/SP forms (Figure 12.9).
        case PabsExp(vs, body) => PabsExp(vs, goSimExp(binds, body, shadowed ++ vs.toSet))
        case PcallExp(e2, ts) =>
            PcallExp(goSimExp(binds, e2, shadowed),
                     ts.map(t => Subst.substSim(binds, t, shadowed)))

        // Sugar forms: recurse (and into their type annotations / bindings).
        case SugaredPrimOp(op, args) => SugaredPrimOp(op, args.map(goSimExp(binds, _, shadowed)))
        case Cond(branches, d) =>
            Cond(branches.map { case (t1, th) => (goSimExp(binds, t1, shadowed), goSimExp(binds, th, shadowed)) },
                 d.map(goSimExp(binds, _, shadowed)))
        case Scand(es) => Scand(es.map(goSimExp(binds, _, shadowed)))
        case Scor(es) => Scor(es.map(goSimExp(binds, _, shadowed)))
        case BeginExp(e1, e2) => BeginExp(goSimExp(binds, e1, shadowed), goSimExp(binds, e2, shadowed))
        case ListExp(t, es) => ListExp(Subst.substSim(binds, t, shadowed), es.map(goSimExp(binds, _, shadowed)))
        case LetTypeExp(binds2, body) =>
            LetTypeExp(binds2.map { case (n, d) => (n, Subst.substSim(binds, d, shadowed)) },
                       goSimExp(binds, body, shadowed))
        case LetTypeStarExp(binds2, body) =>
            LetTypeStarExp(binds2.map { case (n, d) => (n, Subst.substSim(binds, d, shadowed)) },
                           goSimExp(binds, body, shadowed))

        // Non-FLEX nodes: returned unchanged.
        case e => e
    }
}
