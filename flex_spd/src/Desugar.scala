package DSL.flex_spd

import DSL.fl._
import DSL.flex._
import DSL.flex_sp._

// The desugaring function for FLEX/SPD: the FLEX desugaring (Figures 11.2
// and 11.21) restricted to the sugar forms that remain in FLEX/SPD (the cond
// / scand / scor / begin / @primop forms). The list sugar (Figure 11.24) and
// the let-type / let-type* sugar are replaced in FLEX/SPD by the
// standard-library values and by plet / pletrec (Figure 12.19). The plet /
// pletrec forms are already in kernel form for the checker, which realizes
// their transparency by extending the description environment (Figure 12.18).
//
// (The flex/SPD program sugar — def, def-desc, def-datatype, and the
// standard library — is handled by the program checker, per Figure 12.19.)
object Desugar {

    // The primitive operators available in FLEX: the usual FL primops except
    // the type predicates and the pair operators (Figure 11.1: "no type
    // predicates or pair operators").
    val legalPrimops: Set[String] =
        Set("not", "and", "or", "bool=?", "=", "!=", "<", "<=", ">", ">=",
            "+", "-", "*", "/", "%", "sym=?")

    private var counter = 0
    private def fresh(): String = {
        counter += 1
        s"@@flexspd_fresh_$counter"
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
        case SetExp(n, e2) => SetExp(n, apply(e2))
        case CellExp(e2) => CellExp(apply(e2))
        case DerefExp(e2) => DerefExp(apply(e2))
        case CellSetExp(c, e2) => CellSetExp(apply(c), apply(e2))
        case CellEqExp(e1, e2) => CellEqExp(apply(e1), apply(e2))

        // FLEX/SP kernel forms (Figure 12.9).
        case PabsExp(vs, body) => PabsExp(vs, apply(body))
        case PcallExp(e2, ts) => PcallExp(apply(e2), ts)

        // FLEX/SPD description bindings (Figure 12.18): the bindings are
        // descriptions (type-level), so only the body is desugared.
        case PletExp(bs, body) => PletExp(bs, apply(body))
        case PletRecExp(bs, body) => PletRecExp(bs, apply(body))

        // Sugar forms (Figures 11.2 and 11.21).
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

        case BeginExp(e1, e2) =>
            // (begin E1 E2) -> (let ((Ifresh E1)) E2)
            Let(List((fresh(), apply(e1))), apply(e2))

        // Should not occur inside a FLEX/SPD expression (the parser does not
        // produce the list / pair kernel forms or the let-type / list sugar).
        case _ => FlexError("internal error: non-FLEX/SPD expression node", TBase("unit"))
    }
}
