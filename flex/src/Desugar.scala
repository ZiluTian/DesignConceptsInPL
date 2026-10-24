package DSL.flex

import DSL.fl._

// The desugaring function for FLEX: it maps FLEX expressions (kernel + sugar)
// to full-FLEX kernel expressions by removing the syntactic sugar. It is the
// identity on kernel expressions.
//
// The sugar (Figures 11.2, 11.21, and 11.24 of the book):
//
//   DS[[(@O E*)]]                  = (prim O E*)          { O a FLEX primop }
//   DS[[(cond (T E) ... (else D))]] = as in FL (nested if)
//   DS[[(scand E*)]]               = short-circuit conjunction (as in FL)
//   DS[[(scor E*)]]                = short-circuit disjunction (as in FL)
//   DS[[(let-type ((tau T)*) E)]]  = [T/tau]E            { simultaneous }
//   DS[[(let-type* ((tau T)*) E)]] = nested let-type      { sequential }
//   DS[[(begin E1 E2)]]            = (let ((Ifresh E1)) E2)
//   DS[[(list T)]]                 = (null T)
//   DS[[(list T E Erest*)]]        = (cons E (list T Erest*))
//
// (The flex-program sugar — def, def-type, and the standard-library let — is
// handled by the program checker, per Figure 11.2.)
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
        s"@@flex_fresh_$counter"
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

        case LetTypeExp(binds, body) =>
            Subst.substSimExp(binds, body)

        case LetTypeStarExp(binds, body) =>
            binds match {
                case Nil => apply(body)
                case (tau, td) :: rest =>
                    // The substitution applies to the remaining definitions as
                    // well as the body (let-type* desugars to nested let-type).
                    apply(LetTypeStarExp(
                        rest.map { case (n, d) => (n, Subst.substType(td, tau, d)) },
                        Subst.substExp(td, tau, body)))
            }

        case BeginExp(e1, e2) =>
            // (begin E1 E2) -> (let ((Ifresh E1)) E2)
            Let(List((fresh(), apply(e1))), apply(e2))

        case ListExp(t, es) =>
            es match {
                case Nil => NullExp(t)
                case e :: rest => ConsExp(apply(e), apply(ListExp(t, rest)))
            }

        // Should not occur inside a FLEX expression.
        case _ => FlexError("internal error: non-FLEX expression node", TBase("unit"))
    }
}
