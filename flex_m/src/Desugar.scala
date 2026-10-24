package DSL.flex_m

import DSL.fl._
import DSL.flex._
// Explicit import beats the wildcard: DSL.flex also has a Subst object.
import DSL.flex_m.Subst

// Desugars FLEX/M sugar (Figure 15.2 and the FL sugar of Figure 6.3) into
// kernel forms. The desugaring is a walk over the expression tree:
//
//   (letrec ((I T E)*) Ebody)  ->  (open (module (def I T E)*) Ebody)
//   (mselect I Emod)           ->  (open Emod I)
//   (let-type ((τ T)*) Ebody)  ->  [T/τ]Ebody          (simultaneous)
//   (let-type* ((τ T)*) Ebody) ->  nested let-type     (sequential)
//   (cond ...) / (scand ...) / (scor ...) / (begin ...) / @O
//                              ->  If / Let / PrimOp    (the FL sugar, Fig 6.4)
//
// Type substitution (let-type / let-type* / def-type) is carried by the
// MT-aware walkers substTypeDefsExp / substSimTypeDefsExp below; they are
// binder-aware: a pabs-bound type identifier is not substituted in the pabs
// body.

object Desugar {

    // The primitive operators available in FLEX/M: the usual FL primops
    // except the type predicates and the pair operators (FLEX/M has no pair
    // kernel form; fst/snd/cons/... are ordinary value names).
    val legalPrimops: Set[String] =
        Set("not", "and", "or", "bool=?", "=", "!=", "<", "<=", ">", ">=",
            "+", "-", "*", "/", "%", "sym=?")

    private var counter = 0
    private def fresh(): String = {
        counter += 1
        s"@@flexm_fresh_$counter"
    }

    def apply(e: Exp): Exp = e match {
        // Leaves: unchanged.
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions (type annotations are
        // final MTs; the desugaring does not rewrite them).
        case MError(msg, t) => MError(msg, t)
        case If(t1, t2, t3) => If(apply(t1), apply(t2), apply(t3))
        case PrimOp(op, args) => PrimOp(op, args.map(apply))
        case MAbs(params, body) => MAbs(params, apply(body))
        case MApp(r, args) => MApp(apply(r), args.map(apply))
        case Let(bs, body) =>
            Let(bs.map { case (n, e2) => (n, apply(e2)) }, apply(body))
        case MThe(t, e2) => MThe(t, apply(e2))
        case MOne(t, tag, p) => MOne(t, tag, apply(p))
        case MPabs(vs, body) => MPabs(vs, apply(body))
        case MPcall(e2, ts) => MPcall(apply(e2), ts)
        case ProdExp(cs) => ProdExp(cs.map(apply))
        case GetExp(n, e2) => GetExp(n, apply(e2))
        case SeqExp(cs) => SeqExp(cs.map(apply))
        case SeqGetExp(i, s) => SeqGetExp(apply(i), apply(s))
        case SeqSizeExp(e2) => SeqSizeExp(apply(e2))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, apply(e2)) })
        case SelectExp(n, e2) => SelectExp(n, apply(e2))
        case WithExp(r, b) => WithExp(apply(r), apply(b))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(apply(d), pn, cs.map { case (n, e2) => (n, apply(e2)) }, el.map(apply))
        case SetExp(n, e2) => SetExp(n, apply(e2))
        case CellExp(e2) => CellExp(apply(e2))
        case DerefExp(e2) => DerefExp(apply(e2))
        case CellSetExp(c, e2) => CellSetExp(apply(c), apply(e2))
        case CellEqExp(e1, e2) => CellEqExp(apply(e1), apply(e2))

        // FLEX/M module forms (Figure 15.1): recurse.
        case MModule(dts, vds) =>
            MModule(dts, vds.map { vd => MValDef(vd.name, vd.t, apply(vd.e)) })
        case MOpen(emod, body) => MOpen(apply(emod), apply(body))
        case MLoad(file, t) => MLoad(file, t)
        case MMatch(disc, clauses) =>
            MMatch(apply(disc), clauses.map { case (p, b) => (p, apply(b)) })

        // FLEX/M sugar (Figure 15.2).
        case MLetRec(bs, body) =>
            MOpen(MModule(Nil, bs.map { case (n, t, e) => MValDef(n, t, apply(e)) }),
                  apply(body))
        case MMselect(n, emod) => MOpen(apply(emod), Var(n))
        case MLetType(binds, body) => substSimTypeDefsExp(binds, apply(body))
        case MLetTypeStar(binds, body) =>
            binds match {
                case Nil => apply(body)
                case (tau, td) :: rest =>
                    // The substitution applies to the remaining definitions
                    // as well as the body (let-type* desugars to nested
                    // let-type).
                    apply(MLetTypeStar(
                        rest.map { case (n, d) => (n, Subst.substType(td, tau, d)) },
                        substTypeDefsExp(td, tau, body)))
            }

        // FL sugar (Figures 6.3 and 6.4).
        case SugaredPrimOp(op, args) =>
            if (legalPrimops.contains(op))
                PrimOp(PrimOpTag.fromName(op).get, args.map(apply))
            else
                MError(s"$op is not a FLEX/M primitive operator", MTBase("unit"))

        case Cond(branches, d) =>
            branches match {
                case Nil =>
                    d.map(apply).getOrElse(MError("cond: no branches and no else", MTBase("unit")))
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

        // Should not occur inside a FLEX/M expression.
        case _ => MError("internal error: non-FLEX/M expression node", MTBase("unit"))
    }

    // ------------------------------------------------------------------
    // Type substitution for FLEX/M expressions (the FLEX/M version of
    // DSL.flex.Subst's expression substitution). A pabs-bound type
    // identifier is not substituted in the pabs body.
    // ------------------------------------------------------------------

    // [T/tau]E (Figure 15.2), the expression version.
    def substTypeDefsExp(repl: MT, tau: String, e: Exp): Exp =
        goExp(repl, tau, e, Set.empty)

    private def goExp(repl: MT, tau: String, e: Exp, shadowed: Set[String]): Exp = e match {
        // Leaves: unchanged (literals and variables carry no types).
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions and type annotations.
        case MError(m, t) => MError(m, substAt(repl, tau, t, shadowed))
        case If(t1, t2, t3) => If(goExp(repl, tau, t1, shadowed), goExp(repl, tau, t2, shadowed), goExp(repl, tau, t3, shadowed))
        case PrimOp(op, args) => PrimOp(op, args.map(goExp(repl, tau, _, shadowed)))
        case MAbs(params, body) =>
            MAbs(params.map { case (n, t) => (n, substAt(repl, tau, t, shadowed)) },
                 goExp(repl, tau, body, shadowed))
        case MApp(r, args) => MApp(goExp(repl, tau, r, shadowed), args.map(goExp(repl, tau, _, shadowed)))
        case Let(binds, body) =>
            Let(binds.map { case (n, e2) => (n, goExp(repl, tau, e2, shadowed)) },
                goExp(repl, tau, body, shadowed))
        case MThe(t, e2) => MThe(substAt(repl, tau, t, shadowed), goExp(repl, tau, e2, shadowed))
        case MOne(t, tag, p) => MOne(substAt(repl, tau, t, shadowed), tag, goExp(repl, tau, p, shadowed))
        case MPabs(vs, body) => MPabs(vs, goExp(repl, tau, body, shadowed ++ vs.toSet))
        case MPcall(e2, ts) =>
            MPcall(goExp(repl, tau, e2, shadowed),
                   ts.map(t => substAt(repl, tau, t, shadowed)))
        case ProdExp(cs) => ProdExp(cs.map(goExp(repl, tau, _, shadowed)))
        case GetExp(n, e2) => GetExp(n, goExp(repl, tau, e2, shadowed))
        case SeqExp(cs) => SeqExp(cs.map(goExp(repl, tau, _, shadowed)))
        case SeqGetExp(i, s) => SeqGetExp(goExp(repl, tau, i, shadowed), goExp(repl, tau, s, shadowed))
        case SeqSizeExp(e2) => SeqSizeExp(goExp(repl, tau, e2, shadowed))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, goExp(repl, tau, e2, shadowed)) })
        case SelectExp(n, e2) => SelectExp(n, goExp(repl, tau, e2, shadowed))
        case WithExp(r, b) => WithExp(goExp(repl, tau, r, shadowed), goExp(repl, tau, b, shadowed))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(goExp(repl, tau, d, shadowed), pn,
                       cs.map { case (n, e2) => (n, goExp(repl, tau, e2, shadowed)) },
                       el.map(goExp(repl, tau, _, shadowed)))
        case SetExp(n, e2) => SetExp(n, goExp(repl, tau, e2, shadowed))
        case CellExp(e2) => CellExp(goExp(repl, tau, e2, shadowed))
        case DerefExp(e2) => DerefExp(goExp(repl, tau, e2, shadowed))
        case CellSetExp(c, e2) => CellSetExp(goExp(repl, tau, c, shadowed), goExp(repl, tau, e2, shadowed))
        case CellEqExp(e1, e2) => CellEqExp(goExp(repl, tau, e1, shadowed), goExp(repl, tau, e2, shadowed))

        // FLEX/M module forms (Figure 15.1). The data-type component types
        // are type positions too: a let-type / def-type name may occur in
        // a def-datatype component type.
        case MModule(dts, vds) =>
            MModule(dts.map { dt =>
                MDtDef(dt.name, dt.params,
                       dt.ctors.map { case (tag, ts) => tag -> ts.map(t => substAt(repl, tau, t, shadowed)) }) },
                  vds.map { vd =>
                    MValDef(vd.name, substAt(repl, tau, vd.t, shadowed), goExp(repl, tau, vd.e, shadowed)) })
        case MOpen(emod, body) => MOpen(goExp(repl, tau, emod, shadowed), goExp(repl, tau, body, shadowed))
        case MLoad(file, t) => MLoad(file, substAt(repl, tau, t, shadowed))
        case MMatch(disc, clauses) =>
            MMatch(goExp(repl, tau, disc, shadowed),
                   clauses.map { case (p, b) => (p, goExp(repl, tau, b, shadowed)) })

        // Sugar forms: recurse (and into their type annotations / bindings).
        case MLetRec(bs, body) =>
            MLetRec(bs.map { case (n, t, e2) => (n, substAt(repl, tau, t, shadowed), goExp(repl, tau, e2, shadowed)) },
                    goExp(repl, tau, body, shadowed))
        case MMselect(n, emod) => MMselect(n, goExp(repl, tau, emod, shadowed))
        case MLetType(bs, body) =>
            MLetType(bs.map { case (n, t) => (n, substAt(repl, tau, t, shadowed)) },
                     goExp(repl, tau, body, shadowed))
        case MLetTypeStar(bs, body) =>
            MLetTypeStar(bs.map { case (n, t) => (n, substAt(repl, tau, t, shadowed)) },
                         goExp(repl, tau, body, shadowed))
        case SugaredPrimOp(op, args) => SugaredPrimOp(op, args.map(goExp(repl, tau, _, shadowed)))
        case Cond(branches, d) =>
            Cond(branches.map { case (t1, th) => (goExp(repl, tau, t1, shadowed), goExp(repl, tau, th, shadowed)) },
                 d.map(goExp(repl, tau, _, shadowed)))
        case Scand(es) => Scand(es.map(goExp(repl, tau, _, shadowed)))
        case Scor(es) => Scor(es.map(goExp(repl, tau, _, shadowed)))
        case BeginExp(e1, e2) => BeginExp(goExp(repl, tau, e1, shadowed), goExp(repl, tau, e2, shadowed))

        // Non-FLEX/M nodes: returned unchanged.
        case e => e
    }

    // [T1/tau1, ..., Tn/taun]E (Figure 15.2), applied simultaneously.
    def substSimTypeDefsExp(binds: List[(String, MT)], e: Exp): Exp =
        goSimExp(binds, e, Set.empty)

    private def goSimExp(binds: List[(String, MT)], e: Exp, shadowed: Set[String]): Exp = e match {
        // Leaves: unchanged.
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions and type annotations.
        case MError(m, t) => MError(m, substSimAt(binds, t, shadowed))
        case If(t1, t2, t3) => If(goSimExp(binds, t1, shadowed), goSimExp(binds, t2, shadowed), goSimExp(binds, t3, shadowed))
        case PrimOp(op, args) => PrimOp(op, args.map(goSimExp(binds, _, shadowed)))
        case MAbs(params, body) =>
            MAbs(params.map { case (n, t) => (n, substSimAt(binds, t, shadowed)) },
                 goSimExp(binds, body, shadowed))
        case MApp(r, args) => MApp(goSimExp(binds, r, shadowed), args.map(goSimExp(binds, _, shadowed)))
        case Let(binds2, body) =>
            Let(binds2.map { case (n, e2) => (n, goSimExp(binds, e2, shadowed)) },
                goSimExp(binds, body, shadowed))
        case MThe(t, e2) => MThe(substSimAt(binds, t, shadowed), goSimExp(binds, e2, shadowed))
        case MOne(t, tag, p) => MOne(substSimAt(binds, t, shadowed), tag, goSimExp(binds, p, shadowed))
        case MPabs(vs, body) => MPabs(vs, goSimExp(binds, body, shadowed ++ vs.toSet))
        case MPcall(e2, ts) =>
            MPcall(goSimExp(binds, e2, shadowed),
                   ts.map(t => substSimAt(binds, t, shadowed)))
        case ProdExp(cs) => ProdExp(cs.map(goSimExp(binds, _, shadowed)))
        case GetExp(n, e2) => GetExp(n, goSimExp(binds, e2, shadowed))
        case SeqExp(cs) => SeqExp(cs.map(goSimExp(binds, _, shadowed)))
        case SeqGetExp(i, s) => SeqGetExp(goSimExp(binds, i, shadowed), goSimExp(binds, s, shadowed))
        case SeqSizeExp(e2) => SeqSizeExp(goSimExp(binds, e2, shadowed))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, goSimExp(binds, e2, shadowed)) })
        case SelectExp(n, e2) => SelectExp(n, goSimExp(binds, e2, shadowed))
        case WithExp(r, b) => WithExp(goSimExp(binds, r, shadowed), goSimExp(binds, b, shadowed))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(goSimExp(binds, d, shadowed), pn,
                       cs.map { case (n, e2) => (n, goSimExp(binds, e2, shadowed)) },
                       el.map(goSimExp(binds, _, shadowed)))
        case SetExp(n, e2) => SetExp(n, goSimExp(binds, e2, shadowed))
        case CellExp(e2) => CellExp(goSimExp(binds, e2, shadowed))
        case DerefExp(e2) => DerefExp(goSimExp(binds, e2, shadowed))
        case CellSetExp(c, e2) => CellSetExp(goSimExp(binds, c, shadowed), goSimExp(binds, e2, shadowed))
        case CellEqExp(e1, e2) => CellEqExp(goSimExp(binds, e1, shadowed), goSimExp(binds, e2, shadowed))

        // FLEX/M module forms (Figure 15.1). The data-type component types
        // are type positions too (see goExp).
        case MModule(dts, vds) =>
            MModule(dts.map { dt =>
                MDtDef(dt.name, dt.params,
                       dt.ctors.map { case (tag, ts) => tag -> ts.map(t => substSimAt(binds, t, shadowed)) }) },
                  vds.map { vd =>
                    MValDef(vd.name, substSimAt(binds, vd.t, shadowed), goSimExp(binds, vd.e, shadowed)) })
        case MOpen(emod, body) => MOpen(goSimExp(binds, emod, shadowed), goSimExp(binds, body, shadowed))
        case MLoad(file, t) => MLoad(file, substSimAt(binds, t, shadowed))
        case MMatch(disc, clauses) =>
            MMatch(goSimExp(binds, disc, shadowed),
                   clauses.map { case (p, b) => (p, goSimExp(binds, b, shadowed)) })

        // Sugar forms: recurse (and into their type annotations / bindings).
        case MLetRec(bs, body) =>
            MLetRec(bs.map { case (n, t, e2) => (n, substSimAt(binds, t, shadowed), goSimExp(binds, e2, shadowed)) },
                    goSimExp(binds, body, shadowed))
        case MMselect(n, emod) => MMselect(n, goSimExp(binds, emod, shadowed))
        case MLetType(bs, body) =>
            MLetType(bs.map { case (n, t) => (n, substSimAt(binds, t, shadowed)) },
                     goSimExp(binds, body, shadowed))
        case MLetTypeStar(bs, body) =>
            MLetTypeStar(bs.map { case (n, t) => (n, substSimAt(binds, t, shadowed)) },
                         goSimExp(binds, body, shadowed))
        case SugaredPrimOp(op, args) => SugaredPrimOp(op, args.map(goSimExp(binds, _, shadowed)))
        case Cond(branches, d) =>
            Cond(branches.map { case (t1, th) => (goSimExp(binds, t1, shadowed), goSimExp(binds, th, shadowed)) },
                 d.map(goSimExp(binds, _, shadowed)))
        case Scand(es) => Scand(es.map(goSimExp(binds, _, shadowed)))
        case Scor(es) => Scor(es.map(goSimExp(binds, _, shadowed)))
        case BeginExp(e1, e2) => BeginExp(goSimExp(binds, e1, shadowed), goSimExp(binds, e2, shadowed))

        // Non-FLEX/M nodes: returned unchanged.
        case e => e
    }

    // The type-level substitution at a type position, respecting the
    // pabs-bound type identifiers in `shadowed` (a pabs binding of τ blocks
    // the [T/τ] substitution in the pabs body).
    private def substAt(repl: MT, tau: String, t: MT, shadowed: Set[String]): MT =
        if (shadowed.contains(tau)) t else Subst.substType(repl, tau, t)

    private def substSimAt(binds: List[(String, MT)], t: MT, shadowed: Set[String]): MT = {
        val active = binds.filter { case (tau, _) => !shadowed.contains(tau) }
        if (active.isEmpty) t else Subst.substSim(active, t)
    }
}
