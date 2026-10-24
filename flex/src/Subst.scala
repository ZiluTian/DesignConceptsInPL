package DSL.flex

import DSL.fl._

// Substitution for FLEX (Figures 11.4 and 11.5 of the book). Because value
// identifiers (I) and type identifiers (tau) are in separate namespaces,
// type substitution never captures or is captured by value binders, but it
// must respect the type binders (trec / tletrec) inside types: a binding
// shadows the identifier it names in the body and sibling definitions.
object Subst {

    // ------------------------------------------------------------------
    // Type substitution
    // ------------------------------------------------------------------

    // [T/tau]Type  (Figure 11.5)
    def substType(repl: T, tau: String, target: T): T =
        goType(repl, tau, target, Set.empty)

    // As substType, but with a set of type identifiers that are locally
    // bound (e.g. by an enclosing pabs in FLEX/SP) and therefore must not
    // be substituted.
    def substType(repl: T, tau: String, target: T, shadowed: Set[String]): T =
        goType(repl, tau, target, shadowed)

    private def goType(repl: T, tau: String, target: T, shadowed: Set[String]): T =
        target match {
            case TVar(n) => if (!shadowed.contains(n) && n == tau) repl else target
            case TBase(_) => target
            case TArrow(args, ret) =>
                TArrow(args.map(goType(repl, tau, _, shadowed)), goType(repl, tau, ret, shadowed))
            case TPair(f, s) =>
                TPair(goType(repl, tau, f, shadowed), goType(repl, tau, s, shadowed))
            case TProd(cs) => TProd(cs.map(goType(repl, tau, _, shadowed)))
            case TSeq(e) => TSeq(goType(repl, tau, e, shadowed))
            case TRecord(fs) => TRecord(fs.map { case (n, d) => (n, goType(repl, tau, d, shadowed)) })
            case TOneof(ts) => TOneof(ts.map { case (n, d) => (n, goType(repl, tau, d, shadowed)) })
            case TList(e) => TList(goType(repl, tau, e, shadowed))
            case TCell(e) => TCell(goType(repl, tau, e, shadowed))
            case TTrec(name, body) =>
                // A trec binding tau shadows every occurrence of tau in its body.
                if (name == tau) target
                else TTrec(name, goType(repl, tau, body, shadowed + name))
            case TTletrec(binds, body) =>
                // A tletrec binding tau shadows tau in all definitions and the body.
                if (binds.exists(_._1 == tau)) target
                else TTletrec(binds.map { case (n, d) => (n, goType(repl, tau, d, shadowed)) },
                              goType(repl, tau, body, shadowed))
            case TForall(vars, body) =>
                // A forall binding tau shadows every occurrence of tau in its body.
                if (vars.contains(tau)) target
                else TForall(vars, goType(repl, tau, body, shadowed ++ vars.toSet))
            // FLEX/SPD description forms (Section 12.3.1): substitution into a
            // description respects its binders (a dabs / dletrec binding
            // shadows tau in its body), and a base type constructor is atomic.
            case TBaseCtor(_) => target
            case TDabs(vars, body) =>
                if (vars.contains(tau)) target
                else TDabs(vars, goType(repl, tau, body, shadowed ++ vars.toSet))
            case TDApp(rator, args) =>
                TDApp(goType(repl, tau, rator, shadowed),
                      args.map(goType(repl, tau, _, shadowed)))
            case TDletrec(binds, body) =>
                if (binds.exists(_._1 == tau)) target
                else TDletrec(binds.map { case (n, d) => (n, goType(repl, tau, d, shadowed)) },
                              goType(repl, tau, body, shadowed))
            // FLEX/SPDK kind-annotated forms (Section 12.3.2): same shadowing
            // as their unkinded counterparts.
            case TForallK(binds, body) =>
                if (binds.exists(_._1 == tau)) target
                else TForallK(binds, goType(repl, tau, body, shadowed ++ binds.map(_._1).toSet))
            case TDabsK(binds, body) =>
                if (binds.exists(_._1 == tau)) target
                else TDabsK(binds, goType(repl, tau, body, shadowed ++ binds.map(_._1).toSet))
        }

    // Simultaneous type substitution [T1/tau1, ..., Tn/taun]Type, used by
    // the (let-type ((tau T)*) T) sugar.
    def substSim(binds: List[(String, T)], target: T): T =
        goSim(binds.toMap, target, Set.empty)

    // As substSim, but with a set of type identifiers that are locally
    // bound (e.g. by an enclosing pabs in FLEX/SP) and therefore must not
    // be substituted.
    def substSim(binds: List[(String, T)], target: T, shadowed: Set[String]): T =
        goSim(binds.toMap, target, shadowed)

    private def goSim(bs: Map[String, T], target: T, shadowed: Set[String]): T = target match {
        case TVar(n) => bs.get(n).filter(_ => !shadowed.contains(n)).getOrElse(target)
        case TBase(_) => target
        case TArrow(args, ret) =>
            TArrow(args.map(goSim(bs, _, shadowed)), goSim(bs, ret, shadowed))
        case TPair(f, s) =>
            TPair(goSim(bs, f, shadowed), goSim(bs, s, shadowed))
        case TProd(cs) => TProd(cs.map(goSim(bs, _, shadowed)))
        case TSeq(e) => TSeq(goSim(bs, e, shadowed))
        case TRecord(fs) => TRecord(fs.map { case (n, d) => (n, goSim(bs, d, shadowed)) })
        case TOneof(ts) => TOneof(ts.map { case (n, d) => (n, goSim(bs, d, shadowed)) })
        case TList(e) => TList(goSim(bs, e, shadowed))
        case TCell(e) => TCell(goSim(bs, e, shadowed))
        case TTrec(name, body) =>
            TTrec(name, goSim(bs, body, shadowed + name))
        case TTletrec(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TTletrec(binds.map { case (n, d) => (n, goSim(bs, d, sh)) }, goSim(bs, body, sh))
        case TForall(vars, body) =>
            val sh = shadowed ++ vars.toSet
            TForall(vars, goSim(bs, body, sh))
        // FLEX/SPD description forms (Section 12.3.1).
        case TBaseCtor(_) => target
        case TDabs(vars, body) =>
            val sh = shadowed ++ vars.toSet
            TDabs(vars, goSim(bs, body, sh))
        case TDApp(rator, args) =>
            TDApp(goSim(bs, rator, shadowed), args.map(goSim(bs, _, shadowed)))
        case TDletrec(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TDletrec(binds.map { case (n, d) => (n, goSim(bs, d, sh)) }, goSim(bs, body, sh))
        // FLEX/SPDK kind-annotated forms (Section 12.3.2).
        case TForallK(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TForallK(binds, goSim(bs, body, sh))
        case TDabsK(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TDabsK(binds, goSim(bs, body, sh))
    }

    // ------------------------------------------------------------------
    // Expression substitution (Figure 11.4, type variant)
    //
    // [T/tau]E: replace free occurrences of the type identifier tau by T in
    // every type position of the expression. Each type position is a
    // self-contained type (its own trec/tletrec binders), so the shadowed
    // set restarts at every type position.
    // ------------------------------------------------------------------

    def substExp(repl: T, tau: String, e: Exp): Exp =
        mapExp((t, sh) => goType(repl, tau, t, sh))(e)

    // Simultaneous version [T1/tau1, ..., Tn/taun]E, used by the
    // (let-type ((tau T)*) Ebody) sugar (Figure 11.2 of the book).
    def substSimExp(binds: List[(String, T)], e: Exp): Exp =
        mapExp((t, sh) => goSim(binds.toMap, t, sh))(e)

    // The common walker: recurse into subexpressions and apply `subT` to
    // every type annotation.
    private def mapExp(subT: (T, Set[String]) => T)(e: Exp): Exp = e match {
        // Leaves: unchanged (types cannot harbor value identifiers, and
        // literals carry no types).
        case e: UnitLit => e
        case e: BoolLit => e
        case e: IntLit => e
        case e: Sym => e
        case e: Var => e

        // Kernel forms: recurse into subexpressions and type annotations.
        case FlexError(m, t) => FlexError(m, subT(t, Set.empty))
        case If(t1, t2, t3) => If(mapExp(subT)(t1), mapExp(subT)(t2), mapExp(subT)(t3))
        case PrimOp(op, args) => PrimOp(op, args.map(mapExp(subT)))
        case AbsExp(params, body) =>
            AbsExp(params.map { case (n, t) => (n, subT(t, Set.empty)) }, mapExp(subT)(body))
        case AppExp(r, args) => AppExp(mapExp(subT)(r), args.map(mapExp(subT)))
        case Let(binds, body) =>
            Let(binds.map { case (n, e2) => (n, mapExp(subT)(e2)) }, mapExp(subT)(body))
        case LetRecExp(bs, body) =>
            LetRecExp(bs.map { case (n, t, e2) => (n, subT(t, Set.empty), mapExp(subT)(e2)) },
                      mapExp(subT)(body))
        case TheExp(t, e2) => TheExp(subT(t, Set.empty), mapExp(subT)(e2))
        case Pair(f, s) => Pair(mapExp(subT)(f), mapExp(subT)(s))
        case FstExp(e2) => FstExp(mapExp(subT)(e2))
        case SndExp(e2) => SndExp(mapExp(subT)(e2))
        case ProdExp(cs) => ProdExp(cs.map(mapExp(subT)))
        case GetExp(n, e2) => GetExp(n, mapExp(subT)(e2))
        case SeqExp(cs) => SeqExp(cs.map(mapExp(subT)))
        case SeqGetExp(i, s) => SeqGetExp(mapExp(subT)(i), mapExp(subT)(s))
        case SeqSizeExp(e2) => SeqSizeExp(mapExp(subT)(e2))
        case RecordExp(fs) => RecordExp(fs.map { case (n, e2) => (n, mapExp(subT)(e2)) })
        case SelectExp(n, e2) => SelectExp(n, mapExp(subT)(e2))
        case WithExp(r, b) => WithExp(mapExp(subT)(r), mapExp(subT)(b))
        case OneExp(t, tag, p) => OneExp(subT(t, Set.empty), tag, mapExp(subT)(p))
        case TagCaseExp(d, pn, cs, el) =>
            TagCaseExp(mapExp(subT)(d), pn,
                       cs.map { case (n, e2) => (n, mapExp(subT)(e2)) },
                       el.map(mapExp(subT)))
        case ConsExp(h, t2) => ConsExp(mapExp(subT)(h), mapExp(subT)(t2))
        case CarExp(e2) => CarExp(mapExp(subT)(e2))
        case CdrExp(e2) => CdrExp(mapExp(subT)(e2))
        case NullExp(t) => NullExp(subT(t, Set.empty))
        case NullQExp(e2) => NullQExp(mapExp(subT)(e2))
        case SetExp(n, e2) => SetExp(n, mapExp(subT)(e2))
        case CellExp(e2) => CellExp(mapExp(subT)(e2))
        case DerefExp(e2) => DerefExp(mapExp(subT)(e2))
        case CellSetExp(c, e2) => CellSetExp(mapExp(subT)(c), mapExp(subT)(e2))
        case CellEqExp(e1, e2) => CellEqExp(mapExp(subT)(e1), mapExp(subT)(e2))

        // Sugar forms: recurse (and into their type annotations / bindings).
        case SugaredPrimOp(op, args) => SugaredPrimOp(op, args.map(mapExp(subT)))
        case Cond(branches, d) =>
            Cond(branches.map { case (t1, th) => (mapExp(subT)(t1), mapExp(subT)(th)) },
                 d.map(mapExp(subT)))
        case Scand(es) => Scand(es.map(mapExp(subT)))
        case Scor(es) => Scor(es.map(mapExp(subT)))
        case BeginExp(e1, e2) => BeginExp(mapExp(subT)(e1), mapExp(subT)(e2))
        case ListExp(t, es) => ListExp(subT(t, Set.empty), es.map(mapExp(subT)))
        case LetTypeExp(binds, body) =>
            LetTypeExp(binds.map { case (n, d) => (n, subT(d, Set.empty)) },
                       mapExp(subT)(body))
        case LetTypeStarExp(binds, body) =>
            LetTypeStarExp(binds.map { case (n, d) => (n, subT(d, Set.empty)) },
                           mapExp(subT)(body))

        // Non-FLEX nodes (e.g. FL kernel forms built by hand): types cannot
        // harbor value identifiers, so they are returned unchanged.
        case e => e
    }

    // ------------------------------------------------------------------
    // Alpha-renaming of top-level-bound type identifiers (used by
    // CT.renameEnv when composing types with possibly colliding
    // environments). renames: old name -> fresh name.
    // ------------------------------------------------------------------

    def renameType(t: T, renames: Map[String, String]): T =
        goRename(t, renames, Set.empty)

    def renameName(n: String, renames: Map[String, String]): String =
        renames.getOrElse(n, n)

    private def goRename(t: T, renames: Map[String, String], shadowed: Set[String]): T = t match {
        case TVar(n) =>
            renames.get(n).filter(_ => !shadowed.contains(n)) map (x => TVar(x)) getOrElse t
        case TBase(_) => t
        case TArrow(args, ret) =>
            TArrow(args.map(goRename(_, renames, shadowed)), goRename(ret, renames, shadowed))
        case TPair(f, s) =>
            TPair(goRename(f, renames, shadowed), goRename(s, renames, shadowed))
        case TProd(cs) => TProd(cs.map(goRename(_, renames, shadowed)))
        case TSeq(e) => TSeq(goRename(e, renames, shadowed))
        case TRecord(fs) => TRecord(fs.map { case (n, d) => (n, goRename(d, renames, shadowed)) })
        case TOneof(ts) => TOneof(ts.map { case (n, d) => (n, goRename(d, renames, shadowed)) })
        case TList(e) => TList(goRename(e, renames, shadowed))
        case TCell(e) => TCell(goRename(e, renames, shadowed))
        case TTrec(name, body) =>
            TTrec(name, goRename(body, renames, shadowed + name))
        case TTletrec(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TTletrec(binds.map { case (n, d) => (n, goRename(d, renames, sh)) },
                     goRename(body, renames, sh))
        case TForall(vars, body) =>
            // Like the trec/tletrec binders, forall binders are never renamed
            // by an environment renaming; occurrences in the body that are
            // bound by the forall are protected by the shadowed set.
            val sh = shadowed ++ vars.toSet
            TForall(vars, goRename(body, renames, sh))
        // FLEX/SPD description forms (Section 12.3.1): dabs / dletrec binders
        // protect their bound names, as the type binders do.
        case TBaseCtor(_) => t
        case TDabs(vars, body) =>
            val sh = shadowed ++ vars.toSet
            TDabs(vars, goRename(body, renames, sh))
        case TDApp(rator, args) =>
            TDApp(goRename(rator, renames, shadowed),
                  args.map(goRename(_, renames, shadowed)))
        case TDletrec(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TDletrec(binds.map { case (n, d) => (n, goRename(d, renames, sh)) },
                     goRename(body, renames, sh))
        // FLEX/SPDK kind-annotated forms (Section 12.3.2): binders protect
        // their names, as the unkinded binders do.
        case TForallK(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TForallK(binds, goRename(body, renames, sh))
        case TDabsK(binds, body) =>
            val sh = shadowed ++ binds.map(_._1).toSet
            TDabsK(binds, goRename(body, renames, sh))
    }
}
