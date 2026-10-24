package DSL.flex_spd

import DSL.flex._

// Description evaluation for FLEX/SPD (Section 12.3.1 of the book).
//
// A description either denotes a *type* (the type of a value) or a *description
// operator* (a function on descriptions, e.g. a dabs or a base type
// constructor). The type checker only needs descriptions that denote types, so
// `DescEval.normalize` reduces a description to a type, when it has one:
//
//   - it follows named-description aliases (the description environment: the
//     standard-library descriptions pairof / listof, the program's def-desc
//     descriptions, and plet / pletrec bindings);
//   - it applies description operators: a dabs by beta-reduction
//     ([dabs-beta-≈], Figure 12.20), and the base type constructors cellof
//     and seqof (which take one description argument);
//   - it converts recursive descriptions (dletrec, and its sugar drec) to the
//     type-level recursion (tletrec), with the bound names treated as
//     recursive type identifiers;
//   - it leaves free description variables (bound by an enclosing pabs /
//     forall / dletrec) as rigid type variables.
//
// Normalizing every description to a type and comparing the results with the
// existing CT machinery (CT.equiv / Subtype.subtype) subsumes the
// description-equivalence rules of Figure 12.20 ([dabs-alpha-≈] / [dabs-beta-≈]
// / [dabs-eta-≈] and [dapply-≈]) at every position where a description is
// used as a type.
//
// A description that does not denote a type — a bare dabs, a bare base type
// constructor, an application whose operator is not a description operator,
// an arity mismatch, or a non-terminating description — normalizes to None
// and is rejected by the checker (the book's "safe nonsense", p.757).
//
// Because description equivalence is undecidable in general (the description
// domain embeds the untyped lambda calculus; book p.758), the normalizer is
// given a reduction bound: a description that does not reduce to a type
// within the bound is reported as non-normalizing (None) rather than looping.
// This is what makes the book's looping description
// ((dabs (d) (d d)) (dabs (d) (d d))) terminate (with a "not a type" verdict)
// instead of running forever. The reduction loop is iterative (a trampoline),
// so a non-terminating description also cannot blow the stack.

object DescEval {

    // The description keywords (Figure 12.18): the base types, the base type
    // constructors, the kernel description keywords, and the sugar keywords.
    // A name in this set may not be a description identifier (δ). Note that
    // listof, pairof, trec, and tletrec are NOT description keywords in
    // FLEX/SPD: listof and pairof are standard-library description
    // identifiers (Figure 12.19), and trec / tletrec are replaced by drec /
    // dletrec.
    val DescKeywords: Set[String] =
        T.BaseTypeNames ++
            Set("cellof", "seqof") ++                                   // base type constructors
            Set("->", "dabs", "dletrec", "forall", "oneof", "prodof", "recordof") ++ // kernel
            Set("dlet", "drec", "plet", "pletrec")                      // sugar

    // The base type constructors (Figure 12.18, footnote 9): one-argument
    // description operators that build the cellof / seqof types.
    val BaseTypeConstructors: Set[String] = Set("cellof", "seqof")

    // The reduction bound: the maximum number of alias-following /
    // beta-reduction / operator-evaluation steps before giving up. Every
    // description the book's examples use normalizes in far fewer than this
    // many steps.
    private val MaxSteps = 10000

    // Reduce a description to a type in the description environment
    // `descEnv` (description name -> description), with `bound` holding the
    // description variables currently in scope (pabs / forall / dletrec
    // binders) that must not be followed as aliases — they denote variables,
    // not definitions. Returns None if the description does not denote a
    // type.
    def normalize(d: T, descEnv: Map[String, T], bound: Set[String]): Option[T] = {
        // The reduction loop: iteratively follow description aliases and
        // beta-reduce description applications. Iteration (not recursion)
        // keeps a non-terminating description — the book's
        // ((dabs (d) (d d)) (dabs (d) (d d))), p.758 — from blowing the
        // stack: it is simply cut off at MaxSteps.
        var head: T = d
        var alias: Set[String] = Set.empty // names whose definition is on the reduction stack
        var steps: Int = 0
        while (steps <= MaxSteps) {
            head match {
                // A description variable in scope: a rigid type variable.
                case TVar(n) if bound.contains(n) =>
                    return Some(head)
                // A description alias: follow its definition.
                case TVar(n) =>
                    descEnv.get(n) match {
                        case Some(defn) if !alias.contains(n) =>
                            head = defn; alias += n; steps += 1
                        case _ =>
                            // Unbound (or cyclic) description variable: a
                            // rigid type variable; T.wellFormed at the use
                            // site rejects it unless it is in scope.
                            return Some(head)
                    }
                // A description application: reduce one step.
                case TDApp(rator, args) =>
                    evalRator(rator, descEnv, bound) match {
                        case Some(Op.Dabs(vars, body)) if args.size == vars.size =>
                            // [dabs-beta-≈]: substitute the arguments for the
                            // variables and reduce the result (which must be
                            // a description that denotes a type).
                            head = Subst.substSim(vars.zip(args), body)
                            steps += 1
                        case Some(Op.Ctor(name)) if args.size == 1 =>
                            // A base type constructor: normalize the single
                            // argument, then build the type.
                            normalize(args.head, descEnv, bound) match {
                                case Some(x) =>
                                    return Some(if (name == "cellof") TCell(x) else TSeq(x))
                                case None => return None
                            }
                        case _ =>
                            // Not a description operator, or an arity
                            // mismatch: the application does not denote a
                            // type (the book's "safe nonsense", p.757).
                            return None
                    }
                // A structural description form (a base type, an arrow, a
                // oneof / prodof / recordof, a forall, a recursive
                // description): normalize each component (each of which may
                // itself be an alias or an application) and rebuild.
                case _ =>
                    return evalStructural(head, descEnv, bound)
            }
        }
        None // reduction bound exceeded: a non-terminating description
    }

    // ------------------------------------------------------------------
    // Description operators (the results of evaluating a rator position).
    // ------------------------------------------------------------------

    private sealed trait Op
    private object Op {
        case class Dabs(vars: List[String], body: T) extends Op
        case class Ctor(name: String) extends Op
    }

    // Evaluate a rator position to a description operator, following
    // description aliases and beta-reducing description applications in
    // rator position (a higher-order description operator, e.g. the book's
    // ((dabs (t) (prodof t t)) int), p.753). Alias-following is iterative
    // (bounded by MaxSteps and by the cycle guard); the beta-reduction
    // recurses only into a strictly smaller subdescription.
    private def evalRator(rator: T, env: Map[String, T], bound: Set[String]): Option[Op] = {
        var cur: T = rator
        var alias: Set[String] = Set.empty
        var steps: Int = 0
        while (steps <= MaxSteps) {
            cur match {
                case TBaseCtor(name) => return Some(Op.Ctor(name))
                case TDabs(vars, body) => return Some(Op.Dabs(vars, body))
                // A variable in scope is a variable, not an operator.
                case TVar(n) if bound.contains(n) => return None
                case TVar(n) =>
                    env.get(n) match {
                        case Some(defn) if !alias.contains(n) =>
                            cur = defn; alias += n; steps += 1
                        case _ => return None
                    }
                // A description application in rator position: beta-reduce
                // its rator and evaluate the result as an operator.
                case TDApp(r2, a2) =>
                    evalRator(r2, env, bound) match {
                        case Some(Op.Dabs(vars, body)) if a2.size == vars.size =>
                            cur = Subst.substSim(vars.zip(a2), body)
                            steps += 1
                        case _ => return None
                    }
                case _ => return None
            }
        }
        None
    }

    // Normalize the components of a structural description form and rebuild
    // it. (The recursion depth is bounded by the nesting depth of the
    // description, which is bounded by its size; only alias-following and
    // beta-reduction are unbounded, and those run in the iterative loop.)
    private def evalStructural(d: T, env: Map[String, T], bound: Set[String]): Option[T] = d match {
        case TBase(_) => Some(d)
        case TVar(_) => Some(d) // cannot reach here (handled by the loop); defensive
        case TArrow(args, ret) =>
            for {
                a <- all(args.map(normalize(_, env, bound)))
                r <- normalize(ret, env, bound)
            } yield TArrow(a, r)
        case TPair(f, s) =>
            for {
                x <- normalize(f, env, bound)
                y <- normalize(s, env, bound)
            } yield TPair(x, y)
        case TProd(cs) => all(cs.map(normalize(_, env, bound))) map (TProd(_))
        case TSeq(e) => normalize(e, env, bound) map (TSeq(_))
        case TRecord(fs) =>
            all(fs.map { case (n, d2) => normalize(d2, env, bound) map (n -> _) }) map (TRecord(_))
        case TOneof(ts) =>
            all(ts.map { case (n, d2) => normalize(d2, env, bound) map (n -> _) }) map (TOneof(_))
        case TList(e) => normalize(e, env, bound) map (TList(_))
        case TCell(e) => normalize(e, env, bound) map (TCell(_))
        case TTrec(name, body) => normalize(body, env, bound) map (b => TTrec(name, b))
        case TTletrec(binds, body) =>
            for {
                nb <- all(binds.map { case (n, d2) => normalize(d2, env, bound) map (n -> _) })
                nb2 <- normalize(body, env, bound)
            } yield TTletrec(nb, nb2)
        case TForall(vars, body) =>
            // The forall's variables are locally bound (they shadow any
            // same-named description alias); the body is normalized with
            // them in the bound set, so they are left as rigid variables.
            normalize(body, env, bound ++ vars.toSet) map (b => TForall(vars, b))
        // A recursive description: convert to type-level recursion, with the
        // bound names treated as recursive type identifiers (locally bound,
        // not followed as aliases) — the description analogue of the
        // equirecursive trec / tletrec handling (book p.757).
        case TDletrec(binds, body) =>
            val lr = bound ++ binds.map(_._1).toSet
            for {
                nb <- all(binds.map { case (n, d2) => normalize(d2, env, lr) map (n -> _) })
                nb2 <- normalize(body, env, lr)
            } yield TTletrec(nb, nb2)
        // A description that does not denote a type.
        case TBaseCtor(_) => None
        case TDabs(_, _) => None
    }

    private def all[A](oas: List[Option[A]]): Option[List[A]] =
        oas.foldRight[Option[List[A]]](Some(Nil)) { (oa, acc) =>
            acc flatMap { as => oa map (_ +: as) }
        }
}
