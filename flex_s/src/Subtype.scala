package DSL.flex_s

import DSL.flex._

// The FLEX/S subtype relation (Chapter 12.1 of the book): p ≤ q holds iff
// every value of type p can be used, in a type-safe manner, in every
// situation where a value of type q is expected (the [inclusion] rule,
// Figure 12.1). Viewing types as sets of values, p ≤ q means p ⊆ q.
//
// The algorithm is the equirecursive two-finger comparison of Figure 12.4,
// the directional variant of the equirecursive equivalence of Figure 11.28
// (used by FLEX itself; see DSL.flex.CT.equiv). An assumption set of type
// pairs already assumed to be in the subtype relation makes the search
// terminate on (potentially) infinite recursive unwoundings:
//
//   [assumed-≤AS]  (p, q) ∈ AS                  p ≤AS q
//   [equiv-≤]      p ≈ q                        p ≤ q
//   [structural]   p, q both non-recursive: the rules of Figure 12.2
//   [trec-left-≤AS] p recursive:
//                   p ≤AS q  iff  step(p) ≤AS∪{(p, q)} q
//   [trec-right-≤AS] q recursive:
//                   p ≤AS q  iff  p ≤AS∪{(p, q)} step(q)
//
// where "step" is the two-finger step of DSL.flex.CT (it exposes the body
// of a trec / tletrec / type-identifier pointer, adding the binder to the
// environment).
//
// Structural rules (Figure 12.2), applied only when both sides are
// non-recursive:
//
//   base types / unbound identifiers : equality
//   pairof, prodof, seqof, listof    : covariant in the components
//   recordof : the subtype has every field of the supertype, and the
//              common fields are covariant (subtypes have more fields)
//   oneof    : every tag of the subtype occurs in the supertype, and the
//              common tags are covariant (subtypes have fewer tags)
//   arrow    : equal arity, contravariant in the argument types, covariant
//              in the result type
//   cellof   : invariant in the content type — the content types must be
//              EQUIVALENT, not merely related by subtyping (book p.705; a
//              covariant cellof rule would be unsound for mutable cells)
//
// Because every FLEX type equivalence is a FLEX/S subtype relation (via
// [equiv-≤]), FLEX/S is a superset of FLEX: every FLEX program type-checks
// under FLEX/S.

object Subtype {

    // p ≤ q ?
    def subtype(p: CT, q: CT): Boolean = sub(p, q, Set.empty)

    private def sub(p: CT, q: CT, AS: Set[(CT, CT)]): Boolean =
        if (AS.contains((p, q))) true // [assumed-≤AS]
        else if (CT.equiv(p, q)) true // [equiv-≤]
        else if (!CT.isRecursive(p) && !CT.isRecursive(q)) structural(p, q, AS)
        else if (CT.isRecursive(p)) sub(CT.step(p), q, AS + ((p, q))) // [trec-left-≤AS]
        else sub(p, CT.step(q), AS + ((p, q))) // [trec-right-≤AS]

    private def structural(p: CT, q: CT, AS: Set[(CT, CT)]): Boolean =
        (p.t, q.t) match {
            case (TBase(a), TBase(b)) => a == b
            case (TVar(a), TVar(b)) => a == b // unbound identifiers (malformed input)
            case (TPair(f1, s1), TPair(f2, s2)) =>
                sub(CT(f1, p.env), CT(f2, q.env), AS) &&
                sub(CT(s1, p.env), CT(s2, q.env), AS)
            case (TProd(cs1), TProd(cs2)) if cs1.size == cs2.size =>
                cs1.zip(cs2).forall { case (t1, t2) => sub(CT(t1, p.env), CT(t2, q.env), AS) }
            case (TSeq(e1), TSeq(e2)) => sub(CT(e1, p.env), CT(e2, q.env), AS)
            case (TList(e1), TList(e2)) => sub(CT(e1, p.env), CT(e2, q.env), AS)
            case (TRecord(fs1), TRecord(fs2)) =>
                // [recordof-≤]: for every field of the supertype (q), the
                // subtype (p) must have a field of the same name whose type
                // is a subtype of the supertype field's type.
                fs2.forall { case (fi, ft) =>
                    fs1.find(_._1 == fi) match {
                        case None => false
                        case Some((_, st)) => sub(CT(st, p.env), CT(ft, q.env), AS)
                    }
                }
            case (TOneof(ts1), TOneof(ts2)) =>
                // [oneof-≤]: for every tag of the subtype (p), the
                // supertype (q) must have the same tag with a supertype
                // payload type.
                ts1.forall { case (ti, tt) =>
                    ts2.find(_._1 == ti) match {
                        case None => false
                        case Some((_, ut)) => sub(CT(tt, p.env), CT(ut, q.env), AS)
                    }
                }
            case (TArrow(args1, r1), TArrow(args2, r2)) if args1.size == args2.size =>
                // [→-≤]: contravariant in the argument types, covariant in
                // the result type.
                args2.zip(args1).forall { case (t2, t1) => sub(CT(t2, q.env), CT(t1, p.env), AS) } &&
                    sub(CT(r1, p.env), CT(r2, q.env), AS)
            case (TCell(e1), TCell(e2)) =>
                // cellof is invariant in its content (book p.705).
                CT.equiv(CT(e1, p.env), CT(e2, q.env))
            case _ => false
        }
}
