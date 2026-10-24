package DSL.flex_sp

import DSL.flex._

// The FLEX/SP subtype relation (Chapter 12.2 of the book): the FLEX/S
// subtype relation of Chapter 12.1 extended with the single [forall-≤] rule
// of Figure 12.9:
//
//   ([τi'/τi]i T' ≤ T)                     (forall (τi' i=1..n) T') ≤ (forall (τi i=1..n) T)
//   where ∀i. τi' ∈ FrTyIds(T')
//
// i.e. a forall type is a subtype of another (of the same arity) when the
// body of the first is a subtype of the body of the second after the bound
// variables of both sides are instantiated with the same fresh type
// variables (which cannot occur free in the bodies, by freshness). The
// bound variables are rigid: they are not subtyped, only instantiated.
//
// The underlying algorithm is the equirecursive two-finger comparison of
// Figure 12.4 (the directional variant of the equirecursive equivalence of
// Figure 11.28), with an assumption set of type pairs already assumed to be
// in the subtype relation:
//
//   [assumed-≤AS]  (p, q) ∈ AS                  p ≤AS q
//   [equiv-≤]      p ≈ q                        p ≤ q
//   [structural]   p, q both non-recursive: the rules of Figure 12.2,
//                  plus [forall-≤] for forall types
//   [trec-left-≤AS] p recursive:
//                   p ≤AS q  iff  step(p) ≤AS∪{(p, q)} q
//   [trec-right-≤AS] q recursive:
//                   p ≤AS q  iff  p ≤AS∪{(p, q)} step(q)
//
// where "step" is the two-finger step of DSL.flex.CT.
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
//   forall   : equal arity; the bodies are compared after instantiating
//              both sides' variables with the same fresh type variables
//              ([forall-≤], Figure 12.9)
//
// Because every FLEX equivalence is a FLEX/SP subtype relation (via
// [equiv-≤]), FLEX/SP is a superset of FLEX/S, which is a superset of FLEX.

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
            case (TForall(vs1, b1), TForall(vs2, b2)) if vs1.size == vs2.size =>
                // [forall-≤] (Figure 12.9): instantiate both sides' bound
                // variables with the same fresh type variables (which are
                // rigid and cannot occur free in either body, by
                // freshness), then compare the instantiated bodies.
                val fns = vs1.indices.map(_ => CT.freshName("pv")).toList
                val r1 = vs1.zip(fns).toMap
                val r2 = vs2.zip(fns).toMap
                sub(CT(Subst.renameType(b1, r1), p.env),
                    CT(Subst.renameType(b2, r2), q.env), AS)
            case (TForallK(bs1, b1), TForallK(bs2, b2)) if bs1.size == bs2.size =>
                // [forall-≤] with kind annotations (Section 12.3.2 of the
                // book): the corresponding binder kinds must agree (kind
                // equality is structural), then the bodies are compared with
                // the same fresh rigid type variables, as above.
                if (!bs1.zip(bs2).forall { case ((_, k1), (_, k2)) => k1 == k2 }) false
                else {
                    val fns = bs1.indices.map(_ => CT.freshName("pv")).toList
                    val r1 = bs1.map(_._1).zip(fns).toMap
                    val r2 = bs2.map(_._1).zip(fns).toMap
                    sub(CT(Subst.renameType(b1, r1), p.env),
                        CT(Subst.renameType(b2, r2), q.env), AS)
                }
            case _ => false
        }
}
