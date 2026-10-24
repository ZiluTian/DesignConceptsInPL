package DSL.flex_spdk

import DSL.flex._

// Kind checking for FLEX/SPDK (Section 12.3.2 of the book, Figure 12.22).
//
// The kind of a description is what a type is to a value:
//
//   K ::= type | (->> (Karg*) Kresult)
//
// `type` is the kind of descriptions that denote types; `(->> (K*) K)` is
// the kind of a description operator (type constructor) that takes
// descriptions of kinds K* and yields a description of kind K. The kind
// judgment  KE ⊢ D :: K  is derived from the rules of Figure 12.22:
//
//   [base-type]  KE ⊢ unit/int/bool/symb :: type
//   [base-tycon] KE ⊢ cellof/seqof :: (->> (type) type)
//   [var]        δ :: K ∈ KE                     KE ⊢ δ :: K
//   [→]          KE ⊢ Di :: type (all i)         KE ⊢ (-> (D*) D0) :: type
//   [prodof] / [recordof] / [oneof]: as [→]
//   [forall]     KE[δi :: Ki] ⊢ Dbody :: type    KE ⊢ (forall ((δi Ki)*) Dbody) :: type
//   [->>-intro]  KE[δi :: Ki] ⊢ Dbody :: Kbody   KE ⊢ (dabs ((δi Ki)*) Dbody) :: (->> (Ki*) Kbody)
//   [->>-elim]   KE ⊢ Drator :: (->> (K1..Kn) Kres), KE ⊢ Di :: Ki (all i)
//                                            KE ⊢ (Drator D1 ... Dn) :: Kres
//   [dletrec]    KE[δi :: type] ⊢ Di :: type (all i), KE[δi :: type] ⊢ Dbody :: K
//                                            KE ⊢ (dletrec ((δi Di)*) Dbody) :: K
//
// The kind environment KE maps kind names to kinds. It contains the base
// kind assignments (KEbase), the kind annotations of the description binders
// in scope (pabs / forall / dabs binders — threaded by the type checker —
// and the dletrec binders, which are always kind type), and, lazily, the
// kinds of NAMED description definitions: standard-library descriptions
// (pairof, listof), the program's def-desc descriptions, and plet / pletrec
// bindings. A named description's kind is computed by kind-checking its
// definition (a binder in KE always shadows a same-named definition).
//
// A description whose definition loops (directly or through other
// definitions) is not well kinded: the `visiting` set cuts the alias
// chain. This is exactly what the book's looping description
// ((dabs (d K) (d d)) (dabs (d K) (d d))) needs to be written — kind-level
// recursion (Exercise 12.24), which the surface syntax does not have.
//
// (Conservative corner: two mutually RECURSIVE named descriptions whose
// definitions reference each other directly (without an enclosing dletrec /
// drec whose binders enter KE) are rejected as well; the book's intended
// spelling for mutual recursion is a single dletrec, whose binders are
// kind-checked simultaneously.)

object KindCheck {

    // KE base (Figure 12.22): the base kind environment.
    val KEbase: Map[String, Kind] = Map(
        "unit" -> KType, "int" -> KType, "bool" -> KType, "symb" -> KType,
        "cellof" -> KArrow(List(KType), KType),
        "seqof" -> KArrow(List(KType), KType))

    // The kind of the description d relative to the description environment
    // (named description definitions) and the kind environment, or None if
    // d is not well kinded. `visiting` holds the named definitions on the
    // current alias-following chain (cycle guard).
    def kindOf(d: T, descEnv: Map[String, T], KE: Map[String, Kind],
               visiting: Set[String]): Option[Kind] = d match {
        // [base-type] / [base-tycon].
        case TBase(n) => KE.get(n)
        case TBaseCtor(n) => KE.get(n)
        // [var]: a binder in KE shadows any same-named definition; a named
        // definition is followed to its definition's kind (with the cycle
        // guard).
        case TVar(n) =>
            KE.get(n) orElse {
                if (visiting.contains(n)) None
                else descEnv.get(n) flatMap (defn => kindOf(defn, descEnv, KE, visiting + n))
            }
        // [→]: all argument descriptions and the result description of kind type.
        case TArrow(args, ret) =>
            if (args.forall(kindIs(_, KType, descEnv, KE, visiting)) &&
                kindIs(ret, KType, descEnv, KE, visiting)) Some(KType)
            else None
        // [prodof] / [recordof] / [oneof] (Figure 12.22: "similar to [→]").
        case TProd(cs) =>
            if (cs.forall(kindIs(_, KType, descEnv, KE, visiting))) Some(KType) else None
        case TRecord(fs) =>
            if (fs.forall { case (_, d2) => kindIs(d2, KType, descEnv, KE, visiting) }) Some(KType)
            else None
        case TOneof(ts) =>
            if (ts.forall { case (_, d2) => kindIs(d2, KType, descEnv, KE, visiting) }) Some(KType)
            else None
        // Type-level forms: they appear only behind a description alias that
        // the SPDK parser cannot produce (the parser builds TDApp for
        // cellof / seqof applications and TVar for pairof / listof); treat
        // them as types of kind type, covariantly in the components.
        case TPair(f, s) =>
            if (kindIs(f, KType, descEnv, KE, visiting) && kindIs(s, KType, descEnv, KE, visiting))
                Some(KType) else None
        case TSeq(e) => if (kindIs(e, KType, descEnv, KE, visiting)) Some(KType) else None
        case TList(e) => if (kindIs(e, KType, descEnv, KE, visiting)) Some(KType) else None
        case TCell(e) => if (kindIs(e, KType, descEnv, KE, visiting)) Some(KType) else None
        case TTrec(_, body) => if (kindIs(body, KType, descEnv, KE, visiting)) Some(KType) else None
        case TTletrec(binds, body) =>
            val KEp = KE ++ binds.map { case (n, _) => n -> KType }.toMap
            if (binds.forall { case (_, d2) => kindIs(d2, KType, descEnv, KEp, visiting) } &&
                kindIs(body, KType, descEnv, KEp, visiting))
                Some(KType) else None
        // [forall]: the binders' kinds come from the annotations; the body
        // must have kind type. (An unkinded forall — which the SPDK parser
        // never produces — is read defensively as all binders kind type.)
        case TForall(vars, body) =>
            if (kindIs(body, KType, descEnv, KE ++ vars.map(_ -> KType).toMap, visiting))
                Some(KType) else None
        case TForallK(binds, body) =>
            val names = binds.map(_._1)
            if (names.distinct.size != names.size) None
            else if (kindIs(body, KType, descEnv, KE ++ binds.toMap, visiting)) Some(KType)
            else None
        // [->>-intro]: the result kind is (->> (K1 ... Kn) Kbody), where
        // Kbody is the body's kind under the binders' kind assignments.
        case TDabs(vars, body) =>
            if (vars.distinct.size != vars.size) None
            else kindOf(body, descEnv, KE ++ vars.map(_ -> KType).toMap, visiting) map (kb =>
                KArrow(List.fill(vars.size)(KType), kb))
        case TDabsK(binds, body) =>
            val names = binds.map(_._1)
            if (names.distinct.size != names.size) None
            else kindOf(body, descEnv, KE ++ binds.toMap, visiting) map (kb =>
                KArrow(binds.map(_._2), kb))
        // [->>-elim]: the rator must have an arrow kind of exactly the
        // application's arity, and each argument must have the
        // corresponding argument kind.
        case TDApp(rator, args) =>
            kindOf(rator, descEnv, KE, visiting) match {
                case Some(KArrow(kas, kres)) if args.size == kas.size =>
                    if (args.zip(kas).forall { case (a, k) =>
                            kindIs(a, k, descEnv, KE, visiting) })
                        Some(kres)
                    else None
                case _ => None
            }
        // [dletrec]: the binders are required to be of kind type, each
        // definition must have kind type, and the result is the body's kind
        // (all under the kind environment extended with the binders).
        case TDletrec(binds, body) =>
            val names = binds.map(_._1)
            if (names.distinct.size != names.size) None
            else {
                val KEp = KE ++ names.map(_ -> KType).toMap
                if (binds.forall { case (_, d2) => kindIs(d2, KType, descEnv, KEp, visiting) })
                    kindOf(body, descEnv, KEp, visiting)
                else None
            }
    }

    private def kindIs(d: T, k: Kind, descEnv: Map[String, T], KE: Map[String, Kind],
                       visiting: Set[String]): Boolean =
        kindOf(d, descEnv, KE, visiting).contains(k)
}
