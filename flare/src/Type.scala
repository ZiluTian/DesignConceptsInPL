package DSL.flare

// The type domain of the full FLARE language (Figure 13.24 of the book):
//
//   T  ∈ Type   ::= BT | τ | (-> (T*) Tresult)
//                  | (pairof Tfst Tsnd) | (listof T) | (cellof T)
//   BT ∈ BaseType = {unit, int, bool, symb}
//   τ  ∈ TypeId = a fresh type identifier (reconstruction variables ?vN)
//
// and the type schemas of μFLARELP (Figure 13.19):
//
//   TS ∈ TypeSchema ::= T | (generic (τ*) T)
//
// Schemas occur only in type environments (TE: Ident -> TypeSchema); a
// reference to a name bound to (generic (τ*) T) is instantiated with fresh
// type identifiers for each τi ([genvarLPR], Figure 13.20).
//
// Unification follows Figure 13.8 (occurs check, arrow-arity agreement,
// structural pairof/listof/cellof), and a type-constraint set is solved by
// the lazy left-to-right unify loop of Figure 13.11.

sealed trait T
final case class TBase(name: String) extends T
final case class TVar(id: String) extends T
final case class TArrow(params: List[T], ret: T) extends T
final case class TPair(fst: T, snd: T) extends T
final case class TList(elem: T) extends T
final case class TCell(elem: T) extends T

sealed trait TS
final case class TSClosed(t: T) extends TS
final case class TSGeneric(bound: List[String], body: T) extends TS

object T {

    val unit: T = TBase("unit")
    val int: T = TBase("int")
    val bool: T = TBase("bool")
    val symb: T = TBase("symb")

    def arrow(params: List[T], ret: T): T = TArrow(params, ret)

    // ------------------------------------------------------------------
    // Display
    // ------------------------------------------------------------------

    def show(t: T): String = t match {
        case TBase(n) => n
        case TVar(v) => v
        case TArrow(ps, r) =>
            "(-> (" + ps.map(show).mkString(" ") + ") " + show(r) + ")"
        case TPair(a, b) => "(pairof " + show(a) + " " + show(b) + ")"
        case TList(e) => "(listof " + show(e) + ")"
        case TCell(e) => "(cellof " + show(e) + ")"
    }

    // ------------------------------------------------------------------
    // Free type identifiers
    // ------------------------------------------------------------------

    def freeIds(t: T): Set[String] = t match {
        case TBase(_) => Set.empty
        case TVar(v) => Set(v)
        case TArrow(ps, r) => ps.iterator.flatMap(freeIds).toSet ++ freeIds(r)
        case TPair(a, b) => freeIds(a) ++ freeIds(b)
        case TList(e) => freeIds(e)
        case TCell(e) => freeIds(e)
    }

    // ------------------------------------------------------------------
    // Substitution (Figure 13.9): a substitution maps type identifiers to
    // types and is lifted to types (chains are fully resolved) and to type
    // environments.
    // ------------------------------------------------------------------

    def subst(σ: Map[String, T], t: T): T = t match {
        case TVar(v) => σ.get(v) match {
            case Some(u) => subst(σ, u)
            case None => t
        }
        case TArrow(ps, r) => TArrow(ps.map(subst(σ, _)), subst(σ, r))
        case TPair(a, b) => TPair(subst(σ, a), subst(σ, b))
        case TList(e) => TList(subst(σ, e))
        case TCell(e) => TCell(subst(σ, e))
        case other => other
    }

    // ------------------------------------------------------------------
    // Canonicalization for final display: the free fresh identifiers left
    // in a program type (e.g. of an unused formal, or of a generic
    // top-level procedure) are renamed to T1, T2, ... in order of first
    // appearance, as in the book's display of reconstructed types.
    // ------------------------------------------------------------------

    def firstAppearance(t: T): List[String] = {
        val order = collection.mutable.LinkedHashSet[String]()
        def walk(t: T): Unit = t match {
            case TVar(v) => order += v
            case TArrow(ps, r) => ps.foreach(walk); walk(r)
            case TPair(a, b) => walk(a); walk(b)
            case TList(e) => walk(e)
            case TCell(e) => walk(e)
            case _ => ()
        }
        walk(t)
        order.toList
    }

    def canonicalize(t: T): T =
        subst(firstAppearance(t).zipWithIndex
            .map { case (v, i) => v -> TVar(s"T${i + 1}") }.toMap, t)
}

object TS {
    // FrTyIdsTS (Figure 13.19): the free identifiers of a schema exclude
    // its generic-bound identifiers.
    def freeIds(ts: TS): Set[String] = ts match {
        case TSClosed(t) => T.freeIds(t)
        case TSGeneric(bound, body) => T.freeIds(body) -- bound.toSet
    }

    def show(ts: TS): String = ts match {
        case TSClosed(t) => T.show(t)
        case TSGeneric(bound, body) =>
            "(generic (" + bound.mkString(" ") + ") " + T.show(body) + ")"
    }

    // Substitution lifted to type schemas (used for FrTyIdsTE on σ(TE)).
    // Bound identifiers are not substituted (schema binding).
    def subst(σ: Map[String, T], ts: TS): TS = ts match {
        case TSClosed(t) => TSClosed(T.subst(σ, t))
        case TSGeneric(bound, body) => TSGeneric(bound, T.subst(σ, body))
    }
}

// FrTyIdsTE (Figure 13.19), lifted over a substitution.
def freeIdsTE(σ: Map[String, T], te: Map[String, TS]): Set[String] =
    te.values.flatMap(ts => TS.freeIds(TS.subst(σ, ts))).toSet

// ---------------------------------------------------------------------------
// Fresh type identifiers (the ?vN supply)
// ---------------------------------------------------------------------------

object Fresh {
    private var counter = 0

    def reset(): Unit = { counter = 0 }

    def next(): String = { counter += 1; s"?v$counter" }

    // Order key for a fresh identifier (numeric, so first-appearance order
    // is deterministic): used to order generic-bound identifiers.
    def order(v: String): Int = v.stripPrefix("?v").toInt
}

// ---------------------------------------------------------------------------
// Unification (Figure 13.8) and constraint-set solving (Figure 13.11)
// ---------------------------------------------------------------------------

object Unify {

    sealed trait Solve
    final case class Solved(σ: Map[String, T]) extends Solve
    final case class Unsolvable(failed: (T, T)) extends Solve

    def occurs(v: String, t: T): Boolean = t match {
        case TVar(w) => w == v
        case TArrow(ps, r) => ps.exists(occurs(v, _)) || occurs(v, r)
        case TPair(a, b) => occurs(v, a) || occurs(v, b)
        case TList(e) => occurs(v, e)
        case TCell(e) => occurs(v, e)
        case _ => false
    }

    // unify(T1, T2) returns the most general unifier of T1 and T2, if one
    // exists. The inputs are assumed to already have the ambient
    // substitution applied.
    def unify(t1: T, t2: T): Option[Map[String, T]] = (t1, t2) match {
        case (TBase(n1), TBase(n2)) =>
            if (n1 == n2) Some(Map.empty) else None
        case (TVar(v1), TVar(v2)) =>
            if (v1 == v2) Some(Map.empty) else Some(Map(v1 -> TVar(v2)))
        case (TVar(v), t) =>
            if (occurs(v, t)) None else Some(Map(v -> t))
        case (t, TVar(v)) =>
            if (occurs(v, t)) None else Some(Map(v -> t))
        case (TArrow(p1, r1), TArrow(p2, r2)) =>
            if (p1.size != p2.size) None
            else p1.zip(p2).foldLeft[Option[Map[String, T]]](Some(Map.empty)) {
                case (Some(σ), (a, b)) => unify(subst(σ, a), subst(σ, b)).map(compose(σ, _))
                case (None, _) => None
            }.flatMap(σ => unify(subst(σ, r1), subst(σ, r2)).map(compose(σ, _)))
        case (TPair(f1, s1), TPair(f2, s2)) =>
            unify(f1, f2).flatMap(σ => unify(subst(σ, s1), subst(σ, s2)).map(compose(σ, _)))
        case (TList(e1), TList(e2)) => unify(e1, e2)
        case (TCell(e1), TCell(e2)) => unify(e1, e2)
        case _ => None
    }

    // Lifted substitution (apply σ first, then compose the new bindings).
    def compose(σ1: Map[String, T], σ2: Map[String, T]): Map[String, T] =
        σ2 ++ σ1.map { case (k, v) => k -> subst(σ2, v) }

    def subst(σ: Map[String, T], t: T): T = T.subst(σ, t)

    // The lazy type-constraint-set solver (Figure 13.11): process the
    // constraints left to right, carrying a substitution; stop at the first
    // constraint that does not unify.
    def solveTCS(constraints: List[(T, T)]): Solve =
        constraints.foldLeft[Option[Map[String, T]]](Some(Map.empty)) {
            case (Some(σ), (a, b)) =>
                val (a2, b2) = (subst(σ, a), subst(σ, b))
                unify(a2, b2) match {
                    case Some(s) => Some(compose(σ, s))
                    case None => None
                }
            case (None, _) => None
        } match {
            case Some(σ) => Solved(σ)
            case None =>
                // Re-run to locate the first failing constraint (with the
                // substitution accumulated up to it applied), for the error
                // message.
                val failed = locateFailure(constraints)
                Unsolvable(failed)
        }

    private def locateFailure(constraints: List[(T, T)]): (T, T) =
        constraints.foldLeft[(Option[Map[String, T]], (T, T))](
            (Some(Map.empty), (T.unit, T.unit))) {
            case ((Some(σ), _), (a, b)) =>
                val (a2, b2) = (subst(σ, a), subst(σ, b))
                unify(a2, b2) match {
                    case Some(s) => (Some(compose(σ, s)), (a2, b2))
                    case None => (None, (a2, b2))
                }
            case (state, _) => state
        }._2

    def failureMessage(failed: (T, T)): String =
        s"type reconstruction failed: cannot unify ${T.show(failed._1)} and ${T.show(failed._2)}"
}

// ---------------------------------------------------------------------------
// The primitive type environment TEprim (Figure 13.24): the base primops
// have plain arrow types; the pair / list / cell primops have generic type
// schemas (the book gives the pair examples; the list and cell schemas
// follow the same pattern, with := returning unit as in FLEX [cell-set]
// (Figure 11.21) and the FLICK value of a cell assignment (p.399)).
// ---------------------------------------------------------------------------

object TEPrim {

    // O ∈ Primop (Figure 13.23): the μFLARE primops (the usual FL primops
    // except the type predicates and the pair operators) plus the pair,
    // list, and mutable-cell operators of full FLARE.
    val primops: Set[String] = Set(
        "not", "and", "or", "bool=?",
        "=", "!=", "<", "<=", ">", ">=",
        "+", "-", "*", "/", "%", "sym=?",
        "pair", "fst", "snd",
        "cons", "car", "cdr", "null", "null?",
        "cell", "^", ":=", "cell=?")

    private def closed(t: T): TS = TSClosed(t)
    private def generic(bound: List[String], t: T): TS = TSGeneric(bound, t)
    private def tv(s: String): T = TVar(s)

    val schemas: Map[String, TS] = Map(
        "not" -> closed(T.arrow(List(T.bool), T.bool)),
        "and" -> closed(T.arrow(List(T.bool, T.bool), T.bool)),
        "or" -> closed(T.arrow(List(T.bool, T.bool), T.bool)),
        "bool=?" -> closed(T.arrow(List(T.bool, T.bool), T.bool)),
        "=" -> closed(T.arrow(List(T.int, T.int), T.bool)),
        "!=" -> closed(T.arrow(List(T.int, T.int), T.bool)),
        "<" -> closed(T.arrow(List(T.int, T.int), T.bool)),
        "<=" -> closed(T.arrow(List(T.int, T.int), T.bool)),
        ">" -> closed(T.arrow(List(T.int, T.int), T.bool)),
        ">=" -> closed(T.arrow(List(T.int, T.int), T.bool)),
        "+" -> closed(T.arrow(List(T.int, T.int), T.int)),
        "-" -> closed(T.arrow(List(T.int, T.int), T.int)),
        "*" -> closed(T.arrow(List(T.int, T.int), T.int)),
        "/" -> closed(T.arrow(List(T.int, T.int), T.int)),
        "%" -> closed(T.arrow(List(T.int, T.int), T.int)),
        "sym=?" -> closed(T.arrow(List(T.symb, T.symb), T.bool)),
        // Figure 13.24 (the pair examples, verbatim from the book)
        "pair" -> generic(List("?a", "?b"),
            T.arrow(List(tv("?a"), tv("?b")), TPair(tv("?a"), tv("?b")))),
        "fst" -> generic(List("?a", "?b"),
            T.arrow(List(TPair(tv("?a"), tv("?b"))), tv("?a"))),
        "snd" -> generic(List("?a", "?b"),
            T.arrow(List(TPair(tv("?a"), tv("?b"))), tv("?b"))),
        // List primops (homogeneous lists)
        "cons" -> generic(List("?a"),
            T.arrow(List(tv("?a"), TList(tv("?a"))), TList(tv("?a")))),
        "car" -> generic(List("?a"),
            T.arrow(List(TList(tv("?a"))), tv("?a"))),
        "cdr" -> generic(List("?a"),
            T.arrow(List(TList(tv("?a"))), TList(tv("?a")))),
        "null" -> generic(List("?a"),
            T.arrow(Nil, TList(tv("?a")))),
        "null?" -> generic(List("?a"),
            T.arrow(List(TList(tv("?a"))), T.bool)),
        // Mutable-cell primops
        "cell" -> generic(List("?a"),
            T.arrow(List(tv("?a")), TCell(tv("?a")))),
        "^" -> generic(List("?a"),
            T.arrow(List(TCell(tv("?a"))), tv("?a"))),
        ":=" -> generic(List("?a"),
            T.arrow(List(TCell(tv("?a")), tv("?a")), T.unit)),
        "cell=?" -> generic(List("?a"),
            T.arrow(List(TCell(tv("?a")), TCell(tv("?a"))), T.bool))
    )

    def schema(op: String): TS = schemas(op)
}
