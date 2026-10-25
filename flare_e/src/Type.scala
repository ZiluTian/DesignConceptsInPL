package DSL.flare_e

// The type, effect, and region domain of FLARE/E (Figure 16.1 of the book).
//
// A description identifier (DescId) is a fresh ?vN that can name any
// description — a type, an effect, or a region. Types, effects, and regions
// are separate trees, but they all draw their variables from the same ?vN
// supply, so a single unifier and substitution handle all three.
//
//   T  ∈ Type   ::= δ | BT | (-> (T* ) Flatent Tresult)
//                   | (pairof T T) | (listof T) | (cellof T R)
//   BF ∈ BaseEffect ::= δ | (FCR R)
//    F ∈ Effect  ::= BF | (maxeff F*)
//    R ∈ Region  ::= δ
//
//   TS ∈ TypeSchema (algebraic, Figure 16.8) ::=
//            T | (generic (δ*) T (FCS))
//
//   FC ∈ EffectConstraint ::= (>= δ F)   — the effect named by δ must be at
//                                            least as large as F.
//
// Effects are combined with maxeff, which is ACUI (associative, commutative,
// unit = pure, idempotent), so an effect is treated as a *set* of base
// effects. Unification follows Figure 16.4: type equality is unified as in
// FLARE, plus the latent effects of -> types (guaranteed to be effect
// variables) and the regions of cellof types (guaranteed to be region
// variables). A type-constraint set is solved by the lazy left-to-right unify
// loop of Figure 13.11; an effect-constraint set is solved to its least
// solution by the least-fixed-point iteration of Figure 16.4.

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

sealed trait Eff
final case class EPure() extends Eff                       // pure = (maxeff)
final case class EVar(id: String) extends Eff              // δ (effect variable)
final case class EMax(es: List[Eff]) extends Eff           // (maxeff ...)
final case class EBase(ctor: String, region: String) extends Eff  // (FCR R)

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

sealed trait T
final case class TBase(name: String) extends T
final case class TVar(id: String) extends T
final case class TArrow(params: List[T], latent: Eff, ret: T) extends T
final case class TPair(fst: T, snd: T) extends T
final case class TList(elem: T) extends T
final case class TCell(elem: T, region: String) extends T  // region is a ?vN id

object T {
    val unit: T = TBase("unit")
    val int: T = TBase("int")
    val bool: T = TBase("bool")
    val symb: T = TBase("symb")

    def arrow(params: List[T], latent: Eff, ret: T): T = TArrow(params, latent, ret)

    // ------------------------------------------------------------------
    // Display (no normalization; used for error messages and intermediate
    // debugging). Normalization for final program-type display lives in
    // check.scala.
    // ------------------------------------------------------------------

    def show(t: T): String = t match {
        case TBase(n) => n
        case TVar(v) => v
        case TArrow(ps, lat, r) =>
            "(-> (" + ps.map(show).mkString(" ") + ") " + Eff.show(lat) + " " + show(r) + ")"
        case TPair(a, b) => "(pairof " + show(a) + " " + show(b) + ")"
        case TList(e) => "(listof " + show(e) + ")"
        case TCell(e, reg) => "(cellof " + show(e) + " " + reg + ")"
    }

    // ------------------------------------------------------------------
    // Free description identifiers (type, effect, and region variables)
    // ------------------------------------------------------------------

    def freeDescIds(t: T): Set[String] = t match {
        case TVar(v) => Set(v)
        case TArrow(ps, lat, r) =>
            ps.iterator.flatMap(freeDescIds).toSet ++ Eff.freeDescIds(lat) ++ freeDescIds(r)
        case TPair(a, b) => freeDescIds(a) ++ freeDescIds(b)
        case TList(e) => freeDescIds(e)
        case TCell(e, reg) => freeDescIds(e) ++ Set(reg)
        case _ => Set.empty
    }
}

object Eff {
    def show(e: Eff): String = e match {
        case EPure() => "pure"
        case EVar(v) => v
        case EMax(es) =>
            if (es.isEmpty) "pure"
            else "(maxeff " + es.map(show).mkString(" ") + ")"
        case EBase(c, reg) => s"($c $reg)"
    }

    def freeDescIds(e: Eff): Set[String] = e match {
        case EVar(v) => Set(v)
        case EMax(es) => es.iterator.flatMap(freeDescIds).toSet
        case EBase(_, reg) => Set(reg)
        case EPure() => Set.empty
    }

    // Combine a list of effects into a single maxeff (flattened, pure removed).
    def maxeff(es: List[Eff]): Eff = {
        val flat = es.flatMap {
            case EMax(xs) => xs
            case other => List(other)
        }.filterNot(_ == EPure())
        if (flat.isEmpty) EPure()
        else if (flat.sizeIs == 1) flat.head
        else EMax(flat)
    }

    // The set of base effects (ctor, region) that an effect denotes, resolving
    // effect variables via sigma (a map from effect var id to base-effect set).
    def baseSet(e: Eff, sigma: Map[String, Set[(String, String)]]): Set[(String, String)] = e match {
        case EPure() => Set.empty
        case EVar(v) => sigma.getOrElse(v, Set.empty)
        case EMax(es) => es.iterator.flatMap(baseSet(_, sigma)).toSet
        case EBase(c, reg) => Set((c, reg))
    }

    // Rebuild a canonical effect from a set of base effects.
    def fromSet(s: Set[(String, String)]): Eff =
        if (s.isEmpty) EPure()
        else EMax(s.toList.map { case (c, r) => EBase(c, r) })
}

// ---------------------------------------------------------------------------
// Effect constraints and algebraic type schemas
// ---------------------------------------------------------------------------

// (>= δ F) — the effect named by description variable δ must be at least as
// large as F.
final case class EffCon(delta: String, f: Eff)

sealed trait TS
final case class TSClosed(t: T) extends TS
final case class TSGeneric(bound: List[String], body: T, fcs: List[EffCon]) extends TS

// ---------------------------------------------------------------------------
// Descriptions and description substitutions
// ---------------------------------------------------------------------------

sealed trait Desc
final case class DType(t: T) extends Desc
final case class DEff(e: Eff) extends Desc
final case class DReg(id: String) extends Desc

// ---------------------------------------------------------------------------
// Fresh description identifiers (the shared ?vN supply)
// ---------------------------------------------------------------------------

object FreshE {
    private var counter = 0

    def reset(): Unit = { counter = 0 }

    def next(): String = { counter += 1; s"?v$counter" }

    // Numeric order key for a fresh identifier (used to order generic-bound
    // identifiers deterministically).
    def order(v: String): Int = v.stripPrefix("?v").toInt
}

// ---------------------------------------------------------------------------
// Renaming (instantiation): replace description variables with fresh ones,
// uniformly across type, effect, and region positions. Used by [genvarZ] and
// by primitive-schema freshening.
// ---------------------------------------------------------------------------

object Rename {
    def t(σ: Map[String, String], ty: T): T = ty match {
        case TVar(v) => TVar(σ.getOrElse(v, v))
        case TArrow(ps, lat, r) =>
            TArrow(ps.map(x => t(σ, x)), e(σ, lat), t(σ, r))
        case TPair(a, b) => TPair(t(σ, a), t(σ, b))
        case TList(e0) => TList(t(σ, e0))
        case TCell(e0, reg) => TCell(t(σ, e0), σ.getOrElse(reg, reg))
        case other => other
    }

    def e(σ: Map[String, String], e0: Eff): Eff = e0 match {
        case EVar(v) => EVar(σ.getOrElse(v, v))
        case EMax(es) => EMax(es.map(e(σ, _)))
        case EBase(c, reg) => EBase(c, σ.getOrElse(reg, reg))
        case EPure() => EPure()
    }
}

// ---------------------------------------------------------------------------
// Unification (Figure 16.4) and constraint-set solving
// ---------------------------------------------------------------------------

object UnifyE {

    sealed trait Solve
    final case class Solved(σ: Map[String, Desc]) extends Solve
    final case class Unsolvable(failed: (T, T)) extends Solve

    // Does type variable v occur in type t? (Type variables never occur in
    // effect or region positions.)
    def occursType(v: String, t: T): Boolean = t match {
        case TVar(w) => w == v
        case TArrow(ps, _, r) => ps.exists(occursType(v, _)) || occursType(v, r)
        case TPair(a, b) => occursType(v, a) || occursType(v, b)
        case TList(e) => occursType(v, e)
        case TCell(e, _) => occursType(v, e)
        case _ => false
    }

    // Does effect variable v occur in effect e?
    def occursEff(v: String, e: Eff): Boolean = e match {
        case EVar(w) => w == v
        case EMax(es) => es.exists(occursEff(v, _))
        case _ => false
    }

    // Unify two effects. By construction (Figure 16.4) at least one side of an
    // effect unification is an effect variable, so only the variable cases and
    // pure/pure arise in practice.
    def unifyEff(e1: Eff, e2: Eff): Option[Map[String, Desc]] = (e1, e2) match {
        case (EVar(v1), EVar(v2)) =>
            if (v1 == v2) Some(Map.empty)
            else Some(Map(v1 -> DEff(EVar(v2))))
        case (EVar(v), e) =>
            if (occursEff(v, e)) None else Some(Map(v -> DEff(e)))
        case (e, EVar(v)) =>
            if (occursEff(v, e)) None else Some(Map(v -> DEff(e)))
        case (EPure(), EPure()) => Some(Map.empty)
        case _ => None
    }

    // Unify two regions (both are region variables).
    def unifyRegion(r1: String, r2: String): Option[Map[String, Desc]] =
        if (r1 == r2) Some(Map.empty) else Some(Map(r1 -> DReg(r2)))

    def unify(t1: T, t2: T): Option[Map[String, Desc]] = (t1, t2) match {
        case (TBase(n1), TBase(n2)) =>
            if (n1 == n2) Some(Map.empty) else None
        case (TVar(v1), TVar(v2)) =>
            if (v1 == v2) Some(Map.empty)
            else Some(Map(v1 -> DType(TVar(v2))))
        case (TVar(v), t) =>
            if (occursType(v, t)) None else Some(Map(v -> DType(t)))
        case (t, TVar(v)) =>
            if (occursType(v, t)) None else Some(Map(v -> DType(t)))
        case (TArrow(p1, l1, r1), TArrow(p2, l2, r2)) =>
            if (p1.size != p2.size) None
            else p1.zip(p2).foldLeft[Option[Map[String, Desc]]](Some(Map.empty)) {
                case (Some(σ), (a, b)) =>
                    unify(substT(σ, a), substT(σ, b)).map(compose(σ, _))
                case (None, _) => None
            }.flatMap { σ =>
                unifyEff(substEff(σ, l1), substEff(σ, l2)).map(compose(σ, _))
            }.flatMap { σ =>
                unify(substT(σ, r1), substT(σ, r2)).map(compose(σ, _))
            }
        case (TPair(f1, s1), TPair(f2, s2)) =>
            unify(f1, f2).flatMap(σ =>
                unify(substT(σ, s1), substT(σ, s2)).map(compose(σ, _)))
        case (TList(e1), TList(e2)) => unify(e1, e2)
        case (TCell(e1, r1), TCell(e2, r2)) =>
            unify(e1, e2).flatMap { σ =>
                unifyRegion(substReg(σ, r1), substReg(σ, r2)).map(compose(σ, _))
            }
        case _ => None
    }

    // ------------------------------------------------------------------
    // Substitution (a description substitution maps ?vN to a description)
    // ------------------------------------------------------------------

    def subst(σ: Map[String, Desc], d: Desc): Desc = d match {
        case DType(t) => DType(substT(σ, t))
        case DEff(e) => DEff(substEff(σ, e))
        case DReg(id) => DReg(substReg(σ, id))
    }

    def substT(σ: Map[String, Desc], t: T): T = t match {
        case TVar(v) => σ.get(v) match {
            case Some(DType(u)) => substT(σ, u)
            case _ => t
        }
        case TArrow(ps, lat, r) =>
            TArrow(ps.map(substT(σ, _)), substEff(σ, lat), substT(σ, r))
        case TPair(a, b) => TPair(substT(σ, a), substT(σ, b))
        case TList(e) => TList(substT(σ, e))
        case TCell(e, reg) => TCell(substT(σ, e), substReg(σ, reg))
        case other => other
    }

    def substEff(σ: Map[String, Desc], e: Eff): Eff = e match {
        case EVar(v) => σ.get(v) match {
            case Some(DEff(u)) => substEff(σ, u)
            case _ => e
        }
        case EMax(es) => EMax(es.map(substEff(σ, _)))
        case EBase(c, reg) => EBase(c, substReg(σ, reg))
        case EPure() => EPure()
    }

    def substReg(σ: Map[String, Desc], r: String): String = σ.get(r) match {
        case Some(DReg(u)) => substReg(σ, u)
        case _ => r
    }

    // compose(σ1, σ2) = the substitution that applies σ2 first, then σ1.
    def compose(σ1: Map[String, Desc], σ2: Map[String, Desc]): Map[String, Desc] =
        σ2 ++ σ1.map { case (k, v) => k -> subst(σ2, v) }

    // ------------------------------------------------------------------
    // Type-constraint-set solver (Figure 13.11, extended for latent effects
    // and regions)
    // ------------------------------------------------------------------

    def solveTCS(constraints: List[(T, T)]): Solve =
        constraints.foldLeft[Option[(Map[String, Desc], (T, T))]](
            Some((Map.empty, (T.unit, T.unit)))) {
            case (Some((σ, _)), (a, b)) =>
                val (a2, b2) = (substT(σ, a), substT(σ, b))
                unify(a2, b2) match {
                    case Some(s) => Some((compose(σ, s), (a2, b2)))
                    case None => None
                }
            case (None, _) => None
        } match {
            case Some((σ, _)) => Solved(σ)
            case None => Unsolvable(locateFailure(constraints))
        }

    private def locateFailure(constraints: List[(T, T)]): (T, T) =
        constraints.foldLeft[(Option[Map[String, Desc]], (T, T))](
            (Some(Map.empty), (T.unit, T.unit))) {
            case ((Some(σ), _), (a, b)) =>
                val (a2, b2) = (substT(σ, a), substT(σ, b))
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
// Effect-constraint-set solver (Figure 16.4): the least solution, computed as
// the least fixed point of  σ'(δ) = maxeff(σ(δ), σ(F1), ..., σ(Fn))  over the
// constraints (>= δ Fi), starting from σ0(δ) = pure.
// ---------------------------------------------------------------------------

object SolveFCS {
    def solve(fcs: List[EffCon], σTCS: Map[String, Desc]): Map[String, Desc] = {
        // Apply σTCS to both sides of every constraint (to incorporate
        // information from unifying latent-effect and region variables). Keep
        // only the constraints whose left-hand side is still an effect
        // variable; those left-hand variables are exactly dom(FCS).
        val constraints: List[(String, Eff)] =
            fcs.collect {
                case EffCon(d, f) =>
                    val d2 = UnifyE.substEff(σTCS, EVar(d))
                    val f2 = UnifyE.substEff(σTCS, f)
                    d2 match {
                        case EVar(dv) => (dv, f2)
                        case _ => // left-hand side resolved to a base effect /
                                  // pure: the constraint is either trivially
                                  // satisfied or irrelevant to the solution.
                                  null
                    }
            }.filter(_ != null)

        val dom = constraints.map(_._1).toSet
        // Each effect variable is approximated by the set of base effects it
        // denotes; start from the bottom (the empty set).
        var sigma: Map[String, Set[(String, String)]] = dom.map(_ -> Set.empty).toMap
        var changed = true
        while (changed) {
            changed = false
            val newSigma = dom.map { d =>
                val added = constraints
                    .filter(_._1 == d)
                    .map { case (_, f) => Eff.baseSet(f, sigma) }
                val s = sigma(d) ++ added.flatten
                if (s != sigma(d)) changed = true
                (d, s)
            }.toMap
            sigma = newSigma
        }
        sigma.map { case (d, s) => d -> DEff(Eff.fromSet(s)) }
    }
}

// ---------------------------------------------------------------------------
// The primitive type environment TEprim (Figure 16.2, page 952): the base
// primops have pure latent effects; the cell operators carry base-effect
// latents (init / read / write) parameterized by the cell's region. All
// schemas have an empty effect-constraint set (the reference FLARE/E system
// does not use effect-based masking, §16.2.4).
// ---------------------------------------------------------------------------

object TEPrimE {

    val primops: Set[String] = Set(
        "not", "and", "or", "bool=?",
        "=", "!=", "<", "<=", ">", ">=",
        "+", "-", "*", "/", "%", "sym=?",
        "pair", "fst", "snd",
        "cons", "car", "cdr", "null", "null?",
        "cell", "^", ":=", "cell=?")

    private def closed(t: T): TS = TSClosed(t)
    private def generic(bound: List[String], t: T): TS = TSGeneric(bound, t, Nil)
    private def tv(s: String): T = TVar(s)
    private def pure: Eff = EPure()

    val schemas: Map[String, TS] = Map(
        "not" -> closed(T.arrow(List(T.bool), pure, T.bool)),
        "and" -> closed(T.arrow(List(T.bool, T.bool), pure, T.bool)),
        "or" -> closed(T.arrow(List(T.bool, T.bool), pure, T.bool)),
        "bool=?" -> closed(T.arrow(List(T.bool, T.bool), pure, T.bool)),
        "=" -> closed(T.arrow(List(T.int, T.int), pure, T.bool)),
        "!=" -> closed(T.arrow(List(T.int, T.int), pure, T.bool)),
        "<" -> closed(T.arrow(List(T.int, T.int), pure, T.bool)),
        "<=" -> closed(T.arrow(List(T.int, T.int), pure, T.bool)),
        ">" -> closed(T.arrow(List(T.int, T.int), pure, T.bool)),
        ">=" -> closed(T.arrow(List(T.int, T.int), pure, T.bool)),
        "+" -> closed(T.arrow(List(T.int, T.int), pure, T.int)),
        "-" -> closed(T.arrow(List(T.int, T.int), pure, T.int)),
        "*" -> closed(T.arrow(List(T.int, T.int), pure, T.int)),
        "/" -> closed(T.arrow(List(T.int, T.int), pure, T.int)),
        "%" -> closed(T.arrow(List(T.int, T.int), pure, T.int)),
        "sym=?" -> closed(T.arrow(List(T.symb, T.symb), pure, T.bool)),
        "pair" -> generic(List("?a", "?b"),
            T.arrow(List(tv("?a"), tv("?b")), pure, TPair(tv("?a"), tv("?b")))),
        "fst" -> generic(List("?a", "?b"),
            T.arrow(List(TPair(tv("?a"), tv("?b"))), pure, tv("?a"))),
        "snd" -> generic(List("?a", "?b"),
            T.arrow(List(TPair(tv("?a"), tv("?b"))), pure, tv("?b"))),
        "cons" -> generic(List("?a"),
            T.arrow(List(tv("?a"), TList(tv("?a"))), pure, TList(tv("?a")))),
        "car" -> generic(List("?a"),
            T.arrow(List(TList(tv("?a"))), pure, tv("?a"))),
        "cdr" -> generic(List("?a"),
            T.arrow(List(TList(tv("?a"))), pure, TList(tv("?a")))),
        "null" -> generic(List("?a"),
            T.arrow(Nil, pure, TList(tv("?a")))),
        "null?" -> generic(List("?a"),
            T.arrow(List(TList(tv("?a"))), pure, T.bool)),
        // Figure 16.2 (the cell operators, verbatim from the book)
        "cell" -> generic(List("?t", "?r"),
            T.arrow(List(tv("?t")), EBase("init", "?r"), TCell(tv("?t"), "?r"))),
        "^" -> generic(List("?t", "?r"),
            T.arrow(List(TCell(tv("?t"), "?r")), EBase("read", "?r"), tv("?t"))),
        ":=" -> generic(List("?t", "?r"),
            T.arrow(List(TCell(tv("?t"), "?r"), tv("?t")), EBase("write", "?r"), T.unit)),
        "cell=?" -> generic(List("?t", "?r1", "?r2"),
            T.arrow(List(TCell(tv("?t"), "?r1"), TCell(tv("?t"), "?r2")), pure, T.bool))
    )

    def schema(op: String): TS = schemas(op)
}
