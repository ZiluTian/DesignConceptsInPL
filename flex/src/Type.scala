package DSL.flex

import DSL.fl._

// The type domain of FLEX (Figure 11.31 of the book):
//
//   T ::= BT                    [BaseType]
//       | τ                     [TypeIdentifier]
//       | (-> (Targ*) Tresult)  [ArrowType]
//       | (cellof T)
//       | (pairof T T)
//       | (prodof T*)
//       | (seqof T)
//       | (listof T)
//       | (recordof (I T)*)
//       | (oneof (I T)*)
//       | (trec τ T)            [single recursive type]
//       | (tletrec ((τ T)*) T)  [mutually recursive types]
//
// BT ∈ BaseType = {unit, int, bool, symb}
// τ ∈ TypeId   = SymLit − TypeKeyword
//
// Value identifiers and type identifiers are in separate namespaces (book
// p.635); a type may therefore never name a value, and vice versa.

sealed trait T

final case class TBase(name: String) extends T            // unit | int | bool | symb
final case class TVar(name: String) extends T             // a type identifier τ
final case class TArrow(args: List[T], ret: T) extends T
final case class TPair(fst: T, snd: T) extends T
final case class TProd(comps: List[T]) extends T
final case class TSeq(elem: T) extends T
final case class TRecord(fields: List[(String, T)]) extends T
final case class TOneof(tags: List[(String, T)]) extends T
final case class TList(elem: T) extends T
final case class TCell(elem: T) extends T
final case class TTrec(name: String, body: T) extends T
final case class TTletrec(bindings: List[(String, T)], body: T) extends T

object T {

    val BaseTypeNames: Set[String] = Set("unit", "int", "bool", "symb")
    val TypeKeywords: Set[String] = BaseTypeNames ++
        Set("->", "cellof", "listof", "oneof", "pairof", "prodof", "recordof",
            "seqof", "tletrec", "trec")

    // ------------------------------------------------------------------
    // Parsing (raw s-expression tree -> type)
    // ------------------------------------------------------------------

    def parse(raw: Raw): Option[T] = raw match {
        case RawAtom(a) =>
            if (BaseTypeNames.contains(a)) Some(TBase(a))
            else if (TypeKeywords.contains(a)) None // a keyword is not a type identifier
            else Some(TVar(a))
        case RawList(items) => items match {
            case List(RawAtom("->"), argsRaw, retRaw) =>
                parseTypeList(argsRaw) flatMap { args => parse(retRaw) map (ret => TArrow(args, ret)) }
            case List(RawAtom("pairof"), t1, t2) =>
                both(parse(t1), parse(t2)) (TPair(_, _))
            case List(RawAtom("prodof"), ts @ _*) =>
                all(ts.toList.map(parse)) (cs => TProd(cs))
            case List(RawAtom("seqof"), t) => parse(t) map (x => TSeq(x))
            case List(RawAtom("listof"), t) => parse(t) map (x => TList(x))
            case List(RawAtom("cellof"), t) => parse(t) map (x => TCell(x))
            case List(RawAtom("recordof"), assocs @ _*) =>
                parseAssocs(assocs.toList) map (fs => TRecord(fs))
            case List(RawAtom("oneof"), assocs @ _*) =>
                parseAssocs(assocs.toList) map (ts => TOneof(ts))
            case List(RawAtom("trec"), RawAtom(name), body) =>
                if (TypeKeywords.contains(name)) None
                else parse(body) map (b => TTrec(name, b))
            case List(RawAtom("tletrec"), bindsRaw, body) =>
                parseBindings(bindsRaw) flatMap { bs => parse(body) map (b => TTletrec(bs, b)) }
            case _ => None
        }
    }

    // ((T1 T2 ...) ) -> List[T1, T2, ...]
    def parseTypeList(raw: Raw): Option[List[T]] = raw match {
        case RawList(items) => all(items.map(parse)) (identity)
        case _ => None
    }

    // ((I1 T1) ... (In Tn)) -> List((I1, T1), ..., (In, Tn))
    def parseAssocs(raws: List[Raw]): Option[List[(String, T)]] =
        all(raws.map {
            case RawList(List(RawAtom(n), tRaw)) =>
                if (TypeKeywords.contains(n)) None else parse(tRaw) map (n -> _)
            case _ => None
        }) (identity)

    // ((τ1 T1) ... (τn Tn)) -> List((τ1, T1), ...)
    def parseBindings(raw: Raw): Option[List[(String, T)]] = raw match {
        case RawList(items) =>
            all(items.map {
                case RawList(List(RawAtom(n), tRaw)) =>
                    if (TypeKeywords.contains(n)) None else parse(tRaw) map (n -> _)
                case _ => None
            }) (identity)
        case _ => None
    }

    private def both[A, B, C](oa: Option[A], ob: Option[B])(f: (A, B) => C): Option[C] =
        oa flatMap { a => ob map (b => f(a, b)) }
    private def all[A, B](oas: List[Option[A]])(f: List[A] => B): Option[B] =
        oas.foldRight[Option[List[A]]](Some(Nil)) { (oa, acc) =>
            acc flatMap { as => oa map (a => a :: as) }
        } map f

    // ------------------------------------------------------------------
    // Well-formedness: every free type identifier must be bound, either by
    // an enclosing trec/tletrec inside the type, or by `outer`.
    // Returns None if well formed, Some(message) otherwise.
    // ------------------------------------------------------------------

    def wellFormed(t: T, outer: Set[String]): Option[String] = {
        def firstErr(oas: List[Option[String]]): Option[String] =
            oas.collectFirst { case Some(m) => m }
        def go(x: T, binders: Set[String]): Option[String] = x match {
            case TBase(_) => None
            case TVar(n) =>
                if (binders.contains(n) || outer.contains(n)) None
                else Some(s"unbound type identifier: $n")
            case TArrow(args, ret) => firstErr(args.map(go(_, binders)) :+ go(ret, binders))
            case TPair(f, s) => firstErr(List(go(f, binders), go(s, binders)))
            case TProd(cs) => firstErr(cs.map(go(_, binders)))
            case TSeq(e) => go(e, binders)
            case TRecord(fs) => firstErr(fs.map { case (_, d) => go(d, binders) })
            case TOneof(ts) => firstErr(ts.map { case (_, d) => go(d, binders) })
            case TList(e) => go(e, binders)
            case TCell(e) => go(e, binders)
            case TTrec(name, body) => go(body, binders + name)
            case TTletrec(binds, body) =>
                val bs = binders ++ binds.map(_._1).toSet
                firstErr(binds.map { case (_, d) => go(d, bs) } :+ go(body, bs))
        }
        go(t, Set.empty)
    }

    // ------------------------------------------------------------------
    // Display
    // ------------------------------------------------------------------

    def show(t: T): String = t match {
        case TBase(name) => name
        case TVar(name) => name
        case TArrow(args, ret) => "(-> (" + args.map(show).mkString(" ") + ") " + show(ret) + ")"
        case TPair(f, s) => "(pairof " + show(f) + " " + show(s) + ")"
        case TProd(cs) => "(prodof" + (if (cs.isEmpty) "" else " " + cs.map(show).mkString(" ")) + ")"
        case TSeq(e) => "(seqof " + show(e) + ")"
        case TRecord(fs) => "(recordof" + (if (fs.isEmpty) "" else " " + fs.map { case (n, d) => s"($n ${show(d)})" }.mkString(" ")) + ")"
        case TOneof(ts) => "(oneof" + (if (ts.isEmpty) "" else " " + ts.map { case (n, d) => s"($n ${show(d)})" }.mkString(" ")) + ")"
        case TList(e) => "(listof " + show(e) + ")"
        case TCell(e) => "(cellof " + show(e) + ")"
        case TTrec(name, body) => "(trec " + name + " " + show(body) + ")"
        case TTletrec(binds, body) =>
            "(tletrec (" + binds.map { case (n, d) => s"($n ${show(d)})" }.mkString(" ") + ") " + show(body) + ")"
    }
}

// A type "in context": a type tree plus the environment that interprets its
// free type identifiers. Invariant: every type identifier that occurs free in
// `t` (and in any value of `env`) is a key of `env`, and `env` is
// self-contained (its values are interpreted in `env` itself). A type with no
// free identifiers has an empty environment.
final case class CT(t: T, env: Map[String, T]) {
    def show: String = T.show(t)
}

object CT {

    def closed(t: T): CT = CT(t, Map.empty)

    // Open a top-level type annotation (a formal type, a declared letrec type,
    // a `the`/`one`/`null` type, a def-type): it must be closed, i.e. well
    // formed relative to the empty environment.
    def open(t: T): Option[CT] =
        T.wellFormed(t, Set.empty) match {
            case None => Some(CT(t, Map.empty)) // well formed: open with an empty environment
            case Some(m) => None // malformed (e.g. an unbound type identifier)
        }

    // One "two-finger" step (book p.691): if the pointer is a type identifier
    // with an environment definition, a trec, or a tletrec, expose its
    // body/definition; otherwise leave the type unchanged.
    def step(p: CT): CT = p.t match {
        case TVar(n) => p.env.get(n) match {
            case Some(d) => CT(d, p.env)
            case None => p
        }
        case TTrec(name, body) => CT(body, p.env.updated(name, p.t))
        case TTletrec(bindings, body) =>
            CT(body, p.env ++ bindings.map { case (n, d) => n -> d }.toMap)
        case _ => p
    }

    def isRecursive(p: CT): Boolean = p.t match {
        case TVar(n) => p.env.contains(n)
        case TTrec(_, _) => true
        case TTletrec(_, _) => true
        case _ => false
    }

    // ------------------------------------------------------------------
    // Equirecursive type equivalence (Figure 11.28 of the book).
    //
    // A two-finger comparison of the (potentially infinite) unwoundings of
    // the two types, with an assumption set of type pairs already assumed
    // equal. When both fingers point at a recursive type (a trec, a tletrec,
    // or a type identifier with a definition), the pair is recorded as an
    // assumption and the comparison continues on the unwound types;
    // re-encountering an assumed pair ends that branch, which is what makes
    // the search terminate on (potentially) infinite unwoundings.
    // recordof / oneof compare up to permutation of their associations
    // (Section 11.8.2 and the [oneof-approx] rule).
    // ------------------------------------------------------------------

    def equiv(c1: CT, c2: CT): Boolean = cmp(c1, c2, Set.empty)

    private def cmp(p1: CT, p2: CT, AS: Set[(CT, CT)]): Boolean =
        if (!isRecursive(p1) && !isRecursive(p2)) structural(p1, p2, AS)
        else if (AS.contains((p1, p2))) true
        else cmp(step(p1), step(p2), AS + ((p1, p2)))

    private def structural(p1: CT, p2: CT, AS: Set[(CT, CT)]): Boolean =
        (p1.t, p2.t) match {
            case (TBase(a), TBase(b)) => a == b
            case (TVar(a), TVar(b)) => a == b // unbound identifiers (malformed input)
            case (TArrow(a1, r1), TArrow(a2, r2)) =>
                a1.size == a2.size &&
                    a1.zip(a2).forall { case (x, y) => cmp(CT(x, p1.env), CT(y, p2.env), AS) } &&
                    cmp(CT(r1, p1.env), CT(r2, p2.env), AS)
            case (TPair(f1, s1), TPair(f2, s2)) =>
                cmp(CT(f1, p1.env), CT(f2, p2.env), AS) &&
                cmp(CT(s1, p1.env), CT(s2, p2.env), AS)
            case (TProd(c1), TProd(c2)) =>
                c1.size == c2.size &&
                    c1.zip(c2).forall { case (x, y) => cmp(CT(x, p1.env), CT(y, p2.env), AS) }
            case (TSeq(e1), TSeq(e2)) => cmp(CT(e1, p1.env), CT(e2, p2.env), AS)
            case (TRecord(f1), TRecord(f2)) => fieldsEquiv(f1, f2, p1.env, p2.env, AS)
            case (TOneof(f1), TOneof(f2)) => fieldsEquiv(f1, f2, p1.env, p2.env, AS)
            case (TList(e1), TList(e2)) => cmp(CT(e1, p1.env), CT(e2, p2.env), AS)
            case (TCell(e1), TCell(e2)) => cmp(CT(e1, p1.env), CT(e2, p2.env), AS)
            case _ => false
        }

    private def fieldsEquiv(f1: List[(String, T)], f2: List[(String, T)],
                            e1: Map[String, T], e2: Map[String, T],
                            AS: Set[(CT, CT)]): Boolean =
        f1.size == f2.size && f1.forall { case (n, t) =>
            f2.find(_._1 == n).exists { case (_, t2) => cmp(CT(t, e1), CT(t2, e2), AS) }
        }

    // ------------------------------------------------------------------
    // Unwrapping: "is this type, possibly behind recursive indirections, an
    // arrow / pair / ...?" The type rules for ->-elim, pairof-elim,
    // oneof-intro/elim, listof-elim, cellof-elim, ... need to inspect the
    // constructor underneath recursive types. Example (Exercise 11.24):
    // (trec s (-> (s) T)) unwinds to an arrow whose argument type is the
    // trec itself.
    // ------------------------------------------------------------------

    // Step through recursive indirections until the pointer is a
    // non-recursive type, or give up (None) on an indirection cycle.
    private def concrete(p: CT): Option[CT] = {
        def go(c: CT, seen: Set[CT]): Option[CT] =
            if (isRecursive(c)) {
                if (seen.contains(c)) None
                else go(step(c), seen + c)
            } else Some(c)
        go(p, Set.empty)
    }

    def asArrow(p: CT): Option[(List[CT], CT)] =
        concrete(p) flatMap { c => c.t match {
            case TArrow(args, ret) => Some((args.map(a => CT(a, c.env)), CT(ret, c.env)))
            case _ => None
        } }

    def asPair(p: CT): Option[(CT, CT)] =
        concrete(p) flatMap { c => c.t match {
            case TPair(f, s) => Some((CT(f, c.env), CT(s, c.env)))
            case _ => None
        } }

    def asProd(p: CT): Option[List[CT]] =
        concrete(p) flatMap { c => c.t match {
            case TProd(cs) => Some(cs.map(x => CT(x, c.env)))
            case _ => None
        } }

    def asSeq(p: CT): Option[CT] =
        concrete(p) flatMap { c => c.t match {
            case TSeq(e) => Some(CT(e, c.env))
            case _ => None
        } }

    def asRecord(p: CT): Option[List[(String, CT)]] =
        concrete(p) flatMap { c => c.t match {
            case TRecord(fs) => Some(fs.map { case (n, d) => (n, CT(d, c.env)) })
            case _ => None
        } }

    def asOneof(p: CT): Option[List[(String, CT)]] =
        concrete(p) flatMap { c => c.t match {
            case TOneof(ts) => Some(ts.map { case (n, d) => (n, CT(d, c.env)) })
            case _ => None
        } }

    def asListof(p: CT): Option[CT] =
        concrete(p) flatMap { c => c.t match {
            case TList(e) => Some(CT(e, c.env))
            case _ => None
        } }

    def asCell(p: CT): Option[CT] =
        concrete(p) flatMap { c => c.t match {
            case TCell(e) => Some(CT(e, c.env))
            case _ => None
        } }

    // ------------------------------------------------------------------
    // Environment-clash renaming: when composing types (e.g. building the
    // arrow type of an abs from its parameter types and its body type), the
    // resulting type may carry several distinct environments. If two
    // components bound the same type identifier to different definitions,
    // the names are renamed (type identifiers are bound by trec/tletrec, so
    // alpha-renaming is safe) until the environments are disjoint.
    // ------------------------------------------------------------------

    private var nameCounter = 0
    private def freshType(name: String): String = {
        nameCounter += 1
        s"@@$name$nameCounter"
    }

    def renameEnv(ct: CT, avoid: Set[String]): CT = {
        val renames: Map[String, String] =
            ct.env.keys.filter(avoid.contains).map(n => n -> freshType(n)).toMap
        if (renames.isEmpty) ct
        else {
            val t2 = Subst.renameType(ct.t, renames)
            val env2 = ct.env.map { case (n, d) =>
                (Subst.renameName(n, renames), Subst.renameType(d, renames))
            }
            CT(t2, env2)
        }
    }
}
