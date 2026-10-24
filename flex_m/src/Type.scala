package DSL.flex_m

import DSL.fl._
import DSL.sexp._
import DSL.flex._

// The type domain of FLEX/M (Chapter 15.2, Figure 15.1 of the book).
//
// FLEX/M extends FLEX/SP with static dependent types: apart from the
// dependent type constructors (dselect θ Emod), value identifiers may occur
// only inside type constructors. There are no recursive types (trec /
// tletrec were removed: all recursion is abstracted inside modules), so the
// type-level machinery of FLEX (the CT equirecursive environment) is
// replaced by plain structural relations with alpha-renaming.
//
// Types (the T domain of Figure 15.1):
//
//   (unit | int | bool | symb)               base types
//   τ                                        type identifiers (pabs / forall-bound)
//   ?v                                       unification variables (implicit projection;
//                                           never legal in an annotation)
//   (-> ((I1 T1) ... (In Tn)) T0)           parameterized arrow type — the
//                                           parameter names are value names
//                                           (bound in the later parameter types and the
//                                           result); the sugar form (-> (T1 ... Tn) T0)
//                                           desugars with fresh parameter names
//   (recordof (I1 T1) ...) (oneof ...) (prodof ...) (seqof T) (cellof T)
//   (forall (τ1 ... τn) T)
//   (moduleof ((θ1 τ1* ...) ...) (I1 T1) ...)  module (signature) type; the AT
//                                           dummies have no binding power
//   (TC T1 ... Tn)                           type-constructor application, where
//                                           TC ::= θ  |  (dselect θ Emod)
//
// Identifier namespaces (Figure 15.1):
//
//   θ ∈ TyConId   = names ending in "of" − TypeKwd   (listof, pairof, envof, ...)
//   τ ∈ TypeId    = SymLit − (TypeKwd ∪ UniVar ∪ TyConId)
//   I ∈ Ident     = IdentFLEX/SP − (ExpKwd ∪ TypeKwd ∪ TyConId)
//   TypeKwd       = BaseType ∪ {->, cellof, moduleof, oneof, prodof, recordof, seqof}

sealed trait MT

// ---------------------------------------------------------------------------
// The type domain
// ---------------------------------------------------------------------------

case class MTBase(name: String) extends MT                    // unit | int | bool | symb
case class MTVar(name: String) extends MT                     // a type identifier
case class MTUnif(name: String) extends MT                    // a unification variable (?v)

// (-> ((I1 T1) ... (In Tn)) T0): the parameter names are value names; they
// shadow in the later parameter types and the result type (a parameter type
// may mention earlier parameter names, inside dselects).
case class MTArrow(params: List[(String, MT)], ret: MT) extends MT

case class MTRecord(fields: List[(String, MT)]) extends MT
case class MTOneof(tags: List[(String, MT)]) extends MT
case class MTProd(comps: List[MT]) extends MT
case class MTSeq(elem: MT) extends MT
case class MTCell(elem: MT) extends MT                        // cellof (invariant content)
case class MTForall(vars: List[String], body: MT) extends MT  // (forall (τ*) T)

// (moduleof (AT*) (I T)*): the abstract-type specifications (name, dummy
// parameter names — the dummies are pure names with no binding power; only
// their number matters) and the value-component types.
case class MTModuleof(ats: List[(String, List[String])], vals: List[(String, MT)]) extends MT

// A type constructor (the TC domain of Figure 15.1).
sealed trait TyCon
// θ — a (possibly local or ambient) type-constructor name.
case class TyConName(name: String) extends TyCon
// (dselect θ Emod) — a dependent type constructor selected from the module
// denoted by the (pure) expression Emod.
case class TyConSelect(name: String, emod: Exp) extends TyCon

// (TC T1 ... Tn) — a type-constructor application (a bare θ is not a type;
// a nullary application is written (θ)).
case class MTyConApp(tc: TyCon, args: List[MT]) extends MT

// ---------------------------------------------------------------------------
// Scopes of type-constructor names (the scoping of Section 15.4.1)
// ---------------------------------------------------------------------------
//
// Two kinds of tycon scopes nest in the checker:
//
//   ScopeDeclare(names)  — the type-constructor names declared by a module
//                          (or by a moduleof type's AT list): a bare θ
//                          resolves to TyConName(θ) (an opaque local name).
//   ScopeOpen(names, m)  — the type-constructor names of an opened module:
//                          a bare θ resolves to TyConSelect(θ, m)
//                          (a dependent type constructor).
//
// The innermost scope wins.

sealed trait TyconScope
case class ScopeDeclare(names: Set[String]) extends TyconScope
case class ScopeOpen(names: Set[String], emod: Exp) extends TyconScope

// ---------------------------------------------------------------------------
// Fresh names
// ---------------------------------------------------------------------------

object Fresh {
    private var counter = 0
    def next(): String = {
        counter += 1
        counter.toString
    }
}

// ---------------------------------------------------------------------------
// Display (MT.show)
// ---------------------------------------------------------------------------
//
// The display matches the book's notation: sugar arrow types (-> (T*) T0)
// whenever no parameter name occurs free in the parameter types or the
// result, and the parameterized form (-> ((I T)*) T0) otherwise. Type-
// constructor applications display as (θ T*) (a nullary application as
// (θ)); dependent ones as ((dselect θ <Emod>) T*).

object MT {

    val TypeKeywords: Set[String] =
        Set("unit", "int", "bool", "symb", "->", "cellof", "moduleof",
            "oneof", "prodof", "recordof", "seqof")

    // θ ∈ TyConId: names ending in "of", excluding the type keywords.
    def isTyConName(n: String): Boolean =
        n.endsWith("of") && !TypeKeywords.contains(n)

    // τ ∈ TypeId: not a type keyword, not a unification variable, not a
    // type-constructor name, and not reserved for the concrete syntax of
    // the dependent forms.
    def isTypeIdent(n: String): Boolean =
        !n.startsWith("?") && !n.startsWith("@") &&
            !TypeKeywords.contains(n) && !isTyConName(n) &&
            n != "forall" && n != "dselect"

    def show(t: MT): String = t match {
        case MTBase(n) => n
        case MTVar(n) => n
        case MTUnif(n) => n
        case MTArrow(params, ret) =>
            // The parameterized form (-> ((I Ti)*) T0) is displayed when a
            // parameter name occurs in a later parameter type or in the
            // result (the binding scope of Ii is Ti+1* T0, book Figure 15.2
            // footnote 3). Occurrences of a parameter name in its own
            // parameter type are not references (the binding starts
            // after it), so they do not trigger the parameterized form.
            val dependent = params.indices.exists { i =>
                val n = params(i)._1
                params.drop(i + 1).map(_._2).flatMap(Fr.valueRefs).toSet.contains(n)
                    || Fr.valueRefs(ret).contains(n)
            }
            if (dependent)
                "(-> ((" + params.map { case (n, pt) => n + " " + show(pt) }.mkString(" ") +
                ")) " + show(ret) + ")"
            else
                "(-> (" + params.map(_._2).map(show).mkString(" ") + ") " + show(ret) + ")"
        case MTRecord(fields) =>
            "(recordof (" + fields.map { case (n, ft) => n + " " + show(ft) }.mkString(" ") + "))"
        case MTOneof(tags) =>
            "(oneof (" + tags.map { case (n, tt) => n + " " + show(tt) }.mkString(" ") + "))"
        case MTProd(comps) =>
            "(prodof (" + comps.map(show).mkString(" ") + "))"
        case MTSeq(elem) => "(seqof " + show(elem) + ")"
        case MTCell(elem) => "(cellof " + show(elem) + ")"
        case MTForall(vars, body) =>
            "(forall (" + vars.mkString(" ") + ") " + show(body) + ")"
        case MTModuleof(ats, vals) =>
            // (moduleof ((θ τ*)*) (I T)*) — the value components are
            // individual items of the form list (matching the parser).
            "(moduleof (" + ats.map { case (n, dummies) =>
                "(" + n + (if (dummies.isEmpty) "" else " " + dummies.mkString(" ")) + ")"
            }.mkString(" ") + ")" +
            vals.map { case (n, vt) => " (" + n + " " + show(vt) + ")" }.mkString("") + ")"
        case MTyConApp(TyConName(name), args) =>
            "(" + name + (if (args.isEmpty) "" else " " + args.map(show).mkString(" ")) + ")"
        case MTyConApp(TyConSelect(name, emod), args) =>
            "((dselect " + name + " " + FlexMExp.show(emod) + ")" +
            (if (args.isEmpty) "" else " " + args.map(show).mkString(" ")) + ")"
    }

    // ------------------------------------------------------------------
    // Parsing (raw s-expression tree -> type)
    // ------------------------------------------------------------------

    // Map Option over a list, collecting Some into a list; None if any is None.
    private def allOf[A](opts: List[Option[A]]): Option[List[A]] =
        opts.foldRight[Option[List[A]]](Some(Nil)) { (o, acc) =>
            (o, acc) match {
                case (Some(a), Some(as)) => Some(a :: as)
                case _ => None
            }
        }

    def parse(raw: Raw): Option[MT] = raw match {
        case RawAtom(a) => parseAtom(a)
        case RawList(items) => parseList(items)
    }

    private def parseAtom(a: String): Option[MT] =
        if (TypeKeywords.contains(a) && Set("unit", "int", "bool", "symb").contains(a))
            Some(MTBase(a))
        else if (a.startsWith("?"))
            Some(MTUnif(a))            // rejected by open (unification variables)
        else if (isTypeIdent(a))
            Some(MTVar(a))
        else
            None                       // a keyword or a tycon name is not a bare type

    private def parseList(items: List[Raw]): Option[MT] = items match {
        case Nil => None
        case RawAtom(head) :: rest =>
            head match {
                case "->" => parseArrow(rest)
                case "cellof" => rest match {
                    case List(tRaw) => parse(tRaw) map (MTCell(_))
                    case _ => None
                }
                case "seqof" => rest match {
                    case List(tRaw) => parse(tRaw) map (MTSeq(_))
                    case _ => None
                }
                case "recordof" => rest match {
                    case List(fieldsRaw) =>
                        parseRecordFields(fieldsRaw) map (MTRecord(_))
                    case _ => None
                }
                case "oneof" => rest match {
                    case List(tagsRaw) =>
                        parseRecordFields(tagsRaw) map (MTOneof(_))
                    case _ => None
                }
                case "prodof" => allOf(rest.map(parse)) map (MTProd(_))
                case "forall" => rest match {
                    case List(varsRaw, bodyRaw) =>
                        (parseTypeVars(varsRaw), parse(bodyRaw)) match {
                            case (Some(vs), Some(b)) => Some(MTForall(vs, b))
                            case _ => None
                        }
                    case _ => None
                }
                case "moduleof" => rest match {
                    // (moduleof ((θ τ*)*) (I T)*) — the value components
                    // are individual items of the form list (matching MT.show).
                    case atsRaw :: pairs =>
                        (parseAbsTySpec(atsRaw), parseModuleVals(RawList(pairs))) match {
                            case (Some(ats), Some(vals)) => Some(MTModuleof(ats, vals))
                            case _ => None
                        }
                    case _ => None
                }
                // A type-constructor application (θ T*), where θ ends in "of".
                case name if isTyConName(name) =>
                    allOf(rest.map(parse)) map (args => MTyConApp(TyConName(name), args))
                case _ => None
            }
        // ((dselect θ Emod) T*) — a dependent type-constructor application.
        // The module expression Emod is interpreted by the program parser
        // (FlexMProgram.interpretExp); it must denote a pure module value
        // (the [moduleof-elim] rule rejects impure ones at check time).
        case RawList(List(RawAtom("dselect"), RawAtom(name), emodRaw)) :: rest =>
            if (isTyConName(name))
                (FlexMProgram.interpretExp(emodRaw), allOf(rest.map(parse))) match {
                    case (Some(emod), Some(args)) =>
                        Some(MTyConApp(TyConSelect(name, emod), args))
                    case _ => None
                }
            else None
        // A nullary dependent type-constructor application (dselect θ Emod).
        case RawAtom("dselect") :: RawAtom(name) :: emodRaw :: Nil =>
            if (isTyConName(name))
                FlexMProgram.interpretExp(emodRaw) match {
                    case Some(emod) => Some(MTyConApp(TyConSelect(name, emod), Nil))
                    case None => None
                }
            else None
        case _ => None
    }

    // (-> (T*) T0) or (-> ((I T)*) T0). The two forms are unambiguous
    // (book p.895, note 4): tycon names and type keywords cannot be value
    // identifiers, so a parameter-list item that begins with a type keyword
    // or a tycon name is a single list-form type, not a sequence of
    // parameters.
    // Atoms that head a list-form type in type position (the parseList
    // keyword heads plus type-constructor names).
    private def arrowListFormHead(h: String): Boolean =
        Set("cellof", "seqof", "recordof", "oneof", "prodof", "forall", "moduleof", "->")
            .contains(h) || isTyConName(h)

    private def parseArrow(items: List[Raw]): Option[MT] = items match {
        case List(paramsRaw, retRaw) =>
            val params: Option[List[(String, MT)]] = paramsRaw match {
                case RawList(pItems) =>
                    pItems.headOption match {
                        // A single list-form type as the whole parameter list:
                        // (-> (moduleof ...) T), (-> (listof int) T), (-> (-> ...) T), ...
                        case Some(RawAtom(h)) if arrowListFormHead(h) =>
                            parse(paramsRaw) map (t => List("@@flexm_ap" + Fresh.next() -> t))
                        case _ =>
                            val named: List[Option[(String, MT)]] = pItems.map {
                                case RawList(List(RawAtom(n), tRaw)) if Idents.validValueIdent(n) =>
                                    parse(tRaw) map (t => n -> t)
                                case _ => None
                            }
                            val typed: List[Option[MT]] = pItems.map(parse)
                            if (pItems.nonEmpty && named.forall(_.isDefined) && named.exists(_.isDefined))
                                allOf(named)
                            else if (typed.forall(_.isDefined))
                                // Sugar form: fresh parameter names that never leak
                                // into a displayed type (they are never free).
                                allOf(typed) map (ts =>
                                    ts.zipWithIndex.map { case (t, i) => "@@flexm_ap" + Fresh.next() -> t })
                            else
                                None
                    }
                case _ => None
            }
            (params, parse(retRaw)) match {
                case (Some(ps), Some(ret)) => Some(MTArrow(ps, ret))
                case _ => None
            }
        case _ => None
    }

    // (I1 T1 I2 T2 ...) — the field list of a recordof / oneof type
    // (Figure 12.12: (recordof (Iname Tdefn)*)): a flat sequence of
    // name / type items, matching MT.show.
    private def parseRecordFields(raw: Raw): Option[List[(String, MT)]] = raw match {
        case RawList(items) if items.size % 2 == 0 => allOf(items.grouped(2).toList.map {
            case List(RawAtom(n), tRaw) if Idents.validValueIdent(n) =>
                parse(tRaw) map (t => n -> t)
            case _ => None
        })
        case RawList(items) => allOf(items.map {
            case RawList(List(RawAtom(n), tRaw)) if Idents.validValueIdent(n) =>
                parse(tRaw) map (t => n -> t)
            case _ => None
        })
        case _ => None
    }

    // ((θ1 τ1* ...) ...) — the abstract-type specifications of a moduleof.
    private def parseAbsTySpec(raw: Raw): Option[List[(String, List[String])]] = raw match {
        case RawList(items) => allOf(items.map {
            case RawList(RawAtom(name) :: dummies) if isTyConName(name) =>
                val ds: List[Option[String]] = dummies.map {
                    case RawAtom(d) if isTypeIdent(d) => Some(d)
                    case _ => None
                }
                if (ds.forall(_.isDefined)) Some(name -> ds.map(_.get)) else None
            case _ => None
        })
        case _ => None
    }

    // (I1 T1) ... — the value components of a moduleof type.
    private def parseModuleVals(raw: Raw): Option[List[(String, MT)]] = raw match {
        case RawList(items) => allOf(items.map {
            case RawList(List(RawAtom(n), tRaw)) if Idents.validValueIdent(n) =>
                parse(tRaw) map (t => n -> t)
            case _ => None
        })
        case _ => None
    }

    // (I1 ... In) — a list of type identifiers (a forall binder list).
    private def parseTypeVars(raw: Raw): Option[List[String]] = raw match {
        case RawList(items) =>
            val vs: List[Option[String]] = items.map {
                case RawAtom(n) if isTypeIdent(n) => Some(n)
                case _ => None
            }
            if (vs.forall(_.isDefined) && vs.map(_.get).toSet.size == vs.size)
                Some(vs.map(_.get))
            else None
        case _ => None
    }

}

// A value-identifier position: not a keyword, not a type keyword, and not a
// type-constructor name (Figure 15.1: I ∈ Ident = IdentFLEX/SP − (ExpKwd ∪
// TypeKwd ∪ TyConId)).
object Idents {
    // FLEX/M keywords (Figures 15.1 and 15.2): the FLEX/SP keywords except
    // letrec (now sugar), except the pair / list forms (pair, fst, snd,
    // cons, car, cdr, null, null? are ordinary value names in FLEX/M), plus
    // the new forms module, open, load, match, mselect.
    val keywords: Set[String] = Set(
        // program keywords
        "flex/M", "flex/Mk",
        // kernel expression keywords
        "error", "if", "prim", "abs", "let", "the", "sym",
        "prod", "get",
        "seq", "seq-get", "seq-size",
        "record", "select", "with",
        "one", "tagcase",
        "set!", "cell", "^", ":=", "cell=?",
        "pabs", "pcall",
        "module", "open", "load", "match",
        // sugar keywords
        "cond", "def", "def-type", "def-datatype", "else", "let-type",
        "let-type*", "letrec", "mselect", "scand", "scor", "begin")

    def validValueIdent(name: String): Boolean =
        !name.startsWith("@") && !keywords.contains(name) &&
            !MT.TypeKeywords.contains(name) && !MT.isTyConName(name)
}

// ---------------------------------------------------------------------------
// Opening a type against the type-variable scope and the tycon scope stack
// ---------------------------------------------------------------------------
//
// A type annotation is well formed when every type identifier is bound by an
// enclosing pabs / forall, every type-constructor name is declared (by a
// module, a moduleof, or an open in scope), and no unification variable
// occurs. Opening resolves bare tycon names against the scope stack:
// a declared name stays bare (TyConName); a name selected from an opened
// module becomes a dependent type constructor (TyConSelect θ emod).

object Open {

    sealed trait Out
    case class Ok(t: MT) extends Out
    case class Err(msg: String) extends Out

    def open(t: MT, tyScope: Set[String], scopes: List[TyconScope]): Out =
        go(t, tyScope, scopes)

    private def go(t: MT, tyScope: Set[String], scopes: List[TyconScope]): Out = t match {
        case MTBase(_) => Ok(t)
        case MTVar(n) =>
            if (tyScope.contains(n)) Ok(t)
            else Err(s"the type identifier $n is not bound (pabs / forall) in this context")
        case MTUnif(n) =>
            Err(s"unification variables such as $n may not appear in a type annotation")
        case MTArrow(params, ret) =>
            // Parameter names are value names: they do not affect the type
            // scope. A parameter type may mention earlier parameter names
            // (inside dselects), which are value references, not types.
            go(ret, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(ret2) =>
                    params.foldLeft[Option[MTArrow]](Some(MTArrow(Nil, ret2))) {
                        (acc, param) => (acc, param) match {
                            case (Some(cur), (n, pt)) =>
                                go(pt, tyScope, scopes) match {
                                    case Ok(pt2) => Some(MTArrow(cur.params :+ (n -> pt2), cur.ret))
                                    case _ => None
                                }
                            case (None, _) => None
                        }
                    } match {
                        case Some(at) => Ok(at)
                        case None =>
                            Err(recordErr(params.map(_._2), tyScope, scopes, "arrow parameter type"))
                    }
            }
        case MTRecord(fields) =>
            fields.foldLeft[Option[List[(String, MT)]]](Some(Nil)) {
                (acc, f) => (acc, f) match {
                    case (Some(cur), (n, ft)) =>
                        go(ft, tyScope, scopes) match {
                            case Ok(ft2) => Some(cur :+ (n, ft2))
                            case Err(_) => None
                        }
                    case (None, _) => None
                }
            } match {
                case Some(fs) => Ok(MTRecord(fs))
                case None => Err(recordErr(fields.map(_._2), tyScope, scopes, "record field type"))
            }
        case MTOneof(tags) =>
            tags.foldLeft[Option[List[(String, MT)]]](Some(Nil)) {
                (acc, f) => (acc, f) match {
                    case (Some(cur), (n, tt)) =>
                        go(tt, tyScope, scopes) match {
                            case Ok(tt2) => Some(cur :+ (n, tt2))
                            case Err(_) => None
                        }
                    case (None, _) => None
                }
            } match {
                case Some(ts) => Ok(MTOneof(ts))
                case None => Err(recordErr(tags.map(_._2), tyScope, scopes, "oneof payload type"))
            }
        case MTProd(comps) =>
            all(comps, tyScope, scopes) match {
                case Some(cs) => Ok(MTProd(cs))
                case None => Err(prodErr(comps, tyScope, scopes))
            }
        case MTSeq(elem) => go(elem, tyScope, scopes) match {
            case Ok(e2) => Ok(MTSeq(e2))
            case Err(m) => Err(m)
        }
        case MTCell(elem) => go(elem, tyScope, scopes) match {
            case Ok(e2) => Ok(MTCell(e2))
            case Err(m) => Err(m)
        }
        case MTForall(vars, body) =>
            go(body, tyScope ++ vars.toSet, scopes) match {
                case Ok(b2) => Ok(MTForall(vars, b2))
                case Err(m) => Err(m)
            }
        case MTModuleof(ats, vals) =>
            // The AT names are binding occurrences for the value-component
            // types (the dummies bind nothing); they shadow outer scopes.
            val innerScopes = scopes :+ ScopeDeclare(ats.map(_._1).toSet)
            vals.foldLeft[Option[List[(String, MT)]]](Some(Nil)) {
                (acc, f) => (acc, f) match {
                    case (Some(cur), (n, vt)) =>
                        go(vt, tyScope, innerScopes) match {
                            case Ok(vt2) => Some(cur :+ (n, vt2))
                            case Err(_) => None
                        }
                    case (None, _) => None
                }
            } match {
                case Some(vs) => Ok(MTModuleof(ats, vs))
                case None =>
                    Err(recordErr(vals.map(_._2), tyScope, innerScopes, "moduleof value type"))
            }
        case MTyConApp(tc, args) =>
            val rc: Option[TyCon] = tc match {
                case TyConName(name) => resolveTycon(name, scopes)
                case TyConSelect(name, emod) => Some(TyConSelect(name, emod))
            }
            rc match {
                case None =>
                    // Only a bare TyConName can fail to resolve.
                    tc match {
                        case TyConName(name) =>
                            Err(s"the type constructor $name is not declared in this context")
                        case _ => Err("internal error: unresolvable type constructor")
                    }
                case Some(t2) => all(args, tyScope, scopes) match {
                    case Some(as) => Ok(MTyConApp(t2, as))
                    case None =>
                        Err(recordErr(args, tyScope, scopes, "type-constructor argument"))
                }
            }
    }

    // Resolve a bare tycon name against the scope stack (innermost wins).
    private def resolveTycon(name: String, scopes: List[TyconScope]): Option[TyCon] =
        scopes.reverse.find {
            case ScopeDeclare(ns) => ns.contains(name)
            case ScopeOpen(ns, _) => ns.contains(name)
        } match {
            case Some(ScopeOpen(_, emod)) => Some(TyConSelect(name, emod))
            case Some(ScopeDeclare(_)) => Some(TyConName(name))
            case None => None
        }

    // A first error message from a list of component types.
    private def recordErr(ts: List[MT], tyScope: Set[String], scopes: List[TyconScope],
                          what: String): String =
        ts.map(go(_, tyScope, scopes)).collectFirst { case Err(m) => m }
            .getOrElse(what + " is malformed")

    private def prodErr(ts: List[MT], tyScope: Set[String], scopes: List[TyconScope]): String =
        ts.map(go(_, tyScope, scopes)).collectFirst { case Err(m) => m }
            .getOrElse("malformed prodof type")

    private def goRet(t: MT, tyScope: Set[String], scopes: List[TyconScope]): Out =
        go(t, tyScope, scopes)

    private def all(ts: List[MT], tyScope: Set[String], scopes: List[TyconScope]): Option[List[MT]] =
        ts.foldLeft[Option[List[MT]]](Some(Nil)) { (acc, t) =>
            (acc, go(t, tyScope, scopes)) match {
                case (Some(cur), Ok(t2)) => Some(cur :+ t2)
                case _ => None
            }
        }
}

// ---------------------------------------------------------------------------
// Free identifiers of (and inside) types
// ---------------------------------------------------------------------------

object Fr {

    // Free type-constructor names of a type (the FrTyconIds of the book):
    // bare tycon names, excluding those bound by an enclosing moduleof's
    // AT list. A dependent type constructor (dselect θ Emod) contributes no
    // free tycon names.
    def tyconIds(t: MT): Set[String] = t match {
        case MTBase(_) | MTVar(_) | MTUnif(_) => Set.empty
        case MTArrow(params, ret) =>
            val paramFr = params.map(_._2).map(tyconIds).reduceOption(_ ++ _).getOrElse(Set.empty)
            tyconIds(ret) ++ paramFr
        case MTRecord(fields) => fields.map(_._2).map(tyconIds).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTOneof(tags) => tags.map(_._2).map(tyconIds).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTProd(comps) => comps.map(tyconIds).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTSeq(e) => tyconIds(e)
        case MTCell(e) => tyconIds(e)
        case MTForall(_, body) => tyconIds(body)
        case MTModuleof(ats, vals) =>
            vals.map(_._2).map(tyconIds).reduceOption(_ ++ _).getOrElse(Set.empty) --
                ats.map(_._1).toSet
        case MTyConApp(tc, args) =>
            (tc match {
                case TyConName(n) => Set(n)
                case TyConSelect(_, _) => Set.empty
            }) ++ args.map(tyconIds).reduceOption(_ ++ _).getOrElse(Set.empty)
    }

    // Free type identifiers of a type (FrTyIds): the MTVar names not bound
    // by an enclosing forall in the type. Used by the pabs import
    // restriction (the polytest of book p.732, generalized to FLEX/M).
    def tyIds(t: MT): Set[String] = goTyIds(t, Set.empty)

    private def goTyIds(t: MT, bound: Set[String]): Set[String] = t match {
        case MTBase(_) | MTUnif(_) => Set.empty
        case MTVar(n) => if (bound.contains(n)) Set.empty else Set(n)
        case MTArrow(params, ret) =>
            params.map(_._2).map(p => goTyIds(p, bound)).reduceOption(_ ++ _).getOrElse(Set.empty) ++
                goTyIds(ret, bound)
        case MTRecord(fields) => fields.map(_._2).map(p => goTyIds(p, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTOneof(tags) => tags.map(_._2).map(p => goTyIds(p, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTProd(comps) => comps.map(p => goTyIds(p, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTSeq(e) => goTyIds(e, bound)
        case MTCell(e) => goTyIds(e, bound)
        case MTForall(vars, body) => goTyIds(body, bound ++ vars.toSet)
        case MTModuleof(ats, vals) =>
            vals.map(_._2).map(p => goTyIds(p, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTyConApp(_, args) => args.map(p => goTyIds(p, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
    }

    // Free unification variables of a type (FrUniVars, book p.920). Forall
    // binders are type identifiers and cannot shadow unification variables.
    def uniVars(t: MT): Set[String] = t match {
        case MTBase(_) | MTVar(_) => Set.empty
        case MTUnif(n) => Set(n)
        case MTArrow(params, ret) =>
            params.map(_._2).map(uniVars).reduceOption(_ ++ _).getOrElse(Set.empty) ++ uniVars(ret)
        case MTRecord(fields) => fields.map(_._2).map(uniVars).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTOneof(tags) => tags.map(_._2).map(uniVars).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTProd(comps) => comps.map(uniVars).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTSeq(e) => uniVars(e)
        case MTCell(e) => uniVars(e)
        case MTForall(_, body) => uniVars(body)
        case MTModuleof(_, vals) => vals.map(_._2).map(uniVars).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTyConApp(_, args) => args.map(uniVars).reduceOption(_ ++ _).getOrElse(Set.empty)
    }

    // Free value identifiers of a type (FrIds Ty): value names may occur in
    // a type only inside dselect module expressions. Arrow parameter names
    // shadow in the later parameter types and the result.
    def valueIds(t: MT): Set[String] =
        go(t, Set.empty)

    private def go(t: MT, bound: Set[String]): Set[String] = t match {
        case MTBase(_) | MTVar(_) | MTUnif(_) => Set.empty
        case MTArrow(params, ret) =>
            // The outer bound and the earlier parameter names are bound in
            // the later parameter types and in the result.
            val paramFr = params.foldLeft((Set.empty[String], bound)) {
                case ((acc, boundCur), (n, pt)) => (acc ++ go(pt, boundCur), boundCur + n)
            }._1
            go(ret, bound ++ params.map(_._1).toSet) ++ paramFr
        case MTRecord(fields) => fields.map(_._2).flatMap(p => go(p, bound)).toSet
        case MTOneof(tags) => tags.map(_._2).flatMap(p => go(p, bound)).toSet
        case MTProd(comps) => comps.flatMap(p => go(p, bound)).toSet
        case MTSeq(e) => go(e, bound)
        case MTCell(e) => go(e, bound)
        case MTForall(_, body) => go(body, bound)
        case MTModuleof(ats, vals) => vals.map(_._2).flatMap(p => go(p, bound)).toSet
        case MTyConApp(tc, args) =>
            (tc match {
                case TyConSelect(_, emod) => valueIdsExp(emod, bound)
                case TyConName(_) => Set.empty
            }) ++ args.flatMap(p => go(p, bound)).toSet
    }

    // Free value identifiers of an expression (FrIds Exp). The binders:
    // abs / let / letrec / module-definitions / open / pattern variables.
    def valueIdsExp(e: Exp, bound: Set[String] = Set.empty): Set[String] =
        go(e, bound)

    // Every value identifier referenced by a dselect module expression
    // anywhere in the type, with no bound tracking. Used for the
    // sugar / parameterized display decision of arrow types (where the
    // arrow's own parameter names must count as occurrences, not as
    // outer bindings).
    def valueRefs(t: MT): Set[String] = t match {
        case MTBase(_) | MTVar(_) | MTUnif(_) => Set.empty
        case MTArrow(params, ret) =>
            params.map(_._2).flatMap(valueRefs).toSet ++ valueRefs(ret)
        case MTRecord(fields) => fields.map(_._2).flatMap(valueRefs).toSet
        case MTOneof(tags) => tags.map(_._2).flatMap(valueRefs).toSet
        case MTProd(comps) => comps.flatMap(valueRefs).toSet
        case MTSeq(e) => valueRefs(e)
        case MTCell(e) => valueRefs(e)
        case MTForall(_, body) => valueRefs(body)
        case MTModuleof(ats, vals) => vals.map(_._2).flatMap(valueRefs).toSet
        case MTyConApp(tc, args) =>
            (tc match {
                case TyConSelect(_, emod) => valueIdsExp(emod)
                case TyConName(_) => Set.empty
            }) ++ args.flatMap(valueRefs).toSet
    }

    private def go(e: Exp, bound: Set[String]): Set[String] = e match {
        case _: UnitLit | _: BoolLit | _: IntLit => Set.empty
        case Sym(_) => Set.empty
        case Var(n) => if (bound.contains(n)) Set.empty else Set(n)
        case MError(_, t) => Fr.valueIds(t)
        case If(t1, t2, t3) => go(t1, bound) ++ go(t2, bound) ++ go(t3, bound)
        case PrimOp(_, args) => args.flatMap(a => go(a, bound)).toSet
        case MAbs(params, body) =>
            go(body, bound ++ params.map(_._1).toSet)
        case MApp(r, args) => go(r, bound) ++ args.flatMap(a => go(a, bound)).toSet
        case Let(binds, body) =>
            go(body, bound ++ binds.map(_._1).toSet) ++
                binds.map(_._2).flatMap(a => go(a, bound)).toSet
        case MThe(t, e2) => Fr.valueIds(t) ++ go(e2, bound)
        case ProdExp(cs) => cs.flatMap(c => go(c, bound)).toSet
        case GetExp(_, e2) => go(e2, bound)
        case SeqExp(cs) => cs.flatMap(c => go(c, bound)).toSet
        case SeqGetExp(i, s) => go(i, bound) ++ go(s, bound)
        case SeqSizeExp(e2) => go(e2, bound)
        case RecordExp(fs) => fs.map(_._2).flatMap(a => go(a, bound)).toSet
        case SelectExp(_, e2) => go(e2, bound)
        case WithExp(r, b) => go(r, bound) ++ go(b, bound)
        case MOne(t, _, p) => Fr.valueIds(t) ++ go(p, bound)
        case TagCaseExp(d, _, cs, el) =>
            go(d, bound) ++ cs.map(_._2).flatMap(a => go(a, bound)).toSet ++
                el.map(a => go(a, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
        case SetExp(_, e2) => go(e2, bound)
        case CellExp(e2) => go(e2, bound)
        case DerefExp(e2) => go(e2, bound)
        case CellSetExp(c, e2) => go(c, bound) ++ go(e2, bound)
        case CellEqExp(e1, e2) => go(e1, bound) ++ go(e2, bound)
        case MPabs(_, body) => go(body, bound)
        case MPcall(e2, ts) => go(e2, bound) ++ ts.map(Fr.valueIds).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MModule(dts, vds) =>
            vds.map { vd =>
                Fr.valueIds(vd.t) ++ go(vd.e, bound ++ vds.map(_._1).toSet)
            }.reduceOption(_ ++ _).getOrElse(Set.empty)
        case MOpen(emod, body) =>
            // The opened value names are bound in the body (they may occur
            // in dselects of the body types).
            go(body, bound ++ Set.empty) ++ go(emod, bound)
        case MLoad(_, t) => Fr.valueIds(t)
        case MMatch(disc, clauses) =>
            go(disc, bound) ++ clauses.flatMap { case (p, b) =>
                go(b, bound) ++ patFree(p, bound)
            }.toSet
        case MLetRec(bs, body) =>
            go(body, bound ++ bs.map(_._1).toSet) ++
                bs.flatMap(b => Fr.valueIds(b._2) ++ go(b._3, bound ++ bs.map(_._1).toSet)).toSet
        case MMselect(n, emod) => go(emod, bound)
        case MLetType(bs, body) => bs.map(_._2).map(Fr.valueIds).reduceOption(_ ++ _).getOrElse(Set.empty) ++ go(body, bound)
        case MLetTypeStar(bs, body) => bs.map(_._2).map(Fr.valueIds).reduceOption(_ ++ _).getOrElse(Set.empty) ++ go(body, bound)
        case SugaredPrimOp(_, args) => args.flatMap(a => go(a, bound)).toSet
        case Cond(branches, d) =>
            branches.flatMap { case (t1, t2) => go(t1, bound) ++ go(t2, bound) }.toSet ++
                d.map(a => go(a, bound)).reduceOption(_ ++ _).getOrElse(Set.empty)
        case Scand(es) => es.flatMap(a => go(a, bound)).toSet
        case Scor(es) => es.flatMap(a => go(a, bound)).toSet
        case BeginExp(e1, e2) => go(e1, bound) ++ go(e2, bound)
        case _ => Set.empty
    }

    private def patFree(p: Mpat, bound: Set[String]): Set[String] = p match {
        case MpatWild() => Set.empty
        case MpatVar(n) => Set.empty
        case MpatLit(e) => go(e, bound)
        case MpatCons(_, subs) => subs.flatMap(s => patFree(s, bound)).toSet
    }
}

// ---------------------------------------------------------------------------
// Substitutions
// ---------------------------------------------------------------------------
//
// Type identifiers (τ) and value identifiers (I) are in separate
// namespaces, so type substitution never interacts with value binders
// except through the type binders (forall) inside types; value-name
// substitution acts only on dselect module expressions and must respect
// the arrow parameter names (value binders) inside types.

object Subst {

    // [T/τ]MT (Figure 11.5, the FLEX/M version): forall binders shadow.
    // The replacement is alpha-renamed up front (against the target's
    // *bound* type-identifier names, which are the only ones that could
    // capture a free identifier of the replacement) so that no capture can
    // occur. Free identifiers of the target are shared and must not be
    // renamed.
    def substType(repl: MT, tau: String, target: MT): MT = {
        // The substitution variable tau is never a bound name of the
        // target (a free occurrence of tau is not under a binder for
        // tau), so it is not in the avoid set: [T/tau]tau = T, and a
        // replacement that mentions tau free must survive unchanged.
        val renamed = alphaRenameTyVars(repl, allTyVarNames(target))
        goType(renamed, tau, target, Set.empty)
    }

    private def goType(repl: MT, tau: String, target: MT, shadowed: Set[String]): MT =
        target match {
            case MTVar(n) => if (!shadowed.contains(n) && n == tau) repl else target
            case MTForall(vars, body) =>
                MTForall(vars, goType(repl, tau, body, shadowed ++ vars.toSet))
            case MTArrow(params, ret) =>
                MTArrow(params.map { case (n, pt) => n -> goType(repl, tau, pt, shadowed) },
                        goType(repl, tau, ret, shadowed))
            case MTRecord(fields) =>
                MTRecord(fields.map { case (n, ft) => n -> goType(repl, tau, ft, shadowed) })
            case MTOneof(tags) =>
                MTOneof(tags.map { case (n, tt) => n -> goType(repl, tau, tt, shadowed) })
            case MTProd(comps) => MTProd(comps.map(c => goType(repl, tau, c, shadowed)))
            case MTSeq(e) => MTSeq(goType(repl, tau, e, shadowed))
            case MTCell(e) => MTCell(goType(repl, tau, e, shadowed))
            case MTModuleof(ats, vals) =>
                MTModuleof(ats, vals.map { case (n, vt) => n -> goType(repl, tau, vt, shadowed) })
            case MTyConApp(tc, args) => MTyConApp(tc, args.map(a => goType(repl, tau, a, shadowed)))
            case _ => target
        }

    // [T1/τ1, ..., Tn/τn]MT, applied simultaneously (let-type).
    def substSim(binds: List[(String, MT)], target: MT): MT =
        binds.foldRight(target) { (b, acc) =>
            (b, acc) match { case ((tau, t), a) => substType(t, tau, a) }
        }

    // Substitute type-constructor names: bare TyConName(θ) -> m(θ);
    // dependent tycons are explicit and are left alone. A moduleof's AT
    // list shadows the substitution in its value types.
    def substTycon(m: Map[String, TyCon], target: MT): MT =
        goTycon(m, target)

    private def goTycon(m: Map[String, TyCon], t: MT): MT = t match {
        case MTArrow(params, ret) =>
            MTArrow(params.map { case (n, pt) => n -> goTycon(m, pt) }, goTycon(m, ret))
        case MTRecord(fields) =>
            MTRecord(fields.map { case (n, ft) => n -> goTycon(m, ft) })
        case MTOneof(tags) => MTOneof(tags.map { case (n, tt) => n -> goTycon(m, tt) })
        case MTProd(comps) => MTProd(comps.map(goTycon(m, _)))
        case MTSeq(e) => MTSeq(goTycon(m, e))
        case MTCell(e) => MTCell(goTycon(m, e))
        case MTForall(vars, body) => MTForall(vars, goTycon(m, body))
        case MTModuleof(ats, vals) =>
            // The AT names are binding occurrences: they shadow in the
            // value-component types.
            val shadowed = ats.map(_._1).toSet
            MTModuleof(ats, vals.map { case (n, vt) =>
                n -> goTyconShadowed(m, shadowed, vt)
            })
        case MTyConApp(tc, args) =>
            tc match {
                case TyConName(name) =>
                    MTyConApp(m.getOrElse(name, tc), args.map(goTycon(m, _)))
                case TyConSelect(_, _) =>
                    MTyConApp(tc, args.map(goTycon(m, _)))
            }
        case _ => t
    }

    private def goTyconShadowed(m: Map[String, TyCon], shadowed: Set[String], t: MT): MT = t match {
        case MTyConApp(TyConName(name), args) if !shadowed.contains(name) =>
            MTyConApp(m.getOrElse(name, TyConName(name)), args.map(a => goTyconShadowed(m, shadowed, a)))
        case MTModuleof(ats, vals) =>
            MTModuleof(ats, vals.map { case (n, vt) =>
                n -> goTyconShadowed(m, shadowed ++ ats.map(_._1).toSet, vt)
            })
        case _ => goTycon(m, t)
    }

    // Substitute value names inside a type: the names occur only in dselect
    // module expressions. Arrow parameter names shadow (in the later
    // parameter types and the result).
    def substValNames(m: Map[String, Exp], target: MT): MT =
        goVal(m, target, Set.empty)

    // As substValNames, but with an externally accumulated set of bound
    // value names (used when substituting inside a type position of an
    // expression, where earlier arrow-parameter names of the enclosing
    // abstraction may already be bound).
    def substValNamesBound(m: Map[String, Exp], target: MT, bound: Set[String]): MT =
        goVal(m, target, bound)

    private def goVal(m: Map[String, Exp], t: MT, bound: Set[String]): MT = t match {
        case MTArrow(params, ret) =>
            // The outer bound and the earlier parameter names are bound in
            // the later parameter types and in the result.
            val ps = params.foldLeft((List.empty[(String, MT)], bound)) {
                case ((accPs, boundCur), (n, pt)) =>
                    (accPs :+ (n, goVal(m, pt, boundCur)), boundCur + n)
            }
            MTArrow(ps._1, goVal(m, ret, bound ++ ps._2))
        case MTyConApp(TyConSelect(name, emod), args) =>
            MTyConApp(TyConSelect(name, substValExp(m, emod, bound)),
                      args.map(a => goVal(m, a, bound)))
        case MTyConApp(tc, args) => MTyConApp(tc, args.map(a => goVal(m, a, bound)))
        case MTRecord(fields) => MTRecord(fields.map { case (n, ft) => n -> goVal(m, ft, bound) })
        case MTOneof(tags) => MTOneof(tags.map { case (n, tt) => n -> goVal(m, tt, bound) })
        case MTProd(comps) => MTProd(comps.map(c => goVal(m, c, bound)))
        case MTSeq(e) => MTSeq(goVal(m, e, bound))
        case MTCell(e) => MTCell(goVal(m, e, bound))
        case MTForall(vars, body) => MTForall(vars, goVal(m, body, bound))
        case MTModuleof(ats, vals) => MTModuleof(ats, vals.map { case (n, vt) => n -> goVal(m, vt, bound) })
        case _ => t
    }

    // Substitute value names in a (dselect) module expression. The module
    // expression is a full FLEX/M expression (a module may be a value
    // produced by any pure expression), so the walk descends through all
    // expression forms, respecting their value binders. Note: the value
    // names opened by an open are not known from the expression alone
    // (they come from the opened module's type), so an open's body is
    // treated as binding nothing — a conservative approximation (the book
    // itself notes in Exercise 15.3a that free-identifier computation in
    // FLEX/M is not straightforward).
    def substValExp(m: Map[String, Exp], e: Exp, bound: Set[String] = Set.empty): Exp =
        e match {
            case Var(n) if !bound.contains(n) => m.getOrElse(n, e)
            case Var(_) => e
            case MAbs(params, body) =>
                // Earlier parameter names are bound in the later parameter
                // types (inside dselects) and in the body.
                val (ps, boundBody) = params.foldLeft((List.empty[(String, MT)], bound)) {
                    case ((acc, b), (n, pt)) =>
                        (acc :+ (n, substValNamesBound(m, pt, b)), b + n)
                }
                MAbs(ps, substValExp(m, body, boundBody))
            case MApp(r, args) =>
                MApp(substValExp(m, r, bound), args.map(a => substValExp(m, a, bound)))
            case Let(bs, body) =>
                // Each binding expression sees the plain environment (the
                // [let] rule), so no let names are bound in the binding
                // expressions; the body sees all of them.
                Let(bs.map { case (n, ex) => n -> substValExp(m, ex, bound) },
                    substValExp(m, body, bound ++ bs.map(_._1).toSet))
            case MLetRec(bs, body) =>
                // Letrec / module definitions are mutually recursive: every
                // defined name is bound in every definition expression.
                val boundAll = bound ++ bs.map(_._1).toSet
                MLetRec(bs.map { case (n, t, ex) =>
                    (n, substValNamesBound(m, t, boundAll), substValExp(m, ex, boundAll)) },
                        substValExp(m, body, boundAll))
            case MModule(dts, vds) =>
                val boundAll = bound ++ vds.map(_._1).toSet
                MModule(dts, vds.map { vd =>
                    MValDef(vd.name, substValNamesBound(m, vd.t, boundAll), substValExp(m, vd.e, boundAll)) })
            case MOpen(emod, body) =>
                MOpen(substValExp(m, emod, bound), substValExp(m, body, bound))
            case MLoad(file, t) => MLoad(file, substValNamesBound(m, t, bound))
            case MError(msg, t) => MError(msg, substValNamesBound(m, t, bound))
            case MMatch(disc, clauses) =>
                MMatch(substValExp(m, disc, bound),
                       clauses.map { case (p, b) =>
                           (p, substValExp(m, b, bound ++ patNames(p))) })
            case MPcall(ex, ts) =>
                MPcall(substValExp(m, ex, bound), ts.map(t => substValNamesBound(m, t, bound)))
            case MPabs(vars, body) => MPabs(vars, substValExp(m, body, bound))
            case MThe(t, ex) => MThe(substValNamesBound(m, t, bound), substValExp(m, ex, bound))
            case MOne(t, tag, payload) =>
                MOne(substValNamesBound(m, t, bound), tag, substValExp(m, payload, bound))
            case MLetType(bs, body) =>
                MLetType(bs.map { case (n, t) => (n, substValNamesBound(m, t, bound)) },
                         substValExp(m, body, bound))
            case MLetTypeStar(bs, body) =>
                MLetTypeStar(bs.map { case (n, t) => (n, substValNamesBound(m, t, bound)) },
                             substValExp(m, body, bound))
            case BeginExp(e1, e2) =>
                BeginExp(substValExp(m, e1, bound), substValExp(m, e2, bound))
            case _ => e // leaves and forms with only type-free sub-expressions
        }

    // The names bound by a pattern (pattern variables).
    private def patNames(p: Mpat): Set[String] = p match {
        case MpatVar(n) => Set(n)
        case MpatCons(_, subs) => subs.flatMap(patNames).toSet
        case _ => Set.empty
    }

    // ------------------------------------------------------------------
    // Alpha-renaming helpers
    // ------------------------------------------------------------------

    // All type-identifier names bound by a forall inside a type. Free
    // names do not count: only binders can capture a replacement, and
    // the substitution variable itself is never bound by the target.
    def allTyVarNames(t: MT): Set[String] = t match {
        case MTVar(_) => Set.empty
        case MTForall(vars, body) => vars.toSet ++ allTyVarNames(body)
        case MTArrow(params, ret) =>
            params.map(_._2).map(allTyVarNames).reduceOption(_ ++ _).getOrElse(Set.empty) ++ allTyVarNames(ret)
        case MTRecord(fields) => fields.map(_._2).map(allTyVarNames).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTOneof(tags) => tags.map(_._2).map(allTyVarNames).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTProd(comps) => comps.map(allTyVarNames).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTSeq(e) => allTyVarNames(e)
        case MTCell(e) => allTyVarNames(e)
        case MTModuleof(ats, vals) => vals.map(_._2).map(allTyVarNames).reduceOption(_ ++ _).getOrElse(Set.empty)
        case MTyConApp(_, args) => args.map(allTyVarNames).reduceOption(_ ++ _).getOrElse(Set.empty)
        case _ => Set.empty
    }

    // All value names occurring in a type (free or bound by arrow
    // parameter names inside the type).
    def allValueNames(t: MT): Set[String] = {
        def go(t: MT, bound: Set[String]): Set[String] = t match {
            case MTArrow(params, ret) =>
                val ps = params.foldLeft((Set.empty[String], Set.empty[String])) {
                    case ((acc, b), (n, pt)) => (acc ++ go(pt, b), b + n)
                }
                ps._1 ++ (go(ret, bound ++ params.map(_._1).toSet))
            case MTyConApp(TyConSelect(_, emod), args) =>
                Fr.valueIdsExp(emod) ++ args.flatMap(a => go(a, bound)).toSet
            case MTRecord(fields) => fields.map(_._2).flatMap(a => go(a, bound)).toSet
            case MTOneof(tags) => tags.map(_._2).flatMap(a => go(a, bound)).toSet
            case MTProd(comps) => comps.flatMap(a => go(a, bound)).toSet
            case MTSeq(e) => go(e, bound)
            case MTCell(e) => go(e, bound)
            case MTForall(_, body) => go(body, bound)
            case MTModuleof(_, vals) => vals.map(_._2).flatMap(a => go(a, bound)).toSet
            case MTyConApp(_, args) => args.flatMap(a => go(a, bound)).toSet
            case _ => Set.empty
        }
        go(t, Set.empty)
    }

    private def emodNames(e: Exp): Set[String] = Fr.valueIdsExp(e)

    // Rename all free type variables of repl to fresh names (avoiding
    // avoid), returning the renamed type. Used before substitutions to
    // rule out capture.
    def alphaRenameTyVars(t: MT, avoid: Set[String]): MT = {
        // Only free names that would be captured (i.e. that occur in
        // avoid) are renamed; all other free names survive unchanged.
        // Only genuine type identifiers are renamed: fresh internal
        // names (starting with @, such as the @@flexm_avN assigned
        // here) are not type identifiers, and renaming them would
        // recurse without bound (each renamed name would itself be
        // renamed again).
        val free = Fr.tyIds(t).filter(MT.isTypeIdent).filter(avoid.contains).toList
        // Assign a distinct fresh name to each free identifier, avoiding
        // both the given names and the names already assigned here.
        val (m, _) = free.foldLeft((Map.empty[String, String], avoid)) {
            case ((mm, avoidCur), old) =>
                var i = 1
                while (avoidCur.contains("@@flexm_av" + i)) i += 1
                val newn = "@@flexm_av" + i
                (mm + (old -> newn), avoidCur + newn)
        }
        m.foldLeft(t) { (acc, pair) =>
            (acc, pair) match { case (a, (old, newn)) => substType(MTVar(newn), old, a) }
        }
    }
}

// Apply a unification substitution (unification variable -> type) to a type.
def applyUnifySubst(sigma: Map[String, MT], t: MT): MT =
    t match {
        case MTUnif(n) => sigma.get(n) match {
            case Some(r) => applyUnifySubst(sigma, r)
            case None => MTUnif(n)
        }
        case MTArrow(params, ret) =>
            MTArrow(params.map { case (n, pt) => n -> applyUnifySubst(sigma, pt) },
                    applyUnifySubst(sigma, ret))
        case MTRecord(fields) => MTRecord(fields.map { case (n, ft) => n -> applyUnifySubst(sigma, ft) })
        case MTOneof(tags) => MTOneof(tags.map { case (n, tt) => n -> applyUnifySubst(sigma, tt) })
        case MTProd(comps) => MTProd(comps.map(applyUnifySubst(sigma, _)))
        case MTSeq(e) => MTSeq(applyUnifySubst(sigma, e))
        case MTCell(e) => MTCell(applyUnifySubst(sigma, e))
        case MTForall(vars, body) => MTForall(vars, applyUnifySubst(sigma, body))
        case MTModuleof(ats, vals) =>
            MTModuleof(ats, vals.map { case (n, vt) => n -> applyUnifySubst(sigma, vt) })
        case MTyConApp(tc, args) => MTyConApp(tc, args.map(applyUnifySubst(sigma, _)))
        case _ => t
}
