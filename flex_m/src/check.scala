package DSL.flex_m

import DSL.fl._
import DSL.flex._
// The explicit imports beat the wildcard import above: DSL.flex also has
// Subst / Desugar objects (for the non-dependent FLEX types).
import DSL.flex_m.Subst
import DSL.flex_m.Desugar

// The reference static semantics of FLEX/M (Chapter 15 of the book): the
// type checker of Figure 15.17 (moduleof-intro / moduleof-elim /
// the-inclusion), the dependent-package type rules of Figure 14.13
// ([->-intro] / [->-elim] / [let] / [with], inherited by FLEX/M), the
// universal-polymorphism rules of Figure 12.9 (pabs / pcall), implicit
// projection (Section 15.4.5, Figure 15.18), and typed pattern matching
// (Section 15.4.6).
//
// Differences from FLEX/SP:
//
//   * There is no [inclusion] rule: every FLEX/M expression has a unique
//     type (up to alpha-renaming of arrow parameter names and
//     forall-bound type identifiers), and all subtyping is explicit via
//     (the T E) ([the-inclusion], p.917).
//   * Dependent types: value identifiers may occur in types, only inside
//     the module expressions of dependent type constructors (dselect
//     theta Emod). Whenever a value escapes the scope of a value
//     identifier, the identifier must be replaced with the corresponding
//     expression in the value's type (p.876) — the on-the-way-out
//     substitution of [->-elim], [let], [with], [implicit-projection],
//     and [moduleof-elim].
//   * First-class modules: [moduleof-intro] / [moduleof-elim] have a
//     purity restriction (the module expression must be pure) and an
//     import restriction (a local type-constructor binding must not
//     capture a reference to a type constructor of the same name in the
//     outer environment).
//   * No rebinding: a type-environment extension never rebinds an
//     identifier (Figure 15.16).
//
// The checker's state is (TE, tyScope, scopes): TE maps value
// identifiers to opened types (type constructors resolved); tyScope is
// the set of type identifiers bound by enclosing pabs / forall; scopes
// is the stack of type-constructor scopes (a module's DDs push
// ScopeDeclare; an open pushes ScopeOpen).

object FlexMChecker {

    // ------------------------------------------------------------------
    // Results
    // ------------------------------------------------------------------

    sealed trait Result[+A]
    final case class Ok[A](value: A) extends Result[A]
    final case class Err(msg: String) extends Result[Nothing]

    private implicit class ResultOps[A](private val r: Result[A]) {
        def flatMap[B](f: A => Result[B]): Result[B] = r match {
            case Ok(a) => f(a)
            case Err(m) => Err(m)
        }
        def map[B](f: A => B): Result[B] = r match {
            case Ok(a) => Ok(f(a))
            case Err(m) => Err(m)
        }
    }

    // ------------------------------------------------------------------
    // Base types and primitive signatures
    // ------------------------------------------------------------------

    private val unit = MTBase("unit"); private val bool = MTBase("bool")
    private val int = MTBase("int");  private val symb = MTBase("symb")

    // The 16 primitive operators of FLEX/M (Figure 15.1): the FL primops
    // except the type predicates and the pair operators (FLEX/M has no
    // pair kernel form).
    private val TEprim: Map[String, (List[MT], MT)] = Map(
        "not"    -> (List(bool), bool),
        "and"    -> (List(bool, bool), bool),
        "or"     -> (List(bool, bool), bool),
        "bool=?" -> (List(bool, bool), bool),
        "="      -> (List(int, int), bool),
        "!="     -> (List(int, int), bool),
        "<"      -> (List(int, int), bool),
        "<="     -> (List(int, int), bool),
        ">"      -> (List(int, int), bool),
        ">="     -> (List(int, int), bool),
        "+"      -> (List(int, int), int),
        "-"      -> (List(int, int), int),
        "*"      -> (List(int, int), int),
        "/"      -> (List(int, int), int),
        "%"      -> (List(int, int), int),
        "sym=?"  -> (List(symb, symb), bool))

    // ------------------------------------------------------------------
    // Well-formedness: opening a type against the type-variable scope
    // and the tycon scope stack
    // ------------------------------------------------------------------

    private def openType(t: MT, tyScope: Set[String], scopes: List[TyconScope]): Result[MT] =
        Open.open(t, tyScope, scopes) match {
            case Open.Ok(t2) => Ok(t2)
            case Open.Err(m) => Err(m)
        }

    private def openTypes(ts: List[MT], tyScope: Set[String], scopes: List[TyconScope]): Result[List[MT]] =
        ts.indices.foldLeft[Result[List[MT]]](Ok(Nil)) { (acc, i) =>
            acc flatMap { ts2 =>
                openType(ts(i), tyScope, scopes) match {
                    case Err(m) => Err(m)
                    case Ok(t2) => Ok(ts2 :+ t2)
                }
            }
        }

    // ------------------------------------------------------------------
    // The type-checking rules
    // ------------------------------------------------------------------

    def check(e: Exp, TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[MT] = e match {

        // ------------------------------------------------------------------
        // Literals and variables
        // ------------------------------------------------------------------

        case _: UnitLit => Ok(unit)
        case _: BoolLit => Ok(bool)
        case _: IntLit => Ok(int)
        case _: Sym => Ok(symb)

        case MError(_, t) => openType(t, tyScope, scopes)

        case Var(n) => TE.get(n) match {
            case Some(t) => Ok(t)
            case None => Err(s"unbound value identifier: $n")
        }

        // ------------------------------------------------------------------
        // Conditionals and primitives
        // ------------------------------------------------------------------

        case If(test, th, el) =>
            (check(test, TE, tyScope, scopes),
             check(th, TE, tyScope, scopes),
             check(el, TE, tyScope, scopes)) match {
                case (Ok(tt), Ok(t1), Ok(t2)) =>
                    if (equiv(tt, bool)) join(t1, t2)
                    else Err(s"the test of (if ...) must have type bool, but has type ${MT.show(tt)}")
                case (Err(m), _, _) => Err(m)
                case (_, Err(m), _) => Err(m)
                case (_, _, Err(m)) => Err(m)
            }

        case PrimOp(op, args) =>
            TEprim.get(op.toString) match {
                case None => Err(s"unknown primitive operator: ${op.toString}")
                case Some((paramTs, retT)) =>
                    if (args.size != paramTs.size)
                        Err(s"(${op.toString}) expects ${paramTs.size} argument(s), but got ${args.size}")
                    else
                        args.zip(paramTs).foldLeft[Result[Unit]](Ok(())) { (acc, pr) =>
                            (acc, pr) match {
                                case (Ok(()), (ae, pt)) =>
                                    check(ae, TE, tyScope, scopes) match {
                                        case Err(m) => Err(m)
                                        case Ok(at) =>
                                            subtype(at, pt) match {
                                                case None => Ok(())
                                                case Some(m) =>
                                                    Err(s"an argument of (${op.toString}): " + m)
                                            }
                                    }
                                case (Err(m), _) => Err(m)
                            }
                        } map (_ => retT)
            }

        // ------------------------------------------------------------------
        // Abstraction and application (Figure 14.13 / Figure 15.18)
        // ------------------------------------------------------------------

        case MAbs(params, body) =>
            // [->-intro] (Figure 14.13): the formal names must be fresh
            // (no rebinding, Figure 15.16), and a parameter type may
            // mention only earlier parameter names.
            val names = params.map(_._1)
            if (names.toSet.size != names.size)
                Err(s"duplicate formal parameter name in (abs ...): ${names.find(n => names.count(_ == n) > 1).get}")
            else if (names.exists(n => TE.contains(n)))
                Err(s"the formal parameter name ${names.find(n => TE.contains(n)).get} is already bound in this environment (FLEX/M does not permit rebinding)")
            else
                params.indices.foldLeft[Result[List[(String, MT)]]](Ok(Nil)) { (acc, i) =>
                    acc flatMap { ps =>
                        (params(i), names.drop(i + 1).toSet) match {
                            case ((n, pt), later) =>
                                val illegal = Fr.valueIds(pt).intersect(later)
                                if (illegal.nonEmpty)
                                    Err(s"the type of parameter $n mentions the not-yet-bound parameter name ${illegal.head}")
                                else
                                    openType(pt, tyScope, scopes) match {
                                        case Err(m) => Err(m)
                                        case Ok(pt2) => Ok(ps :+ (n -> pt2))
                                    }
                        }
                    }
                } flatMap { ps =>
                    check(body, TE ++ ps, tyScope, scopes) match {
                        case Err(m) => Err(m)
                        case Ok(tb) => Ok(MTArrow(ps, tb))
                    }
                }

        case MApp(rator, args) =>
            check(rator, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(tr) => tr match {
                    case MTArrow(params, ret) if params.size == args.size =>
                        elimArrow(params, ret, args, TE, tyScope, scopes)
                    case MTArrow(params, _) =>
                        Err(s"the procedure expects ${params.size} argument(s), but got ${args.size}")
                    case MTForall(vars, body) =>
                        implicitProjection(vars, body, args, TE, tyScope, scopes)
                    case _ =>
                        Err(s"the rator of an application has type ${MT.show(tr)}, which is not a procedure type")
                }
            }

        // ------------------------------------------------------------------
        // let (Figure 14.13)
        // ------------------------------------------------------------------

        case Let(binds, body) =>
            // [let]: each binding expression is checked in the plain
            // environment; the result type is [Ei/Ii]Tbody, with the
            // purity restriction.
            val names = binds.map(_._1)
            if (names.toSet.size != names.size)
                Err(s"duplicate binding name in (let ...): ${names.find(n => names.count(_ == n) > 1).get}")
            else if (names.exists(TE.contains))
                Err(s"the binding name ${names.find(n => TE.contains(n)).get} of (let ...) is already bound in this environment (FLEX/M does not permit rebinding)")
            else
                binds.indices.foldLeft[Result[List[(String, MT)]]](Ok(Nil)) { (acc, i) =>
                    acc flatMap { bs =>
                        check(binds(i)._2, TE, tyScope, scopes) match {
                            case Err(m) => Err(m)
                            case Ok(tb) => Ok(bs :+ (binds(i)._1 -> tb))
                        }
                    }
                } flatMap { bs =>
                    check(body, TE ++ bs.toMap, tyScope, scopes) match {
                        case Err(m) => Err(m)
                        case Ok(tbody) =>
                            val impure = bs.indices.filter(i =>
                                Fr.valueIds(tbody).contains(bs(i)._1) && !isPure(binds(i)._2))
                            if (impure.nonEmpty)
                                Err(s"(let ...): the binding expression for ${bs(impure.head)._1} is not pure, but the name occurs in the body type ${MT.show(tbody)}")
                            else
                                Ok(Subst.substValNamesBound(
                                    binds.toMap, tbody, Set.empty))
                    }
                }

        // ------------------------------------------------------------------
        // Explicit subtyping (the-inclusion, p.917)
        // ------------------------------------------------------------------

        case MThe(t, e) =>
            (openType(t, tyScope, scopes), check(e, TE, tyScope, scopes)) match {
                case (Ok(t2), Ok(te)) =>
                    subtype(te, t2) match {
                        case None => Ok(t2)
                        case Some(m) => Err(s"(the ...): " + m)
                    }
                case (Err(m), _) => Err(m)
                case (_, Err(m)) => Err(m)
            }

        // ------------------------------------------------------------------
        // Oneofs
        // ------------------------------------------------------------------

        case MOne(t, tag, payload) =>
            openType(t, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(to) => to match {
                    case MTOneof(tags) =>
                        tags.find(_._1 == tag) match {
                            case None => Err(s"(one ...): the tag $tag does not occur in the type ${MT.show(to)}")
                            case Some((_, tagT)) =>
                                check(payload, TE, tyScope, scopes) match {
                                    case Err(m) => Err(m)
                                    case Ok(tp) =>
                                        subtype(tp, tagT) match {
                                            case None => Ok(to)
                                            case Some(m) => Err(s"(one ...): the payload: " + m)
                                        }
                                }
                        }
                    case _ => Err(s"(one ...) requires a oneof type, but the type is ${MT.show(to)}")
                }
            }

        case TagCaseExp(disc, payloadName, clauses, elseExp) =>
            check(disc, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(td) => td match {
                    case MTOneof(tags) =>
                        if (TE.contains(payloadName))
                            Err(s"the payload name $payloadName of (tagcase ...) is already bound in this environment (FLEX/M does not permit rebinding)")
                        else if (clauses.map(_._1).distinct.size != clauses.size)
                            Err("a tagcase clause tag occurs more than once")
                        else {
                            val unknown = clauses.collect { case (t, _) if !tags.exists(_._1 == t) => t }
                            if (unknown.nonEmpty)
                                Err(s"the tagcase clause tag(s) " + unknown.mkString(", ") + s" are not in the oneof type ${MT.show(td)}")
                            else {
                                val coverOk = elseExp match {
                                    case Some(_) => true
                                    case None => clauses.size == tags.size
                                }
                                if (!coverOk)
                                    Err(s"tagcase: the clauses (without an else) must cover all ${tags.size} tag(s) of ${MT.show(td)}")
                                else
                                    clauses.indices.foldLeft[Result[List[MT]]](Ok(Nil)) { (acc, i) =>
                                        acc flatMap { ts =>
                                            clauses(i) match { case (tag, b) =>
                                                tags.find(_._1 == tag) match {
                                                    case Some((_, tagT)) =>
                                                        check(b, TE + (payloadName -> tagT), tyScope, scopes) match {
                                                            case Err(m) => Err(m)
                                                            case Ok(tb) => Ok(ts :+ tb)
                                                        }
                                                    case None => Err(s"tagcase: the tag $tag is not in ${MT.show(td)}")
                                                }
                                            }
                                        }
                                    } flatMap { ts =>
                                        elseExp match {
                                            case Some(el) =>
                                                check(el, TE, tyScope, scopes) match {
                                                    case Err(m) => Err(m)
                                                    case Ok(te) => joinList(ts :+ te)
                                                }
                                            case None => joinList(ts)
                                        }
                                    }
                            }
                        }
                    case _ => Err(s"(tagcase ...) requires a oneof type, but the discriminant has type ${MT.show(td)}")
                }
            }

        // ------------------------------------------------------------------
        // Universal polymorphism (Figure 12.9)
        // ------------------------------------------------------------------

        case MPabs(vars, body) =>
            // [forall-intro]: the body must be pure, and the import
            // restriction (p.732) forbids a pabs-bound type identifier
            // from occurring in the type of a free value of the body.
            if (!isPure(body))
                Err("a pabs body must be pure (it may not contain set! or :=)")
            else {
                val viol = vars.flatMap { tau =>
                    Fr.valueIdsExp(body).flatMap { n =>
                        TE.get(n).filter(t => Fr.tyIds(t).contains(tau)).map(_ => (n, tau))
                    }
                }
                if (viol.nonEmpty)
                    Err(s"import restriction (pabs): the type identifier ${viol.head._2} would capture the reference in the type of the value ${viol.head._1}")
                else
                    check(body, TE, tyScope ++ vars.toSet, scopes) match {
                        case Err(m) => Err(m)
                        case Ok(tb) => Ok(MTForall(vars, tb))
                    }
            }

        case MPcall(e, types) =>
            // [forall-elim]: project a forall onto its type arguments.
            check(e, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(te) => te match {
                    case MTForall(vars, body) =>
                        if (types.size != vars.size)
                            Err(s"pcall: the polymorphic value binds ${vars.size} type identifier(s), but ${types.size} type argument(s) were given")
                        else
                            types.indices.foldLeft[Result[List[MT]]](Ok(Nil)) { (acc, i) =>
                                acc flatMap { ts =>
                                    openType(types(i), tyScope, scopes) match {
                                        case Err(m) => Err(m)
                                        case Ok(t2) => Ok(ts :+ t2)
                                    }
                                }
                            } map { ots => Subst.substSim(vars.zip(ots), body) }
                    case _ => Err(s"pcall: the value has type ${MT.show(te)}, which is not a forall type")
                }
            }

        // ------------------------------------------------------------------
        // Products, sequences, records (inherited from FLEX)
        // ------------------------------------------------------------------

        case ProdExp(comps) =>
            checkAll(comps, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(ts) => Ok(MTProd(ts))
            }

        case GetExp(i, e2) =>
            check(e2, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(te) => te match {
                    case MTProd(comps) if i >= 1 && i <= comps.size => Ok(comps(i - 1))
                    case MTProd(comps) => Err(s"(get $i ...) is out of range for a product of ${comps.size} component(s)")
                    case _ => Err(s"(get ...) requires a prodof type, but the expression has type ${MT.show(te)}")
                }
            }

        case SeqExp(comps) =>
            if (comps.isEmpty) Err("an empty sequence (seq) has no element type")
            else
                checkAll(comps, TE, tyScope, scopes) flatMap { ts =>
                    ts.drop(1).foldLeft[Result[MT]](Ok(ts.head)) { (acc, u) =>
                        acc flatMap (x => join(x, u))
                    } map (elem => MTSeq(elem))
                }

        case SeqGetExp(i, s) =>
            (check(i, TE, tyScope, scopes), check(s, TE, tyScope, scopes)) match {
                case (Ok(it), Ok(st)) =>
                    if (equiv(it, int)) st match {
                        case MTSeq(elem) => Ok(elem)
                        case _ => Err(s"(seq-get ...) requires a seqof type, but the sequence has type ${MT.show(st)}")
                    }
                    else Err(s"the sequence index must have type int, but has type ${MT.show(it)}")
                case (Err(m), _) => Err(m)
                case (_, Err(m)) => Err(m)
            }

        case SeqSizeExp(e2) =>
            check(e2, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(te) => te match {
                    case MTSeq(_) => Ok(int)
                    case _ => Err(s"(seq-size ...) requires a seqof type, but the expression has type ${MT.show(te)}")
                }
            }

        case RecordExp(fields) =>
            fields.indices.foldLeft[Result[List[(String, MT)]]](Ok(Nil)) { (acc, i) =>
                acc flatMap { fs =>
                    (fields(i), fs.exists(_._1 == fields(i)._1)) match {
                        case ((n, e2), true) => Err(s"duplicate record field: $n")
                        case ((n, e2), false) =>
                            check(e2, TE, tyScope, scopes) match {
                                case Err(m) => Err(m)
                                case Ok(ft) => Ok(fs :+ (n -> ft))
                            }
                    }
                }
            } map (fs => MTRecord(fs))

        case SelectExp(name, e2) =>
            check(e2, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(te) => te match {
                    case MTRecord(fields) => fields.find(_._1 == name) match {
                        case Some((_, ft)) => Ok(ft)
                        case None =>
                            Err(s"the record has no field named $name (fields: ${fields.map(_._1).mkString(", ")})")
                    }
                    case _ => Err(s"(select ...) requires a recordof type, but the expression has type ${MT.show(te)}")
                }
            }

        case WithExp(rcd, body) =>
            // [with] (Figure 14.13): the body type gets the on-the-way-out
            // substitution [(select Ii Ercd)/Ii].
            check(rcd, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(tr) => tr match {
                    case MTRecord(fields) =>
                        val rebind = fields.map(_._1).find(TE.contains)
                        if (rebind.isDefined)
                            Err(s"(with ...) introduces the name ${rebind.get} that is already bound in this environment (FLEX/M does not permit rebinding)")
                        else
                            check(body, TE ++ fields.toMap, tyScope, scopes) match {
                                case Err(m) => Err(m)
                                case Ok(tbody) =>
                                    val used = Fr.valueIds(tbody).intersect(fields.map(_._1).toSet)
                                    if (used.nonEmpty && !isPure(rcd))
                                        Err(s"(with ...) requires a pure record expression, because the field name(s) ${used.mkString(", ")} occur in the body type ${MT.show(tbody)}")
                                    else
                                        Ok(Subst.substValNamesBound(
                                            fields.map { case (n, _) => n -> SelectExp(n, rcd) }.toMap,
                                            tbody, Set.empty))
                            }
                    case _ => Err(s"(with ...) requires a recordof type, but the record expression has type ${MT.show(tr)}")
                }
            }

        // ------------------------------------------------------------------
        // Mutation (inherited from FLEX)
        // ------------------------------------------------------------------

        case SetExp(name, e) =>
            TE.get(name) match {
                case None => Err(s"unbound value identifier: $name")
                case Some(te) => te match {
                    case MTCell(elem) =>
                        check(e, TE, tyScope, scopes) match {
                            case Err(m) => Err(m)
                            case Ok(tp) =>
                                subtype(tp, elem) match {
                                    case None => Ok(unit)
                                    case Some(m) => Err(s"(set! ...): " + m)
                                }
                        }
                    case _ => Err(s"(set! ...) requires the identifier to have a cellof type, but ${name} has type ${MT.show(te)}")
                }
            }

        case CellExp(e) =>
            check(e, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(te) => Ok(MTCell(te))
            }

        case DerefExp(e) =>
            check(e, TE, tyScope, scopes) match {
                case Err(m) => Err(m)
                case Ok(te) => te match {
                    case MTCell(elem) => Ok(elem)
                    case _ => Err(s"the dereference (^ ...) requires a cellof type, but the expression has type ${MT.show(te)}")
                }
            }

        case CellSetExp(c, e) =>
            (check(c, TE, tyScope, scopes), check(e, TE, tyScope, scopes)) match {
                case (Ok(ct), Ok(tp)) => ct match {
                    case MTCell(elem) =>
                        subtype(tp, elem) match {
                            case None => Ok(unit)
                            case Some(m) => Err(s"(:= ...) the value: " + m)
                        }
                    case _ => Err(s"(:= ...) requires a cellof type, but the cell has type ${MT.show(ct)}")
                }
                case (Err(m), _) => Err(m)
                case (_, Err(m)) => Err(m)
            }

        case CellEqExp(e1, e2) =>
            (check(e1, TE, tyScope, scopes), check(e2, TE, tyScope, scopes)) match {
                case (Ok(c1), Ok(c2)) => (c1, c2) match {
                    case (MTCell(el1), MTCell(el2)) =>
                        if (equiv(el1, el2)) Ok(bool)
                        else Err(s"cell=? requires cells with the same content type: ${MT.show(el1)} and ${MT.show(el2)}")
                    case _ => Err("cell=? requires two cellof types")
                }
                case (Err(m), _) => Err(m)
                case (_, Err(m)) => Err(m)
            }

        // ------------------------------------------------------------------
        // FLEX/M module forms (Figure 15.17)
        // ------------------------------------------------------------------

        case MModule(dts, vds) =>
            checkModuleIntro(dts, vds, TE, tyScope, scopes)

        case MOpen(emod, body) =>
            checkModuleElim(emod, body, TE, tyScope, scopes)

        case MLoad(_, t) =>
            // [loadLTstat] (Section 15.6): (load Y T) : T.
            openType(t, tyScope, scopes)

        case MMatch(disc, clauses) =>
            check(disc, TE, tyScope, scopes) flatMap { td =>
                checkMatch(td, clauses, TE, tyScope, scopes)
            }

        // ------------------------------------------------------------------
        // Sugar (defensive: sugar is desugared before checking)
        // ------------------------------------------------------------------

        case MLetRec(_, _) | MMselect(_, _) | MLetType(_, _) | MLetTypeStar(_, _) |
            BeginExp(_, _) | Cond(_, _) | Scand(_) | Scor(_) | SugaredPrimOp(_, _) =>
            Err("internal error: sugar form not desugared")

        case _ => Err("internal error: non-FLEX/M expression node")
    }

    // ------------------------------------------------------------------
    // [->-elim] (Figure 14.13)
    // ------------------------------------------------------------------

    private def elimArrow(params: List[(String, MT)], ret: MT, args: List[Exp],
                          TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[MT] = {
        // Each argument is checked in the plain environment; the i-th
        // argument's target is the i-th parameter type with the earlier
        // arguments substituted for the earlier parameter names (p.876).
        args.indices.foldLeft[Result[List[(Exp, MT)]]](Ok(Nil)) { (acc, i) =>
            acc flatMap { prev =>
                val target = Subst.substValNamesBound(
                    params.take(i).map(_._1).zip(prev.map(_._1)).toMap,
                    params(i)._2, Set.empty)
                check(args(i), TE, tyScope, scopes) match {
                    case Err(m) => Err(m)
                    case Ok(at) =>
                        subtype(at, target) match {
                            case None => Ok(prev :+ (args(i), at))
                            case Some(m) => Err(s"the " + (i + 1) + "th argument of the application: " + m)
                        }
                }
            }
        } flatMap { prev =>
            // Purity: an argument whose parameter name occurs in the
            // result type must be pure (its expression is substituted
            // into the result type on the way out).
            val impure = params.indices.filter(i =>
                Fr.valueIds(ret).contains(params(i)._1) && !isPure(args(i)))
            if (impure.nonEmpty)
                Err(s"the " + (impure.head + 1) + "th argument of the application is not pure, but its parameter name " + params(impure.head)._1 + " occurs in the result type " + MT.show(ret))
            else
                Ok(Subst.substValNamesBound(
                    params.map(_._1).zip(prev.map(_._1)).toMap, ret, Set.empty))
        }
    }

    // ------------------------------------------------------------------
    // [implicit-projection] (Section 15.4.5, Figure 15.18)
    // ------------------------------------------------------------------

    private def implicitProjection(vars: List[String], body: MT, args: List[Exp],
                                   TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[MT] =
        body match {
            case MTArrow(params, ret0) =>
                if (args.size != params.size)
                    Err(s"the polymorphic procedure expects ${params.size} argument(s), but got ${args.size}")
                else
                    args.indices.foldLeft[Result[List[MT]]](Ok(Nil)) { (acc, i) =>
                        acc flatMap { ts =>
                            check(args(i), TE, tyScope, scopes) match {
                                case Err(m) => Err(m)
                                case Ok(at) => Ok(ts :+ at)
                            }
                        }
                    } flatMap { ats =>
                        // Project onto fresh unification variables
                        // (Figure 15.18): the forall-bound type
                        // identifiers become unification variables.
                        val freshes = vars.map(v => "?v" + Fresh.next()).toList
                        val instM: List[(String, MT)] =
                            vars.zip(freshes).map { case (v, f) => v -> MTUnif(f) }
                        val instParams = params.map { case (_, pt) => Subst.substSim(instM, pt) }
                        // Capture restriction: no arrow parameter name may
                        // occur free in the (instantiated) parameter types
                        // or in the actual argument types.
                        val capture = params.map(_._1).toSet.intersect(
                            instParams.flatMap(Fr.valueIds).toSet ++ ats.flatMap(Fr.valueIds).toSet)
                        if (capture.nonEmpty)
                            Err(s"implicit projection: the parameter name(s) " + capture.mkString(", ") + " occur in dependent types; use an explicit pcall")
                        else
                            Unify.unifyAll(instParams.zip(ats)) match {
                                case Err(m) => Err(s"implicit projection failed: " + m + " (use an explicit pcall)")
                                case Ok(sigma) =>
                                    val retSigma = applyUnifySubst(sigma, Subst.substSim(instM, ret0))
                                    // Locality restriction: no unresolved
                                    // unification variables may remain.
                                    if (Fr.uniVars(retSigma).nonEmpty)
                                        Err(s"implicit projection: the result type " + MT.show(retSigma) + " still contains unresolved type variable(s) " + Fr.uniVars(retSigma).mkString(", ") + "; use an explicit pcall")
                                    else {
                                        val impure = params.indices.filter(i =>
                                            Fr.valueIds(ret0).contains(params(i)._1) && !isPure(args(i)))
                                        if (impure.nonEmpty)
                                            Err(s"implicit projection: the " + (impure.head + 1) + "th argument is not pure, but its parameter name " + params(impure.head)._1 + " occurs in the result type")
                                        else
                                            Ok(Subst.substValNamesBound(
                                                params.map(_._1).zip(args).toMap, retSigma, Set.empty))
                                    }
                            }
                    }
            case _ =>
                Err(s"the body of a polymorphic procedure type must be an arrow type, but it is " + MT.show(body))
        }

    // ------------------------------------------------------------------
    // Unification (the Figure 13.8 machinery, extended for FLEX/M:
    // substitutions map unification variables to types; forall-bound
    // type identifiers are rigid constants; two foralls unify by
    // substituting the same fresh rigid type-identifier sequence into
    // both, p.920)
    // ------------------------------------------------------------------

    object Unify {
        def unifyAll(pairs: List[(MT, MT)]): FlexMChecker.Result[Map[String, MT]] =
            pairs.foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(Map.empty)) { (acc, pr) =>
                acc flatMap { sigma =>
                    (pr match { case (t1, t2) => unify(t1, t2, sigma) })
                }
            }

        def unify(t1raw: MT, t2raw: MT, sigma: Map[String, MT]): FlexMChecker.Result[Map[String, MT]] = {
            val t1 = applyUnifySubst(sigma, t1raw)
            val t2 = applyUnifySubst(sigma, t2raw)
            (t1, t2) match {
                case (MTUnif(n), _) => bind(n, t2, sigma)
                case (_, MTUnif(n)) => bind(n, t1, sigma)
                case (MTBase(a), MTBase(b)) =>
                    if (a == b) Ok(sigma) else Err(s"the base types $a and $b differ")
                case (MTVar(a), MTVar(b)) =>
                    if (a == b) Ok(sigma) else Err(s"the type identifiers $a and $b differ (forall-bound type identifiers are rigid)")
                case (MTArrow(p1, r1), MTArrow(p2, r2)) =>
                    if (p1.size != p2.size)
                        Err(s"the arrows have different arities (${p1.size} vs ${p2.size})")
                    else {
                        // Normalize the parameter names (value names) by
                        // substituting the same fresh names into both.
                        val fresh = p1.map(_ => Fresh.next()).toList
                        val m1 = p1.map(_._1).zip(fresh).map { case (o, n) => (o, Var(n)) }.toMap
                        val m2 = p2.map(_._1).zip(fresh).map { case (o, n) => (o, Var(n)) }.toMap
                        val p1s = p1.map { case (_, pt) => Subst.substValNamesBound(m1, pt, Set.empty) }
                        val p2s = p2.map { case (_, pt) => Subst.substValNamesBound(m2, pt, Set.empty) }
                        val r1s = Subst.substValNamesBound(m1, r1, Set.empty)
                        val r2s = Subst.substValNamesBound(m2, r2, Set.empty)
                        p1s.zip(p2s).foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(sigma)) { (acc, pr) =>
                            acc flatMap { s => (pr match { case (a, b) => unify(a, b, s) }) }
                        } flatMap { s => unify(r1s, r2s, s) }
                    }
                case (MTRecord(f1), MTRecord(f2)) =>
                    if (f1.map(_._1).toSet == f2.map(_._1).toSet)
                        f1.foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(sigma)) { (acc, f) =>
                            (f, acc) match { case ((n, ft), r) =>
                                r flatMap { s =>
                                    f2.find(_._1 == n) match {
                                        case Some((_, ft2)) => unify(ft, ft2, s)
                                        case None => Err(s"the field $n is missing")
                                    }
                                }
                            }
                        }
                    else Err("the records have different fields")
                case (MTOneof(g1), MTOneof(g2)) =>
                    if (g1.map(_._1).toSet == g2.map(_._1).toSet)
                        g1.foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(sigma)) { (acc, f) =>
                            (f, acc) match { case ((n, tt), r) =>
                                r flatMap { s =>
                                    g2.find(_._1 == n) match {
                                        case Some((_, tt2)) => unify(tt, tt2, s)
                                        case None => Err(s"the tag $n is missing")
                                    }
                                }
                            }
                        }
                    else Err("the oneofs have different tags")
                case (MTProd(c1), MTProd(c2)) =>
                    if (c1.size == c2.size)
                        c1.zip(c2).foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(sigma)) { (acc, pr) =>
                            acc flatMap { s => (pr match { case (a, b) => unify(a, b, s) }) }
                        }
                    else Err(s"the products have different component counts (${c1.size} vs ${c2.size})")
                case (MTSeq(e1), MTSeq(e2)) => unify(e1, e2, sigma)
                case (MTCell(e1), MTCell(e2)) => unify(e1, e2, sigma)
                case (MTForall(v1, b1), MTForall(v2, b2)) =>
                    if (v1.size != v2.size)
                        Err(s"the forall types have different arities (${v1.size} vs ${v2.size})")
                    else {
                        // Substitute the same fresh rigid type-identifier
                        // sequence into both (p.920).
                        val fresh = v1.map(_ => Fresh.next()).toList
                        val b1s = Subst.substSim(v1.zip(fresh.map(v => MTVar(v))), b1)
                        val b2s = Subst.substSim(v2.zip(fresh.map(v => MTVar(v))), b2)
                        unify(b1s, b2s, sigma)
                    }
                case (MTModuleof(a1, v1), MTModuleof(a2, v2)) =>
                    if (a1.map { case (n, d) => (n, d.size) }.toSet == a2.map { case (n, d) => (n, d.size) }.toSet)
                        v1.foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(sigma)) { (acc, f) =>
                            (f, acc) match { case ((n, vt), r) =>
                                r flatMap { s =>
                                    v2.find(_._1 == n) match {
                                        case Some((_, vt2)) => unify(vt, vt2, s)
                                        case None => Err(s"the value $n is missing")
                                    }
                                }
                            }
                        }
                    else Err("the moduleof types have different abstract type constructors")
                case (MTyConApp(tc1, a1), MTyConApp(tc2, a2)) =>
                    if (tyconEquiv(tc1, tc2)) {
                        if (a1.size != a2.size)
                            Err(s"the type constructors have different arities (${a1.size} vs ${a2.size})")
                        else
                            a1.zip(a2).foldLeft[FlexMChecker.Result[Map[String, MT]]](Ok(sigma)) { (acc, pr) =>
                                acc flatMap { s => (pr match { case (x, y) => unify(x, y, s) }) }
                            }
                    }
                    else Err(s"the type constructors differ")
                case _ =>
                    Err(s"the types " + MT.show(t1) + " and " + MT.show(t2) + " cannot be unified")
            }
        }

        private def bind(n: String, t: MT, sigma: Map[String, MT]): FlexMChecker.Result[Map[String, MT]] = {
            // t is already sigma-expanded; the occurs-check looks for n
            // among t's unification variables.
            if (Fr.uniVars(t).contains(n))
                Err(s"occurs check: the type variable $n would be bound to a type that mentions it")
            else Ok(sigma + (n -> t))
        }
    }

    // ------------------------------------------------------------------
    // [moduleof-intro] (Figure 15.17)
    // ------------------------------------------------------------------

    private def checkModuleIntro(dts: List[MDtDef], vds: List[MValDef],
                                 TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[MT] = {
        val innerScopes = dts.foldLeft(scopes) { (s, dt) => s :+ ScopeDeclare(Set(dt.name)) }

        // The constructor / deconstructor types (Figure 15.4): with k
        // dummies (tau1* taunk), the constructor has type
        //   (forall (tau1* taunk) (-> (Tcomps) (theta tau1* taunk)))
        // (or (-> (Tcomps) theta) when k = 0), and the deconstructor has
        // type
        //   (forall (r tau1* taunk) (-> ((theta tau1* taunk) (-> (Tcomps) r) (-> () r)) r))
        // (or (forall (r) (-> (theta (-> (Tcomps) r) (-> () r)) r)) when k = 0).
        // The arrow parameter names of the Figure 15.4 types: they are
        // value names that never occur free, so the sugar arrow form
        // (-> (T*) T0) is displayed regardless of what they are.
        def named(comps: List[MT]): List[(String, MT)] =
            comps.zipWithIndex.map { case (t, i) => ("@@c" + i, t) }

        def ctorDctorTypes(dt: MDtDef): List[(String, MT)] =
            dt.ctors.flatMap { case (tag, comps) =>
                val tc = TyConName(dt.name)
                val ctorT: MT =
                    if (dt.params.isEmpty)
                        MTArrow(named(comps), MTyConApp(tc, Nil))
                    else
                        MTForall(dt.params, MTArrow(named(comps), MTyConApp(tc, dt.params.map(MTVar(_)))))
                val rName = if (dt.params.contains("r")) "@@r" + Fresh.next() else "r"
                val dctorParams: List[(String, MT)] =
                    if (dt.params.isEmpty)
                        List(("@@d1", MTyConApp(tc, Nil)),
                             ("@@d2", MTArrow(named(comps), MTVar(rName))),
                             ("@@d3", MTArrow(Nil, MTVar(rName))))
                    else {
                        val tyArgs = dt.params.map(MTVar(_))
                        List(("@@d1", MTyConApp(tc, tyArgs)),
                             ("@@d2", MTArrow(named(comps), MTVar(rName))),
                             ("@@d3", MTArrow(Nil, MTVar(rName))))
                    }
                val dctorT: MT =
                    if (dt.params.isEmpty)
                        MTForall(List(rName), MTArrow(dctorParams, MTVar(rName)))
                    else
                        MTForall(rName +: dt.params, MTArrow(dctorParams, MTVar(rName)))
                List((tag, ctorT), (tag + "~", dctorT))
            }

        // The DD component types are type positions too: they are opened
        // against the scope stack (a component type may mention a type
        // constructor of an enclosing open, which becomes a dependent
        // type constructor, Figure 15.6). The DD's own dummy names are
        // bound in its component types (Figure 15.4: the constructor /
        // deconstructor types quantify over them).
        val openedDts: Result[List[MDtDef]] =
            dts.indices.foldLeft[Result[List[MDtDef]]](Ok(Nil)) { (acc, i) =>
                acc flatMap { ds =>
                    val dt = dts(i)
                    dt.ctors.indices.foldLeft[Result[List[(String, List[MT])]]](Ok(Nil)) { (acc2, j) =>
                        acc2 flatMap { cs =>
                            (dt.ctors(j), openTypes(dt.ctors(j)._2, tyScope ++ dt.params.toSet, innerScopes)) match {
                                case ((tag, _), Err(m)) => Err(s"the data-type declaration " + dt.name + ": " + m)
                                case ((tag, _), Ok(cs2)) => Ok(cs :+ (tag -> cs2))
                            }
                        }
                    } map (cs => ds :+ MDtDef(dt.name, dt.params, cs))
                }
            }

        openedDts flatMap { dts2 =>
            val ctorTypes = dts2.flatMap(ctorDctorTypes)

            // The declared value types, opened in the module's tycon scope.
            vds.indices.foldLeft[Result[List[(String, MT)]]](Ok(Nil)) { (acc, i) =>
                acc flatMap { ts =>
                    openType(vds(i).t, tyScope, innerScopes) match {
                        case Err(m) => Err(m)
                        case Ok(t2) => Ok(ts :+ (vds(i).name -> t2))
                    }
                }
            } flatMap { decl =>
                // No rebinding (Figure 15.16).
                val rebind = (ctorTypes.map(_._1) ++ vds.map(_.name)).find(TE.contains)
                if (rebind.isDefined)
                    Err(s"the module introduces the name " + rebind.get + " that is already bound in this environment (FLEX/M does not permit rebinding)")
                else {
                    // The environment for the definition expressions: the
                    // outer TE, the constructor / deconstructor bindings,
                    // and all the declared value types (the value
                    // definitions are mutually recursive).
                    val TEext = TE ++ ctorTypes.toMap ++ decl.toMap
                    vds.indices.foldLeft[Result[Unit]](Ok(())) { (acc, i) =>
                        acc flatMap { _ =>
                            check(vds(i).e, TEext, tyScope, innerScopes) match {
                                case Err(m) => Err(m)
                                case Ok(te) =>
                                    subtype(te, decl(i)._2) match {
                                        case None => Ok(())
                                        case Some(m) => Err(s"the module definition " + vds(i).name + ": " + m)
                                    }
                            }
                        }
                    } flatMap { _ =>
                        // Import restriction (Figure 15.17): a local
                        // type-constructor name must not occur free in
                        // the type of a value that a definition
                        // expression uses from the outer environment.
                        val viol = dts2.flatMap { dt =>
                            vds.flatMap { vd =>
                                Fr.valueIdsExp(vd.e).flatMap { n =>
                                    TE.get(n).filter(t => Fr.tyconIds(t).contains(dt.name)).map(_ => (n, dt.name))
                                }
                            }
                        }
                        if (viol.nonEmpty)
                            Err(s"import restriction (module): the local type-constructor " + viol.head._2 + " would capture the reference in the type of the value " + viol.head._1)
                        else
                            // The moduleof type: the AT specs are
                            // recorded, the constructor / deconstructor
                            // types come from TE-DD, and the declared
                            // value types follow.
                            Ok(MTModuleof(dts2.map(dt => (dt.name, dt.params)), ctorTypes ++ decl))
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // [moduleof-elim] (Figure 15.17)
    // ------------------------------------------------------------------

    private def checkModuleElim(emod: Exp, body: Exp,
                                TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[MT] = {
        check(emod, TE, tyScope, scopes) match {
            case Err(m) => Err(m)
            case Ok(tmod) => tmod match {
                case MTModuleof(ats, vals) =>
                    // Purity restriction: the module expression must be
                    // pure (the dependent-type introduction and the
                    // on-the-way-out substitution substitute it into
                    // types).
                    if (!isPure(emod))
                        Err(s"(open ...) requires a pure module expression, but this module expression contains a mutation")
                    else {
                        // Import restriction (Figure 15.17).
                        val atNames = ats.map(_._1).toSet
                        val viol = atNames.flatMap { th =>
                            Fr.valueIdsExp(body).flatMap { n =>
                                TE.get(n).filter(t => Fr.tyconIds(t).contains(th)).map(_ => (n, th))
                            }
                        }
                        if (viol.nonEmpty)
                            Err(s"import restriction (open): the type-constructor " + viol.head._2 + " would capture the reference in the type of the value " + viol.head._1)
                        else {
                            // No rebinding (Figure 15.16).
                            val rebind = vals.map(_._1).find(TE.contains)
                            if (rebind.isDefined)
                                Err(s"(open ...) introduces the name " + rebind.get + " that is already bound in this environment (FLEX/M does not permit rebinding)")
                            else {
                                // Dependent-type introduction: each
                                // abstract type constructor theta becomes
                                // the dependent type constructor
                                // (dselect theta Emod). The TE extension
                                // uses the dsub'd value types, and the
                                // body's bare tycon names resolve through
                                // the open's tycon scope.
                                val dsubM: Map[String, TyCon] =
                                    ats.map { case (th, _) => th -> TyConSelect(th, emod) }.toMap
                                val openedVals: List[(String, MT)] =
                                    vals.map { case (n, vt) => n -> Subst.substTycon(dsubM, vt) }
                                val innerScopes = scopes :+ ScopeOpen(atNames, emod)
                                check(body, TE ++ openedVals, tyScope, innerScopes) match {
                                    case Err(m) => Err(m)
                                    case Ok(tbody) =>
                                        // On-the-way-out value
                                        // substitution (Figure 15.17):
                                        // [ (open Emod Ij) / Ij ] Tbody.
                                        Ok(Subst.substValNamesBound(
                                            vals.map { case (n, _) => (n, MOpen(emod, Var(n))) }.toMap,
                                            tbody, Set.empty))
                                }
                            }
                        }
                    }
                case _ =>
                    Err(s"(open ...) requires a module expression with a moduleof type, but the module expression has type " + MT.show(tmod))
            }
        }
    }

    // ------------------------------------------------------------------
    // Typed pattern matching (Section 15.4.6)
    // ------------------------------------------------------------------

    private def checkMatch(disc: MT, clauses: List[(Mpat, Exp)],
                           TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[MT] =
        disc match {
            case MTyConApp(_, _) =>
                clauses.indices.foldLeft[Result[List[MT]]](Ok(Nil)) { (acc, i) =>
                    acc flatMap { ts =>
                        clauses(i) match { case (p, b) =>
                            typePattern(p, disc, TE, tyScope, scopes, Map.empty) match {
                                case Err(m) => Err(m)
                                case Ok(pv) =>
                                    check(b, TE ++ pv, tyScope, scopes) match {
                                        case Err(m) => Err(m)
                                        case Ok(tb) => Ok(ts :+ tb)
                                    }
                            }
                        }
                    }
                } flatMap (ts => joinList(ts))
            case _ =>
                Err(s"match: the discriminant must have a type-constructor-application type, but it has type " + MT.show(disc))
        }

    // Type-check one pattern against the expected type et (a
    // type-constructor application for a constructor pattern; any type
    // for a variable or literal). The pattern variables are accumulated
    // in acc.
    private def typePattern(p: Mpat, et: MT, TE: Map[String, MT],
                            tyScope: Set[String], scopes: List[TyconScope], acc: Map[String, MT]): Result[Map[String, MT]] =
        p match {
            case MpatWild() => Ok(acc)

            case MpatVar(n) =>
                if (TE.contains(n) || acc.contains(n))
                    Err(s"the pattern variable $n is already bound in this environment")
                else Ok(acc + (n -> et))

            case MpatLit(l) =>
                check(l, TE, tyScope, scopes) match {
                    case Err(m) => Err(m)
                    case Ok(tl) =>
                        if (equiv(tl, et)) Ok(acc)
                        else Err(s"the literal pattern has type " + MT.show(tl) + ", which does not match the expected type " + MT.show(et))
                }

            case MpatCons(head, subs) =>
                et match {
                    case MTyConApp(tc, targs) =>
                        TE.get(head) match {
                            case None => Err(s"match: the constructor $head is not bound in this environment")
                            case Some(th) =>
                                // Case A: a polymorphic constructor of the
                                // form (forall (tau*) (-> (Tcomps) (theta
                                // tau*))); the sub-pattern variable types
                                // are [Targs/tau*]Tcomps.
                                val caseA: Option[List[MT]] = th match {
                                    case MTForall(vars, b) => b match {
                                        case MTArrow(paramTs, resT) => resT match {
                                            case MTyConApp(tc2, args2)
                                                if tyconEquiv(tc2, tc) && args2.size == vars.size &&
                                                    args2.zip(vars).forall { case (a, v) => a == MTVar(v) } &&
                                                    subs.size == paramTs.size =>
                                                Some(paramTs.map { case (_, pt) => Subst.substSim(vars.zip(targs), pt) })
                                            case _ => None
                                        }
                                        case _ => None
                                    }
                                    case _ => None
                                }
                                // Case B: a monomorphic constructor of a
                                // nullary type constructor (-> (Tcomps)
                                // theta); the sub-pattern variable types
                                // are the component types.
                                val caseB: Option[List[MT]] = th match {
                                    case MTArrow(paramTs, resT) => resT match {
                                        case MTyConApp(tc2, args2)
                                            if tyconEquiv(tc2, tc) && args2.size == targs.size &&
                                                args2.zip(targs).forall { case (a, b) => equiv(a, b) } &&
                                                subs.size == paramTs.size =>
                                            Some(paramTs.map(_._2))
                                        case _ => None
                                    }
                                    case _ => None
                                }
                                (caseA.orElse(caseB)) match {
                                    case Some(subTs) =>
                                        subs.zip(subTs).foldLeft[Result[Map[String, MT]]](Ok(acc)) { (accR, pr) =>
                                            (pr, accR) match { case ((sp, st), r) =>
                                                r flatMap (m => typePattern(sp, st, TE, tyScope, scopes, m))
                                            }
                                        }
                                    case None =>
                                        Err(s"match: the pattern (" + head + " ...) does not match the discriminant type " + MT.show(et) + " (the constructor " + head + " has type " + MT.show(th) + ")")
                                }
                    case _ =>
                        Err(s"match: the constructor pattern (" + head + " ...) expects a type-constructor-application type, but the expected type is " + MT.show(et))
                }
        }
        }

    // ------------------------------------------------------------------
    // Purity (Figure 13.25 of the book, the FLEX/M version)
    // ------------------------------------------------------------------

    def isPure(e: Exp): Boolean = !containsMutation(e)

    private def containsMutation(e: Exp): Boolean = e match {
        case SetExp(_, _) => true
        case CellSetExp(_, _) => true
        case If(t1, t2, t3) => containsMutation(t1) || containsMutation(t2) || containsMutation(t3)
        case PrimOp(_, args) => args.exists(containsMutation)
        case MAbs(_, body) => containsMutation(body)
        case MApp(r, args) => containsMutation(r) || args.exists(containsMutation)
        case Let(bs, body) => bs.map(_._2).exists(containsMutation) || containsMutation(body)
        case MThe(_, e2) => containsMutation(e2)
        case MOne(_, _, p) => containsMutation(p)
        case MPabs(_, body) => containsMutation(body)
        case MPcall(e2, _) => containsMutation(e2)
        case MError(_, _) => false
        case MModule(_, vds) => vds.map(_.e).exists(containsMutation)
        case MOpen(emod, body) => containsMutation(emod) || containsMutation(body)
        case MLoad(_, _) => false
        case MMatch(d, cls) => containsMutation(d) || cls.map(_._2).exists(containsMutation)
        case MLetRec(bs, body) => bs.map(_._3).exists(containsMutation) || containsMutation(body)
        case MMselect(_, emod) => containsMutation(emod)
        case MLetType(_, body) => containsMutation(body)
        case MLetTypeStar(_, body) => containsMutation(body)
        case TagCaseExp(d, _, cs, el) =>
            containsMutation(d) || cs.map(_._2).exists(containsMutation) || el.exists(containsMutation)
        case ProdExp(cs) => cs.exists(containsMutation)
        case GetExp(_, e2) => containsMutation(e2)
        case SeqExp(cs) => cs.exists(containsMutation)
        case SeqGetExp(i, s) => containsMutation(i) || containsMutation(s)
        case SeqSizeExp(e2) => containsMutation(e2)
        case RecordExp(fs) => fs.map(_._2).exists(containsMutation)
        case SelectExp(_, e2) => containsMutation(e2)
        case WithExp(r, b) => containsMutation(r) || containsMutation(b)
        case CellExp(e2) => containsMutation(e2)
        case DerefExp(e2) => containsMutation(e2)
        case CellEqExp(e1, e2) => containsMutation(e1) || containsMutation(e2)
        case BeginExp(e1, e2) => containsMutation(e1) || containsMutation(e2)
        case Cond(bs, d) =>
            bs.map { case (t1, th) => containsMutation(t1) || containsMutation(th) }.exists(identity) || d.exists(containsMutation)
        case Scand(es) => es.exists(containsMutation)
        case Scor(es) => es.exists(containsMutation)
        case SugaredPrimOp(_, args) => args.exists(containsMutation)
        case _ => false
    }

    // ------------------------------------------------------------------
    // Type equivalence (Figure 15.14)
    // ------------------------------------------------------------------

    def equiv(t1: MT, t2: MT): Boolean = (t1, t2) match {
        case (MTBase(a), MTBase(b)) => a == b
        case (MTVar(a), MTVar(b)) => a == b
        case (MTUnif(a), MTUnif(b)) => a == b
        case (MTArrow(p1, r1), MTArrow(p2, r2)) =>
            if (p1.size != p2.size) false
            else {
                // [->-≈] (Figure 14.12): the parameter names (value
                // names) are normalized to the same fresh names.
                val fresh = p1.map(_ => Fresh.next()).toList
                val m1 = p1.map(_._1).zip(fresh).map { case (o, n) => (o, Var(n)) }.toMap
                val m2 = p2.map(_._1).zip(fresh).map { case (o, n) => (o, Var(n)) }.toMap
                val (p1s, r1s) = canonArrow(p1, r1, m1)
                val (p2s, r2s) = canonArrow(p2, r2, m2)
                p1s.zip(p2s).forall { pr => (pr match { case (a, b) => equiv(a, b) }) } && equiv(r1s, r2s)
            }
        case (MTRecord(f1), MTRecord(f2)) =>
            f1.map(_._1).toSet == f2.map(_._1).toSet &&
                f1.forall { case (n, ft) => f2.find(_._1 == n).exists { case (_, ft2) => equiv(ft, ft2) } }
        case (MTOneof(g1), MTOneof(g2)) =>
            g1.map(_._1).toSet == g2.map(_._1).toSet &&
                g1.forall { case (n, tt) => g2.find(_._1 == n).exists { case (_, tt2) => equiv(tt, tt2) } }
        case (MTProd(c1), MTProd(c2)) =>
            c1.size == c2.size && c1.zip(c2).forall { pr => (pr match { case (a, b) => equiv(a, b) }) }
        case (MTSeq(e1), MTSeq(e2)) => equiv(e1, e2)
        case (MTCell(e1), MTCell(e2)) => equiv(e1, e2)
        case (MTForall(v1, b1), MTForall(v2, b2)) =>
            if (v1.size != v2.size) false
            else {
                val fresh = v1.map(_ => Fresh.next()).toList
                val b1s = Subst.substSim(v1.zip(fresh.map(v => MTVar(v))), b1)
                val b2s = Subst.substSim(v2.zip(fresh.map(v => MTVar(v))), b2)
                equiv(b1s, b2s)
            }
        case (MTModuleof(a1, v1), MTModuleof(a2, v2)) =>
            // [moduleof-≈] (Figure 15.14): the ATs are matched by name and
            // arity (the dummies have no binding power); the values are
            // matched by name. Since the AT sets are equal here, every
            // bare tycon name either refers to the corresponding AT on
            // both sides or is free on both sides.
            a1.map { case (n, d) => (n, d.size) }.toSet == a2.map { case (n, d) => (n, d.size) }.toSet &&
                v1.map(_._1).toSet == v2.map(_._1).toSet &&
                v1.forall { case (n, vt) => v2.find(_._1 == n).exists { case (_, vt2) => equiv(vt, vt2) } }
        case (MTyConApp(tc1, a1), MTyConApp(tc2, a2)) =>
            // [tyconapp-≈] (Figure 15.14): same type constructor (a
            // dependent one: same name and textually equal module
            // expression — the ≈depends default) and equivalent arguments.
            a1.size == a2.size && tyconEquiv(tc1, tc2) &&
                a1.zip(a2).forall { pr => (pr match { case (x, y) => equiv(x, y) }) }
        case _ => false
    }

    private def canonArrow(params: List[(String, MT)], ret: MT, m: Map[String, Exp]): (List[MT], MT) =
        (params.map { case (_, pt) => Subst.substValNamesBound(m, pt, Set.empty) },
         Subst.substValNamesBound(m, ret, Set.empty))

    // Two type constructors are the same: same name; a dependent type
    // constructor additionally requires textually equal module
    // expressions (the book's ≈depends, p.742, in its conservative form).
    private def tyconEquiv(tc1: TyCon, tc2: TyCon): Boolean = (tc1, tc2) match {
        case (TyConName(a), TyConName(b)) => a == b
        case (TyConSelect(a, e1), TyConSelect(b, e2)) =>
            a == b && FlexMExp.show(e1) == FlexMExp.show(e2)
        case _ => false
    }

    // ------------------------------------------------------------------
    // Subtyping (Figure 15.15): None when t1 ≤ t2, Some(reason)
    // otherwise.
    // ------------------------------------------------------------------

    def subtype(t1: MT, t2: MT): Option[String] =
        if (equiv(t1, t2)) None
        else (t1, t2) match {
            case (MTArrow(p1, r1), MTArrow(p2, r2)) =>
                if (p1.size != p2.size)
                    Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + " (different arities)")
                else {
                    val fresh = p1.map(_ => Fresh.next()).toList
                    val m1 = p1.map(_._1).zip(fresh).map { case (o, n) => (o, Var(n)) }.toMap
                    val m2 = p2.map(_._1).zip(fresh).map { case (o, n) => (o, Var(n)) }.toMap
                    val (p1s, r1s) = canonArrow(p1, r1, m1)
                    val (p2s, r2s) = canonArrow(p2, r2, m2)
                    // Contravariant in the parameters: the supertype's
                    // (t2's) parameter types must be subtypes of the
                    // subtype's (t1's) parameter types.
                    val paramErr = p2s.zip(p1s).foldLeft[Option[String]](None) { (acc, pr) =>
                        (acc, pr) match {
                            case (None, (a, b)) => subtype(a, b).map(m => s"parameter type: $m")
                            case (Some(_), _) => acc
                        }
                    }
                    paramErr match {
                        case Some(m) => Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": " + m)
                        case None =>
                            subtype(r1s, r2s).map(m => s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": result type: " + m)
                    }
                }
            case (MTRecord(f1), MTRecord(f2)) =>
                // The subtype has at least the supertype's fields, with
                // each supertype field's type a supertype of the
                // subtype's.
                val missing = f2.collect { case (n, _) if !f1.exists(_._1 == n) => n }
                if (missing.nonEmpty)
                    Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": the field(s) " + missing.mkString(", ") + " are missing")
                else
                    f2.foldLeft[Option[String]](None) { (acc, f) =>
                        (acc, f) match {
                            case (None, (n, ft2)) =>
                                f1.find(_._1 == n) match {
                                    case Some((_, ft1)) => subtype(ft1, ft2).map(m => s"the field $n: $m")
                                    case None => None
                                }
                            case (Some(_), _) => acc
                        }
                    } match {
                        case Some(m) => Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": " + m)
                        case None => None
                    }
            case (MTOneof(g1), MTOneof(g2)) =>
                // The subtype has at most the supertype's tags, with each
                // subtype tag's type a subtype of the supertype's.
                val extra = g1.collect { case (n, _) if !g2.exists(_._1 == n) => n }
                if (extra.nonEmpty)
                    Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": the tag(s) " + extra.mkString(", ") + " do not occur in the supertype")
                else
                    g1.foldLeft[Option[String]](None) { (acc, f) =>
                        (acc, f) match {
                            case (None, (n, tt1)) =>
                                g2.find(_._1 == n) match {
                                    case Some((_, tt2)) => subtype(tt1, tt2).map(m => s"the tag $n: $m")
                                    case None => None
                                }
                            case (Some(_), _) => acc
                        }
                    } match {
                        case Some(m) => Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": " + m)
                        case None => None
                    }
            case (MTProd(c1), MTProd(c2)) =>
                if (c1.size != c2.size)
                    Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + " (different component counts)")
                else
                    c1.zip(c2).foldLeft[Option[String]](None) { (acc, pr) =>
                        (acc, pr) match {
                            case (None, (a, b)) => subtype(a, b).map(m => s"component type: $m")
                            case (Some(_), _) => acc
                        }
                    } match {
                        case Some(m) => Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": " + m)
                        case None => None
                    }
            case (MTSeq(e1), MTSeq(e2)) =>
                subtype(e1, e2).map(m => s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + ": element type: " + m)
            case (MTCell(e1), MTCell(e2)) =>
                // cellof is invariant in its content type.
                if (equiv(e1, e2)) None
                else Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + " (cellof content types are invariant)")
            case (MTForall(v1, b1), MTForall(v2, b2)) =>
                if (v1.size != v2.size)
                    Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + " (different forall arities)")
                else {
                    val fresh = v1.map(_ => Fresh.next()).toList
                    val b1s = Subst.substSim(v1.zip(fresh.map(v => MTVar(v))), b1)
                    val b2s = Subst.substSim(v2.zip(fresh.map(v => MTVar(v))), b2)
                    subtype(b1s, b2s)
                }
            case (m1 @ MTModuleof(_, _), m2 @ MTModuleof(_, _)) => moduleofSubtype(m1, m2)
            case (MTyConApp(_, _), _) =>
                Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2) + " (type-constructor applications are not subtypes unless they are equivalent)")
            case _ =>
                Some(s"the type " + MT.show(t1) + " is not a subtype of " + MT.show(t2))
        }

    // [moduleof-≤] (Figure 15.15, p.912):
    //   (a) the supertype's abstract types must exist in the subtype with
    //       the same name and arity;
    //   (b) every supertype value component must be present in the
    //       subtype with a subtype type (the abstract-type names present
    //       in both signatures are identified; a name present in only
    //       one signature is renamed apart so it cannot be confused with
    //       an outer type constructor of the same name — the Tmod1 /
    //       Tmod2 example of p.912);
    //   (c) all free type-constructor names of the supertype must also
    //       be free in the subtype (the variable-capture restriction).
    private def moduleofSubtype(m1: MTModuleof, m2: MTModuleof): Option[String] = {
        val m1arity = m1.ats.map { case (n, d) => n -> d.size }.toMap
        val missing = m2.ats.collect {
            case (n, d) if !m1arity.contains(n) || m1arity(n) != d.size => n
        }
        if (missing.nonEmpty)
            Some(s"the type " + MT.show(m1) + " is not a subtype of " + MT.show(m2) + ": the abstract type constructor(s) " + missing.mkString(", ") + " are missing")
        else {
            val matched = m2.ats.map(_._1).filter(n =>
                m1.ats.exists { case (n2, d2) => n2 == n && d2.size == m2.ats.find(_._1 == n).map(_._2.size).getOrElse(-1) }
            ).toSet
            val rename1 = m1.ats.collect { case (n, _) if !matched.contains(n) => n -> TyConName("@@opq1_" + n) }.toMap
            val rename2 = m2.ats.collect { case (n, _) if !matched.contains(n) => n -> TyConName("@@opq2_" + n) }.toMap
            val valErr = m2.vals.foldLeft[Option[(String, String)]](None) { (acc, f) =>
                (acc, f) match {
                    case (None, (n, t2)) =>
                        m1.vals.find(_._1 == n) match {
                            case Some((_, t1)) =>
                                subtype(Subst.substTycon(rename1, t1), Subst.substTycon(rename2, t2))
                                    .map(m => (n, m))
                            case None => Some((n, "the value is missing"))
                        }
                    case (Some(_), _) => acc
                }
            }
            valErr match {
                case Some((n, m)) => Some(s"the type " + MT.show(m1) + " is not a subtype of " + MT.show(m2) + ": the component " + n + ": " + m)
                case None =>
                    val fr2 = Fr.tyconIds(m2)
                    val fr1 = Fr.tyconIds(m1)
                    if (fr2.subsetOf(fr1)) None
                    else Some(s"the type " + MT.show(m1) + " is not a subtype of " + MT.show(m2) + ": the type-constructor name(s) " + (fr2 -- fr1).mkString(", ") + " are free in the supertype but not in the subtype (variable capture)")
            }
        }
    }

    // ------------------------------------------------------------------
    // Joining (FLEX/M has no [inclusion]; the join of two types is
    // used for the branches of (if ...), the components of (seq ...),
    // the clause results of (tagcase ...) and (match ...), and the
    // record / oneof union forms)
    // ------------------------------------------------------------------

    def join(t1: MT, t2: MT): Result[MT] = {
        if (equiv(t1, t2)) Ok(t1)
        else subtype(t1, t2) match {
            case None => Ok(t2)
            case Some(_) => subtype(t2, t1) match {
                case None => Ok(t1)
                case Some(_) => (t1, t2) match {
                    case (MTRecord(f1), MTRecord(f2)) => joinFields(f1, f2).map(MTRecord(_))
                    case (MTOneof(g1), MTOneof(g2)) => joinTags(g1, g2).map(MTOneof(_))
                    case (MTSeq(e1), MTSeq(e2)) => join(e1, e2).map(MTSeq(_))
                    case (MTCell(e1), MTCell(e2)) =>
                        if (equiv(e1, e2)) Ok(MTCell(e1))
                        else Err(s"cannot join the types " + MT.show(t1) + " and " + MT.show(t2) + " (cellof content types are invariant)")
                    case (MTForall(v1, b1), MTForall(v2, b2)) =>
                        if (v1.size == v2.size) {
                            val fresh = v1.map(_ => Fresh.next()).toList
                            val b1s = Subst.substSim(v1.zip(fresh.map(v => MTVar(v))), b1)
                            val b2s = Subst.substSim(v2.zip(fresh.map(v => MTVar(v))), b2)
                            join(b1s, b2s).map(b => MTForall(v1, b))
                        }
                        else Err(s"cannot join the types " + MT.show(t1) + " and " + MT.show(t2) + " (different forall arities)")
                    case _ =>
                        Err(s"cannot join the types " + MT.show(t1) + " and " + MT.show(t2) + " (FLEX/M has no implicit inclusion; use (the ...))")
                }
            }
        }
    }

    // The least upper bound of two record types: the union of the
    // fields, with the shared fields joined.
    private def joinFields(f1: List[(String, MT)], f2: List[(String, MT)]): Result[List[(String, MT)]] = {
        val newIn2 = f2.filterNot(f => f1.exists(_._1 == f._1))
        f1.foldRight[Result[List[(String, MT)]]](Ok(newIn2)) { (f, acc) =>
            (f, acc) match {
                case ((n, tf), Ok(rest)) =>
                    f2.find(_._1 == n) match {
                        case Some((_, tf2)) => join(tf, tf2).map(j => (n, j) :: rest)
                        case None => Ok((n, tf) :: rest)
                    }
                case (_, Err(m)) => Err(m)
            }
        }
    }

    // The least upper bound of two oneof types: the common tags, with
    // the payload types joined.
    private def joinTags(g1: List[(String, MT)], g2: List[(String, MT)]): Result[List[(String, MT)]] = {
        val common = g1.filter(g => g2.exists(_._1 == g._1))
        if (common.isEmpty)
            Err("cannot join oneof types with disjoint tags")
        else
            common.foldLeft[Result[List[(String, MT)]]](Ok(Nil)) { (acc, f) =>
                (f, acc) match {
                    case ((n, tg), Ok(init)) =>
                        g2.find(_._1 == n) match {
                            case Some((_, tg2)) => join(tg, tg2).map(j => init :+ (n, j))
                            case None => Ok(init :+ (n, tg))
                        }
                    case (_, Err(m)) => Err(m)
                }
            }
    }

    private def joinList(ts: List[MT]): Result[MT] = ts match {
        case Nil => Err("no results to join")
        case t :: rest => rest.foldLeft[Result[MT]](Ok(t)) { (acc, u) => acc flatMap (x => join(x, u)) }
    }

    private def checkAll(es: List[Exp], TE: Map[String, MT], tyScope: Set[String], scopes: List[TyconScope]): Result[List[MT]] =
        es.indices.foldLeft[Result[List[MT]]](Ok(Nil)) { (acc, i) =>
            acc flatMap { ts =>
                check(es(i), TE, tyScope, scopes) match {
                    case Err(m) => Err(m)
                    case Ok(t) => Ok(ts :+ t)
                }
            }
        }
}

// -----------------------------------------------------------------------
// Program-level checking (Figure 15.2)
// -----------------------------------------------------------------------

object FlexMProgramChecker {

    private val unit = MTBase("unit"); private val bool = MTBase("bool")
    private val int = MTBase("int");  private val symb = MTBase("symb")

    private def fn1(a: MT, r: MT): MT = MTArrow(List(("@@sl1", a)), r)
    private def fn2(a: MT, b: MT, r: MT): MT = MTArrow(List(("@@sl1", a), ("@@sl2", b)), r)

    // The standard library of a FLEX/M program (Figure 15.2): a global
    // procedure for each primitive operator, plus true / false. In
    // contrast to FLEX/SP, the standard list procedures are NOT part of
    // the standard library: in FLEX/M, lists are a module, not a kernel
    // construct.
    val TstandardLib: MT = MTModuleof(Nil, List(
        "not" -> fn1(bool, bool),
        "and" -> fn2(bool, bool, bool),
        "or" -> fn2(bool, bool, bool),
        "bool=?" -> fn2(bool, bool, bool),
        "=" -> fn2(int, int, bool),
        "!=" -> fn2(int, int, bool),
        "<" -> fn2(int, int, bool),
        "<=" -> fn2(int, int, bool),
        ">" -> fn2(int, int, bool),
        ">=" -> fn2(int, int, bool),
        "+" -> fn2(int, int, int),
        "-" -> fn2(int, int, int),
        "*" -> fn2(int, int, int),
        "/" -> fn2(int, int, int),
        "%" -> fn2(int, int, int),
        "sym=?" -> fn2(symb, symb, bool),
        "true" -> bool,
        "false" -> bool))

    def check(p: FlexMPgm): FlexResult = p match {
        case FlexMKernelProgram(formals, body) =>
            // Desugar is the identity on kernel expressions; it also
            // removes any sugar that was (permissively) admitted in a
            // flex/Mk program.
            checkFormalsAndBody(formals, Desugar(body), Map.empty)

        case FlexMSugarProgram(formals, body, typeDefs, dts, vds) =>
            // (1) The def-type declarations: each definition must be
            //     well formed relative to the earlier def-types (a type
            //     identifier defined by one def-type can be used in
            //     subsequent def-types).
            val typeErr = typeDefs.zipWithIndex.foldLeft[Option[String]](None) {
                (acc, item) =>
                    (acc, item) match {
                        case (None, ((_, td), i)) =>
                            Open.open(td, typeDefs.take(i).map(_._1).toSet, Nil) match {
                                case Open.Ok(_) => None
                                case Open.Err(m) => Some(s"def-type: " + m)
                            }
                        case (Some(m), _) => Some(m)
                    }
            }
            typeErr match {
                case Some(m) => FlexErr(m)
                case None =>
                    // (2) Desugar the value definitions and the body
                    //     (Figure 15.2).
                    val vds2 = vds.map(vd => MValDef(vd.name, vd.t, Desugar(vd.e)))
                    val body2 = Desugar(body)
                    // (3) The kernel program form (Figure 15.2):
                    //     (flex/Mk formals
                    //       (open (load standard-library.flxm TstandardLib)
                    //         (open (module DD* VD*) Ebody)))
                    val innerExpr = MOpen(MModule(dts, vds2), body2)
                    // (4) The sequential def-type substitution (the
                    //     let-type* desugaring): the type of the i-th
                    //     def-type is substituted by the earlier
                    //     def-types, and then all the def-types are
                    //     substituted into the module and the body.
                    val substitutedTypeDefs: List[(String, MT)] = typeDefs.indices.map { i =>
                        val (tau, td) = typeDefs(i)
                        val tdSub = typeDefs.take(i).foldRight(td) { (prev, t) =>
                            prev match { case (ptau, ptd) => Subst.substType(ptd, ptau, t) }
                        }
                        (tau, tdSub)
                    }.toList
                    val innerExpr2 = substitutedTypeDefs.foldLeft[Exp](innerExpr) { (ex, item) =>
                        item match { case (tau, tdSub) => Desugar.substTypeDefsExp(tdSub, tau, ex) }
                    }
                    val kernelBody = MOpen(MLoad("standard-library.flxm", TstandardLib), innerExpr2)
                    // (5) Check the kernel program.
                    checkFormalsAndBody(formals, kernelBody, Map.empty)
            }
    }

    // Check the body of a (desugared) program: open the formal types,
    // then check the body with an empty type-variable scope and an
    // empty tycon-scope stack. The reported program type is
    // (=> (Tformal*) Tbody) (Figure 11.1 of the book); with no formals,
    // it is just the body type.
    def checkFormalsAndBody(formals: List[(String, MT)], body: Exp, preTE: Map[String, MT]): FlexResult = {
        var TE: Map[String, MT] = preTE
        var errOpt: Option[String] = None
        for ((n, t) <- formals if errOpt.isEmpty) {
            Open.open(t, Set.empty, Nil) match {
                case Open.Err(m) => errOpt = Some(s"malformed type in formal parameter $n: $m")
                case Open.Ok(t2) => TE = TE + (n -> t2)
            }
        }
        errOpt match {
            case Some(m) => FlexErr(m)
            case None =>
                FlexMChecker.check(body, TE, Set.empty, Nil) match {
                    case FlexMChecker.Ok(ct) =>
                        val progStr = if (formals.isEmpty) MT.show(ct)
                        else "(=> (" + formals.map { case (_, t) => MT.show(t) }.mkString(" ") + ") " + MT.show(ct) + ")"
                        FlexOk(progStr)
                    case FlexMChecker.Err(m) => FlexErr(m)
                }
        }
    }
}

// Parse and type-check a FLEX/M program.
def flexmCheck(input: String): FlexResult =
    FlexMProgram(input) match {
        case Some(p) => FlexMProgramChecker.check(p)
        case None => FlexErr("parse error")
    }

// Test helper:  "(flex/M ...)" shouldFlexMCheckTo (FlexOk("..."))
extension (input: String)
    def shouldFlexMCheckTo(expected: FlexResult): Unit = {
        val got = flexmCheck(input)
        assert(got == expected, s"expected $expected but got $got for: $input")
    }
