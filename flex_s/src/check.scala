package DSL.flex_s

import DSL.fl._
import DSL.flex._

// The reference static semantics of FLEX/S (Chapter 12.1 of the book): the
// FLEX type checker in which every "the types must be equivalent" test of
// FLEX (Figures 11.7, 11.15–11.18, 11.21–11.24) is replaced by a directional
// subtype test (Figures 12.1, 12.2, and 12.4 of the book), computed by the
// equirecursive algorithm in Subtype.scala. Where the book's rule keeps an
// exact match, the checker keeps one too: the if-test type (bool), the
// sequence-index type (int), and the cellof content type of cell=?
// (invariance, book p.705).
//
// The match points and their subtyping directions (T' is the inferred
// type, T the expected one):
//
//   if-branches      : a common supertype of the two branch types
//   ->-elim          : argument type ≤ formal-parameter type
//   letrec bindings  : inferred type ≤ declared type
//   the              : inferred type ≤ ascribed type
//   seq components   : a common supertype of the component types
//   one payload      : inferred payload type ≤ tag type
//   tagcase bodies   : a common supertype of the clause-result types
//   cons head        : inferred head type ≤ list element type
//   set!             : inferred value type ≤ variable's declared type
//   :=               : inferred value type ≤ cell content type
//   primop args      : inferred argument type ≤ declared argument type
//   (def bindings go through the letrec rule above)
//
// Because every equivalence is a subtype relation ([equiv-≤]), FLEX/S is a
// strict superset of FLEX: every FLEX program type-checks under FLEX/S.
//
// A type check yields Ok(ct) — the inferred type (a CT, i.e. a type tree
// plus the environment that interprets its free type identifiers) — or
// Err(message).
object SubtypeChecker {

    // Result[CT] is the type of a check; the generic parameter is used for
    // internal accumulators (Result[Unit], Result[List[CT]]).
    sealed trait Result[+A]
    final case class Ok[A](value: A) extends Result[A]
    final case class Err(msg: String) extends Result[Nothing]

    private val bool = TBase("bool")
    private val int = TBase("int")

    // The primitive type environment TEprim (Figure 11.6 of the book). The
    // case objects (Not, And, ...) are top-level members of DSL.fl.
    val TEprim: Map[PrimOpTag, (List[T], T)] = Map(
        Not -> (List(bool), bool),
        And -> (List(bool, bool), bool),
        Or -> (List(bool, bool), bool),
        BoolEq -> (List(bool, bool), bool),
        Eq -> (List(int, int), bool),
        Neq -> (List(int, int), bool),
        Lt -> (List(int, int), bool),
        Le -> (List(int, int), bool),
        Gt -> (List(int, int), bool),
        Ge -> (List(int, int), bool),
        Plus -> (List(int, int), int),
        Minus -> (List(int, int), int),
        Star -> (List(int, int), int),
        Slash -> (List(int, int), int),
        Percent -> (List(int, int), int),
        SymEq -> (List(TBase("symb"), TBase("symb")), bool)
    )

    def check(e: Exp, TE: Map[String, CT]): Result[CT] = e match {

        // ------------------------------------------------------------------
        // Literals and variables (Figures 11.7: [unit] [int] [bool] [symb]
        // [error] [var])
        // ------------------------------------------------------------------

        case UnitLit() => Ok(CT.closed(TBase("unit")))
        case BoolLit(_) => Ok(CT.closed(bool))
        case IntLit(_) => Ok(CT.closed(int))
        case Sym(_) => Ok(CT.closed(TBase("symb")))

        case FlexError(msg, t) => CT.open(t) match {
            case Some(ct) => Ok(ct)
            case None => Err("malformed type in an (error ...) expression")
        }

        case Var(name) => TE.get(name) match {
            case Some(ct) => Ok(ct)
            case None => Err(s"unbound variable: $name")
        }

        // ------------------------------------------------------------------
        // Conditionals and primitives ([if], [prim])
        // ------------------------------------------------------------------

        case If(test, th, el) =>
            check(test, TE) match {
                case Ok(ct) if CT.equiv(ct, CT.closed(bool)) =>
                    (check(th, TE), check(el, TE)) match {
                        case (Ok(c1), Ok(c2)) =>
                            // FLEX/S: the branches need only have a common
                            // supertype (Figure 12.1 inclusion).
                            if (Subtype.subtype(c1, c2)) Ok(c2)
                            else if (Subtype.subtype(c2, c1)) Ok(c1)
                            else Err(s"the if branches have incompatible types: ${c1.show} and ${c2.show}")
                        case (Err(m), _) => Err(m)
                        case (_, Err(m)) => Err(m)
                    }
                case Ok(ct) => Err(s"the if test must have type bool, but has type ${ct.show}")
                case Err(m) => Err(m)
            }

        case PrimOp(op, args) => TEprim.get(op) match {
            case None => Err(s"unknown primitive operator: $op")
            case Some((argTs, ret)) =>
                checkArgs(args, argTs.map(CT.closed), TE) match {
                    case Ok(_) => Ok(CT.closed(ret))
                    case Err(m) => Err(m)
                }
        }

        // ------------------------------------------------------------------
        // Procedures ([->-intro], [->-elim])
        // ------------------------------------------------------------------

        case AbsExp(params, body) =>
            val (teP, envAcc, errOpt) = params.foldLeft((TE, Map.empty[String, T], None: Option[String])) {
                (state, param) =>
                    state match {
                        case (teCur, envCur, None) =>
                            param match {
                                case (n, t) =>
                                    CT.open(t) match {
                                        case None => (teCur, envCur, Some(s"malformed type in formal parameter $n"))
                                        case Some(ct) =>
                                            val ct2 = CT.renameEnv(ct, envCur.keys.toSet)
                                            (teCur + (n -> ct2), envCur ++ ct2.env, None)
                                    }
                            }
                        case other => other
                    }
            }
            errOpt match {
                case Some(m) => Err(m)
                case None =>
                    check(body, teP) match {
                        case Err(m) => Err(m)
                        case Ok(cb) =>
                            val cb2 = CT.renameEnv(cb, envAcc.keys.toSet)
                            Ok(CT(TArrow(params.map { case (n, _) => teP(n).t }, cb2.t),
                                  envAcc ++ cb2.env))
                    }
            }

        case AppExp(rator, args) =>
            check(rator, TE) match {
                case Err(m) => Err(m)
                case Ok(rt) => CT.asArrow(rt) match {
                    case None => Err(s"the rator has type ${rt.show}, which is not a procedure type")
                    case Some((argTs, ret)) =>
                        args.zip(argTs).foldLeft[Result[Unit]](Ok(())) {
                            (acc, pair) =>
                                (acc, pair) match {
                                    case (Ok(_), (a, at)) =>
                                        check(a, TE) match {
                                            case Err(m) => Err(m)
                                            case Ok(a2) =>
                                                if (Subtype.subtype(a2, at)) Ok(())
                                                else Err(s"the argument has type ${a2.show}, but the procedure expects ${at.show}")
                                        }
                                    case (Err(m), _) => Err(m)
                                }
                        } match {
                            case Ok(_) => Ok(ret)
                            case Err(m) => Err(m)
                        }
                }
            }

        // ------------------------------------------------------------------
        // Bindings ([let], [letrec])
        // ------------------------------------------------------------------

        case Let(binds, body) =>
            binds.foldLeft[Either[String, Map[String, CT]]](Right(TE)) {
                (acc, binding) =>
                    (acc, binding) match {
                        case (Right(teCur), (n, e2)) =>
                            check(e2, teCur) match {
                                case Ok(ct) => Right(teCur + (n -> ct))
                                case Err(m) => Left(m)
                            }
                        case (Left(m), _) => Left(m)
                    }
            } match {
                case Right(teCur) => check(body, teCur)
                case Left(m) => Err(m)
            }

        case LetRecExp(bindings, body) =>
            // Open the declared types (type annotations must be closed) and
            // build the extended environment all at once (the bindings are
            // mutually recursive).
            val declared = bindings.foldLeft[Either[String, Map[String, CT]]](Right(TE)) {
                (acc, binding) =>
                    (acc, binding) match {
                        case (Right(teCur), (n, t, _)) =>
                            CT.open(t) match {
                                case None => Left(s"malformed type in letrec binding $n")
                                case Some(ct) => Right(teCur + (n -> ct))
                            }
                        case (Left(m), _) => Left(m)
                    }
            }
            declared match {
                case Left(m) => Err(m)
                case Right(tec) =>
                    bindings.foldLeft[Either[String, Unit]](Right(())) {
                        (acc, binding) =>
                            (acc, binding) match {
                                case (Right(_), (n, _, e2)) =>
                                    check(e2, tec) match {
                                        case Err(m) => Left(m)
                                        case Ok(et) =>
                                            if (Subtype.subtype(et, tec(n))) Right(())
                                            else Left(s"the letrec binding $n has type ${et.show}, but is declared to have type ${tec(n).show}")
                                    }
                                case (Left(m), _) => Left(m)
                            }
                    } match {
                        case Left(m) => Err(m)
                        case Right(_) => check(body, tec)
                    }
            }

        // ------------------------------------------------------------------
        // Type ascription ([the])
        // ------------------------------------------------------------------

        case TheExp(t, e2) => CT.open(t) match {
            case None => Err("malformed type in a (the ...) expression")
            case Some(ct) =>
                check(e2, TE) match {
                    case Err(m) => Err(m)
                    case Ok(et) =>
                        if (Subtype.subtype(et, ct)) Ok(ct)
                        else Err(s"the type ascription says ${ct.show}, but the expression has type ${et.show}, which is not a subtype of it")
                }
        }

        // ------------------------------------------------------------------
        // Pairs (Figure 11.15)
        // ------------------------------------------------------------------

        case Pair(f, s) => (check(f, TE), check(s, TE)) match {
            case (Ok(c1), Ok(c2)) =>
                val c2b = CT.renameEnv(c2, c1.env.keys.toSet)
                Ok(CT(TPair(c1.t, c2b.t), c1.env ++ c2b.env))
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        case FstExp(e2) => elimPair(e2, TE, "fst") { case (f, _) => f }
        case SndExp(e2) => elimPair(e2, TE, "snd") { case (_, s) => s }

        // ------------------------------------------------------------------
        // Tuples (Figure 11.16)
        // ------------------------------------------------------------------

        case ProdExp(comps) =>
            checkAll(comps, TE) match {
                case Err(m) => Err(m)
                case Ok(cts) =>
                    val (ts, env) = foldRename(cts)
                    Ok(CT(TProd(ts), env))
            }

        case GetExp(index, e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asProd(ct) match {
                    case None => Err(s"(get ...) requires a prodof type, but got ${ct.show}")
                    case Some(comps) =>
                        if (index >= 1 && index <= comps.size) Ok(comps(index - 1))
                        else Err(s"(get $index ...) is out of range for a product of ${comps.size} components")
                }
            }

        // ------------------------------------------------------------------
        // Sequences (Figure 11.17)
        // ------------------------------------------------------------------

        case SeqExp(comps) =>
            if (comps.isEmpty) Err("an empty sequence (seq) has no element type")
            else checkAll(comps, TE) match {
                case Err(m) => Err(m)
                case Ok(cts) =>
                    cts.drop(1).foldLeft[Result[CT]](Ok(cts.head)) {
                        (acc, ct) =>
                            (acc, ct) match {
                                case (Ok(elem), _) =>
                                    // FLEX/S: the components need only have a
                                    // common supertype.
                                    if (Subtype.subtype(ct, elem)) Ok(elem)
                                    else if (Subtype.subtype(elem, ct)) Ok(ct)
                                    else Err(s"sequence components must have a common supertype, but found ${elem.show} and ${ct.show}")
                                case (Err(m), _) => Err(m)
                            }
                    } match {
                        case Ok(elem) => Ok(CT(TSeq(elem.t), elem.env))
                        case Err(m) => Err(m)
                    }
            }

        case SeqGetExp(index, seq) => (check(index, TE), check(seq, TE)) match {
            case (Ok(ict), Ok(sct)) =>
                if (!CT.equiv(ict, CT.closed(int)))
                    Err(s"the sequence index must have type int, but has type ${ict.show}")
                else CT.asSeq(sct) match {
                    case Some(elem) => Ok(elem)
                    case None => Err(s"(seq-get ...) requires a seqof type, but got ${sct.show}")
                }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        case SeqSizeExp(e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asSeq(ct) match {
                    case Some(_) => Ok(CT.closed(int))
                    case None => Err(s"(seq-size ...) requires a seqof type, but got ${ct.show}")
                }
            }

        // ------------------------------------------------------------------
        // Records (Figure 11.18)
        // ------------------------------------------------------------------

        case RecordExp(fields) =>
            fields.foldLeft[Either[String, List[(String, CT)]]](Right(Nil)) {
                (acc, field) =>
                    (acc, field) match {
                        case (Right(acc2), (n, e2)) =>
                            if (acc2.exists(_._1 == n)) Left(s"duplicate record field: $n")
                            else check(e2, TE) match {
                                case Err(m) => Left(m)
                                case Ok(ct) => Right(acc2 :+ (n, ct))
                            }
                        case (Left(m), _) => Left(m)
                    }
            } match {
                case Left(m) => Err(m)
                case Right(pairs) =>
                    val (ts, env) = foldRename(pairs.map(_._2))
                    Ok(CT(TRecord(pairs.zip(ts).map { case ((n, _), t2) => (n, t2) }), env))
            }

        case SelectExp(name, e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asRecord(ct) match {
                    case None => Err(s"(select ...) requires a recordof type, but got ${ct.show}")
                    case Some(fields) => fields.find(_._1 == name) match {
                        case Some((_, fct)) => Ok(fct)
                        case None =>
                            Err(s"the record has no field named $name (fields: ${fields.map(_._1).mkString(", ")})")
                    }
                }
            }

        case WithExp(rcd, body) =>
            check(rcd, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asRecord(ct) match {
                    case None => Err(s"(with ...) requires a recordof type, but got ${ct.show}")
                    case Some(fields) =>
                        val TE2 = TE ++ fields.map { case (n, fct) => n -> fct }.toMap
                        check(body, TE2)
                }
            }

        // ------------------------------------------------------------------
        // Oneofs (Figure 11.22)
        // ------------------------------------------------------------------

        case OneExp(oneofT, tag, payload) => CT.open(oneofT) match {
            case None => Err("malformed oneof type in a (one ...) expression")
            case Some(ct) => CT.asOneof(ct) match {
                case None => Err(s"the type ${ct.show} in a (one ...) expression is not a oneof type")
                case Some(tags) => tags.find(_._1 == tag) match {
                    case None => Err(s"the tag $tag is not in the oneof type ${ct.show}")
                    case Some((_, ptype)) =>
                        check(payload, TE) match {
                            case Err(m) => Err(m)
                            case Ok(pt) =>
                                if (Subtype.subtype(pt, ptype)) Ok(ct)
                                else Err(s"the payload has type ${pt.show}, but the tag $tag expects ${ptype.show}")
                        }
                }
            }
        }

        case TagCaseExp(disc, payloadName, clauses, elseExp) =>
            check(disc, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asOneof(ct) match {
                    case None => Err(s"(tagcase ...) requires a oneof type, but got ${ct.show}")
                    case Some(tags) =>
                        val n = tags.size
                        if (clauses.isEmpty && elseExp.isEmpty)
                            Err("a tagcase without an else clause needs at least one clause")
                        else {
                            val coverOk = elseExp match {
                                case Some(_) => clauses.size <= n
                                case None => clauses.size == n
                            }
                            if (!coverOk)
                                Err(s"the tagcase has ${clauses.size} clause(s) and ${if (elseExp.isDefined) "an" else "no"} else clause, but the oneof type has $n tag(s)")
                            else {
                                val orderOk = clauses.zip(tags).forall { case ((ctag, _), (ttag, _)) => ctag == ttag }
                                if (!orderOk)
                                    Err("the tagcase clause tags must follow the oneof type's tag order")
                                else {
                                    clauses.zip(tags).foldLeft[Either[String, Option[CT]]](Right(None)) {
                                        (acc, pair) =>
                                            (acc, pair) match {
                                                case (Right(None), ((_, body), (_, ptype))) =>
                                                    check(body, TE + (payloadName -> ptype)) match {
                                                        case Err(m) => Left(m)
                                                        case Ok(bt) => Right(Some(bt))
                                                    }
                                                case (Right(Some(t1)), ((_, body), (_, ptype))) =>
                                                    check(body, TE + (payloadName -> ptype)) match {
                                                        case Err(m) => Left(m)
                                                        case Ok(bt) =>
                                                            if (Subtype.subtype(bt, t1)) Right(Some(t1))
                                                            else if (Subtype.subtype(t1, bt)) Right(Some(bt))
                                                            else Left(s"the tagcase clause bodies have incompatible types: ${t1.show} and ${bt.show}")
                                                    }
                                                case (Left(m), _) => Left(m)
                                            }
                                    } match {
                                        case Left(m) => Err(m)
                                        case Right(Some(t1)) =>
                                            elseExp match {
                                                case None => Ok(t1)
                                                case Some(e2) =>
                                                    // The payload name is not in
                                                    // scope in the else branch.
                                                    check(e2, TE) match {
                                                        case Err(m) => Err(m)
                                                        case Ok(bt) =>
                                                            if (Subtype.subtype(bt, t1)) Ok(t1)
                                                            else if (Subtype.subtype(t1, bt)) Ok(bt)
                                                            else Err(s"the tagcase else body has type ${bt.show}, which is incompatible with the clause bodies' type ${t1.show}")
                                                    }
                                            }
                                        case Right(None) => Err("internal error: no clause result type")
                                    }
                                }
                            }
                        }
                }
            }

        // ------------------------------------------------------------------
        // Lists (Figure 11.24)
        // ------------------------------------------------------------------

        case ConsExp(h, t2) => (check(h, TE), check(t2, TE)) match {
            case (Ok(ht), Ok(tt)) => CT.asListof(tt) match {
                case Some(elem) =>
                    if (Subtype.subtype(ht, elem)) Ok(CT(TList(elem.t), elem.env))
                    else Err(s"(cons ...) expects a head whose type is a subtype of ${elem.show}, but got ${ht.show}")
                case None => Err(s"the tail of (cons ...) must have a listof type, but has type ${tt.show}")
            }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        case CarExp(e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asListof(ct) match {
                    case Some(elem) => Ok(elem)
                    case None => Err(s"(car ...) requires a listof type, but got ${ct.show}")
                }
            }

        case CdrExp(e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asListof(ct) match {
                    case Some(elem) => Ok(CT(TList(elem.t), elem.env))
                    case None => Err(s"(cdr ...) requires a listof type, but got ${ct.show}")
                }
            }

        case NullExp(t) => CT.open(t) match {
            case None => Err("malformed type in a (null ...) expression")
            case Some(ct) => Ok(CT(TList(ct.t), ct.env))
        }

        case NullQExp(e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asListof(ct) match {
                    case Some(_) => Ok(CT.closed(bool))
                    case None => Err(s"(null? ...) requires a listof type, but got ${ct.show}")
                }
            }

        // ------------------------------------------------------------------
        // Mutable data (Figure 11.21)
        // ------------------------------------------------------------------

        case SetExp(name, e2) => TE.get(name) match {
            case None => Err(s"unbound variable: $name")
            case Some(vt) =>
                check(e2, TE) match {
                    case Err(m) => Err(m)
                    case Ok(et) =>
                        if (Subtype.subtype(et, vt)) Ok(CT.closed(TBase("unit")))
                        else Err(s"set! of $name expects a value whose type is a subtype of ${vt.show}, but got ${et.show}")
                }
        }

        case CellExp(e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => Ok(CT(TCell(ct.t), ct.env))
            }

        case DerefExp(e2) =>
            check(e2, TE) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asCell(ct) match {
                    case Some(elem) => Ok(elem)
                    case None => Err(s"(^ ...) requires a cellof type, but got ${ct.show}")
                }
            }

        case CellSetExp(c, e2) => (check(c, TE), check(e2, TE)) match {
            case (Ok(cct), Ok(et)) => CT.asCell(cct) match {
                case Some(elem) =>
                    if (Subtype.subtype(et, elem)) Ok(CT.closed(TBase("unit")))
                    else Err(s"(:= ...) expects a value whose type is a subtype of ${elem.show}, but got ${et.show}")
                case None => Err(s"(:= ...) requires a cellof type, but got ${cct.show}")
            }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        case CellEqExp(e1, e2) => (check(e1, TE), check(e2, TE)) match {
            case (Ok(c1), Ok(c2)) => (CT.asCell(c1), CT.asCell(c2)) match {
                case (Some(el1), Some(el2)) =>
                    if (CT.equiv(el1, el2)) Ok(CT.closed(bool))
                    else Err(s"cell=? requires cells with the same content type: ${el1.show} and ${el2.show}")
                case _ => Err("cell=? requires two cellof types")
            }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        // Anything else (FL kernel nodes such as Lam/App/Rec, or sugar that
        // survived desugaring) is an internal error.
        case _ => Err("internal error: non-FLEX expression node")
    }

    // (fst/snd E): E must have a pairof type.
    private def elimPair(e: Exp, TE: Map[String, CT], name: String)
                        (sel: (CT, CT) => CT): Result[CT] =
        check(e, TE) match {
            case Err(m) => Err(m)
            case Ok(ct) => CT.asPair(ct) match {
                case Some(ps) => Ok(sel(ps._1, ps._2))
                case None => Err(s"($name ...) requires a pairof type, but got ${ct.show}")
            }
        }

    // Check a list of expressions, collecting their types.
    private def checkAll(es: List[Exp], TE: Map[String, CT]): Result[List[CT]] =
        es.foldLeft[Result[List[CT]]](Ok(Nil)) {
            (acc, e2) =>
                (acc, e2) match {
                    case (Ok(acc2), _) => check(e2, TE) match {
                        case Ok(ct) => Ok(acc2 :+ ct)
                        case Err(m) => Err(m)
                    }
                    case (Err(m), _) => Err(m)
                }
        }

    // Check a list of arguments against expected types (primitive operators).
    private def checkArgs(es: List[Exp], expected: List[CT], TE: Map[String, CT]): Result[Unit] =
        if (es.size != expected.size)
            Err(s"expected ${expected.size} argument(s), got ${es.size}")
        else es.zip(expected).foldLeft[Result[Unit]](Ok(())) {
            (acc, pair) =>
                (acc, pair) match {
                    case (Ok(_), (e2, et)) =>
                        check(e2, TE) match {
                            case Err(m) => Err(m)
                            case Ok(at) =>
                                if (Subtype.subtype(at, et)) Ok(())
                                else Err(s"the argument has type ${at.show}, but the primitive expects ${et.show}")
                        }
                    case (Err(m), _) => Err(m)
                }
        }

    // Rename each CT's environment keys against the accumulated set and
    // return the (renamed) type trees and the combined environment.
    private def foldRename(cts: List[CT]): (List[T], Map[String, T]) =
        cts.foldLeft((List.empty[T], Map.empty[String, T])) {
            (acc, ct) =>
                acc match {
                    case (ts, envAcc) =>
                        val ct2 = CT.renameEnv(ct, envAcc.keys.toSet)
                        (ts :+ ct2.t, envAcc ++ ct2.env)
                }
        }
}

// ---------------------------------------------------------------------------
// Program-level checking
// ---------------------------------------------------------------------------

object SubtypeProgramChecker {

    // The standard library of a flex program (Figure 11.2 of the book): a
    // global procedure for each primitive operator, plus true / false.
    val StdLib: Map[String, CT] = {
        val bool = TBase("bool"); val int = TBase("int"); val symb = TBase("symb")
        def fn2(argT: T, retT: T): CT = CT.closed(TArrow(List(argT, argT), retT))
        Map(
            "not" -> CT.closed(TArrow(List(bool), bool)),
            "and" -> fn2(bool, bool),
            "or" -> fn2(bool, bool),
            "bool=?" -> fn2(bool, bool),
            "=" -> fn2(int, bool),
            "!=" -> fn2(int, bool),
            "<" -> fn2(int, bool),
            "<=" -> fn2(int, bool),
            ">" -> fn2(int, bool),
            ">=" -> fn2(int, bool),
            "+" -> fn2(int, int),
            "-" -> fn2(int, int),
            "*" -> fn2(int, int),
            "/" -> fn2(int, int),
            "%" -> fn2(int, int),
            "sym=?" -> fn2(symb, bool),
            "true" -> CT.closed(bool),
            "false" -> CT.closed(bool)
        )
    }

    def check(p: FlexPgm): FlexResult = p match {
        case FlexKernelProgram(formals, body) =>
            // Desugar is the identity on kernel expressions; it also removes
            // any muFLEX sugar that was (permissively) admitted in a flexk
            // program by the parser.
            checkFormalsAndBody(formals, DSL.flex.Desugar(body), Map.empty)

        case FlexSugarProgram(formals, body, typeDefs, defs) =>
            // (1) def-types: each definition must be well formed relative to
            //     the earlier def-types (a type identifier defined by one
            //     def-type can be used in subsequent def-types, book p.636).
            val typeErr = typeDefs.zipWithIndex.foldLeft[Option[String]](None) {
                (acc, item) =>
                    (acc, item) match {
                        case (None, ((_, td), i)) => T.wellFormed(td, typeDefs.take(i).map(_._1).toSet)
                        case (Some(m), _) => Some(m)
                    }
            }
            typeErr match {
                case Some(m) => FlexErr(m)
                case None =>
                    // (2) let-type* over the def-types (Figure 11.2):
                    //     sequential substitution into the remaining
                    //     def-types, the value definitions, and the body.
                    val (defs2, body2) = applyTypeDefs(typeDefs, defs, body)
                    val defs3 = defs2.map(d => (d.name, d.t, DSL.flex.Desugar(d.e)))
                    val body3 = DSL.flex.Desugar(body2)
                    // (3) (flexk formals (let StdLib (letrec defs body)))
                    checkFormalsAndBody(formals, LetRecExp(defs3, body3), StdLib)
            }
    }

    // Sequential application of the def-type substitutions (the let-type*
    // desugaring): the last def-type is the innermost let-type, so the first
    // def-type's substitution is applied last.
    def applyTypeDefs(typeDefs: List[(String, T)], defs: List[FlexDef], body: Exp): (List[FlexDef], Exp) =
        typeDefs.foldRight((defs, body)) {
            (item, state) =>
                (item, state) match {
                    case ((tau, td), (ds, b)) =>
                        (ds.map(d => FlexDef(d.name, Subst.substType(td, tau, d.t),
                                             Subst.substExp(td, tau, d.e))),
                         Subst.substExp(td, tau, b))
                }
        }

    // Check the body of a (desugared) flexk program: open the (closed)
    // formal types, then check the body. The reported program type is
    // (=> (Tformal*) Tbody) (Figure 11.1 of the book); with no formals it
    // is just the body type.
    def checkFormalsAndBody(formals: List[(String, T)], body: Exp, preTE: Map[String, CT]): FlexResult = {
        var TE: Map[String, CT] = preTE
        var errOpt: Option[String] = None
        for ((n, t) <- formals if errOpt.isEmpty) {
            CT.open(t) match {
                case None => errOpt = Some(s"malformed type in formal parameter $n")
                case Some(ct) => TE = TE + (n -> ct)
            }
        }
        errOpt match {
            case Some(m) => FlexErr(m)
            case None =>
                SubtypeChecker.check(body, TE) match {
                    case SubtypeChecker.Ok(ct) =>
                        val progStr = if (formals.isEmpty) T.show(ct.t)
                        else "(=> (" + formals.map { case (_, t) => T.show(t) }.mkString(" ") +
                             ") " + T.show(ct.t) + ")"
                        FlexOk(progStr)
                    case SubtypeChecker.Err(m) => FlexErr(m)
                }
        }
    }
}

// Parse and type-check a FLEX/S program.
def flexsCheck(input: String): FlexResult =
    FlexProgram(input) match {
        case Some(p) => SubtypeProgramChecker.check(p)
        case None => FlexErr("parse error")
    }

// Test helper:  "(flex ...)" shouldFlexSCheckTo (FlexOk("int"))
extension (input: String)
    def shouldFlexSCheckTo(expected: FlexResult): Unit = {
        val got = flexsCheck(input)
        assert(got == expected, s"expected $expected but got $got for: $input")
    }
