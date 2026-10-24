package DSL.flex_spd

import DSL.fl._
import DSL.flex._
import DSL.flex_sp._

// The reference static semantics of FLEX/SPD (Section 12.3.1 of the book):
// the FLEX/SP type checker (directional subtyping, Chapter 12.2) in which
// every type annotation is a *description* (Figure 12.18), and the type
// rules of FLEX/SP are applied with description equivalence in place of type
// equivalence (Figure 12.20).
//
// Descriptions are handled by normalization (DescEval.normalize): a
// description used as a type is reduced — following description aliases
// (the standard-library descriptions pairof / listof, the program's
// def-descs, and plet / pletrec bindings), beta-reducing description
// applications ([dabs-beta-≈]), and converting recursive descriptions
// (dletrec) to type-level recursion (tletrec) — to a type, which is then
// checked with the existing CT machinery (CT.equiv / Subtype.subtype). This
// subsumes the description-equivalence rules of Figure 12.20 at every type
// position. A description that does not denote a type (a bare dabs, a bare
// base type constructor, a non-operator application, an arity mismatch, or
// a non-terminating description) is rejected (the book's "safe nonsense",
// p.757).
//
// The checker threads three environments:
//
//   TE       : value identifier -> CT        (the value environment)
//   descEnv  : description identifier -> T   (the description environment:
//              description aliases, realized transparently — a name is
//              equivalent to its definition, book p.757)
//   tyScope  : the set of description variables currently in scope (pabs /
//              forall binders): type annotations may name them, and they
//              normalize to rigid type variables (they are never added to
//              CT.env — see the FLEX/SP checker, and put a variable into its
//              own environment would make the CT walk treat it as a
//              self-recursive pointer).
//
// The pair and list expression forms (pair, fst, snd, cons, car, cdr, null,
// null?) are not part of the FLEX/SPD kernel (book p.755): they are
// polymorphic standard-library values bound in the program-level value
// environment (Figure 12.19), to be projected with pcall.
//
// Because FLEX/SPD is FLEX/SP with a richer type domain, every FLEX/SP
// program type-checks under FLEX/SPD, with the sole spelling change that the
// type keywords trec / tletrec are written as the description forms drec /
// dletrec (and def-type as def-desc, which is accepted as an alias).

object SPDChecker {

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

    // Open a description annotation: normalize the description to a type in
    // the description environment (relative to the enclosing
    // description-variable scope), then check the resulting type. (The
    // monomorphic CT.open is the special case of a closed type in an empty
    // description environment.)
    def openDesc(d: T, descEnv: Map[String, T], scope: Set[String]): Option[CT] =
        DescEval.normalize(d, descEnv, scope) match {
            case None => None
            case Some(t) => T.wellFormed(t, scope) match {
                case None => Some(CT(t, Map.empty))
                case Some(_) => None
            }
        }

    def check(e: Exp, TE: Map[String, CT], descEnv: Map[String, T], tyScope: Set[String]): Result[CT] = e match {

        // ------------------------------------------------------------------
        // Literals and variables (Figures 11.7: [unit] [int] [bool] [symb]
        // [error] [var])
        // ------------------------------------------------------------------

        case UnitLit() => Ok(CT.closed(TBase("unit")))
        case BoolLit(_) => Ok(CT.closed(bool))
        case IntLit(_) => Ok(CT.closed(int))
        case Sym(_) => Ok(CT.closed(TBase("symb")))

        case FlexError(msg, t) => openDesc(t, descEnv, tyScope) match {
            case Some(ct) => Ok(ct)
            case None => Err(s"malformed description in an (error ...) expression: ${T.show(t)}")
        }

        case Var(name) => TE.get(name) match {
            case Some(ct) => Ok(ct)
            case None => Err(s"unbound variable: $name")
        }

        // ------------------------------------------------------------------
        // Conditionals and primitives ([if], [prim])
        // ------------------------------------------------------------------

        case If(test, th, el) =>
            check(test, TE, descEnv, tyScope) match {
                case Ok(ct) if CT.equiv(ct, CT.closed(bool)) =>
                    (check(th, TE, descEnv, tyScope), check(el, TE, descEnv, tyScope)) match {
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
                checkArgs(args, argTs.map(CT.closed), TE, descEnv, tyScope) match {
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
                                case (n, d) =>
                                    openDesc(d, descEnv, tyScope) match {
                                        case None => (teCur, envCur, Some(s"malformed description in formal parameter $n: ${T.show(d)}"))
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
                    check(body, teP, descEnv, tyScope) match {
                        case Err(m) => Err(m)
                        case Ok(cb) =>
                            val cb2 = CT.renameEnv(cb, envAcc.keys.toSet)
                            Ok(CT(TArrow(params.map { case (n, _) => teP(n).t }, cb2.t),
                                  envAcc ++ cb2.env))
                    }
            }

        case AppExp(rator, args) =>
            check(rator, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(rt) => CT.asArrow(rt) match {
                    case None => Err(s"the rator has type ${rt.show}, which is not a procedure type")
                    case Some((argTs, ret)) =>
                        args.zip(argTs).foldLeft[Result[Unit]](Ok(())) {
                            (acc, pair) =>
                                (acc, pair) match {
                                    case (Ok(_), (a, at)) =>
                                        check(a, TE, descEnv, tyScope) match {
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
                            check(e2, teCur, descEnv, tyScope) match {
                                case Ok(ct) => Right(teCur + (n -> ct))
                                case Err(m) => Left(m)
                            }
                        case (Left(m), _) => Left(m)
                    }
            } match {
                case Right(teCur) => check(body, teCur, descEnv, tyScope)
                case Left(m) => Err(m)
            }

        case LetRecExp(bindings, body) =>
            // Open the declared descriptions (closed relative to the
            // type-variable scope) and build the extended environment all at
            // once (the bindings are mutually recursive).
            val declared = bindings.foldLeft[Either[String, Map[String, CT]]](Right(TE)) {
                (acc, binding) =>
                    (acc, binding) match {
                        case (Right(teCur), (n, d, _)) =>
                            openDesc(d, descEnv, tyScope) match {
                                case None => Left(s"malformed description in letrec binding $n: ${T.show(d)}")
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
                                    check(e2, tec, descEnv, tyScope) match {
                                        case Err(m) => Left(m)
                                        case Ok(et) =>
                                            if (Subtype.subtype(et, tec(n))) Right(())
                                            else Left(s"the letrec binding $n has type ${et.show}, but is declared to have type ${tec(n).show}")
                                    }
                                case (Left(m), _) => Left(m)
                            }
                    } match {
                        case Left(m) => Err(m)
                        case Right(_) => check(body, tec, descEnv, tyScope)
                    }
            }

        // ------------------------------------------------------------------
        // Type ascription ([the])
        // ------------------------------------------------------------------

        case TheExp(d, e2) => openDesc(d, descEnv, tyScope) match {
            case None => Err(s"malformed description in a (the ...) expression: ${T.show(d)}")
            case Some(ct) =>
                check(e2, TE, descEnv, tyScope) match {
                    case Err(m) => Err(m)
                    case Ok(et) =>
                        if (Subtype.subtype(et, ct)) Ok(ct)
                        else Err(s"the type ascription says ${ct.show}, but the expression has type ${et.show}, which is not a subtype of it")
                }
        }

        // ------------------------------------------------------------------
        // Tuples (Figure 11.16)
        // ------------------------------------------------------------------

        case ProdExp(comps) =>
            checkAll(comps, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(cts) =>
                    val (ts, env) = foldRename(cts)
                    Ok(CT(TProd(ts), env))
            }

        case GetExp(index, e2) =>
            check(e2, TE, descEnv, tyScope) match {
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
            else checkAll(comps, TE, descEnv, tyScope) match {
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

        case SeqGetExp(index, seq) => (check(index, TE, descEnv, tyScope), check(seq, TE, descEnv, tyScope)) match {
            case (Ok(ict), Ok(sct)) =>
                if (!CT.equiv(ict, CT.closed(int)))
                    Err(s"the sequence index must have type int, but has type ${ict.show}")
                else CT.asSeq(sct) match {
                    case Some(elem) => Ok(elem)
                    case None => Err(s"(seq-get ...) requires a seqof type, but has type ${sct.show}")
                }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        case SeqSizeExp(e2) =>
            check(e2, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asSeq(ct) match {
                    case Some(_) => Ok(CT.closed(int))
                    case None => Err(s"(seq-size ...) requires a seqof type, but has type ${ct.show}")
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
                            else check(e2, TE, descEnv, tyScope) match {
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
            check(e2, TE, descEnv, tyScope) match {
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
            check(rcd, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asRecord(ct) match {
                    case None => Err(s"(with ...) requires a recordof type, but got ${ct.show}")
                    case Some(fields) =>
                        val TE2 = TE ++ fields.map { case (n, fct) => n -> fct }.toMap
                        check(body, TE2, descEnv, tyScope)
                }
            }

        // ------------------------------------------------------------------
        // Oneofs (Figure 11.22)
        // ------------------------------------------------------------------

        case OneExp(oneofD, tag, payload) => openDesc(oneofD, descEnv, tyScope) match {
            case None => Err(s"malformed description in a (one ...) expression: ${T.show(oneofD)}")
            case Some(ct) => CT.asOneof(ct) match {
                case None => Err(s"the type ${ct.show} in a (one ...) expression is not a oneof type")
                case Some(tags) => tags.find(_._1 == tag) match {
                    case None => Err(s"the tag $tag is not in the oneof type ${ct.show}")
                    case Some((_, ptype)) =>
                        check(payload, TE, descEnv, tyScope) match {
                            case Err(m) => Err(m)
                            case Ok(pt) =>
                                if (Subtype.subtype(pt, ptype)) Ok(ct)
                                else Err(s"the payload has type ${pt.show}, but the tag $tag expects ${ptype.show}")
                        }
                }
            }
        }

        case TagCaseExp(disc, payloadName, clauses, elseExp) =>
            check(disc, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asOneof(ct) match {
                    case None => Err(s"(tagcase ...) requires a oneof type, but got ${ct.show}")
                    case Some(tags) =>
                        val n = tags.size
                        // [oneof-elim1/2] (Figure 11.22), with the tag order of
                        // the oneof type made irrelevant by [oneof-approx]: a
                        // clause's payload type is looked up by its tag, and
                        // the clauses may appear in any order. Without an
                        // else clause, the clauses must cover every tag; with
                        // an else clause, they may cover any subset.
                        if (clauses.map(_._1).distinct.size != clauses.size)
                            Err("a tagcase clause tag occurs more than once")
                        else {
                            val payloadOf = tags.toMap
                            val unknown = clauses.collect { case (t, _) if !payloadOf.contains(t) => t }
                            if (unknown.nonEmpty)
                                Err(s"the tagcase clause tag(s) " + unknown.mkString(", ") + s" are not in the oneof type ${ct.show}")
                            else {
                                val coverOk = elseExp match {
                                    case Some(_) => true
                                    case None => clauses.size == n
                                }
                                if (!coverOk)
                                    Err(s"the tagcase has ${clauses.size} clause(s) and no else clause, but the oneof type has $n tag(s)")
                                else {
                                    clauses.foldLeft[Either[String, Option[CT]]](Right(None)) {
                                        (acc, clause) =>
                                            (acc, clause) match {
                                                case (Right(None), (tag, body)) =>
                                                    check(body, TE + (payloadName -> payloadOf(tag)), descEnv, tyScope) match {
                                                        case Err(m) => Left(m)
                                                        case Ok(bt) => Right(Some(bt))
                                                    }
                                                case (Right(Some(t1)), (tag, body)) =>
                                                    check(body, TE + (payloadName -> payloadOf(tag)), descEnv, tyScope) match {
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
                                                    check(e2, TE, descEnv, tyScope) match {
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
        // Mutable data (Figure 11.21)
        // ------------------------------------------------------------------

        case SetExp(name, e2) => TE.get(name) match {
            case None => Err(s"unbound variable: $name")
            case Some(vt) =>
                check(e2, TE, descEnv, tyScope) match {
                    case Err(m) => Err(m)
                    case Ok(et) =>
                        if (Subtype.subtype(et, vt)) Ok(CT.closed(TBase("unit")))
                        else Err(s"set! of $name expects a value whose type is a subtype of ${vt.show}, but got ${et.show}")
                }
        }

        case CellExp(e2) =>
            check(e2, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(ct) => Ok(CT(TCell(ct.t), ct.env))
            }

        case DerefExp(e2) =>
            check(e2, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asCell(ct) match {
                    case Some(elem) => Ok(elem)
                    case None => Err(s"(^ ...) requires a cellof type, but has type ${ct.show}")
                }
            }

        case CellSetExp(c, e2) => (check(c, TE, descEnv, tyScope), check(e2, TE, descEnv, tyScope)) match {
            case (Ok(cct), Ok(et)) => CT.asCell(cct) match {
                case Some(elem) =>
                    if (Subtype.subtype(et, elem)) Ok(CT.closed(TBase("unit")))
                    else Err(s"(:= ...) expects a value whose type is a subtype of ${elem.show}, but got ${et.show}")
                case None => Err(s"(:= ...) requires a cellof type, but has type ${cct.show}")
            }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        case CellEqExp(e1, e2) => (check(e1, TE, descEnv, tyScope), check(e2, TE, descEnv, tyScope)) match {
            case (Ok(c1), Ok(c2)) => (CT.asCell(c1), CT.asCell(c2)) match {
                case (Some(el1), Some(el2)) =>
                    if (CT.equiv(el1, el2)) Ok(CT.closed(bool))
                    else Err(s"cell=? requires cells with the same content type: ${el1.show} and ${el2.show}")
                case _ => Err("cell=? requires two cellof types")
            }
            case (Err(m), _) => Err(m)
            case (_, Err(m)) => Err(m)
        }

        // ------------------------------------------------------------------
        // Universal polymorphism (Figure 12.9)
        // ------------------------------------------------------------------

        case PabsExp(vars, body) =>
            if (vars.toSet.size != vars.size)
                Err(s"duplicate type variable in pabs: " + vars.diff(vars.distinct).mkString(", "))
            else {
                // [import restriction] (Figure 12.9): a pabs-bound type
                // identifier must not occur among the free type identifiers
                // of the types of the free value identifiers of the body —
                // otherwise the pabs would capture a type identifier that a
                // free value's type imports (the book's polytest example,
                // p.732).
                val freeVals = freeValueIds(body)
                vars.find { v =>
                    freeVals.exists { i =>
                        TE.get(i).exists(ct => freeTypeIds(ct.t).contains(v))
                    }
                } match {
                    case Some(v) =>
                        Err(s"import restriction violated: the pabs type variable $v occurs in the type of a free value of the pabs body (variable capture)")
                    case None =>
                        // [purity restriction] (Figure 12.9): the body must
                        // not perform mutation (set! or :=).
                        if (containsMutation(body))
                            Err("purity restriction violated: a pabs body may not contain set! or :=")
                        else check(body, TE, descEnv, tyScope ++ vars.toSet) match {
                            case Ok(ct) => Ok(CT(TForall(vars, ct.t), ct.env))
                            case Err(m) => Err(m)
                        }
                }
            }

        case PcallExp(e, ds) =>
            check(e, TE, descEnv, tyScope) match {
                case Err(m) => Err(m)
                case Ok(ct) => CT.asForall(ct) match {
                    case None =>
                        Err(s"the rator of (pcall ...) has type ${ct.show}, which is not a polymorphic (forall) type")
                    case Some((vs, bct)) =>
                        if (vs.size != ds.size)
                            Err(s"(pcall ...) supplies ${ds.size} type argument(s), but the polymorphic value is parameterized over ${vs.size} type variable(s)")
                        else {
                            // [forall-elim] (Figure 12.9): instantiate the
                            // formal type parameters with the actual types,
                            // which are opened relative to the enclosing
                            // pabs scope (they may name enclosing type
                            // variables).
                            val opened = ds.foldLeft[Either[String, List[CT]]](Right(Nil)) {
                                (acc, d) =>
                                    (acc, d) match {
                                        case (Right(acc2), _) => openDesc(d, descEnv, tyScope) match {
                                            case None => Left(s"malformed description argument in (pcall ...): " + T.show(d))
                                            case Some(cti) => Right(acc2 :+ cti)
                                        }
                                        case (Left(m), _) => Left(m)
                                    }
                            }
                            opened match {
                                case Left(m) => Err(m)
                                case Right(ctis) =>
                                    // Substitute the instantiation types for
                                    // the formal parameters, alpha-renaming
                                    // each instantiation's environment keys
                                    // against the running environment (and
                                    // the enclosing scope) so that no free
                                    // identifier is captured.
                                    val substituted = vs.zip(ctis).foldLeft[Either[String, CT]](Right(CT(bct.t, bct.env))) {
                                        (acc, pair) =>
                                            (acc, pair) match {
                                                case (Right(cur), (v, cti)) =>
                                                    val ct2 = CT.renameEnv(cti, (cur.env.keys ++ tyScope ++ vs).toSet)
                                                    Right(CT(Subst.substType(ct2.t, v, cur.t), cur.env ++ ct2.env))
                                                case (Left(m), _) => Left(m)
                                            }
                                    }
                                    substituted match {
                                        case Right(result) => Ok(result)
                                        case Left(m) => Err(m)
                                    }
                            }
                        }
                }
            }

        // ------------------------------------------------------------------
        // Description bindings in expressions (Figure 12.18): plet /
        // pletrec bind descriptions in the body's type positions and return
        // a value. The bindings are transparent (a name is equivalent to its
        // definition, book p.757), realized by extending the description
        // environment. In pletrec the scope of each definition includes all
        // the other definitions as well as the body (book p.755).
        // ------------------------------------------------------------------

        case PletExp(binds, body) =>
            // A plet-bound name is in scope only in the plet body (book
            // p.755): each binding's definition is well formed relative to
            // the outer description environment, not the siblings.
            val wfErr = binds.foldLeft[Option[String]](None) {
                (acc, binding) =>
                    (acc, binding) match {
                        case (Some(m), _) => Some(m)
                        case (None, (n, d)) =>
                            T.wellFormed(d, tyScope ++ descEnv.keySet) match {
                                case Some(m) => Some(s"malformed description in plet binding $n: $m")
                                case None => None
                            }
                    }
            }
            wfErr match {
                case Some(m) => Err(m)
                case None =>
                    check(body, TE, descEnv ++ binds.map { case (n, d) => n -> d }.toMap, tyScope)
            }

        case PletRecExp(binds, body) =>
            val wfErr = binds.foldLeft[Option[String]](None) {
                (acc, binding) =>
                    (acc, binding) match {
                        case (Some(m), _) => Some(m)
                        case (None, (n, d)) =>
                            T.wellFormed(d, tyScope ++ binds.map(_._1).toSet ++ descEnv.keySet) match {
                                case Some(m) => Some(s"malformed description in pletrec binding $n: $m")
                                case None => None
                            }
                    }
            }
            wfErr match {
                case Some(m) => Err(m)
                case None =>
                    check(body, TE, descEnv ++ binds.map { case (n, d) => n -> d }.toMap, tyScope)
            }

        // Anything else (FL kernel nodes such as Lam/App/Rec, or the list /
        // pair kernel forms, which are not part of the FLEX/SPD kernel) is an
        // internal error.
        case _ => Err("internal error: non-FLEX/SPD expression node")
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    // Check a list of expressions, collecting their types.
    private def checkAll(es: List[Exp], TE: Map[String, CT], descEnv: Map[String, T], tyScope: Set[String]): Result[List[CT]] =
        es.foldLeft[Result[List[CT]]](Ok(Nil)) {
            (acc, e2) =>
                (acc, e2) match {
                    case (Ok(acc2), _) => check(e2, TE, descEnv, tyScope) match {
                        case Ok(ct) => Ok(acc2 :+ ct)
                        case Err(m) => Err(m)
                    }
                    case (Err(m), _) => Err(m)
                }
        }

    // Check a list of arguments against expected types (primitive operators).
    private def checkArgs(es: List[Exp], expected: List[CT], TE: Map[String, CT], descEnv: Map[String, T], tyScope: Set[String]): Result[Unit] =
        if (es.size != expected.size)
            Err(s"expected ${expected.size} argument(s), got ${es.size}")
        else es.zip(expected).foldLeft[Result[Unit]](Ok(())) {
            (acc, pair) =>
                (acc, pair) match {
                    case (Ok(_), (e2, et)) =>
                        check(e2, TE, descEnv, tyScope) match {
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

    // The free type identifiers of a type (its bound identifiers — trec /
    // tletrec / forall binders — are not free). Used by the import
    // restriction (FrTyIds of Figure 12.9). The description forms are
    // defensive: a checked CT never contains them (descriptions are
    // normalized to types before a CT is built).
    private def freeTypeIds(t: T): Set[String] = t match {
        case TBase(_) => Set.empty
        case TVar(n) => Set(n)
        case TArrow(args, ret) => args.flatMap(freeTypeIds).toSet ++ freeTypeIds(ret)
        case TPair(f, s) => freeTypeIds(f) ++ freeTypeIds(s)
        case TProd(cs) => cs.flatMap(freeTypeIds).toSet
        case TSeq(e) => freeTypeIds(e)
        case TList(e) => freeTypeIds(e)
        case TCell(e) => freeTypeIds(e)
        case TRecord(fs) => fs.flatMap { case (_, d) => freeTypeIds(d) }.toSet
        case TOneof(ts) => ts.flatMap { case (_, d) => freeTypeIds(d) }.toSet
        case TTrec(name, body) => freeTypeIds(body) - name
        case TTletrec(binds, body) =>
            (binds.flatMap { case (_, d) => freeTypeIds(d) }.toSet ++ freeTypeIds(body)) -- binds.map(_._1)
        case TForall(vars, body) => freeTypeIds(body) -- vars
        // FLEX/SPD description forms (Section 12.3.1).
        case TBaseCtor(_) => Set.empty
        case TDabs(vars, body) => freeTypeIds(body) -- vars
        case TDApp(rator, args) => freeTypeIds(rator) ++ args.flatMap(freeTypeIds).toSet
        case TDletrec(binds, body) =>
            (binds.flatMap { case (_, d) => freeTypeIds(d) }.toSet ++ freeTypeIds(body)) -- binds.map(_._1)
    }

    // Does the expression contain a mutation (set! or :=)? (The purity
    // restriction of the [forall-intro] rule.)
    private def containsMutation(e: Exp): Boolean = e match {
        case SetExp(_, _) | CellSetExp(_, _) => true
        case UnitLit() | BoolLit(_) | IntLit(_) | Sym(_) | Var(_) | FlexError(_, _) | NullExp(_) => false
        case If(t1, t2, t3) => containsMutation(t1) || containsMutation(t2) || containsMutation(t3)
        case PrimOp(_, args) => args.exists(containsMutation)
        case AbsExp(_, body) => containsMutation(body)
        case AppExp(r, args) => containsMutation(r) || args.exists(containsMutation)
        case Let(bs, body) => bs.map(_._2).exists(containsMutation) || containsMutation(body)
        case LetRecExp(bs, body) => bs.map(_._3).exists(containsMutation) || containsMutation(body)
        case TheExp(_, e2) => containsMutation(e2)
        case Pair(f, s) => containsMutation(f) || containsMutation(s)
        case FstExp(e2) => containsMutation(e2)
        case SndExp(e2) => containsMutation(e2)
        case ProdExp(cs) => cs.exists(containsMutation)
        case GetExp(_, e2) => containsMutation(e2)
        case SeqExp(cs) => cs.exists(containsMutation)
        case SeqGetExp(i, s) => containsMutation(i) || containsMutation(s)
        case SeqSizeExp(e2) => containsMutation(e2)
        case RecordExp(fs) => fs.map(_._2).exists(containsMutation)
        case SelectExp(_, e2) => containsMutation(e2)
        case WithExp(rcd, body) => containsMutation(rcd) || containsMutation(body)
        case OneExp(_, _, p) => containsMutation(p)
        case TagCaseExp(d, _, cs, el) =>
            containsMutation(d) || cs.map(_._2).exists(containsMutation) || el.exists(containsMutation)
        case ConsExp(h, t2) => containsMutation(h) || containsMutation(t2)
        case CarExp(e2) => containsMutation(e2)
        case CdrExp(e2) => containsMutation(e2)
        case NullQExp(e2) => containsMutation(e2)
        case CellExp(e2) => containsMutation(e2)
        case DerefExp(e2) => containsMutation(e2)
        case CellEqExp(e1, e2) => containsMutation(e1) || containsMutation(e2)
        case PabsExp(_, body) => containsMutation(body)
        case PcallExp(e2, _) => containsMutation(e2)
        case PletExp(_, body) => containsMutation(body)
        case PletRecExp(_, body) => containsMutation(body)
        // Sugar (desugared before checking; defensive traversal anyway).
        case SugaredPrimOp(_, args) => args.exists(containsMutation)
        case Cond(bs, d) => bs.exists { case (t1, th) => containsMutation(t1) || containsMutation(th) } || d.exists(containsMutation)
        case Scand(es) => es.exists(containsMutation)
        case Scor(es) => es.exists(containsMutation)
        case BeginExp(e1, e2) => containsMutation(e1) || containsMutation(e2)
        case ListExp(_, es) => es.exists(containsMutation)
        case LetTypeExp(_, body) => containsMutation(body)
        case LetTypeStarExp(_, body) => containsMutation(body)
        case _ => false
    }

    // The free value identifiers of an expression (FrIds of Figure 12.9):
    // the value names used but not bound by an abs / let / letrec / tagcase
    // payload (pabs binds type identifiers, not values; plet / pletrec bind
    // description identifiers, not values).
    private def freeValueIds(e: Exp): Set[String] = {
        def go(x: Exp, bound: Set[String]): Set[String] = x match {
            case Var(n) => if (bound.contains(n)) Set.empty else Set(n)
            case UnitLit() | BoolLit(_) | IntLit(_) | Sym(_) | FlexError(_, _) | NullExp(_) => Set.empty
            case If(t1, t2, t3) => go(t1, bound) ++ go(t2, bound) ++ go(t3, bound)
            case PrimOp(_, args) => args.flatMap(a => go(a, bound)).toSet
            case AbsExp(ps, body) => go(body, bound ++ ps.map(_._1).toSet)
            case AppExp(r, args) => go(r, bound) ++ args.flatMap(a => go(a, bound)).toSet
            case Let(bs, body) => go(body, bound ++ bs.map(_._1).toSet)
            case LetRecExp(bs, body) => go(body, bound ++ bs.map(_._1).toSet)
            case TheExp(_, e2) => go(e2, bound)
            case Pair(f, s) => go(f, bound) ++ go(s, bound)
            case FstExp(e2) => go(e2, bound)
            case SndExp(e2) => go(e2, bound)
            case SeqSizeExp(e2) => go(e2, bound)
            case CarExp(e2) => go(e2, bound)
            case CdrExp(e2) => go(e2, bound)
            case NullQExp(e2) => go(e2, bound)
            case DerefExp(e2) => go(e2, bound)
            case CellExp(e2) => go(e2, bound)
            case GetExp(_, e2) => go(e2, bound)
            case SelectExp(_, e2) => go(e2, bound)
            case SetExp(_, e2) => go(e2, bound)
            case ProdExp(cs) => cs.flatMap(a => go(a, bound)).toSet
            case SeqExp(cs) => cs.flatMap(a => go(a, bound)).toSet
            case SeqGetExp(i, s) => go(i, bound) ++ go(s, bound)
            case RecordExp(fs) => fs.flatMap { case (_, e2) => go(e2, bound) }.toSet
            case WithExp(rcd, body) =>
                // The record's fields are bound in the body; their names are
                // only known from the record type, so they are not added to
                // `bound` (the import-restriction check is then conservative
                // in the rare case a field name shadows a free value).
                go(rcd, bound) ++ go(body, bound)
            case OneExp(_, _, p) => go(p, bound)
            case TagCaseExp(d, pn, cs, el) =>
                go(d, bound) ++ cs.flatMap { case (_, b) => go(b, bound + pn) }.toSet ++
                    el.map(e2 => go(e2, bound)).getOrElse(Set.empty)
            case ConsExp(h, t2) => go(h, bound) ++ go(t2, bound)
            case CellSetExp(c, e2) => go(c, bound) ++ go(e2, bound)
            case CellEqExp(e1, e2) => go(e1, bound) ++ go(e2, bound)
            case PabsExp(_, body) => go(body, bound)
            case PcallExp(e2, _) => go(e2, bound)
            case PletExp(_, body) => go(body, bound)
            case PletRecExp(_, body) => go(body, bound)
            // Sugar (desugared before checking; defensive traversal anyway).
            case SugaredPrimOp(_, args) => args.flatMap(a => go(a, bound)).toSet
            case Cond(bs, d) =>
                bs.flatMap { case (t1, th) => go(t1, bound) ++ go(th, bound) }.toSet ++
                    d.map(e2 => go(e2, bound)).getOrElse(Set.empty)
            case Scand(es) => es.flatMap(a => go(a, bound)).toSet
            case Scor(es) => es.flatMap(a => go(a, bound)).toSet
            case BeginExp(e1, e2) => go(e1, bound) ++ go(e2, bound)
            case ListExp(_, es) => es.flatMap(a => go(a, bound)).toSet
            case LetTypeExp(_, body) => go(body, bound)
            case LetTypeStarExp(_, body) => go(body, bound)
            case _ => Set.empty
        }
        go(e, Set.empty)
    }
}

// ---------------------------------------------------------------------------
// Program-level checking (Figure 12.19 of the book)
// ---------------------------------------------------------------------------

object FlexSPDProgramChecker {

    // The standard-library descriptions of a flex/SPD program (Figure 12.19):
    // pairof and listof as description operators. listof t is the recursive
    // sum of products (null unit | cons (t, listof t)).
    val StdDescs: Map[String, T] = Map(
        "pairof" -> TDabs(List("s", "t"), TProd(List(TVar("s"), TVar("t")))),
        "listof" -> TDabs(List("t"),
            TDletrec(List("listof-t" -> TOneof(List(
                ("null", TBase("unit")),
                ("cons", TProd(List(TVar("t"), TVar("listof-t"))))))),
                TVar("listof-t")))
    )

    // The standard-library values (Figure 12.19): the monomorphic primop
    // procedures and true / false (as in FLEX/SP), plus the polymorphic list
    // and pair procedures, which replace the kernel list and pair expression
    // forms (book p.755).
    val StdLib: Map[String, CT] = {
        val bool = TBase("bool"); val int = TBase("int"); val symb = TBase("symb")
        val unit = TBase("unit")
        def fn2(argT: T, retT: T): CT = CT.closed(TArrow(List(argT, argT), retT))
        // The (closed) type of (listof t) with t rigid: the standard-library
        // list type, as Figure 12.19 defines it.
        def listOf(t: T): T =
            TTletrec(List("listof-t" -> TOneof(List(
                ("null", unit),
                ("cons", TProd(List(t, TVar("listof-t"))))))), TVar("listof-t"))
        def pairof2(s: T, t: T): T = TProd(List(s, t))
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
            "false" -> CT.closed(bool),
            "null" -> CT.closed(TForall(List("t"), TArrow(Nil, listOf(TVar("t"))))),
            "cons" -> CT.closed(TForall(List("t"), TArrow(List(TVar("t"), listOf(TVar("t"))), listOf(TVar("t"))))),
            "null?" -> CT.closed(TForall(List("t"), TArrow(List(listOf(TVar("t"))), bool))),
            "car" -> CT.closed(TForall(List("t"), TArrow(List(listOf(TVar("t"))), TVar("t")))),
            "cdr" -> CT.closed(TForall(List("t"), TArrow(List(listOf(TVar("t"))), listOf(TVar("t"))))),
            "pair" -> CT.closed(TForall(List("s", "t"), TArrow(List(TVar("s"), TVar("t")), pairof2(TVar("s"), TVar("t"))))),
            "fst" -> CT.closed(TForall(List("s", "t"), TArrow(List(pairof2(TVar("s"), TVar("t"))), TVar("s")))),
            "snd" -> CT.closed(TForall(List("s", "t"), TArrow(List(pairof2(TVar("s"), TVar("t"))), TVar("t"))))
        )
    }

    def check(p: FlexSPDPgm): FlexResult = p match {
        case FlexSPDKernel(formals, body) =>
            // Desugar is the identity on kernel expressions; it also removes
            // any sugar that was (permissively) admitted in a flexk/SPD
            // program by the parser.
            checkFormalsAndBody(formals, DSL.flex_spd.Desugar(body))

        case FlexSPDSugar(formals, body, descDefs, defs) =>
            // (1) The def-desc descriptions must be well formed relative to
            //     the other def-desc names (the mutual-recursion scope of
            //     the pletrec of Figure 12.19) and the description
            //     environment.
            val descErr = descDefs.foldLeft[Option[String]](None) {
                (acc, binding) =>
                    (acc, binding) match {
                        case (Some(m), _) => Some(m)
                        case (None, (n, d)) =>
                            T.wellFormed(d, descDefs.map(_._1).toSet ++ StdDescs.keySet) match {
                                case Some(m) => Some(s"malformed description in def-desc $n: $m")
                                case None => None
                            }
                    }
            }
            descErr match {
                case Some(m) => FlexErr(m)
                case None =>
                    // (2) The Figure 12.19 desugaring: pletrec of the
                    //     def-desc descriptions, letrec of the value
                    //     definitions, over the standard library (the
                    //     standard-library descriptions are threaded as the
                    //     initial description environment).
                    val defs2 = defs.map(d => (d.name, d.t, DSL.flex_spd.Desugar(d.e)))
                    val body2 = DSL.flex_spd.Desugar(body)
                    val wrapped = PletRecExp(descDefs, LetRecExp(defs2, body2))
                    checkFormalsAndBody(formals, wrapped)
            }
    }

    // Check the body of a (desugared) flexk/SPD program: open the (closed)
    // formal descriptions, then check the body. The reported program type is
    // (=> (Dformal*) Dbody) (Figure 12.18); with no formals it is just the
    // body type.
    def checkFormalsAndBody(formals: List[(String, T)], body: Exp): FlexResult = {
        var TE: Map[String, CT] = StdLib
        var descEnv: Map[String, T] = StdDescs
        var errOpt: Option[String] = None
        for ((n, d) <- formals if errOpt.isEmpty) {
            SPDChecker.openDesc(d, descEnv, Set.empty) match {
                case None => errOpt = Some(s"malformed description in formal parameter $n: ${T.show(d)}")
                case Some(ct) => TE = TE + (n -> ct)
            }
        }
        errOpt match {
            case Some(m) => FlexErr(m)
            case None =>
                SPDChecker.check(body, TE, descEnv, Set.empty) match {
                    case SPDChecker.Ok(ct) =>
                        val progStr = if (formals.isEmpty) T.show(ct.t)
                        else "(=> (" + formals.map { case (_, d) => T.show(d) }.mkString(" ") +
                             ") " + T.show(ct.t) + ")"
                        FlexOk(progStr)
                    case SPDChecker.Err(m) => FlexErr(m)
                }
        }
    }
}

// Parse and type-check a FLEX/SPD program.
def flexspdCheck(input: String): FlexResult =
    FlexSPDProgram(input) match {
        case Some(p) => FlexSPDProgramChecker.check(p)
        case None => FlexErr("parse error")
    }

// Test helper:  "(flex/SPD ...)" shouldFlexSPDCheckTo (FlexOk("int"))
extension (input: String)
    def shouldFlexSPDCheckTo(expected: FlexResult): Unit = {
        val got = flexspdCheck(input)
        assert(got == expected, s"expected $expected but got $got for: $input")
    }
