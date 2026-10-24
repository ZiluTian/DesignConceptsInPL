package DSL.flex

import DSL.fl._
import scala.util.parsing.combinator._

// Parses FLEX concrete syntax (s-expressions) into the typed FLEX AST.
//
// The parser first reads a raw s-expression tree (the Raw domain of
// DSL.fl.lexer), then `interpretProgram` / `interpret` build the typed AST by
// dispatching on the leading keyword of each parenthesized list, exactly as in
// the FL and HOOPLA parsers. Types appear at specific positions (formal
// parameter lists, letrec bindings, the / one / null / list / error /
// let-type / def / def-type) and are parsed by T.parse; a malformed type is a
// parse error (the whole program is rejected).
//
// Programs (Figure 11.31 / Figure 11.2 of the book):
//
//   (flexk ((I T)*) Ebody)
//   (flex  ((I T)*) Ebody (def-type tau T)* (def I T E)*)
//
// where all def-type items must precede all def items. The procedure-defining
// sugar (def (Iproc Treturn (I1 T1) ... (In Tn)) Ebody) is converted to
// (def I (-> (T1 ... Tn) Treturn) (abs ((I1 T1) ... (In Tn)) Ebody)) at parse
// time.
//
// Identifiers (value names, Figure 11.31) may not be keywords or sugar
// keywords; type identifiers (Figure 11.31) may not be type keywords (base
// types or type constructors).
object FlexProgram extends FlLexer {

    // All FLEX keywords (kernel + sugar + program), per Figure 11.31.
    private val keywords = Set(
        // program keywords
        "flexk", "flex",
        // kernel expression keywords
        "error", "if", "prim", "abs", "let", "letrec", "the", "sym",
        "pair", "fst", "snd", "prod", "get",
        "seq", "seq-get", "seq-size",
        "record", "select", "with",
        "one", "tagcase",
        "cons", "car", "cdr", "null", "null?",
        "set!", "cell", "^", ":=", "cell=?",
        // sugar keywords
        "cond", "def", "def-type", "else", "let-type", "let-type*",
        "scand", "scor", "list", "begin")

    def apply(input: String): Option[FlexPgm] = {
        parse(sExp, input) match {
            case Success(raw, _) => interpretProgram(raw)
            case _ => None
        }
    }

    def interpretProgram(raw: Raw): Option[FlexPgm] = raw match {
        case RawList(List(RawAtom("flexk"), formalsRaw, bodyRaw)) =>
            for {
                fs <- typedFormals(formalsRaw)
                body <- interpret(bodyRaw)
            } yield FlexKernelProgram(fs, body)
        case RawList(List(RawAtom("flex"), formalsRaw, bodyRaw, items @ _*)) =>
            for {
                fs <- typedFormals(formalsRaw)
                (typeDefs, defs) <- splitTypeDefsAndDefs(items.toList)
                body <- interpret(bodyRaw)
            } yield FlexSugarProgram(fs, body, typeDefs, defs)
        case _ => None
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    def interpret(raw: Raw): Option[Exp] = raw match {
        case RawAtom(a) => interpretAtom(a)
        case RawList(items) => interpretList(items)
    }

    // A value position: a literal or a value identifier (which may not be a
    // keyword, Figure 11.31).
    def interpretAtom(a: String): Option[Exp] = {
        if (keywords.contains(a)) None
        else Some(a match {
            case "#u" => UnitLit()
            case "#t" => BoolLit(true)
            case "#f" => BoolLit(false)
            case n if isInt(n) => IntLit(n.toInt)
            case other => Var(other)
        })
    }

    private def isInt(s: String): Boolean = {
        val digits = if (s.nonEmpty && s.head == '-') s.tail else s
        digits.nonEmpty && digits.forall(_.isDigit)
    }

    def interpretList(items: List[Raw]): Option[Exp] = items match {
        case Nil => None
        case RawAtom(k) :: rest if keywords.contains(k) => interpretKeyword(k, rest)
        case RawAtom(a) :: rest if a.startsWith("@") =>
            allOf(rest.map(interpret)) map (args => SugaredPrimOp(a.drop(1), args))
        case first :: rest =>
            for {
                rator <- interpret(first)
                args <- allOf(rest.map(interpret))
            } yield AppExp(rator, args)
    }

    def interpretKeyword(k: String, rest: List[Raw]): Option[Exp] = k match {
        // Kernel forms (Figure 11.31).
        case "error" => rest match {
            case List(RawAtom(msg), tRaw) => T.parse(tRaw) map (FlexError(msg, _))
            case _ => None
        }
        case "if" => rest match {
            case List(t, th, el) => lift3(interpret(t), interpret(th), interpret(el)) (If(_, _, _))
            case _ => None
        }
        case "prim" => rest match {
            case List(RawAtom(opName), args @ _*) =>
                for {
                    tag <- PrimOpTag.fromName(opName)
                    a <- allOf(args.toList.map(interpret))
                } yield PrimOp(tag, a)
            case _ => None
        }
        case "abs" => rest match {
            case List(formalsRaw, body) =>
                for {
                    fs <- typedFormals(formalsRaw)
                    b <- interpret(body)
                } yield AbsExp(fs, b)
            case _ => None
        }
        // let is a kernel form in FLEX (book p.632): bindings are untyped.
        case "let" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- untypedBindings(bindsRaw)
                    b <- interpret(body)
                } yield Let(bs, b)
            case _ => None
        }
        case "letrec" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- typedBindings(bindsRaw)
                    b <- interpret(body)
                } yield LetRecExp(bs, b)
            case _ => None
        }
        case "the" => rest match {
            case List(tRaw, e) =>
                for {
                    t <- T.parse(tRaw)
                    ex <- interpret(e)
                } yield TheExp(t, ex)
            case _ => None
        }
        case "sym" => rest match {
            case List(RawAtom(s)) => Some(Sym(s))
            case _ => None
        }
        case "pair" => rest match {
            case List(f, s) => lift2(interpret(f), interpret(s)) (Pair(_, _))
            case _ => None
        }
        case "fst" => unary(rest) (FstExp(_))
        case "snd" => unary(rest) (SndExp(_))
        case "prod" => allOf(rest.map(interpret)) map (cs => ProdExp(cs))
        case "get" => rest match {
            // The index must be an integer literal (Figure 11.16).
            case List(RawAtom(n), e) if isInt(n) =>
                interpret(e) map (GetExp(n.toInt, _))
            case _ => None
        }
        case "seq" => allOf(rest.map(interpret)) map (cs => SeqExp(cs))
        case "seq-get" => rest match {
            case List(i, s) => lift2(interpret(i), interpret(s)) (SeqGetExp(_, _))
            case _ => None
        }
        case "seq-size" => unary(rest) (SeqSizeExp(_))
        case "record" => recordFields(rest) map (fs => RecordExp(fs))
        case "select" => rest match {
            case List(nameRaw, e) =>
                for {
                    n <- selectName(nameRaw)
                    ex <- interpret(e)
                } yield SelectExp(n, ex)
            case _ => None
        }
        case "with" => rest match {
            case List(rcd, body) => lift2(interpret(rcd), interpret(body)) (WithExp(_, _))
            case _ => None
        }
        case "one" => rest match {
            case List(tRaw, tagRaw, payload) =>
                for {
                    t <- T.parse(tRaw)
                    tag <- selectName(tagRaw)
                    p <- interpret(payload)
                } yield OneExp(t, tag, p)
            case _ => None
        }
        case "tagcase" => rest match {
            case List(discRaw, payloadRaw, clauses @ _*) =>
                // A trailing (else E) clause is optional (Figure 11.22).
                val (clausesRaw, elseRaw) = clauses.toList match {
                    case Nil => (Nil, None)
                    case init2 :+ last if isElse(last) => (init2, Some(last))
                    case cs => (cs, None)
                }
                val parsedElse: Option[Option[Exp]] = elseRaw match {
                    case Some(raw) => elseBody(raw) map (Some(_))
                    case None => Some(None)
                }
                for {
                    d <- interpret(discRaw)
                    pn <- selectName(payloadRaw)
                    cs <- allOf(clausesRaw.map(tagClause))
                    el <- parsedElse
                } yield TagCaseExp(d, pn, cs, el)
            case _ => None
        }
        case "cons" => rest match {
            case List(h, t) => lift2(interpret(h), interpret(t)) (ConsExp(_, _))
            case _ => None
        }
        case "car" => unary(rest) (CarExp(_))
        case "cdr" => unary(rest) (CdrExp(_))
        case "null" => rest match {
            case List(tRaw) => T.parse(tRaw) map (t => NullExp(t))
            case _ => None
        }
        case "null?" => unary(rest) (NullQExp(_))
        case "set!" => rest match {
            case List(nameRaw, e) =>
                for {
                    n <- selectName(nameRaw)
                    ex <- interpret(e)
                } yield SetExp(n, ex)
            case _ => None
        }
        case "cell" => unary(rest) (CellExp(_))
        case "^" => unary(rest) (DerefExp(_))
        case ":=" => rest match {
            case List(c, e) => lift2(interpret(c), interpret(e)) (CellSetExp(_, _))
            case _ => None
        }
        case "cell=?" => rest match {
            case List(e1, e2) => lift2(interpret(e1), interpret(e2)) (CellEqExp(_, _))
            case _ => None
        }

        // Sugar forms (Figures 11.2, 11.21, and 11.24).
        case "cond" => interpretCond(rest)
        case "scand" => allOf(rest.map(interpret)) map (es => Scand(es))
        case "scor" => allOf(rest.map(interpret)) map (es => Scor(es))
        case "begin" => rest match {
            case List(e1, e2) => lift2(interpret(e1), interpret(e2)) (BeginExp(_, _))
            case _ => None
        }
        case "let-type" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- typeBindings(bindsRaw)
                    b <- interpret(body)
                } yield LetTypeExp(bs, b)
            case _ => None
        }
        case "let-type*" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- typeBindings(bindsRaw)
                    b <- interpret(body)
                } yield LetTypeStarExp(bs, b)
            case _ => None
        }
        case "list" => rest match {
            // (list T E*) — the element type is explicit (Figure 11.24).
            case List(tRaw, es @ _*) =>
                for {
                    t <- T.parse(tRaw)
                    els <- allOf(es.toList.map(interpret))
                } yield ListExp(t, els)
            case _ => None
        }
        case _ => None
    }

    private def isElse(raw: Raw): Boolean = raw match {
        case RawList(List(RawAtom("else"), _)) => true
        case _ => false
    }

    private def elseBody(raw: Raw): Option[Exp] = raw match {
        case RawList(List(RawAtom("else"), e)) => interpret(e)
        case _ => None
    }

    private def tagClause(raw: Raw): Option[(String, Exp)] = raw match {
        case RawList(List(tagRaw, body)) =>
            for {
                tag <- selectName(tagRaw)
                b <- interpret(body)
            } yield (tag, b)
        case _ => None
    }

    def interpretCond(items: List[Raw]): Option[Exp] = {
        val branches = List.newBuilder[(Exp, Exp)]
        var default: Option[Exp] = None
        var err: Option[String] = None
        items.foreach {
            case RawList(List(RawAtom("else"), d)) if default.isEmpty =>
                interpret(d) match {
                    case Some(e) => default = Some(e)
                    case None => err = Some("cond: malformed else clause")
                }
            case RawList(List(t, th)) =>
                (interpret(t), interpret(th)) match {
                    case (Some(te), Some(ee)) => branches += ((te, ee))
                    case _ => err = Some("cond: malformed branch")
                }
            case _ => err = Some("cond: malformed clause")
        }
        err match {
            case Some(_) => None
            case None => Some(Cond(branches.result(), default))
        }
    }

    // ------------------------------------------------------------------
    // Binding lists and formals
    // ------------------------------------------------------------------

    // ((I T)*) — typed formals (program parameters, abs parameters).
    def typedFormals(raw: Raw): Option[List[(String, T)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), tRaw)) if validIdent(name) =>
                    T.parse(tRaw) map (t => name -> t)
                case _ => None
            })
        case _ => None
    }

    // ((I E)*) — untyped let bindings (the FLEX kernel let, book p.632).
    def untypedBindings(raw: Raw): Option[List[(String, Exp)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), e)) if validIdent(name) =>
                    interpret(e) map (ex => name -> ex)
                case _ => None
            })
        case _ => None
    }

    // ((I T E)*) — typed letrec bindings.
    def typedBindings(raw: Raw): Option[List[(String, T, Exp)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), tRaw, e)) if validIdent(name) =>
                    (T.parse(tRaw), interpret(e)) match {
                        case (Some(t), Some(ex)) => Some((name, t, ex))
                        case _ => None
                    }
                case _ => None
            })
        case _ => None
    }

    // ((tau T)*) — type bindings for let-type / let-type* / def-type bodies.
    def typeBindings(raw: Raw): Option[List[(String, T)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), tRaw)) if validTypeIdent(name) =>
                    T.parse(tRaw) map (t => name -> t)
                case _ => None
            })
        case _ => None
    }

    private def recordFields(raws: List[Raw]): Option[List[(String, Exp)]] =
        allOf(raws.map {
            case RawList(List(RawAtom(name), e)) if validIdent(name) =>
                interpret(e) map (ex => name -> ex)
            case _ => None
        })

    // A value-identifier position: a name that is not a keyword.
    private def selectName(raw: Raw): Option[String] = raw match {
        case RawAtom(n) if validIdent(n) => Some(n)
        case _ => None
    }

    private def validIdent(name: String): Boolean =
        !name.startsWith("@") && !keywords.contains(name)

    private def validTypeIdent(name: String): Boolean =
        !name.startsWith("@") && !T.TypeKeywords.contains(name)

    // ------------------------------------------------------------------
    // def / def-type items of a flex program (Figure 11.2)
    // ------------------------------------------------------------------

    // (def I T E) or the procedure-defining sugar
    // (def (Iproc Treturn (I1 T1) ... (In Tn)) Ebody) — the formal pairs are
    // direct elements of the head list (book p.636: (def (even? bool (x int))
    // ...)), converted at parse time to
    // (def I (-> (T1 ... Tn) Treturn) (abs ((I1 T1) ... (In Tn)) Ebody)).
    def interpretDef(raw: Raw): Option[FlexDef] = raw match {
        case RawList(List(RawAtom("def"), RawAtom(name), tRaw, e)) =>
            for {
                _ <- if (validIdent(name)) Some(()) else None
                t <- T.parse(tRaw)
                ex <- interpret(e)
            } yield FlexDef(name, t, ex)
        case RawList(List(RawAtom("def"), RawList(List(RawAtom(name), tRetRaw, formals @ _*)), e)) =>
            for {
                _ <- if (validIdent(name)) Some(()) else None
                tRet <- T.parse(tRetRaw)
                params <- allOf(formals.toList.map {
                    case RawList(List(RawAtom(n), tRaw2)) if validIdent(n) =>
                        T.parse(tRaw2) map (t => n -> t)
                    case _ => None
                })
                ex <- interpret(e)
            } yield FlexDef(name, TArrow(params.map(_._2), tRet), AbsExp(params, ex))
        case _ => None
    }

    // (def-type tau T)* (def I T E)* — all def-types must precede all defs.
    def splitTypeDefsAndDefs(items: List[Raw]): Option[(List[(String, T)], List[FlexDef])] = {
        val typeDefs = List.newBuilder[(String, T)]
        val defs = List.newBuilder[FlexDef]
        var inDefs = false
        var err: Option[String] = None
        items.foreach {
            case RawList(List(RawAtom("def-type"), RawAtom(name), tRaw)) if !inDefs =>
                if (err.isEmpty)
                    if (!validTypeIdent(name)) err = Some(s"illegal type identifier: $name")
                    else T.parse(tRaw) match {
                        case Some(t) => typeDefs += (name -> t)
                        case None => err = Some(s"malformed type in def-type: $name")
                    }
            case item @ RawList(List(RawAtom("def"), _*)) =>
                inDefs = true
                if (err.isEmpty)
                    interpretDef(item) match {
                        case Some(d) => defs += d
                        case None => err = Some("malformed def")
                    }
            case _ => err = Some("malformed program item")
        }
        err match {
            case Some(_) => None
            case None => Some((typeDefs.result(), defs.result()))
        }
    }

    // ------------------------------------------------------------------
    // Option combinators
    // ------------------------------------------------------------------

    private def allOf[A](oas: List[Option[A]]): Option[List[A]] =
        oas.foldRight[Option[List[A]]](Some(Nil)) { (oa, acc) =>
            acc flatMap { as => oa map (_ +: as) }
        }

    private def lift2[A, B, C](oa: Option[A], ob: Option[B])(f: (A, B) => C): Option[C] =
        for {
            a <- oa
            b <- ob
        } yield f(a, b)

    private def lift3[A, B, C, D](oa: Option[A], ob: Option[B], oc: Option[C])(f: (A, B, C) => D): Option[D] =
        for {
            a <- oa
            b <- ob
            c <- oc
        } yield f(a, b, c)

    private def unary(rest: List[Raw])(f: Exp => Exp): Option[Exp] = rest match {
        case List(e) => interpret(e) map f
        case _ => None
    }
}
