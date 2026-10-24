package DSL.flare

import scala.util.parsing.combinator._
import DSL.fl._

// Parses full-FLARE concrete syntax into the flare AST.
//
// As in DSL.fl.FlProgram and DSL.flex.FlexProgram, the parser first reads a
// raw s-expression tree (DSL.fl.FlLexer), then `interpretProgram` /
// `interpret` build the typed AST by dispatching on the leading keyword /
// @-operator / tagless-application form of each parenthesized list. The
// interpretation is fallible (Option): a malformed expression — a keyword in
// the wrong arity, an identifier in a binding position, an unknown primop —
// yields None, so the whole program is rejected as a parse error.
//
// FLARE program tags: `flarek` (kernel) and `flare` (sugar). Identifiers in
// binding positions (formals, let / letrec / def names) are validated against
// the Ident domain (FlareIdent.valid); primop names in `prim` and `@` forms
// are validated against TEPrim.primops.

object FlareProgram extends FlLexer {

    import FlareIdent.keywords

    def apply(input: String): Option[FlarePgm] =
        parse(sExp, input) match {
            case Success(raw, _) => interpretProgram(raw)
            case _ => None
        }

    def interpretProgram(raw: Raw): Option[FlarePgm] = raw match {
        case RawList(List(RawAtom("flarek"), formalsRaw, bodyRaw)) =>
            for {
                fs <- checkFormals(formalsRaw)
                body <- interpret(bodyRaw)
            } yield FlareKernelProgram(fs, body)
        case RawList(List(RawAtom("flare"), formalsRaw, bodyRaw, defs @ _*)) =>
            for {
                fs <- checkFormals(formalsRaw)
                ds <- interpretDefs(defs)
                body <- interpret(bodyRaw)
            } yield FlareSugarProgram(fs, body, ds)
        case _ => None
    }

    // (def I E) and (def (Iproc Iformal*) Ebody) — the latter is desugared to
    // (def Iproc (abs (Iformal*) Ebody)) here, per the def desugaring rule
    // inherited from FL (page 233).
    def interpretDefs(defs: Seq[Raw]): Option[List[(String, Exp)]] =
        defs.foldLeft[Option[List[(String, Exp)]]](Some(Nil)) {
            case (Some(acc), RawList(List(RawAtom("def"), RawAtom(n), e)))
                    if FlareIdent.valid(n) =>
                interpret(e).map(ex => acc :+ (n, ex))
            case (Some(acc), RawList(List(RawAtom("def"), RawList(items), e))) =>
                val names = items.collect { case RawAtom(a) => a }
                if (items.size == names.size && names.nonEmpty &&
                    names.forall(FlareIdent.valid))
                    interpret(e).map(ex => acc :+ (names.head, Abs(names.tail, ex)))
                else None
            case _ => None
        }

    def interpret(raw: Raw): Option[Exp] = raw match {
        case RawAtom(a) => Some(interpretAtom(a))
        case RawList(items) => interpretList(items)
    }

    def interpretAtom(a: String): Exp = a match {
        case "#u" => UnitLit()
        case "#t" => BoolLit(true)
        case "#f" => BoolLit(false)
        case n if isInt(n) => IntLit(n.toInt)
        case other => Var(other)
    }

    private def isInt(s: String): Boolean = {
        val digits = if (s.nonEmpty && s.head == '-') s.tail else s
        digits.nonEmpty && digits.forall(_.isDigit)
    }

    def interpretList(items: List[Raw]): Option[Exp] = items match {
        case Nil => None
        case first :: rest => first match {
            case RawAtom(k) if keywords.contains(k) || FlareIdent.sugarKeywords.contains(k) =>
                interpretKeyword(k, rest)
            case RawAtom(a) if a.startsWith("@") =>
                val op = a.drop(1)
                if (TEPrim.primops.contains(op))
                    interpretAll(rest).map(as => SugaredPrimOp(op, as))
                else None
            case _ =>
                for {
                    rator <- interpret(first)
                    args <- interpretAll(rest)
                } yield MultiApp(rator, args)
        }
    }

    private def interpretAll(items: List[Raw]): Option[List[Exp]] =
        items.foldLeft[Option[List[Exp]]](Some(Nil)) {
            case (Some(acc), e) => interpret(e).map(ex => acc :+ ex)
            case (None, _) => None
        }

    def interpretKeyword(k: String, rest: List[Raw]): Option[Exp] = k match {
        case "if" => rest match {
            case List(t, th, el) =>
                for {
                    eTest <- interpret(t)
                    eThen <- interpret(th)
                    eElse <- interpret(el)
                } yield If(eTest, eThen, eElse)
            case _ => None
        }
        case "prim" => rest match {
            case List(RawAtom(op), args @ _*) =>
                if (TEPrim.primops.contains(op))
                    interpretAll(args.toList).map(as => FlarePrim(op, as))
                else None
            case _ => None
        }
        case "abs" => rest match {
            case List(formalsRaw, body) =>
                for {
                    fs <- checkFormals(formalsRaw)
                    b <- interpret(body)
                } yield Abs(fs, b)
            case _ => None
        }
        case "error" => rest match {
            case List(RawAtom(msg)) => Some(ErrorExpr(msg))
            case _ => None
        }
        case "sym" => rest match {
            case List(RawAtom(s)) => Some(Sym(s))
            case _ => None
        }
        case "let" => interpretLetLike(rest, (bs, body) => Let(bs, body))
        case "letrec" => interpretLetLike(rest, (bs, body) => LetRec(bs, body))

        // Sugar keywords (Figure 13.23)
        case "cond" => interpretCond(rest)
        case "scand" => interpretAll(rest).map(Scand(_))
        case "scor" => interpretAll(rest).map(Scor(_))
        case "recur" => rest match {
            case List(RawAtom(proc), bindsRaw, body) if FlareIdent.valid(proc) =>
                for {
                    bs <- interpretBindings(bindsRaw)
                    b <- interpret(body)
                } yield Recur(proc, bs, b)
            case _ => None
        }
        case "begin" => interpretBegin(rest)
        case "list" => interpretAll(rest).map(ListExpr(_))
        case "def" | "flare" => None // program-level forms, not expressions
        case _ => None
    }

    private def interpretLetLike(rest: List[Raw],
                                 mk: (List[(String, Exp)], Exp) => Exp): Option[Exp] =
        rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- interpretBindings(bindsRaw)
                    b <- interpret(body)
                } yield mk(bs, b)
            case _ => None
        }

    private def interpretBindings(raw: Raw): Option[List[(String, Exp)]] = raw match {
        case RawList(items) =>
            items.foldLeft[Option[List[(String, Exp)]]](Some(Nil)) {
                case (Some(acc), RawList(List(RawAtom(n), e))) if FlareIdent.valid(n) =>
                    interpret(e).map(ex => acc :+ (n, ex))
                case _ => None
            }
        case _ => None
    }

    // (begin) -> #u; (begin E) -> E; (begin E1 Erest*) -> nested BeginExp
    private def interpretBegin(items: List[Raw]): Option[Exp] = items match {
        case Nil => Some(UnitLit())
        case List(e) => interpret(e)
        case _ =>
            interpretAll(items).map { es =>
                es.dropRight(1).foldRight(es.last) { (e, acc) => BeginExp(e, acc) }
            }
    }

    private def interpretCond(items: List[Raw]): Option[Exp] = {
        val acc = items.foldLeft[Option[(List[(Exp, Exp)], Option[Exp])]](Some((Nil, None))) {
            case (Some((branches, default)), RawList(List(RawAtom("else"), d))) =>
                interpret(d).map(dd => (branches, Some(dd)))
            case (Some((branches, default)), RawList(List(t, th))) =>
                for {
                    eTest <- interpret(t)
                    eThen <- interpret(th)
                } yield (branches :+ (eTest, eThen), default)
            case _ => None
        }
        acc.flatMap { case (branches, default) =>
            if (branches.isEmpty && default.isEmpty) None
            else Some(Cond(branches, default))
        }
    }

    private def checkFormals(raw: Raw): Option[List[String]] = raw match {
        case RawList(items) =>
            items.foldLeft[Option[List[String]]](Some(Nil)) {
                case (Some(acc), RawAtom(a)) if FlareIdent.valid(a) => Some(acc :+ a)
                case _ => None
            }
        case _ => None
    }
}
