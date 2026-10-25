package DSL.fil

import scala.util.parsing.combinator._
import DSL.fl.{FlLexer, Raw, RawAtom, RawList}
import DSL.fl._
import DSL.sexp._

// Parses FIL concrete syntax (s-expressions, Figure 17.14 of the book) into
// the typed FIL AST.
//
// As in DSL.fl.FlProgram and DSL.flare.FlareProgram, the parser first reads
// a raw s-expression tree (DSL.fl.FlLexer) and then builds the typed AST.
// The interpretation is fallible (Option): a malformed expression — a
// keyword with the wrong arity, an identifier in a binding position, an
// unknown or ill-formed primop — yields None, so the whole program is
// rejected as a parse error.
//
// The single program tag is `fil`: (fil (Iformal*) Ebody). The body may
// contain both kernel forms and syntactic sugar (the @-abbreviations of
// primops and let*); desugaring and the Figure 17.15 simplifications are
// applied when the AST is constructed (see Desugar), so the parsed program
// is always in simplified kernel form.
//
// Indexed primops: the operator of (prim O E*) may be a parenthesized
// (mget J) or (mset! J), where J must be a positive integer literal — the
// book's "indexed primitive" convention (page 1031): the index is part of
// the operator, not an expression. The @-sugar (@mget J Emprod) and
// (@mset! J Emprod Enew) desugars to the corresponding prim form.

// (fil (I*) Ebody) — a FIL program (kernel and sugar under one tag).
// (Declared in this file so it is a true companion of the FilProgram parser
// object below.)
case class FilProgram(formals: List[String], body: Exp) extends INode with FL {
    label = "FilProgram"
    children = INode(formals.map(s => SymbolicToken(s))) :: List(body)
}

object FilProgram extends FlLexer {

    def apply(input: String): Option[FilProgram] =
        parse(sExp, input) match {
            case Success(raw, _) => interpretProgram(raw)
            case _ => None
        }

    def interpretProgram(raw: Raw): Option[FilProgram] = raw match {
        case RawList(List(RawAtom("fil"), formalsRaw, bodyRaw)) =>
            for {
                fs <- checkFormals(formalsRaw)
                body <- interpret(bodyRaw)
            } yield FilProgram(fs, DSL.fil.Desugar(body))
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
            case RawAtom(k) if FilIdent.keywords.contains(k) =>
                interpretKeyword(k, rest)
            case RawAtom(a) if a.startsWith("@") =>
                interpretSugaredPrim(a.drop(1), rest)
            case _ =>
                for {
                    rator <- interpret(first)
                    args <- interpretAll(rest)
                } yield FilApp(rator, args)
        }
    }

    // (@O E*) for a base operator O; (@mget J Emprod) and (@mset! J Emprod
    // Enew) for the indexed operators, where J must be a positive integer
    // literal.
    private def interpretSugaredPrim(op: String, rest: List[Raw]): Option[Exp] =
        (op, rest) match {
            case ("mget", RawAtom(j) :: args) if FilPrimop.isPosLit(j) =>
                interpretAll(args).map(as => SugaredPrimOp("mget " + j, as))
            case ("mset!", RawAtom(j) :: args) if FilPrimop.isPosLit(j) =>
                interpretAll(args).map(as => SugaredPrimOp("mset! " + j, as))
            case _ if FilPrimop.baseOps.contains(op) =>
                interpretAll(rest).map(as => SugaredPrimOp(op, as))
            case _ => None
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
            case List(opRaw, args @ _*) =>
                interpretPrimOp(opRaw).flatMap { op =>
                    interpretAll(args.toList).map(as => FilPrim(op, as))
                }
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
        case "app" => rest match {
            case ratorRaw :: randsRaw =>
                for {
                    rator <- interpret(ratorRaw)
                    rands <- interpretAll(randsRaw)
                } yield FilApp(rator, rands)
            case Nil => None
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
        case "let*" => interpretLetLike(rest, (bs, body) => LetStar(bs, body))
        case _ => None
    }

    // The operator of (prim O E*): a base primop name, or a parenthesized
    // indexed operator (mget J) / (mset! J) with J a positive integer
    // literal.
    private def interpretPrimOp(raw: Raw): Option[String] = raw match {
        case RawAtom(n) if FilPrimop.baseOps.contains(n) => Some(n)
        case RawList(List(RawAtom("mget"), RawAtom(j))) if FilPrimop.isPosLit(j) =>
            Some("mget " + j)
        case RawList(List(RawAtom("mset!"), RawAtom(j))) if FilPrimop.isPosLit(j) =>
            Some("mset! " + j)
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
                case (Some(acc), RawList(List(RawAtom(n), e))) if FilIdent.valid(n) =>
                    interpret(e).map(ex => acc :+ ((n, ex)))
                case _ => None
            }
        case _ => None
    }

    private def checkFormals(raw: Raw): Option[List[String]] = raw match {
        case RawList(items) =>
            items.foldLeft[Option[List[String]]](Some(Nil)) {
                case (Some(acc), RawAtom(a)) if FilIdent.valid(a) => Some(acc :+ a)
                case _ => None
            }
        case _ => None
    }

    private def interpretAll(items: List[Raw]): Option[List[Exp]] =
        items.foldLeft[Option[List[Exp]]](Some(Nil)) {
            case (Some(acc), e) => interpret(e).map(ex => acc :+ ex)
            case (None, _) => None
        }
}
