package DSL.flavar

import DSL.fl._
import DSL.flic._
import scala.util.parsing.combinator._

// Parses FLAVAR/FLAVARK concrete syntax (s-expressions) into the typed AST.
//
// The parser first reads a raw s-expression tree (the Raw domain of
// DSL.fl.lexer), then `interpretProgram` / `interpret` build the typed AST by
// dispatching on the leading keyword / @-operator / tagless-application form
// of each parenthesized list. The interpretation of the FL / FLK / FLIC
// constructs is the same as in DSL.flic.FlicProgram; the FLAVAR-specific
// constructs are:
//
//   (flavark (I*) E)   unsugared (FLAVARK) program
//   (flavar  (I*) E D*) sugared (FLAVAR) program
//   (set! I E)         variable assignment (FLAVARK kernel)
object FlavarProgram extends FlLexer {

    private val keywords = Set(
        "flavark", "flavar", "if", "prim", "lam", "app", "pair", "rec", "error", "sym",
        "abs", "list", "quote", "cond", "scand", "scor", "let", "letrec", "recur", "def",
        "cell", "begin", "while", "set!")

    def apply(input: String): Option[FL] = {
        parse(sExp, input) match {
            case Success(raw, _) => interpretProgram(raw)
            case _ => None
        }
    }

    def interpretProgram(raw: Raw): Option[FL] = raw match {
        case RawList(List(RawAtom("flavark"), formalsRaw, bodyRaw)) =>
            Some(UnsugaredProgram(formals(formalsRaw), interpret(bodyRaw)))
        case RawList(List(RawAtom("flavar"), formalsRaw, bodyRaw, defs @ _*)) =>
            Some(SugaredProgram(formals(formalsRaw), interpret(bodyRaw), defs.map(interpretDef).toList))
        case _ => None
    }

    def interpret(raw: Raw): Exp = raw match {
        case RawAtom(a) => interpretAtom(a)
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

    def interpretList(items: List[Raw]): Exp = items match {
        case Nil => ErrorExpr("empty expression")
        case first :: rest => first match {
            case RawAtom(k) if keywords.contains(k) => interpretKeyword(k, rest)
            case RawAtom(a) if a.startsWith("@") =>
                SugaredPrimOp(a.drop(1), rest.map(interpret))
            case _ =>
                MultiApp(interpret(first), rest.map(interpret))
        }
    }

    def interpretKeyword(k: String, rest: List[Raw]): Exp = k match {
        // FLAVAR-specific keyword.
        case "set!" => rest match {
            case List(RawAtom(name), e) => SetBang(name, interpret(e))
            case _ => ErrorExpr("set!: expected (set! I E)")
        }
        // FLIC-specific keywords.
        case "cell" => rest match {
            case List(e) => CellExp(interpret(e))
            case _ => ErrorExpr("cell: expected (cell E)")
        }
        case "begin" => BeginListExp(rest.map(interpret))
        case "while" => rest match {
            case List(t, b) => WhileExp(interpret(t), interpret(b))
            case _ => ErrorExpr("while: expected (while Etest Ebody)")
        }
        case "if" => rest match {
            case List(t, th) => ElselessIfExp(interpret(t), interpret(th))
            case List(t, th, el) => If(interpret(t), interpret(th), interpret(el))
            case _ => ErrorExpr("if: expected (if test then else) or (if test then)")
        }
        // FL/FLK keywords (as in DSL.flic.FlicProgram).
        case "prim" => rest match {
            case List(RawAtom(opName), args @ _*) =>
                if (args.isEmpty) ErrorExpr("prim: expected (prim op arg*)")
                else SugaredPrimOp(opName, args.map(interpret).toList)
            case _ => ErrorExpr("prim: expected (prim op arg*)")
        }
        case "lam" => rest match {
            case List(RawAtom(f), body) => Lam(f, interpret(body))
            case _ => ErrorExpr("lam: expected (lam formal body)")
        }
        case "app" => rest match {
            case List(r, a) => App(interpret(r), interpret(a))
            case _ => ErrorExpr("app: expected (app rator rand)")
        }
        case "pair" => rest match {
            case List(f, s) => Pair(interpret(f), interpret(s))
            case _ => ErrorExpr("pair: expected (pair fst snd)")
        }
        case "rec" => rest match {
            case List(RawAtom(n), body) => Rec(n, interpret(body))
            case _ => ErrorExpr("rec: expected (rec name body)")
        }
        case "error" => rest match {
            case List(RawAtom(msg)) => ErrorExpr(msg)
            case _ => ErrorExpr("error: expected (error message)")
        }
        case "sym" => rest match {
            case List(RawAtom(s)) => Sym(s)
            case _ => ErrorExpr("sym: expected (sym Y)")
        }
        case "abs" => rest match {
            case List(formalsRaw, body) => Abs(formals(formalsRaw), interpret(body))
            case _ => ErrorExpr("abs: expected (abs (formals) body)")
        }
        case "list" => ListExpr(rest.map(interpret))
        case "quote" => rest match {
            case List(sx) => Quote(interpretSExp(sx))
            case _ => ErrorExpr("quote: expected (quote SX)")
        }
        case "cond" => interpretCond(rest)
        case "scand" => Scand(rest.map(interpret))
        case "scor" => Scor(rest.map(interpret))
        case "let" => rest match {
            case List(bindsRaw, body) => Let(bindings(bindsRaw), interpret(body))
            case _ => ErrorExpr("let: expected (let ((name def)*) body)")
        }
        case "letrec" => rest match {
            case List(bindsRaw, body) => LetRec(bindings(bindsRaw), interpret(body))
            case _ => ErrorExpr("letrec: expected (letrec ((name def)*) body)")
        }
        case "recur" => rest match {
            case List(RawAtom(proc), bindsRaw, body) => Recur(proc, bindings(bindsRaw), interpret(body))
            case _ => ErrorExpr("recur: expected (recur proc ((name init)*) body)")
        }
        case _ => ErrorExpr(s"unknown keyword $k")
    }

    def interpretCond(items: List[Raw]): Exp = {
        val branches = List.newBuilder[(Exp, Exp)]
        var default: Option[Exp] = None
        items.foreach {
            case RawList(List(RawAtom("else"), d)) => default = Some(interpret(d))
            case RawList(List(t, th)) => branches += ((interpret(t), interpret(th)))
            case _ => ()
        }
        Cond(branches.result(), default)
    }

    def formals(raw: Raw): List[String] = raw match {
        case RawList(items) => items.collect { case RawAtom(a) => a }
        case _ => Nil
    }

    def bindings(raw: Raw): List[(String, Exp)] = raw match {
        case RawList(items) => items.collect {
            case RawList(List(RawAtom(n), e)) => (n, interpret(e))
        }
        case _ => Nil
    }

    def interpretSExp(raw: Raw): SExp = raw match {
        case RawAtom(a) => a match {
            case "#u" => SExpUnit()
            case "#t" => SExpBool(true)
            case "#f" => SExpBool(false)
            case n if isInt(n) => SExpInt(n.toInt)
            case other => SExpSym(other)
        }
        case RawList(items) => SExpList(items.map(interpretSExp))
    }

    def interpretDef(raw: Raw): Def = raw match {
        case RawList(List(RawAtom("def"), RawAtom(name), e)) =>
            ValueDef(name, interpret(e))
        case RawList(List(RawAtom("def"), RawList(List(RawAtom(name), RawAtom(formal))), body)) =>
            FunctionDef(name, formal, interpret(body))
        case _ => ValueDef("_malformed", ErrorExpr("malformed def"))
    }
}
