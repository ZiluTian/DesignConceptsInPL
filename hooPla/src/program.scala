package DSL.hooPla

import DSL.fl._
import scala.util.parsing.combinator._

// Parses HOOK/HOOPLA concrete syntax (s-expressions) into the typed AST.
//
// The parser first reads a raw s-expression tree (the Raw domain of
// DSL.fl.lexer), then `interpretProgram` / `interpret` build the typed AST
// by dispatching on the leading keyword of each parenthesized list. The
// HOOK kernel forms (Figure 7.22) are:
//
//   (hook (I*) Ebody D*)     program (HOOK's tag)
//   (method M (Irecv I*) E)  simple object
//   (compose E1 E2)          object composition
//   (null-object)            the object with no methods
//   (send M Erecv Earg*)     a message send
//   (sym Y)                  a symbolic literal
//
// and the HOOPLA forms (Figure 7.23) are:
//
//   (hoopla (I*) Ebody D*)   program (HOOPLA's tag)
//   (object E*)              compose any number of objects
//   (class (Iinit*) Eobj*)   an instance-creating object (responds to new)
//   (abs (I*) E)             a procedure object (responds to call)
//   (let ((I E)*) Ebody)     local binding
//   (if Etest Ethen Eelse)   conditional (exactly three arguments)
//
// Any other parenthesized list is a tagless application (E Erand*), whose
// rator is the first element. The parser is lenient: it accepts HOOPLA
// sugar in a `hook` program and HOOK kernel forms in a `hoopla` program.
object HooPlaProgram extends FlLexer {

    private val keywords = Set(
        "hook", "hoopla", "method", "compose", "null-object", "send",
        "sym", "object", "class", "abs", "let", "if", "def")

    private var counter = 0
    private def fresh(): String = { counter += 1; s"@@hoo_recv_$counter" }

    def apply(input: String): Option[FL] = {
        parse(sExp, input) match {
            case Success(raw, _) => interpretProgram(raw)
            case _ => None
        }
    }

    def interpretProgram(raw: Raw): Option[FL] = raw match {
        case RawList(List(RawAtom("hook"), formalsRaw, bodyRaw, defs @ _*)) =>
            Some(SugaredProgram(formals(formalsRaw), interpret(bodyRaw), defs.map(interpretDef).toList))
        case RawList(List(RawAtom("hoopla"), formalsRaw, bodyRaw, defs @ _*)) =>
            Some(SugaredProgram(formals(formalsRaw), interpret(bodyRaw), defs.map(interpretDef).toList))
        case _ => None
    }

    def interpret(raw: Raw): Exp = raw match {
        case RawAtom(a) => interpretAtom(a)
        case RawList(items) => interpretList(items)
    }

    def interpretAtom(a: String): Exp = a match {
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
            case _ =>
                TaglessAppExp(interpret(first), rest.map(interpret))
        }
    }

    def interpretKeyword(k: String, rest: List[Raw]): Exp = k match {
        // HOOK kernel keywords.
        case "method" => rest match {
            case List(RawAtom(msg), paramsRaw, body) => formals(paramsRaw) match {
                case recv :: fs => MethodExp(msg, recv, fs, interpret(body))
                // An empty parameter list names no receiver: a method that
                // takes no arguments and ignores its receiver (the book's
                // `(method call ( ) 3)`).
                case Nil => MethodExp(msg, fresh(), Nil, interpret(body))
            }
            case _ => ErrorExpr("method: expected (method M (Ireceiver Iformal*) Ebody)")
        }
        case "compose" => rest match {
            case List(a, b) => ComposeExp(interpret(a), interpret(b))
            case _ => ErrorExpr("compose: expected (compose E1 E2)")
        }
        case "null-object" =>
            if (rest.isEmpty) NullObjectExp()
            else ErrorExpr("null-object: takes no arguments")
        case "send" => rest match {
            case RawAtom(msg) :: (recv :: args) =>
                SendExp(msg, interpret(recv), args.map(interpret))
            case _ => ErrorExpr("send: expected (send M Ereceiver Earg*)")
        }
        case "sym" => rest match {
            case List(RawAtom(s)) => Sym(s)
            case _ => ErrorExpr("sym: expected (sym Y)")
        }
        // HOOPLA keywords (Figure 7.23).
        case "object" => ObjectExp(rest.map(interpret))
        case "class" => rest match {
            case initsRaw :: objsRaw => ClassExp(formals(initsRaw), objsRaw.map(interpret))
            case _ => ErrorExpr("class: expected (class (Iinit*) Eobject*)")
        }
        case "abs" => rest match {
            case List(formalsRaw, body) => HooAbsExp(formals(formalsRaw), interpret(body))
            case _ => ErrorExpr("abs: expected (abs (formals) body)")
        }
        case "let" => rest match {
            case List(bindsRaw, body) => HooLetExp(bindings(bindsRaw), interpret(body))
            case _ => ErrorExpr("let: expected (let ((name def)*) body)")
        }
        case "if" => rest match {
            case List(t, th, el) => HooIfExp(interpret(t), interpret(th), interpret(el))
            case _ => ErrorExpr("if: expected (if test then else)")
        }
        case _ => ErrorExpr(s"unknown keyword $k")
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

    def interpretDef(raw: Raw): Def = raw match {
        case RawList(List(RawAtom("def"), RawAtom(name), e)) =>
            ValueDef(name, interpret(e))
        case _ => ValueDef("_malformed", ErrorExpr("malformed def"))
    }
}
