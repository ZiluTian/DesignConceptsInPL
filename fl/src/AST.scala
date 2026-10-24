package DSL.fl

import DSL.sexp._

// AST of FL (Functional Language) using S-expressions.
//
// FL is the book's core functional language (Chapter 6). It is a kernel
// language, FLK (Figure 6.1), extended with syntactic sugar (Figure 6.3) that
// is removed by the desugaring function DS (Figure 6.4).
//
// FLK kernel (Figure 6.1):
//   P ∈ Prog  ::= (flk (Iformal*) Ebody)              [Program]
//   E ∈ Exp   ::= L                                    [Literal]
//                | I                                    [VariableReference]
//                | (error Ymessage)                     [Errors]
//                | (if Etest Ethen Eelse)               [Conditional]
//                | (prim Oprimop Earg*)                 [PrimitiveApplication]
//                | (lam Iformal Ebody)                  [Abstraction]
//                | (app Erator Erand)                   [Application]
//                | (pair Efst Esnd)                     [Pairing]
//                | (rec Iname Ebody)                    [Recursion]
//
// FL sugar (Figure 6.3): @O-abbreviated primitives, abs (multi-abstraction),
// tagless multi-application, list, quote, cond, scand, scor, let, letrec,
// recur, and top-level def definitions.

// (Deliberately not sealed: the stateful dialects FLIC and FLAVAR introduce
// new expression and value types that mix with these — see DSL.flic and
// DSL.flavar.)
trait FL extends SPTree

trait Exp extends FL

// ---------------------------------------------------------------------------
// Literals and leaves
// ---------------------------------------------------------------------------

case class UnitLit() extends SymbolicToken with Exp {
    label = "UnitLit"; value = "#u"
}

case class BoolLit(b: Boolean) extends SymbolicToken with Exp {
    label = "BoolLit"; value = b.toString
}

case class IntLit(n: Int) extends SymbolicToken with Exp {
    label = "IntLit"; value = n.toString
}

// (sym Y) — a symbolic literal
case class Sym(s: String) extends INode with Exp {
    label = "Sym"; children = List(SymbolicToken(s))
}

// I — a variable reference (an identifier)
case class Var(name: String) extends SymbolicToken with Exp {
    label = "Var"; value = name
}

// ---------------------------------------------------------------------------
// Kernel compound expressions
// ---------------------------------------------------------------------------

// (error Ymessage) — an error expression. Named ErrorExpr because the name
// `Error` is already taken by scala.util.parsing.combinator.Parsers.Error
// inside objects that extend a lexer.
case class ErrorExpr(msg: String) extends INode with Exp {
    label = "Error"; children = List(SymbolicToken(msg))
}

case class If(test: Exp, thenExp: Exp, elseExp: Exp) extends INode with Exp {
    label = "If"; children = List(test, thenExp, elseExp)
}

// (prim O E...) — a primitive application
case class PrimOp(op: PrimOpTag, args: List[Exp]) extends INode with Exp {
    label = "PrimOp"; children = op :: args
}

// (lam I E) — an abstraction with exactly one formal parameter
case class Lam(formal: String, body: Exp) extends INode with Exp {
    label = "Lam"; children = List(SymbolicToken(formal), body)
}

// (app E E) — an application
case class App(rator: Exp, rand: Exp) extends INode with Exp {
    label = "App"; children = List(rator, rand)
}

// (pair E E) — pair creation
case class Pair(fst: Exp, snd: Exp) extends INode with Exp {
    label = "Pair"; children = List(fst, snd)
}

// (rec I E) — simple recursion
case class Rec(name: String, body: Exp) extends INode with Exp {
    label = "Rec"; children = List(SymbolicToken(name), body)
}

// ---------------------------------------------------------------------------
// FL syntactic sugar (removed by the desugaring function DS)
// ---------------------------------------------------------------------------

// (@O E...) — abbreviated primitive application
case class SugaredPrimOp(op: String, args: List[Exp]) extends INode with Exp {
    label = "SugaredPrimOp"; children = SymbolicToken("@" + op) :: args
}

// (abs (I*) E) — a multi-parameter abstraction
case class Abs(formals: List[String], body: Exp) extends INode with Exp {
    label = "Abs"; children = formals.map(s => SymbolicToken(s)) :+ body
}

// (E E...) — a tagless multi-application (the rator is the first element)
case class MultiApp(rator: Exp, rands: List[Exp]) extends INode with Exp {
    label = "MultiApp"; children = rator :: rands
}

// (list E...) — a list (a unit-terminated chain of pairs)
case class ListExpr(elements: List[Exp]) extends INode with Exp {
    label = "ListExpr"; children = elements
}

// (quote SX) — a quoted s-expression
case class Quote(sx: SExp) extends INode with Exp {
    label = "Quote"; children = List(sx)
}

// (cond (Etest Ethen)* (else Edefault)?) — an n-way conditional
case class Cond(branches: List[(Exp, Exp)], default: Option[Exp]) extends INode with Exp {
    label = "Cond"
    children = branches.flatMap { case (t, e) => List(t, e) } ++ default.toList
}

// (scand E*) / (scor E*) — short-circuit conjunction / disjunction
case class Scand(disjuncts: List[Exp]) extends INode with Exp {
    label = "Scand"; children = disjuncts
}
case class Scor(disjuncts: List[Exp]) extends INode with Exp {
    label = "Scor"; children = disjuncts
}

// (let ((I E)*) Ebody) — local (non-recursive) binding
case class Let(binds: List[(String, Exp)], body: Exp) extends INode with Exp {
    label = "Let"
    children = binds.map { case (n, e) => INode(List(SymbolicToken(n), e)) } :+ body
}

// (letrec ((I E)*) Ebody) — local (mutually-recursive) binding
case class LetRec(binds: List[(String, Exp)], body: Exp) extends INode with Exp {
    label = "LetRec"
    children = binds.map { case (n, e) => INode(List(SymbolicToken(n), e)) } :+ body
}

// (recur Iproc ((I E)*) Ebody) — a recursive function call
case class Recur(proc: String, binds: List[(String, Exp)], body: Exp) extends INode with Exp {
    label = "Recur"
    children = List(SymbolicToken(proc)) ++
        (binds.map { case (n, e) => INode(List(SymbolicToken(n), e)) } :+ body)
}

// ---------------------------------------------------------------------------
// Quoted s-expressions (the SX domain of Figure 6.3)
// ---------------------------------------------------------------------------

sealed trait SExp extends SPTree
case class SExpSym(s: String) extends SymbolicToken with SExp {
    label = "SExpSym"; value = s
}
case class SExpUnit() extends SymbolicToken with SExp {
    label = "SExpUnit"; value = "#u"
}
case class SExpBool(b: Boolean) extends SymbolicToken with SExp {
    label = "SExpBool"; value = b.toString
}
case class SExpInt(n: Int) extends SymbolicToken with SExp {
    label = "SExpInt"; value = n.toString
}
case class SExpList(elems: List[SExp]) extends INode with SExp {
    label = "SExpList"; children = elems
}

// ---------------------------------------------------------------------------
// Primitive operators (Figure 6.2)
// ---------------------------------------------------------------------------

sealed trait PrimOpTag extends PhraseTag
case object UnitQ   extends PhraseTag("unit?") with PrimOpTag
case object BoolQ   extends PhraseTag("bool?") with PrimOpTag
case object IntQ    extends PhraseTag("int?")  with PrimOpTag
case object SymQ    extends PhraseTag("sym?")  with PrimOpTag
case object ProcQ   extends PhraseTag("proc?") with PrimOpTag
case object PairQ   extends PhraseTag("pair?") with PrimOpTag
case object Not     extends PhraseTag("not")   with PrimOpTag
case object And     extends PhraseTag("and")   with PrimOpTag
case object Or      extends PhraseTag("or")    with PrimOpTag
case object BoolEq  extends PhraseTag("bool=?") with PrimOpTag
case object Plus    extends PhraseTag("+")     with PrimOpTag
case object Minus   extends PhraseTag("-")     with PrimOpTag
case object Star    extends PhraseTag("*")     with PrimOpTag
case object Slash   extends PhraseTag("/")     with PrimOpTag
case object Percent extends PhraseTag("%")     with PrimOpTag
case object Eq      extends PhraseTag("=")     with PrimOpTag
case object Neq     extends PhraseTag("!=")    with PrimOpTag
case object Lt      extends PhraseTag("<")     with PrimOpTag
case object Le      extends PhraseTag("<=")    with PrimOpTag
case object Gt      extends PhraseTag(">")     with PrimOpTag
case object Ge      extends PhraseTag(">=")    with PrimOpTag
case object SymEq   extends PhraseTag("sym=?") with PrimOpTag
case object Fst     extends PhraseTag("fst")   with PrimOpTag
case object Snd     extends PhraseTag("snd")   with PrimOpTag

object PrimOpTag {
    def fromName(name: String): Option[PrimOpTag] = name match {
        case "unit?" => Some(UnitQ);  case "bool?" => Some(BoolQ)
        case "int?"  => Some(IntQ);   case "sym?"  => Some(SymQ)
        case "proc?" => Some(ProcQ);  case "pair?" => Some(PairQ)
        case "not"   => Some(Not);    case "and"   => Some(And)
        case "or"    => Some(Or);     case "bool=?" => Some(BoolEq)
        case "+"     => Some(Plus);   case "-"     => Some(Minus)
        case "*"     => Some(Star);   case "/"     => Some(Slash)
        case "%"     => Some(Percent); case "="    => Some(Eq)
        case "!="    => Some(Neq);    case "<"     => Some(Lt)
        case "<="    => Some(Le);     case ">"     => Some(Gt)
        case ">="    => Some(Ge);     case "sym=?" => Some(SymEq)
        case "fst"   => Some(Fst);    case "snd"   => Some(Snd)
        case _ => None
    }
}

// ---------------------------------------------------------------------------
// Top-level program definitions and programs
// ---------------------------------------------------------------------------

sealed trait Def extends FL
// (def I E) — a value definition
case class ValueDef(name: String, exp: Exp) extends INode with Def {
    label = "ValueDef"; children = List(SymbolicToken(name), exp)
}
// (def (Iproc Iformal) Ebody) — a function definition
case class FunctionDef(name: String, formal: String, body: Exp) extends INode with Def {
    label = "FunctionDef"
    children = INode(List(SymbolicToken(name), SymbolicToken(formal))) :: List(body)
}

// (flk (I*) Ebody) — an unsugared program
case class UnsugaredProgram(formals: List[String], body: Exp) extends INode with FL {
    label = "Program"
    children = INode(formals.map(s => SymbolicToken(s))) :: List(body)
}
// (fl (I*) Ebody D*) — a sugared program
case class SugaredProgram(formals: List[String], body: Exp, defs: List[Def]) extends INode with FL {
    label = "Program"
    children = List(INode(formals.map(s => SymbolicToken(s))), body) ++ defs
}

extension (c: FL)
    def show(): Unit = {
        val printTree = new PrintFL()
        c.accept(printTree)
    }
