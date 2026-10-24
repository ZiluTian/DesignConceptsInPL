package DSL.elmm

import DSL.sexp._

// AST of ELMM ("EL Minus Minus") using S-expressions.
//
// ELMM is the most restricted stage of the EL family (Figure 3.6 of the
// book): a program is a single numerical expression with no program inputs,
// no boolean expressions, and no conditionals.
//
//   P  ∈ Prog  ::= (elmm NE body)               [Program]
//   NE ∈ NumExp ::= Nnum                        [IntLit]
//                 | (Arator NE rand1 NE rand2)  [ArithmeticOperation]
//   A  ∈ ArithmeticOperator = {+, -, *, /, %}

sealed trait ELMM extends SPTree

sealed trait NumExp extends ELMM

// Primitive syntactic domains
case class IntLit(n: Int) extends SymbolicToken with NumExp {
    label = "IntLit"
    value = n.toString
}

case class ArithmeticOperation(rator: ArithmeticOperator, rand1: NumExp, rand2: NumExp) extends INode with NumExp {
    label = "ArithmeticOperation"
    children = List(rator, rand1, rand2)
}

// Phrase tags in ELMM
case object ELMMTag extends PhraseTag("elmm") with ELMM

// Arithmetic operators
sealed trait ArithmeticOperator extends ELMM
case object ADD  extends PhraseTag("+")  with ArithmeticOperator
case object SUB  extends PhraseTag("-")  with ArithmeticOperator
case object MULT extends PhraseTag("*")  with ArithmeticOperator
case object DIV  extends PhraseTag("/")  with ArithmeticOperator
case object MOD  extends PhraseTag("%")  with ArithmeticOperator

// Compound syntactic domains
case class Program(body: NumExp) extends INode with ELMM {
    children = List(body)
    label = "Program"
    body.edgeLabel = "body"
}

extension (c: ELMM)
    def show(): Unit = {
        val printTree = new PrintELMM()
        c.accept(printTree)
    }
