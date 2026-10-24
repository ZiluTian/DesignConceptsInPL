package DSL.elm

import DSL.sexp._

// AST of ELM ("EL Minus") using S-expressions.
//
// ELM is ELMM extended with indexed references to program inputs
// (Exercise 3.10a of the book): it is EL without conditionals and boolean
// expressions.
//
//   P  ∈ Prog  ::= (elm Nnumargs NE body)         [Program]
//   NE ∈ NumExp ::= Nnum                          [IntLit]
//                 | (arg Nindex)                  [Input]
//                 | (Arator NE rand1 NE rand2)    [ArithmeticOperation]
//   A  ∈ ArithmeticOperator = {+, -, *, /, %}

sealed trait ELM extends SPTree

sealed trait NumExp extends ELM

// Primitive syntactic domains
case class IntLit(n: Int) extends SymbolicToken with NumExp {
    label = "IntLit"
    value = n.toString
}

case class Input(n: IntLit) extends INode with NumExp {
    label = "Input"
    children = List(n)
}

case class ArithmeticOperation(rator: ArithmeticOperator, rand1: NumExp, rand2: NumExp) extends INode with NumExp {
    label = "ArithmeticOperation"
    children = List(rator, rand1, rand2)
}

// Phrase tags in ELM
case object ARG extends PhraseTag("arg") with ELM
case object ELMTag extends PhraseTag("elm") with ELM

// Arithmetic operators
sealed trait ArithmeticOperator extends ELM
case object ADD  extends PhraseTag("+")  with ArithmeticOperator
case object SUB  extends PhraseTag("-")  with ArithmeticOperator
case object MULT extends PhraseTag("*")  with ArithmeticOperator
case object DIV  extends PhraseTag("/")  with ArithmeticOperator
case object MOD  extends PhraseTag("%")  with ArithmeticOperator

// Compound syntactic domains
case class Program(num_args: IntLit, body: NumExp) extends INode with ELM {
    children = List(num_args, body)
    label = "Program"
    num_args.edgeLabel = "num_args"
    body.edgeLabel = "body"
}

extension (c: ELM)
    def show(): Unit = {
        val printTree = new PrintELM()
        c.accept(printTree)
    }
