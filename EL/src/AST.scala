package DSL.el

import DSL.sexp._

// Descirbe AST of EL using S-expression
sealed trait EL extends SPTree

sealed trait NumExp extends EL
sealed trait BoolExp extends EL

// Primitive syntactic domains
case class IntLit(n: Int) extends SymbolicToken with NumExp {
    label = "IntVal"
    value = n.toString
}

case class Input(n: IntLit) extends INode with NumExp {
    label = "Input"
    children = List(n)
}

case class ArithmeticOperation(rator: ArithmeticOperator, rand1: NumExp, rand2: NumExp, rest: NumExp*) extends INode with NumExp {
    label = "ArithmeticOperation"
    children = rator :: rand1 :: rand2 :: rest.toList
}

case class Conditional(test: BoolExp, thenExp: NumExp, elseExp: NumExp) extends INode with NumExp {
    label = "Conditional"
    children = List(test, thenExp, elseExp)
}

case class BoolLit(n: Boolean) extends SymbolicToken with BoolExp {
    label = "BoolVal"
    value = n.toString
}

case class RelationalOperation(rator: RelationalOperator, rand1: NumExp, rand2: NumExp) extends INode with BoolExp {
    label = "RelationalOperation"
    children = List(rator, rand1, rand2)
}

case class LogicalOperation(rator: LogicalOperator, rand1: BoolExp, rand2: BoolExp) extends INode with BoolExp {
    label = "LogicalOperation"
    children = List(rator, rand1, rand2)
}

// Phrase tags in EL
case object IF extends PhraseTag("if") with EL
case object ARG extends PhraseTag("arg") with EL
case object ELTag extends PhraseTag("el") with EL

sealed trait ArithmeticOperator extends EL
case object ADD extends PhraseTag("+") with ArithmeticOperator
case object SUB extends PhraseTag("-") with ArithmeticOperator
case object MULT extends PhraseTag("*") with ArithmeticOperator
case object DIV extends PhraseTag("/") with ArithmeticOperator
case object MOD extends PhraseTag("%") with ArithmeticOperator

sealed trait RelationalOperator extends EL
case object EQ extends PhraseTag("=") with RelationalOperator
case object LT extends PhraseTag("<") with RelationalOperator
case object GT extends PhraseTag(">") with RelationalOperator

sealed trait LogicalOperator extends EL
case object AND extends PhraseTag("and") with LogicalOperator
case object OR extends PhraseTag("or") with LogicalOperator

// Compound syntactic domains
case class Program(num_args: IntLit, body: NumExp) extends INode with EL {
    children = List(num_args, body)
    label = "Program"
    num_args.edgeLabel = "num_args"
    body.edgeLabel = "body"
}

extension (c: EL)
    def show(): Unit = {
        val printTree = new PrintEL()
        c.accept(printTree)
    }