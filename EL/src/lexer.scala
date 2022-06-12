package DSL.el

import scala.util.parsing.combinator._

class ElLexer extends RegexParsers {
  override val whiteSpace = "[ \t\r\f\n]+".r
  override def skipWhitespace = true

  def naturalNumber: Parser[IntLit] = """(0|[1-9]\d*)""".r ^^ {n =>
    IntLit(n.toInt)
  }

  def integerNumber: Parser[IntLit] = """(-?)(0|[1-9]\d*)""".r ^^ {n =>
    IntLit(n.toInt)
  }

  def arithmeticOperator: Parser[ArithmeticOperator] = """([\\+\\-\\*\\/\\%])""".r ^^ {
    case "+" => ADD
    case "-" => SUB
    case "*" => MULT
    case "/" => DIV
    case "%" => MOD
  }

  def logicalOperator: Parser[LogicalOperator] = """(and)|(or)""".r ^^ {
    case "and" => AND
    case "or" => OR
  }

  def boolLit: Parser[BoolLit] = """(true)|(false)""".r ^^ {
    case "true" => BoolLit(true)
    case "false" => BoolLit(false)
  }

  def relationalOperator: Parser[RelationalOperator] = """([=<>])""".r ^^ {
    case "=" => EQ
    case ">" => GT
    case "<" => LT
  }

  def relationalOperation: Parser[BoolExp] = 
    "(" ~ relationalOperator ~ numExp ~ numExp ~ ")" ^^ {
      case _ ~ op ~ ne1 ~ ne2 ~ _ => RelationalOperation(op, ne1, ne2)
  }

  def logicalOperation: Parser[BoolExp] = 
    "(" ~ logicalOperator ~ boolExp ~ boolExp ~ ")" ^^ {
      case _ ~ op ~ be1 ~ be2 ~ _ => LogicalOperation(op, be1, be2)
  }

  def input: Parser[NumExp] = 
      "(" ~ "arg" ~ naturalNumber ~ ")" ^^ {
        case _ ~ _ ~ num ~ _ => Input(num)
  }

  def arithmeticOperation: Parser[NumExp] = 
      "(" ~ arithmeticOperator ~ numExp ~ numExp ~ rep(numExp) ~ ")" ^^ {
        case _ ~ op ~ ne1 ~ ne2 ~ nes ~ _ => ArithmeticOperation(op, ne1, ne2, nes:_*)
      }

  def conditionExp: Parser[NumExp] = 
      "(" ~ "if" ~ boolExp ~ numExp ~ numExp ~ ")" ^^ {
        case _ ~ _ ~ test ~ ne1 ~ ne2 ~ _ => Conditional(test, ne1, ne2)
      }

  def numExp: Parser[NumExp] = integerNumber | input | arithmeticOperation | conditionExp

  def boolExp: Parser[BoolExp] = boolLit | relationalOperation | logicalOperation

  def program: Parser[Program] =
    "(" ~ "el" ~ naturalNumber ~ numExp ~ ")" ^^ {
      case _ ~ _ ~ argNum ~ exp ~ _ => Program(argNum, exp)
    }
}