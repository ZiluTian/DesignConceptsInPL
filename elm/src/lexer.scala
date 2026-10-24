package DSL.elm

import scala.util.parsing.combinator._

class ElmLexer extends RegexParsers {
  override val whiteSpace = "[ \t\r\f\n]+".r
  override def skipWhitespace = true

  def naturalNumber: Parser[IntLit] = """(0|[1-9]\d*)""".r ^^ {n =>
    IntLit(n.toInt)
  }

  def integerNumber: Parser[IntLit] = """(-?)(0|[1-9]\d*)""".r ^^ {n =>
    IntLit(n.toInt)
  }

  def arithmeticOperator: Parser[ArithmeticOperator] = """([+\-*/%])""".r ^^ {
    case "+" => ADD
    case "-" => SUB
    case "*" => MULT
    case "/" => DIV
    case "%" => MOD
  }

  def input: Parser[NumExp] =
      "(" ~ "arg" ~ naturalNumber ~ ")" ^^ {
        case _ ~ _ ~ num ~ _ => Input(num)
      }

  def arithmeticOperation: Parser[NumExp] =
      "(" ~ arithmeticOperator ~ numExp ~ numExp ~ ")" ^^ {
        case _ ~ op ~ ne1 ~ ne2 ~ _ => ArithmeticOperation(op, ne1, ne2)
      }

  def numExp: Parser[NumExp] = integerNumber | input | arithmeticOperation

  def program: Parser[Program] =
    "(" ~ "elm" ~ naturalNumber ~ numExp ~ ")" ^^ {
      case _ ~ _ ~ argNum ~ exp ~ _ => Program(argNum, exp)
    }
}
