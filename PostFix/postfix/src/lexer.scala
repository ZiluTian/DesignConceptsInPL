package postfix

import scala.util.parsing.combinator._

class PostFixLexer extends RegexParsers {
  override val whiteSpace = "[ \t\r\f\n]+".r
  override def skipWhitespace = true

  def lparen: Parser[CommandToken] = "(" ^^ { _ => LPAREN }
  def rparen: Parser[CommandToken] = ")" ^^ { _ => RPAREN }

  def naturalNumber: Parser[CommandToken] = """(0|[1-9]\d*)""".r ^^ {n =>
    INTEGER(n.toInt)
  }

  def integerNumber: Parser[CommandToken] = """(-?)(0|[1-9]\d*)""".r ^^ {n =>
    INTEGER(n.toInt)
  }

  def command: Parser[CommandToken] = """([a-z]+)""".r ^^ {
    case "add" => ADD
    case "div" => DIV
    case "eq" => EQ
    case "exec" => EXEC
    case "gt" => GT
    case "lt" => LT
    case "mul" => MUL
    case "nget" => NGET
    case "pop" => POP
    case "rem" => REM
    case "sel" => SEL
    case "sub" => SUB
    case "swap" => SWAP
  }

  // An executable sequence is a single command, written as a paranthesized list of subcommands separated by whitespace, could be empty subcommand
  def executableSeq: Parser[CommandToken] =
    lparen ~ rep(command | integerNumber | executableSeq) ~ rparen ^^ {
      case a ~ b ~ c => EXECUTABLE(b)
    }

  // A PostFix program is a parenthesized seq. consisting of the token postfix, followed by a natural naturalNumber, and zero or more commands
  def program: Parser[(CommandToken, List[CommandToken])] =
    lparen ~ "postfix" ~ naturalNumber ~ rep(command | integerNumber | executableSeq) ~ rparen ^^ {
      case a ~ b ~ c ~ d ~ e => (c, d)
    }
}