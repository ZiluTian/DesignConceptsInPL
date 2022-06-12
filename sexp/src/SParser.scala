package DSL.sexp

import scala.util.parsing.combinator._

class SParser extends RegexParsers {
  override val whiteSpace = "[ \t\r\f\n]+".r
  override def skipWhitespace = true

  def token: Parser[SymbolicToken] = """([^() \t\r\f\n]+)""".r ^^ {n =>
    SymbolicToken(n)
  }

  // An executable sequence is a single command, written as a paranthesized list of subcommands separated by whitespace, could be empty subcommand
  def iNode: Parser[INode] =
    "(" ~ rep(token | iNode) ~ ")" ^^ {
      case a ~ b ~ c => INode(b)
    }
}

object SExpression extends SParser{

    def apply(input: String): Option[INode] = {
        parse(iNode, input) match {
            case Success(i, _) => {
              Some(i)
            }
            case _ =>
                println("Parsing failed")
                None
        }
    }
}