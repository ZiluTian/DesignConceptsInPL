package DSL.fl

import scala.util.parsing.combinator._

// A raw s-expression tree, used as an intermediate representation between the
// concrete syntax and the typed FL AST (see program.scala for the
// interpretation step).
sealed trait Raw
case class RawAtom(text: String) extends Raw
case class RawList(items: List[Raw]) extends Raw

// Reads FL/FLK concrete syntax (s-expressions) into a Raw tree. An atom is any
// maximal run of non-whitespace, non-parenthesis characters (this matches
// literals such as #u/#t/#f, integers, identifiers, and @-operators).
class FlLexer extends RegexParsers {
    override val whiteSpace = "[ \t\r\f\n]+".r
    override def skipWhitespace = true

    def atom: Parser[RawAtom] = """[^() \t\r\f\n]+""".r ^^ (a => RawAtom(a))

    def sExp: Parser[Raw] =
        "(" ~ rep(sExp | atom) ~ ")" ^^ { case _ ~ items ~ _ => RawList(items) } |
            atom ^^ (a => a: Raw)
}
