package DSL.sexp

class PhraseTag(x: String) extends SymbolicToken {
    value = x
    override def toString(): String = f"$value"
}