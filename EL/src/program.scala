package DSL.el

object ELProgram extends ElLexer {
    def apply(input: String): Option[EL] = {
        parse(program, input) match {
            case Success(x, _) => 
                Some(x)
            case Failure(x, _) => 
                println("Parsing failed! " + x)
                None
            case Error(x, _) => 
                println("Parsing error! " + x)
                None
        }
    }
}