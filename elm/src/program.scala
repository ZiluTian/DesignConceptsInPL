package DSL.elm

object ELMProgram extends ElmLexer {
    def apply(input: String): Option[Program] = {
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
