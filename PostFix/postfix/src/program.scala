package postfix

import scala.collection.mutable.ListBuffer

class PostfixProgram(input_command: String) extends PostFixLexer{
    val stack = new CommandTokenStack()

    // Keep the convention that args(0) is at the top of the stack
    def withArgs(args: Int*): PostfixProgram = {
        args.reverse.map(i => stack.push(INTEGER(i)))
        this
    }

    def finalResult(): Option[Int] = {
        stack.popInt()
    }

    def run(): Option[Int] = {
        parse(program, input_command) match {
            case Success((INTEGER(expected_args), commandTokens),_) => {
                // println("Parsing successful!")
                if (expected_args != stack.stack.size) {
                    None
                } else {
                    val instructions: ListBuffer[CommandToken] = new ListBuffer[CommandToken]()
                    instructions.appendAll(commandTokens)

                    while (!instructions.isEmpty) {
                        // println(f"Instructions ${instructions} Stack ${stack}")
                        val c = instructions.remove(0)
                        c.run(stack) match {
                            case None => return None
                            case _ => {
                                c match {
                                    case EXEC => 
                                        instructions.prependAll(c.runTimeInstructions())
                                    case _ =>
                                }
                            }
                        }
                    }

                    finalResult()
                }
            }
            case _ => 
                println("Parsing failed!")
                None
        }
    }
}

extension (c: PostfixProgram)
    def shouldEvaluateTo(res: Option[Int]): Unit = {
        assert(res == c.run())
    }