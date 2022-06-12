package DSL.sexp

import scala.collection.mutable.ListBuffer

trait SPTreeVisitor {
    def visit(t: SPTree): Unit = ???
}

class PrintTree extends SPTreeVisitor {
    val depth: ListBuffer[Int] = new ListBuffer[Int]() // level of indentation
    depth.append(0)
    var max_height: Int = 0
    var level_indentation: Int = 4 // spaces
    override def visit(t: SPTree): Unit = {
        val current_depth: Int = if (depth.isEmpty) 0 else depth.remove(0)
        val indentation: String = " "* level_indentation * current_depth
        t match {
            case token: SymbolicToken => println(f"$indentation(SToken $t)")
            case iNode: INode => {
                println(f"${indentation}INode")
                depth.prependAll((1 to iNode.children.length).map(_ => current_depth + 1))
                if (current_depth+1 > max_height) {
                    max_height = current_depth + 1
                }
            }
        }
    }
}