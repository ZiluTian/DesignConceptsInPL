package DSL.sexp

trait SPTree {
    var label: String = ""
    var edgeLabel: String = ""

    def accept(visitor: SPTreeVisitor): Unit = {
        visitor.visit(this)
    }
}

// Leaves
class SymbolicToken extends SPTree {
    var value: String = ""
    override def toString(): String = value

    override def accept(visitor: SPTreeVisitor): Unit = {
        visitor.visit(this)
    }
}

object SymbolicToken {
    def apply(x: String): SymbolicToken = {
        val t = new SymbolicToken()
        t.value = x
        t
    }
}
// Intermediate node is a pair of parentheses surrounding s-expressions that represent the subtrees
class INode extends SPTree {
    var children: List[SPTree] = List()
    override def toString(): String = children.toString

    override def accept(visitor: SPTreeVisitor): Unit = {
        visitor.visit(this)
        children.foreach(i => i.accept(visitor))
    }
}

object INode {
    def apply(x: List[SPTree]): INode = {
        val i = new INode()
        i.children = x
        i
    }
}

extension (c: SPTree)
    def show(): Unit = {
        val printTree = new PrintTree()
        c.accept(printTree)
    }