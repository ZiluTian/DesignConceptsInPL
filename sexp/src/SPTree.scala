package DSL.sexp

trait SPTree {
    var label: String = ""
    var edgeLabel: String = ""

    def accept(visitor: SPTreeVisitor): Unit = {
        visitor.visit(this)
    }
}

// Leaves
case class SymbolicToken(x: String) extends SPTree {
    override def toString(): String = x

    override def accept(visitor: SPTreeVisitor): Unit = {
        visitor.visit(this)
    }
}

// Intermediate node is a pair of parentheses surrounding s-expressions that represent the subtrees
case class INode(x: List[SPTree]) extends SPTree {
    override def toString(): String = x.toString

    override def accept(visitor: SPTreeVisitor): Unit = {
        visitor.visit(this)
        x.foreach(i => i.accept(visitor))
    }
}

extension (c: INode)
    def show(): Unit = {
        val printTree = new PrintTree()
        c.accept(printTree)
    }