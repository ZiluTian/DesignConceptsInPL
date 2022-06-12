package DSL.sexp

import org.scalatest.flatspec.AnyFlatSpecLike

class SPTreeSpec extends AnyFlatSpecLike {
    "Balanced parentheses in S-expression" should "success" in {
        assert(SExpression("((this is) an ((example) (s-expression tree)))").run().isDefined)
        assert(SExpression("()").run().isDefined)
    }

    "PrintTree" should "parse the height of the tree correctly" in {
        val ex1 = SExpression("((this is) an ((example) (s-expression tree)))").run()
        val printTree = new PrintTree()
        ex1.get.accept(printTree)
        assert(printTree.max_height == 3)
    }

    "Imbalanced parantheses in S-expressions" should "fail" in {
        assert(!SExpression("((this is an ((example) (s-expression tree)))").run().isDefined)
    }
}