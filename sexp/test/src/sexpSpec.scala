package DSL.sexp

import org.scalatest.flatspec.AnyFlatSpecLike

class SPTreeSpec extends AnyFlatSpecLike {
    "Balanced parentheses in S-expression" should "success" in {
        assert(SExpression("((this is) an ((example) (s-expression tree)))").isDefined)
        assert(SExpression("()").isDefined)
    }

    "PrintTree" should "parse the height of the tree correctly" in {
        val ex1 = SExpression("((this is) an ((example) (s-expression tree)))")
        val printTree = new PrintTree()
        ex1.get.accept(printTree)
        assert(printTree.max_height == 3)
    }

    "The show extension for INode" should "print out a tree on stdout" in {
        val ex = SExpression("(if (= (arg 1) 3) (arg 2) 4)") 
        assert(ex.isDefined)
        ex.get.show()
        val ex2 = SExpression("(cond ((and (> (arg 1) 1) (< (arg 1) 10)) 0) (else (* (arg 2) (arg 3))))")
        assert(ex2.isDefined)
        ex2.get.show()

    }

    "Imbalanced parantheses in S-expressions" should "fail" in {
        assert(!SExpression("((this is an ((example) (s-expression tree)))").isDefined)
    }
}