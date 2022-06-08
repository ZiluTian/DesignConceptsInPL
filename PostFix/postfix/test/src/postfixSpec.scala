package postfix

import org.scalatest.flatspec.AnyFlatSpecLike

class postfixSpec extends AnyFlatSpecLike {

    "Binary operations (sub, add, eq, div, rem, lt, gt)" should "pop two values from the stack and apply the binary operation" in {
        PostfixProgram("(postfix 0 4 7 sub)") shouldEvaluateTo Some(-3)
        PostfixProgram("(postfix 1 4 sub)") withArgs (3) shouldEvaluateTo Some(-1)
        PostfixProgram("(postfix 3 4000 swap pop add)") withArgs (300, 20, 1) shouldEvaluateTo Some(4020)
        PostfixProgram("(postfix 1 3 div)") withArgs (17) shouldEvaluateTo Some(5)
        PostfixProgram("(postfix 1 3 rem)") withArgs (17) shouldEvaluateTo Some(2)
        PostfixProgram("(postfix 0 1 1 eq 2 3 eq add)") shouldEvaluateTo Some(1)
        PostfixProgram("(postfix 1 4 lt)") withArgs (3) shouldEvaluateTo Some(1)
        PostfixProgram("(postfix 1 4 gt)") withArgs (5) shouldEvaluateTo Some(1)
    }

    "Swap" should "change the position of top two elements on the stack" in {
        PostfixProgram("(postfix 0 1 swap)")  shouldEvaluateTo None
        PostfixProgram("(postfix 0 100 98 99 swap)")  shouldEvaluateTo Some(98)
        PostfixProgram("(postfix 2 swap)") withArgs (3, 4) shouldEvaluateTo Some(4)
        PostfixProgram("(postfix 3 pop swap)") withArgs (3, 4, 5) shouldEvaluateTo Some(5)
    }

    "Select" should "selects two values based on a test value (any non-zero integer is true)" in {
        PostfixProgram("(postfix 1 2 3 sel)") withArgs(1)  shouldEvaluateTo Some(2)
        PostfixProgram("(postfix 1 2 3 sel)") withArgs(0)  shouldEvaluateTo Some(3)
        PostfixProgram("(postfix 1 2 3 sel)") withArgs(17)  shouldEvaluateTo Some(2)
        PostfixProgram("(postfix 1 2 3 sel)") withArgs(-10)  shouldEvaluateTo Some(2)
    }

    "NGET" should "Pop v_index off the stack and copy stack(v_index-1) to top of the stack, if applicable" in {
        PostfixProgram("(postfix 2 1 nget)") withArgs(4, 5)  shouldEvaluateTo Some(4)
        PostfixProgram("(postfix 2 2 nget)") withArgs(4, 5)  shouldEvaluateTo Some(5)
        PostfixProgram("(postfix 2 3 nget)") withArgs(4, 5)  shouldEvaluateTo None
        PostfixProgram("(postfix 2 0 nget)") withArgs(4, 5)  shouldEvaluateTo None
        PostfixProgram("(postfix 1 (2 mul) 1 nget)") withArgs(3)  shouldEvaluateTo None
    }

    "EXEC" should "Pop the executable sequence from the top of the stack and prepend its components to the seq of currently executing commands" in {
        PostfixProgram("(postfix 1 (2 mul) exec)") withArgs(7)  shouldEvaluateTo Some(14)
        PostfixProgram("(postfix 0 (0 swap sub) 7 swap exec)")   shouldEvaluateTo Some(-7)
        PostfixProgram("(postfix 0 (2 mul))") shouldEvaluateTo None
        PostfixProgram("(postfix 0 3 (2 mul) gt)") shouldEvaluateTo None
        PostfixProgram("(postfix 0 3 exec)") shouldEvaluateTo None
        PostfixProgram("(postfix 2 (2 (3 mul add) exec) 1 swap exec sub)") withArgs(4, 5)  shouldEvaluateTo Some(-3)
        PostfixProgram("(postfix 0 (7 swap exec) (0 swap sub) swap exec)") shouldEvaluateTo Some(-7)
    }

    "Calculate square" should "return the right value" in {
        PostfixProgram("(postfix 1 1 nget mul)") withArgs(5)  shouldEvaluateTo Some(25)
        PostfixProgram("(postfix 1 1 nget mul)") withArgs(11)  shouldEvaluateTo Some(121)
        PostfixProgram("(postfix 1 1 nget mul)") withArgs(100)  shouldEvaluateTo Some(10000)
        PostfixProgram("(postfix 1 1 nget mul)") withArgs(-7)  shouldEvaluateTo Some(49)
    }

    "Given a, b, c, x, calculate ax^2+bx+c" should "return the right value" in {
        PostfixProgram("(postfix 4 4 nget 5 nget mul mul swap 4 nget mul add add)") withArgs(3, 4, 5, 2)  shouldEvaluateTo Some(25)
    }

    "Given a, b, calculate b-a*b^2" should "return the right value" in {
        PostfixProgram("(postfix 2 (mul sub) (1 nget mul) 4 nget swap exec swap exec)") withArgs(-10, 2)  shouldEvaluateTo Some(42)
    }

    "Calculate the absolute number" should "return the right value" in {
        PostfixProgram("(postfix 1 1 nget 0 lt (0 swap sub) () sel exec)") withArgs(-7)  shouldEvaluateTo Some(7)
        PostfixProgram("(postfix 1 1 nget 0 lt (0 swap sub) () sel exec)") withArgs(6)  shouldEvaluateTo Some(6)
    }

    "Wrong number of arguments, divide by 0, parsing error" should "return error (None)" in {
        PostfixProgram("(postfix 1 4 mul add)") withArgs (3) shouldEvaluateTo None
        PostfixProgram("(postfix 2 4 sub div)") withArgs (4, 5) shouldEvaluateTo None
        PostfixProgram("(postfix 2 swap)") withArgs (3) shouldEvaluateTo None
        PostfixProgram("(postfix 0 1 swap)") shouldEvaluateTo None
        PostfixProgram("(postfix 0 1 pop pop)") shouldEvaluateTo None
        PostfixProgram("(postfix 1 pop)") withArgs (4, 5) shouldEvaluateTo None
        PostfixProgram("(postfix 1 pop") withArgs (4) shouldEvaluateTo None
    }
}