package DSL.elm

import org.scalatest.flatspec.AnyFlatSpecLike

class elmSpec extends AnyFlatSpecLike {
    "A valid ELM program" should "parse" in {
        assert(ELMProgram("(elm 0 5)").isDefined)
        assert(ELMProgram("(elm 2 (+ (arg 1) (arg 2)))").isDefined)
        assert(ELMProgram("(elm 1 (* (arg 1) (arg 1)))").isDefined)
        assert(ELMProgram("(elm 2 (/ (arg 1) (arg 2)))").isDefined)
    }

    "Show method of ELM" should "print out the ELM tree with labels" in {
        ELMProgram("(elm 2 (+ (arg 1) (arg 2)))").get.show()
    }

    "Arithmetic over inputs" should "evaluate" in {
        "(elm 2 (+ (arg 1) (arg 2)))"   shouldEvaluateTo (List(3, 4), Some(7))
        "(elm 2 (- (arg 1) (arg 2)))"   shouldEvaluateTo (List(10, 4), Some(6))
        "(elm 2 (* (arg 1) (arg 2)))"   shouldEvaluateTo (List(6, 7), Some(42))
        "(elm 2 (/ (arg 1) (arg 2)))"   shouldEvaluateTo (List(17, 3), Some(5))
        "(elm 2 (% (arg 1) (arg 2)))"   shouldEvaluateTo (List(17, 3), Some(2))
        "(elm 1 (* (arg 1) (arg 1)))"   shouldEvaluateTo (List(11), Some(121)) // square
        "(elm 0 (+ 10 4))"             shouldEvaluateTo (Nil, Some(14))       // no-arg program
    }

    "Nested expressions" should "compose" in {
        "(elm 1 (+ (* (arg 1) 2) 1))"   shouldEvaluateTo (List(5), Some(11))
        "(elm 2 (- (* (arg 1) (arg 2)) (+ (arg 1) (arg 2))))" shouldEvaluateTo (List(6, 3), Some(9))
    }

    "Things ELM does not have" should "fail to parse" in {
        assert(ELMProgram("(elm 1 (if (> (arg 1) 0) 1 0))").isEmpty) // no conditionals
        assert(ELMProgram("(elm 0 true)").isEmpty)                   // no booleans
    }

    "Errors" should "return None" in {
        "(elm 2 (/ (arg 1) (arg 2)))"   shouldEvaluateTo (List(5, 0), None)    // div by zero
        "(elm 2 (% (arg 1) (arg 2)))"   shouldEvaluateTo (List(5, 0), None)    // mod by zero
        "(elm 1 (arg 2))"               shouldEvaluateTo (List(1), None)       // missing arg
        "(elm 2 (arg 1))"               shouldEvaluateTo (List(1, 2, 3), None) // arg count mismatch
    }
}
