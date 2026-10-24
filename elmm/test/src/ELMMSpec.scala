package DSL.elmm

import org.scalatest.flatspec.AnyFlatSpecLike

class elmmSpec extends AnyFlatSpecLike {
    "A valid ELMM program" should "parse" in {
        assert(ELMMProgram("(elmm 5)").isDefined)
        assert(ELMMProgram("(elmm -5)").isDefined)
        assert(ELMMProgram("(elmm (+ 10 4))").isDefined)
        assert(ELMMProgram("(elmm (- 10 4))").isDefined)
        assert(ELMMProgram("(elmm (* (+ 2 3) 4))").isDefined)
        assert(ELMMProgram("(elmm (+ (* (- 5 1) 2) (/ 21 7)))").isDefined)
    }

    "Show method of ELMM" should "print out the ELMM tree with labels" in {
        ELMMProgram("(elmm 5)").get.show()
        ELMMProgram("(elmm (+ (* (- 5 1) 2) (/ 21 7)))").get.show()
    }

    "Arithmetic" should "evaluate binary, nested expressions" in {
        "(elmm 5)"                     shouldEvaluateTo Some(5)
        "(elmm -5)"                    shouldEvaluateTo Some(-5)
        "(elmm (+ 10 4))"              shouldEvaluateTo Some(14)
        "(elmm (- 10 4))"              shouldEvaluateTo Some(6)
        "(elmm (* 6 7))"               shouldEvaluateTo Some(42)
        "(elmm (/ 17 3))"              shouldEvaluateTo Some(5)
        "(elmm (% 17 3))"              shouldEvaluateTo Some(2)
        "(elmm (+ (* (- 5 1) 2) (/ 21 7)))" shouldEvaluateTo Some(11) // book, Fig 3.9
        "(elmm (/ 100 (* (- 7 4) (+ 5 6))))"  shouldEvaluateTo Some(3) // book, Fig 3.9
    }

    "Things ELMM does not have" should "fail to parse" in {
        assert(ELMMProgram("(elmm (arg 1))").isEmpty)      // no inputs
        assert(ELMMProgram("(elmm (if (= 1 1) 0 4))").isEmpty) // no conditionals
        assert(ELMMProgram("(elmm true)").isEmpty)         // no booleans
        assert(ELMMProgram("(elmm (+ 1 2 3))").isEmpty)    // arithmetic is binary
        assert(ELMMProgram("(elmm 1 2)").isEmpty)          // a program is one expression
    }

    "Errors" should "return None" in {
        "(elmm (/ 5 0))"  shouldEvaluateTo None // div by zero
        "(elmm (% 5 0))"  shouldEvaluateTo None // mod by zero
    }
}
