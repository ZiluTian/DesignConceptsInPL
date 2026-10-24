package DSL.el

import org.scalatest.flatspec.AnyFlatSpecLike

class elSpec extends AnyFlatSpecLike {
    "A valid EL program" should "parse" in {
        assert(ELProgram("(el 0 (arg 1))").isDefined)
        assert(ELProgram("(el 0 3))").isDefined)
        assert(ELProgram("(el 0 (arg 2))").isDefined)
        assert(ELProgram("(el 0 (+ (arg 2) (arg 3) (arg 10)))").isDefined)
        assert(ELProgram("(el 0 (if (= (arg 1) 3) (arg 2) 4))").isDefined)
    }

    "Show method of EL" should "print out the EL tree with label" in {
        ELProgram("(el 0 (arg 1))").get.show()
        ELProgram("(el 0 (if (= (arg 1) 3) (arg 2) 4))").get.show()
        ELProgram("(el 0 (+ (arg 2) (arg 3) (arg 10)))").get.show()
    }

    "Arithmetic" should "evaluate n-ary, left-associative expressions" in {
        "(el 2 (+ (arg 1) (arg 2)))"              shouldEvaluateTo (List(3, 4), Some(7))
        "(el 2 (- (arg 1) (arg 2)))"              shouldEvaluateTo (List(10, 4), Some(6))
        "(el 2 (* (arg 1) (arg 2)))"              shouldEvaluateTo (List(6, 7), Some(42))
        "(el 2 (/ (arg 1) (arg 2)))"              shouldEvaluateTo (List(17, 3), Some(5))
        "(el 2 (% (arg 1) (arg 2)))"              shouldEvaluateTo (List(17, 3), Some(2))
        "(el 3 (+ (arg 1) (arg 2) (arg 3)))"      shouldEvaluateTo (List(1, 2, 3), Some(6))
        "(el 3 (- (arg 1) (arg 2) (arg 3)))"      shouldEvaluateTo (List(10, 3, 2), Some(5))
        "(el 1 (+ 2 3 (arg 1)))"                  shouldEvaluateTo (List(4), Some(9))
    }

    "Relational and logical" should "produce booleans and drive conditionals" in {
        "(el 2 (if (= (arg 1) (arg 2)) 1 0))"     shouldEvaluateTo (List(5, 5), Some(1))
        "(el 2 (if (= (arg 1) (arg 2)) 1 0))"     shouldEvaluateTo (List(5, 6), Some(0))
        "(el 2 (if (> (arg 1) (arg 2)) 1 0))"     shouldEvaluateTo (List(9, 2), Some(1))
        "(el 2 (if (< (arg 1) (arg 2)) 1 0))"     shouldEvaluateTo (List(2, 9), Some(1))
        "(el 0 (and true true))"                  shouldEvaluateTo (Nil, None) // a bool is not a valid program body
    }

    "Nested conditionals and inputs" should "compose" in {
        "(el 1 (if (> (arg 1) 0) (arg 1) 0))"     shouldEvaluateTo (List(-4), Some(0))
        "(el 1 (if (> (arg 1) 0) (arg 1) 0))"     shouldEvaluateTo (List(4), Some(4))
        "(el 1 (* (arg 1) (if (= (arg 1) 0) 1 (arg 1))))" shouldEvaluateTo (List(3), Some(9))
    }

    "Errors" should "return None" in {
        "(el 2 (/ (arg 1) (arg 2)))"              shouldEvaluateTo (List(5, 0), None) // div by zero
        "(el 2 (% (arg 1) (arg 2)))"              shouldEvaluateTo (List(5, 0), None) // mod by zero
        "(el 1 (arg 2))"                          shouldEvaluateTo (List(1), None)   // missing arg
        "(el 2 (arg 1))"                          shouldEvaluateTo (List(1, 2, 3), None) // arg count mismatch
        "(el 0 1 2)"                              shouldEvaluateTo (Nil, None)        // bad program text
    }
}