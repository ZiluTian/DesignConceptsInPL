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
}