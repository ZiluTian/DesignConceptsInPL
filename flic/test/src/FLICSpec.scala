package DSL.flic

import DSL.fl.{ Val, Err, BoolValue, IntValue, SymValue, UnitValue, PairValue }
import org.scalatest.flatspec.AnyFlatSpecLike

class FLICSpec extends AnyFlatSpecLike {

    "A valid FLIC program" should "parse" in {
        assert(FlicProgram("(flick (x) (cell x))").isDefined)
        assert(FlicProgram("(flic () (@^ (cell 5)))").isDefined)
        assert(FlicProgram("(flic () (begin 1 2 3))").isDefined)
        assert(FlicProgram("(flic (x) (while (@< x 10) (@:= c 1)))").isDefined)
        assert(FlicProgram("(flic (x) (if (@> x 0) 1))").isDefined)
    }

    "Cell creation and fetch" should "work" in {
        "(flic () (@^ (cell 5)))"  shouldFlicEvalTo (Nil, Val(IntValue(5)))
        "(flic (x) (@^ (cell x)))" shouldFlicEvalTo (List(42), Val(IntValue(42)))
    }

    "Cell assignment (:=)" should "store and yield unit (book example)" in {
        "(flic () (let ((c (cell 1))) (list (@^ c) (@:= c 4) (@^ c))))" shouldFlicEvalTo (Nil, Val(PairValue(IntValue(1), PairValue(UnitValue, PairValue(IntValue(4), UnitValue)))))
    }

    "cell=?" should "compare cell identity (book example)" in {
        "(flic () (let ((c1 (cell 1)) (c2 (cell 1))) (let ((c3 c1)) (list (@cell=? c1 c1) (@cell=? c1 c2) (@cell=? c1 c3)))))" shouldFlicEvalTo (Nil, Val(PairValue(BoolValue(true), PairValue(BoolValue(false), PairValue(BoolValue(true), UnitValue)))))
    }

    "cell?" should "recognize cells (book example)" in {
        "(flic () (pair (@cell? 0) (@cell? (cell 0))))" shouldFlicEvalTo (Nil, Val(PairValue(BoolValue(false), BoolValue(true))))
    }

    "Cell errors" should "return Err" in {
        "(flic () (@^ 3))"        shouldFlicEvalTo (Nil, Err("error:not-a-cell"))
        "(flic () (@:= 3 4))"    shouldFlicEvalTo (Nil, Err("error:not-a-cell"))
        "(flic () (@cell=? 3 4))" shouldFlicEvalTo (Nil, Err("error:not-a-cell"))
    }

    "begin (extended sequencing)" should "evaluate left-to-right and yield the last value" in {
        "(flic () (begin))"      shouldFlicEvalTo (Nil, Val(UnitValue))
        "(flic () (begin 7))"    shouldFlicEvalTo (Nil, Val(IntValue(7)))
        "(flic () (begin 1 2 3))" shouldFlicEvalTo (Nil, Val(IntValue(3)))
        "(flic () (let ((c (cell 0))) (begin (@:= c 1) (@:= c 2) (@^ c))))" shouldFlicEvalTo (Nil, Val(IntValue(2)))
    }

    "elseless if" should "return unit when the test is false" in {
        "(flic (x) (if (@> x 0) 1))" shouldFlicEvalTo (List(5),  Val(IntValue(1)))
        "(flic (x) (if (@> x 0) 1))" shouldFlicEvalTo (List(-5), Val(UnitValue))
    }

    "while" should "loop until the test is false (book's iterative factorial)" in {
        val fact = "(flic (n) (let ((num (cell n)) (ans (cell 1))) (begin (while (@> (@^ num) 0) (begin (@:= ans (@* (@^ num) (@^ ans))) (@:= num (@- (@^ num) 1)))) (@^ ans))))"
        fact shouldFlicEvalTo (List(5),  Val(IntValue(120)))
        fact shouldFlicEvalTo (List(0),  Val(IntValue(1)))
        fact shouldFlicEvalTo (List(7),  Val(IntValue(5040)))
    }

    "Closures capturing cells" should "see mutations" in {
        "(flic () (let ((c (cell 1))) (let ((incr (lam d (begin (@:= c (@+ (@^ c) 1)) (@^ c))))) (list (app incr #u) (app incr #u)))))" shouldFlicEvalTo (Nil, Val(PairValue(IntValue(2), PairValue(IntValue(3), UnitValue))))
    }

    "Bank accounts (Figure 8.10)" should "maintain separate cell state" in {
        // NB: program form is (flic (I*) Ebody D*) — the body comes before the defs.
        val bank = "(flic () (begin (app (app deposit! 17) b) (pair (balance a) (balance b))) (def (make-account amount) (if (@< amount 0) (sym failed) (cell amount))) (def (balance account) (@^ account)) (def (deposit! amount) (abs (account) (if (@< amount 0) (sym failed) (begin (@:= account (@+ amount (@^ account))) (sym succeeded))))) (def a (make-account 100)) (def b (make-account 100)))"
        bank shouldFlicEvalTo (Nil, Val(PairValue(IntValue(100), IntValue(117))))
    }

    "Argument-count mismatches" should "return Err" in {
        "(flic (x y) (@+ x y))"  shouldFlicEvalTo (List(1), Err("expected 2 argument(s), got 1"))
    }
}
