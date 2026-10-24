package DSL.flavar

import DSL.fl.{ Val, Err, BoolValue, IntValue, SymValue, UnitValue, PairValue }
import org.scalatest.flatspec.AnyFlatSpecLike

class FLAVARSpec extends AnyFlatSpecLike {

    "A valid FLAVAR program" should "parse" in {
        assert(FlavarProgram("(flavark (x) (set! x 1))").isDefined)
        assert(FlavarProgram("(flavar () (let ((a 3)) (set! a 4)))").isDefined)
        assert(FlavarProgram("(flavar () (list (cell 1) 2))").isDefined)
        assert(FlavarProgram("(flavar (n) n)").isDefined)
    }

    "set! (variable assignment)" should "assign and yield unit" in {
        "(flavar () (let ((a 3)) (set! a 4)))" shouldFlavarEvalTo (Nil, Val(UnitValue))
        // book p.430: (let ((a 3)) (list a (set! a 4) a)) => (3, unit, 4)
        "(flavar () (let ((a 3)) (list a (set! a 4) a)))" shouldFlavarEvalTo (Nil, Val(PairValue(IntValue(3), PairValue(UnitValue, PairValue(IntValue(4), UnitValue)))))
    }

    "set! on an unbound variable" should "return Err" in {
        "(flavar () (set! x 5))" shouldFlavarEvalTo (Nil, Err("unbound variable: x"))
    }

    "Mutation through a closure" should "be visible" in {
        // incr closes over the location of n; each call increments it.
        "(flavar () (let ((n 1)) (let ((incr (lam _ (begin (set! n (@+ n 1)) n)))) (list (app incr #u) (app incr #u) n))))" shouldFlavarEvalTo (Nil, Val(PairValue(IntValue(2), PairValue(IntValue(3), PairValue(IntValue(3), UnitValue)))))
    }

    "letrec (mutual recursion via Figure 8.25)" should "compute even/odd" in {
        val evenodd = "(flavar (n) (letrec ((even? (lam k (if (@= k 0) #t (odd? (@- k 1))))) (odd? (lam k (if (@= k 0) #f (even? (@- k 1)))))) (app even? n)))"
        evenodd shouldFlavarEvalTo (List(10), Val(BoolValue(true)))
        evenodd shouldFlavarEvalTo (List(7),  Val(BoolValue(false)))
        evenodd shouldFlavarEvalTo (List(0),  Val(BoolValue(true)))
    }

    "Mutable cells and mutable variables" should "be orthogonal" in {
        // set! writes the variable x; := writes the cell c; they do not mix.
        "(flavar () (let ((c (cell 1)) (x 10)) (begin (set! x 20) (@:= c 30) (list x (@^ c)))))" shouldFlavarEvalTo (Nil, Val(PairValue(IntValue(20), PairValue(IntValue(30), UnitValue))))
    }

    "Top-level function definition" should "be usable in the body" in {
        // NB: program form is (flavar (I*) Ebody D*) — the body comes before the defs.
        "(flavar () (pair (square 3) (square 4)) (def (square x) (@* x x)))" shouldFlavarEvalTo (Nil, Val(PairValue(IntValue(9), IntValue(16))))
    }

    "Top-level value definition" should "be a mutable location" in {
        "(flavar () (begin (set! counter (@+ counter 1)) counter) (def counter 0))" shouldFlavarEvalTo (Nil, Val(IntValue(1)))
    }

    "Argument-count mismatches" should "return Err" in {
        "(flavar (x y) (@+ x y))"  shouldFlavarEvalTo (List(1), Err("expected 2 argument(s), got 1"))
    }
}
