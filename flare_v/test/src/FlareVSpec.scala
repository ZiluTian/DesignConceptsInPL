package DSL.flare_v

import org.scalatest.flatspec.AnyFlatSpecLike
import DSL.flex.{FlexResult, FlexOk, FlexErr}
import DSL.flare.flareRecon

class FlareVSpec extends AnyFlatSpecLike {

    "Parsing" should "accept a set! program" in {
        assert(flareVRecon("(flare () (let ((x 1)) (set! x 2)))") == FlexOk("unit"))
    }

    it should "reject a set! with the wrong arity (parse error)" in {
        "(flare () (set! x))" shouldFlareVReconFail("parse error")
    }

    it should "reject set! as a binding name (parse error)" in {
        "(flare () (set! set! 1))" shouldFlareVReconFail("parse error")
    }

    it should "reject set! on a non-variable with a type error" in {
        "(flare () (set! 1 2))" shouldFlareVReconFail("unbound variable: 1")
    }

    "The set! construct" should "assign to a let-bound variable and yield unit" in {
        "(flare () (let ((x 1)) (set! x 2)))" shouldFlareVReconTo FlexOk("unit")
    }

    it should "assign to a program formal" in {
        "(flarek (x) (set! x 1))" shouldFlareVReconTo FlexOk("(=> (int) unit)")
    }

    it should "reject a value that does not match the variable's type" in {
        "(flare () (let ((x 1)) (set! x #t)))" shouldFlareVReconFail("type reconstruction failed")
    }

    it should "reject an unbound target" in {
        "(flarek () (set! x 1))" shouldFlareVReconFail("unbound variable: x")
    }

    it should "assign to a standard-library name (monomorphic via the restriction)" in {
        "(flare () (set! + (abs (x y) (+ x y))))" shouldFlareVReconTo FlexOk("unit")
    }

    it should "reject a set! whose target is shadowed by an inner, unassigned generic binding" in {
        // The inner let binds g (a pure definition, not assigned in its body,
        // hence generic); the set! in its body targets that inner g -- which
        // the soundness restriction keeps monomorphic, so this reduces to the
        // ordinary type error below. (Assignment to a *generic* schema is
        // itself unreachable: a set! targeting a binding makes that binding
        // monomorphic by construction, so the "polymorphic variable" branch of
        // the set! rule is purely defensive.)
        "(flarek () (let ((g 1)) (let ((g (abs (z) z))) (set! g 2))))" shouldFlareVReconFail(
            "type reconstruction failed")
    }

    it should "type-check a value in a branch that is not taken" in {
        "(flarek () (let ((x 1)) (if #f (set! x #t) x)))" shouldFlareVReconFail("type reconstruction failed")
    }

    "The soundness restriction (Section 13.5.2, Exercise 13.11)" should
        "reject the Ex 13.11b counterexample (f must stay monomorphic)" in {
        "(flarek () (let ((f (abs (x) x))) (begin (set! f (abs (y) (prim + y 1))) (if (f #t) 1 (f 2)))))" shouldFlareVReconFail(
            "type reconstruction failed")
    }

    it should "accept the same program when the call matches the assigned type" in {
        "(flarek () (let ((x (abs (z) z))) (begin (set! x (abs (y) (prim + y 1))) (x 2))))" shouldFlareVReconTo FlexOk("int")
    }

    it should "keep a name monomorphic when it is assigned in an inner let's definition" in {
        // The set! in y's definition (a parallel-let definition sees the outer
        // environment) targets the OUTER x, so x must not be generalized.
        "(flarek () (let ((x (abs (z) z))) (let ((y (set! x (abs (w) w)))) (prim pair y y))))" shouldFlareVReconTo FlexOk(
            "(pairof unit unit)")
    }

    it should "target the letrec's own binding for a set! in a definition" in {
        "(flarek () (letrec ((x (abs (z) z)) (y (set! x (abs (w) w)))) (prim pair x y)))" shouldFlareVReconTo FlexOk(
            "(pairof (-> (T1) T1) unit)")
    }

    "Mutable variables in sugar contexts" should "work with def definitions" in {
        "(flare () (let ((c 1)) (begin (set! c (twice c)) c)) (def twice (abs (x) (+ x x))))" shouldFlareVReconTo FlexOk(
            "int")
    }

    it should "work with top-level def names" in {
        "(flare () (let ((c counter)) (begin (set! counter c) counter)) (def counter 0))" shouldFlareVReconTo FlexOk(
            "int")
    }

    it should "work with letrec bindings" in {
        "(flarek () (letrec ((n 1) (inc (abs () (prim + n 1)))) (begin (set! n (inc)) n)))" shouldFlareVReconTo FlexOk(
            "int")
    }

    it should "respect shadowing (the inner binding is the target)" in {
        "(flarek () (let ((x 1)) (let ((x 2)) (begin (set! x 3) x))))" shouldFlareVReconTo FlexOk("int")
    }

    "The Fig 17.4 revmap program" should "have type (=> (int int) (listof bool))" in {
        "(flare (a b) (let ((revmap (abs (f elts) (let ((ans (null))) (recur loop ((xs elts)) (if (null? xs) ans (begin (set! ans (cons (f (car xs)) ans)) (loop (cdr xs))))))))) (revmap (abs (x) (> x b)) (list a (* a 7)))))" shouldFlareVReconTo FlexOk(
            "(=> (int int) (listof bool))")
    }

    "Theorem: FLARE/V extends FLARE" should "agree with FLARE on every program without set!" in {
        // Accepted programs: the displayed type must be IDENTICAL to FLARE's.
        val accepted = List(
            "(flare () 1)" -> "int",
            "(flare () (let ((f (abs (x) x))) (f 1)))" -> "int",
            "(flare () (let ((f (abs (x) x))) (begin (f 1) (f #t))))" -> "bool",
            "(flarek (x y) (prim + x y))" -> "(=> (int int) int)",
            "(flare () (if #t 1 2))" -> "int",
            "(flare () (let ((p (pair 1 #t))) (snd p)))" -> "bool",
            "(flare () (list 1 2 3))" -> "(listof int)",
            "(flare () (let ((c (cell 0))) (begin (:= c 1) (^ c))))" -> "int"
        )
        for ((p, expected) <- accepted) {
            val v = flareVRecon(p)
            assert(v == FlexOk(expected), s"FLARE/V gave $v for: $p")
            assert(flareRecon(p) == FlexOk(expected), s"FLARE gave ${flareRecon(p)} for: $p")
        }
        // Ill-typed programs: both systems reject.
        val rejected = List(
            "(flarek () (let ((x 1)) (x)))",
            "(flare () (prim + 1))",
            "(flare () (let ((f (abs (x) x))) (f 1 #t)))"
        )
        for (p <- rejected) {
            val v = flareVRecon(p)
            val f = flareRecon(p)
            assert(v.isInstanceOf[FlexErr], s"FLARE/V accepted $p but expected a type error")
            assert(f.isInstanceOf[FlexErr], s"FLARE accepted $p but expected a type error")
        }
        // FLARE/V additionally accepts set! programs that FLARE cannot even parse.
        assert(flareRecon("(flare () (let ((x 1)) (set! x 2)))").isInstanceOf[FlexErr])
        assert(flareVRecon("(flare () (let ((x 1)) (set! x 2)))") == FlexOk("unit"))
    }
}
