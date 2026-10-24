package DSL.flex_s

import DSL.flex._
import org.scalatest.flatspec.AnyFlatSpecLike

class FlexSSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexsErr(input: String): String = {
        flexsCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Parsing (FLEX/S shares FLEX's concrete syntax, Figure 11.31)
    // ------------------------------------------------------------------

    "A valid FLEX/S program" should "parse" in {
        assert(FlexProgram("(flexk () 3)").isDefined)
        assert(FlexProgram("(flex () 3)").isDefined)
        assert(FlexProgram("(foo () 3)").isEmpty) // unknown program tag
    }

    // ------------------------------------------------------------------
    // Subtyping of non-recursive types (Figures 12.1, 12.2)
    // ------------------------------------------------------------------

    "get-age with a superset record (book p.702)" should "accept a record with extra fields" in {
        val prog =
            "(flex () (get-age (record (name (sym Polly_Morwicz)) (age 35) (student? #f)))" +
            " (def get-age (-> ((recordof (age int))) int)" +
            " (abs ((r (recordof (age int)))) (select age r))))"
        prog shouldFlexSCheckTo (FlexOk("int"))
        // In FLEX (no subtyping) the same program is rejected.
        DSL.flex.flexCheck(prog) match {
            case FlexErr(m) => assert(m.contains("the argument has type"))
            case FlexOk(t) => fail(s"expected FLEX to reject the program but got FlexOk($t)")
        }
    }

    "recordof subtyping (book p.703)" should "be covariant in the fields" in {
        // A record with more fields is a subtype of one with fewer.
        "(flexk () (the (recordof (a int)) (record (a 1) (b #t))))" shouldFlexSCheckTo
            (FlexOk("(recordof (a int))"))
        // ... but not in the other direction.
        assert(flexsErr("(flexk () (the (recordof (a int) (b bool)) (record (a 1))))")
            .contains("is not a subtype"))
        // Field types must be covariant as well.
        flexsErr("(flexk () (the (recordof (a int)) (record (a #t) (b #f))))")
    }

    "pairof subtyping (book p.703)" should "be covariant in both components" in {
        "(flexk () (the (pairof int (recordof (a int))) (pair 1 (record (a 2) (b #t)))))" shouldFlexSCheckTo
            (FlexOk("(pairof int (recordof (a int)))"))
        // A base-type mismatch in one component is rejected.
        flexsErr("(flexk () (the (pairof int int) (pair #t 2)))")
    }

    "listof subtyping (book p.703)" should "be covariant in the element type" in {
        "(flexk () (the (listof (recordof (a int)))" +
            " (cons (record (a 1) (b #t)) (null (recordof (a int))))))" shouldFlexSCheckTo
            (FlexOk("(listof (recordof (a int)))"))
        // The head must be a subtype of the tail's element type.
        flexsErr("(flexk () (cons (record (a 1) (b #t)) (null int)))")
    }

    "oneof subtyping (book p.703)" should "accept a subtype with fewer tags" in {
        "(flexk () (the (oneof (a int) (b bool) (c int)) (one (oneof (a int) (b bool)) a 5)))" shouldFlexSCheckTo
            (FlexOk("(oneof (a int) (b bool) (c int))"))
        // A tag absent from the ascribed oneof is rejected.
        flexsErr("(flexk () (the (oneof (a int)) (one (oneof (a int) (b bool)) b #t)))")
        // Payload types are covariant in the common tags.
        "(flexk () (one (oneof (a (recordof (x int)))) a (record (x 1) (y 2))))" shouldFlexSCheckTo
            (FlexOk("(oneof (a (recordof (x int))))"))
    }

    "arrow subtyping (book p.704)" should "be contravariant in the arguments and covariant in the result" in {
        // Contravariant: a procedure taking a narrower record is a subtype
        // of one taking a wider record.
        "(flexk () (the (-> ((recordof (age int) (name symb))) int)" +
            " (abs ((r (recordof (age int)))) (select age r))))" shouldFlexSCheckTo
            (FlexOk("(-> ((recordof (age int) (name symb))) int)"))
        // ... and not in the other direction.
        flexsErr(
            "(flexk () (the (-> ((recordof (age int))) int)" +
            " (abs ((r (recordof (age int) (name symb)))) (select age r))))")
        // Covariant result: a procedure returning a superset record is a
        // subtype of one returning a subset record.
        "(flexk () (the (-> (int) (recordof (a int)))" +
            " (abs ((x int)) (record (a x) (b #t)))))" shouldFlexSCheckTo
            (FlexOk("(-> (int) (recordof (a int)))"))
        // End to end: the contravariance is what makes the call safe.
        "(flexk () (let ((pick-age (abs ((r (recordof (age int)))) (select age r))))" +
            " (let ((f (the (-> ((recordof (age int) (name symb))) int) pick-age)))" +
            " (f (record (age 35) (name (sym Polly)))))))" shouldFlexSCheckTo
            (FlexOk("int"))
    }

    // ------------------------------------------------------------------
    // cellof invariance (book p.705)
    // ------------------------------------------------------------------

    "cellof subtyping (book p.705)" should "keep the content type invariant" in {
        // Equivalent content types are fine.
        "(flexk () (:= (cell (record (a 1) (b #t))) (record (a 2) (b #f))))" shouldFlexSCheckTo
            (FlexOk("unit"))
        // The book's soundness counterexample: with a covariant cellof rule
        // this program would type-check, yet it leads to a dynamic type
        // error (stuffit shrinks the record stored in c, then (select b ...)
        // fails). Invariance makes the call (stuffit c) ill typed.
        val prog =
            "(flexk () (let ((stuffit (abs ((r (cellof (recordof (a int)))))" +
            " (:= r (record (a 2)))))" +
            " (c (cell (record (a 1) (b #t)))))" +
            " (begin (stuffit c) (select b (^ c)))))"
        assert(flexsErr(prog).contains("the argument has type"))
        // := requires the value's type to be a subtype of the content type;
        // invariance then forces the two to be equivalent.
        flexsErr("(flexk () (:= (cell (record (a 1) (b #t))) (record (a 2))))")
    }

    // ------------------------------------------------------------------
    // Subtyping of recursive types (Figure 12.4, book p.706)
    // ------------------------------------------------------------------

    "recursive types (book p.706)" should "establish Trs ≤ Trt and Tru ≤ Trv" in {
        // Trs = (trec s (pairof Tab s)), Trt = (trec t (pairof Ta t)),
        // with Tab = (recordof (a int) (b bool)) a subtype of Ta =
        // (recordof (a int)): infinite lists of pairs, covariant.
        "(flexk () (the (trec t (pairof (recordof (a int)) t))" +
            " (error done (trec s (pairof (recordof (a int) (b bool)) s)))))" shouldFlexSCheckTo
            (FlexOk("(trec t (pairof (recordof (a int)) t))"))
        // Tru = (trec u (pairof Tab (-> (Ta) u))), Trv = (trec v (pairof Ta
        // (-> (Tab) v))): covariant first component, contravariant arrow
        // argument, covariant (assumed) result.
        "(flexk () (the (trec v (pairof (recordof (a int)) (-> ((recordof (a int) (b bool))) v)))" +
            " (error done (trec u (pairof (recordof (a int) (b bool)) (-> ((recordof (a int))) u))))))" shouldFlexSCheckTo
            (FlexOk("(trec v (pairof (recordof (a int)) (-> ((recordof (a int) (b bool))) v)))"))
        // The reversed direction is not a subtyping.
        flexsErr(
            "(flexk () (the (trec s (pairof (recordof (a int) (b bool)) s))" +
            " (error done (trec t (pairof (recordof (a int)) t)))))")
    }

    // ------------------------------------------------------------------
    // The inclusion rule at the expression match points (Figure 12.1)
    // ------------------------------------------------------------------

    "if branches (Figure 12.1)" should "unify on a common supertype" in {
        "(flexk () (if #t (record (a 1)) (record (a 2) (b #t))))" shouldFlexSCheckTo
            (FlexOk("(recordof (a int))"))
        // Base types admit no nontrivial subtyping.
        flexsErr("(flexk () (if #t 1 #f))")
    }

    "seq components (Figure 12.1)" should "unify on a common supertype" in {
        "(flexk () (seq (record (a 1)) (record (a 2) (b #t))))" shouldFlexSCheckTo
            (FlexOk("(seqof (recordof (a int)))"))
    }

    "tagcase clause results (Figure 12.1)" should "unify on a common supertype" in {
        "(flexk () (tagcase (one (oneof (a int) (b bool)) a 1) x" +
            " (a (the (recordof (v int)) (record (v x))))" +
            " (b (the (recordof (v int) (w bool)) (record (v 0) (w x))))))" shouldFlexSCheckTo
            (FlexOk("(recordof (v int))"))
    }

    "set! (Figure 11.21 + 12.1)" should "accept a subtype value" in {
        // A record with extra fields is assignable to a narrower record.
        "(flexk () (let ((r (record (a 1)))) (set! r (record (a 2) (b #t)))))" shouldFlexSCheckTo
            (FlexOk("unit"))
        flexsErr("(flexk () (let ((x 1)) (set! x #t)))")
    }

    "a top-level def (Figures 11.2 + 12.1)" should "allow a subtype in the definition" in {
        // Contravariance: the definition's procedure takes a narrower record
        // (a subtype of the declared formal-parameter type), which is safe:
        // a caller that follows the declared type passes a wider record,
        // which the definition can use.
        "(flex () (id (record (a 3) (b #t)))" +
            " (def id (-> ((recordof (a int) (b bool))) int)" +
            " (abs ((x (recordof (a int)))) (select a x))))" shouldFlexSCheckTo
            (FlexOk("int"))
        // ... but the other direction is not safe, and is rejected.
        flexsErr(
            "(flex () (id (record (a 3)))" +
            " (def id (-> ((recordof (a int))) int)" +
            " (abs ((x (recordof (a int) (b bool)))) (select a x))))")
    }

    // ------------------------------------------------------------------
    // FLEX regression: FLEX/S is a superset of FLEX
    // ------------------------------------------------------------------

    "FLEX programs (superset property)" should "still type-check under FLEX/S" in {
        // The pos?/even? example (book p.636).
        "(flex ((b bool) (i int)) (if b (pos? i) (even? i))" +
            " (def-type intfun (-> (int) int))" +
            " (def-type intpred (-> (int) bool))" +
            " (def dec intfun (abs ((x int)) (- x 1)))" +
            " (def pos? intpred (abs ((y int)) (> y 0)))" +
            " (def even? intpred (abs ((x int)) (if (= x 0) #t (odd? (dec x)))))" +
            " (def odd? intpred (abs ((y int)) (if (= y 0) #f (even? (dec y))))))" shouldFlexSCheckTo
            (FlexOk("(=> (bool int) bool)"))
        // The equirecursively equivalent Tib1–Tib4 chain (book Figure 11.26)
        // still type-checks via [equiv-≤].
        "(flex () (the Tib1 (the Tib2 (the Tib3 (the Tib4 (error done Tib1)))))" +
            " (def-type Tib1 (trec iblist (pairof int (pairof bool iblist))))" +
            " (def-type Tib2 (trec int-bool-list (pairof int (pairof bool int-bool-list))))" +
            " (def-type Tib3 (pairof int (pairof bool (trec iblist (pairof int (pairof bool iblist))))))" +
            " (def-type Tib4 (pairof int (trec bilist (pairof bool (pairof int bilist))))))" shouldFlexSCheckTo
            (FlexOk("(trec iblist (pairof int (pairof bool iblist)))"))
    }
}
