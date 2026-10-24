package DSL.flex_p

import DSL.flex._
import DSL.flex_sp.FlexSPProgram
import org.scalatest.flatspec.AnyFlatSpecLike

class FlexPSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexpErr(input: String): String = {
        flexpCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Parsing (FLEX/P reuses the FLEX/SP parser: the book defines the
    // variant at the type-system level only, with no flex/P tag)
    // ------------------------------------------------------------------

    "A valid FLEX/P program" should "parse" in {
        assert(FlexSPProgram("(flexk/SP () 3)").isDefined)
        assert(FlexSPProgram("(flex/SP () 3)").isDefined)
        assert(FlexSPProgram("(flex/SP () ((pcall (pabs (t) (abs ((x t)) x)) int) 3))").isDefined)
        // The plain FLEX tag is not a FLEX/P (FLEX/SP) tag.
        assert(FlexSPProgram("(flex () 3)").isEmpty)
    }

    // ------------------------------------------------------------------
    // Universal polymorphism (Figure 12.9)
    // ------------------------------------------------------------------

    "EpolyId (book Figure 12.10)" should "type-check to int" in {
        "(flexk/SP () (let ((id (pabs (t) (abs ((x t)) x))))" +
            " (if ((pcall id bool) #t)" +
            " 1" +
            " (((pcall id (-> (int) int)) (pcall id int)) 2))))" shouldFlexPCheckTo (FlexOk("int"))
    }

    "a polymorphic value projected onto an enclosing pabs variable" should "type-check" in {
        "(flexk/SP () (pabs (t) (let ((id (pabs (u) (abs ((x u)) x))))" +
            " ((pcall id (-> (t) t)) (pcall id t) (abs ((x t)) x)))))" shouldFlexPCheckTo
            (FlexOk("(forall (t) (-> (t) t))"))
    }

    "pcall (Figure 12.9)" should "reject a wrong number of type arguments" in {
        flexpErr("(flexk/SP () (pcall (pabs (t u) (abs ((x t)) x)) int))")
        // A monomorphic value is not a polymorphic value.
        flexpErr("(flexk/SP () (pcall (abs ((x int)) x) int))")
    }

    "the import restriction (book p.732)" should "reject polytest" in {
        // The inner pabs would capture the outer pabs' t (used in x's
        // type), so polytest cannot have the type (forall (t) (-> (t)
        // (forall (t) t))).
        val prog =
            "(flex/SP () #u (def polytest (forall (t) (-> (t) (forall (t) t)))" +
                " (pabs (t) (abs ((x t)) (pabs (t) x)))))"
        assert(flexpErr(prog).contains("import restriction"))
    }

    "the purity restriction (Figure 12.9)" should "reject a pabs body that mutates" in {
        val prog = "(flexk/SP () (let ((c (cell 1))) (pabs (t) (:= c 2))))"
        assert(flexpErr(prog).contains("purity restriction"))
        // set! is rejected too.
        flexpErr("(flexk/SP () (let ((x 1)) (pabs (t) (set! x 2))))")
    }

    // ------------------------------------------------------------------
    // The [forall-approx] type rule (Figure 12.9)
    // ------------------------------------------------------------------

    "forall types (Figure 12.9)" should "compare up to alpha-renaming" in {
        // [forall-approx] at a the-ascription.
        "(flexk/SP () (the (forall (t) (-> (t) t)) (pabs (u) (abs ((x u)) x))))" shouldFlexPCheckTo
            (FlexOk("(forall (t) (-> (t) t))"))
        // ... in the other direction as well.
        "(flexk/SP () (the (forall (u) (-> (u) u)) (pabs (t) (abs ((x t)) x))))" shouldFlexPCheckTo
            (FlexOk("(forall (u) (-> (u) u))"))
        // [forall-approx] at the def match point: the declared type binds
        // t, the body binds u — accepted up to alpha-renaming. (The def's
        // value is applied only after a pcall projection, per FLEX/P.)
        "(flex/SP () ((pcall id int) 3)" +
            " (def id (forall (t) (-> (t) t)) (pabs (u) (abs ((x u)) x))))" shouldFlexPCheckTo
            (FlexOk("int"))
        // A body that is not equivalent is rejected.
        flexpErr(
            "(flexk/SP () (the (forall (t) (-> (t) (trec x (pairof t x))))" +
                " (pabs (t) (abs ((x t)) (pair x (abs ((y t)) y))))))")
    }

    // ------------------------------------------------------------------
    // Equivalence, not subtyping: what separates FLEX/P from FLEX/SP
    // (FLEX/SP accepts these same programs; FLEX/P rejects them)
    // ------------------------------------------------------------------

    "a type ascription" should "require equivalence, not subtyping" in {
        // (recordof (a int) (b int)) is a proper subtype of
        // (recordof (a int)) — FLEX/S accepts the ascription, FLEX/P does
        // not.
        val msg = flexpErr("(flexk/SP () (the (recordof (a int)) (record (a 3) (b 4))))")
        assert(msg.contains("type ascription"))
    }

    "a procedure definition" should "not be contravariant in its arguments" in {
        // The definition takes a record with FEWER fields than the declared
        // formal type: a procedure taking a narrower record is a subtype of
        // one taking a wider record (accepted by FLEX/SP, rejected here).
        flexpErr(
            "(flex/SP () ((pcall pick int) (record (a 3) (b 4)))" +
                " (def pick (forall (t) (-> ((recordof (a t) (b t))) t))" +
                " (pabs (t) (abs ((r (recordof (a t)))) (select a r)))))")
    }

    "the get-age program (book p.702)" should "be rejected by FLEX/P" in {
        // The record passed to get-age has more fields than its declared
        // formal type; subtyping would accept the application, equivalence
        // does not.
        val msg = flexpErr(
            "(flex/SP () (get-age (record (name (sym Polly_Morwicz)) (age 35) (student? #f)))" +
                " (def get-age (-> ((recordof (age int))) int)" +
                " (abs ((r (recordof (age int)))) (select age r))))")
        assert(msg.contains("expects"))
    }

    // ------------------------------------------------------------------
    // The standard library's polymorphic list procedures (book p.728)
    // ------------------------------------------------------------------

    "the polymorphic list procedures" should "work through pcall" in {
        // cons : (forall (t) (-> (t (listof t)) (listof t))),
        // null : (forall (t) (-> () (listof t))) — a 0-ary procedure. The
        // polymorphic standard-library values exist only in the flex/SP
        // (sugar) form, which desugars to a let of the standard library;
        // flexk/SP keeps the monomorphic kernel list forms.
        "(flex/SP () ((pcall cons int) 1 (null int)))" shouldFlexPCheckTo
            (FlexOk("(listof int)"))
        "(flex/SP () ((pcall car int) ((pcall cons int) 1 (null int))))" shouldFlexPCheckTo
            (FlexOk("int"))
        // The monomorphic kernel forms remain accepted alongside.
        "(flexk/SP () (car (cons 1 (null int))))" shouldFlexPCheckTo (FlexOk("int"))
    }

    "the FLEX/SP map (book p.730)" should "type-check" in {
        val prog =
            "(flex/SP ()" +
            " ((pcall map int bool) (abs ((x int)) (< x 17)) (list int 23 13 29))" +
            " (def map (forall (s t) (-> ((-> (s) t) (listof s)) (listof t)))" +
            " (pabs (s t)" +
            " (abs ((f (-> (s) t)) (xs (listof s)))" +
            " (if ((pcall null? s) xs)" +
            " ((pcall null t))" +
            " ((pcall cons t) (f ((pcall car s) xs))" +
            " ((pcall map s t)" +
            " f ((pcall cdr s) xs))))))))"
        prog shouldFlexPCheckTo (FlexOk("(listof bool)"))
    }

    // ------------------------------------------------------------------
    // Deconstructible data types (Figures 12.11, 12.12, 12.13)
    // ------------------------------------------------------------------

    // The book's Figures 12.11/12.12 write the data type's type identifier
    // with a T prefix (Tintlist); Figure 12.13's formal desugaring names the
    // def-type after the def-datatype (intlist), which is what the checker
    // implements.
    private val intlistDecl = "(def-datatype intlist (inull) (icons int intlist))"

    "def-datatype intlist (book Figure 12.11)" should "define a constructor and a deconstructor" in {
        // The constructor.
        ("(flex/SP () (icons 1 (inull)) " + intlistDecl + ")") shouldFlexPCheckTo
            (FlexOk("(trec intlist (oneof (inull (prodof)) (icons (prodof int intlist))))"))
        // The deconstructor, projected onto int.
        ("(flex/SP () ((pcall icons~ int) (icons 1 (inull))" +
            " (abs ((n int) (ms intlist)) n)" +
            " (abs () 0)) " + intlistDecl + ")") shouldFlexPCheckTo (FlexOk("int"))
        // A deconstructor argument of the wrong type is rejected.
        flexpErr(
            "(flex/SP () (bad (inull))" +
                " " + intlistDecl +
                " (def bad (-> (intlist) int)" +
                " (abs ((ns intlist)) (pcall inull~ int (inull) (abs () #t) (abs () 1)))))")
    }

    "the intlist procedures (book Figure 12.12)" should "type-check" in {
        // sum
        ("(flex/SP () (sum (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def sum (-> (intlist) int)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ int) ns (abs () 0)" +
            " (abs ()" +
            " ((pcall icons~ int) ns" +
            " (abs ((n int) (ms intlist)) (+ n (sum ms)))" +
            " (abs () (error shouldnt-happen int)))))))" +
            ")") shouldFlexPCheckTo (FlexOk("int"))
        // all-positive?
        ("(flex/SP () (all-positive? (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def all-positive? (-> (intlist) bool)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ bool) ns (abs () #t)" +
            " (abs ()" +
            " ((pcall icons~ bool) ns" +
            " (abs ((n int) (ms intlist)) (scand (> n 0) (all-positive? ms)))" +
            " (abs () (error shouldnt-happen bool)))))))" +
            ")") shouldFlexPCheckTo (FlexOk("bool"))
        // map-square (the book's Figure 12.12 writes (cons ...), which is a
        // typo: building an intlist out of an int and an intlist is the
        // data-type constructor (icons ...), not the list cons).
        ("(flex/SP () (map-square (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def map-square (-> (intlist) intlist)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ intlist) ns (abs () (inull))" +
            " (abs ()" +
            " ((pcall icons~ intlist) ns" +
            " (abs ((n int) (ms intlist)) (icons (* n n) (map-square ms)))" +
            " (abs () (error shouldnt-happen intlist)))))))" +
            ")") shouldFlexPCheckTo
            (FlexOk("(trec intlist (oneof (inull (prodof)) (icons (prodof int intlist))))"))
    }

    // ------------------------------------------------------------------
    // FLEX regression: FLEX/P is a superset of monomorphic FLEX
    // ------------------------------------------------------------------

    "FLEX programs (superset property)" should "still type-check under FLEX/P" in {
        // The pos?/even? FLEX example (book p.636) under the FLEX/SP tag.
        "(flex/SP ((b bool) (i int)) (if b (pos? i) (even? i))" +
            " (def-type intfun (-> (int) int))" +
            " (def-type intpred (-> (int) bool))" +
            " (def dec intfun (abs ((x int)) (- x 1)))" +
            " (def pos? intpred (abs ((y int)) (> y 0)))" +
            " (def even? intpred (abs ((x int)) (if (= x 0) #t (odd? (dec x)))))" +
            " (def odd? intpred (abs ((y int)) (if (= y 0) #f (even? (dec y))))))" shouldFlexPCheckTo
            (FlexOk("(=> (bool int) bool)"))
    }
}
