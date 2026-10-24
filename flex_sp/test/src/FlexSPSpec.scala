package DSL.flex_sp

import DSL.flex._
import org.scalatest.flatspec.AnyFlatSpecLike

class FlexSPSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexspErr(input: String): String = {
        flexspCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Parsing (Figure 12.13: the FLEX syntax plus pabs / pcall / forall /
    // def-datatype)
    // ------------------------------------------------------------------

    "A valid FLEX/SP program" should "parse" in {
        assert(FlexSPProgram("(flexk/SP () 3)").isDefined)
        assert(FlexSPProgram("(flex/SP () 3)").isDefined)
        assert(FlexSPProgram("(flex/SP () ((pcall (pabs (t) (abs ((x t)) x)) int) 3))").isDefined)
        assert(FlexSPProgram("(flex () 3)").isEmpty) // a FLEX tag is not a FLEX/SP tag
        assert(FlexSPProgram("(foo () 3)").isEmpty) // unknown program tag
    }

    "a bare list keyword" should "name a standard-library procedure in a value position" in {
        // cons / car / cdr / null / null? are polymorphic standard-library
        // values in FLEX/SP (book p.728); they are not keywords in a value
        // position any more.
        assert(FlexSPProgram("(flexk/SP () ((pcall cons int) 1 (null int)))").isDefined)
        assert(FlexSPProgram("(flexk/SP () ((pcall null? int) (null int)))").isDefined)
        // The list forms (cons h t), (null T), ... remain kernel constructs.
        assert(FlexSPProgram("(flexk/SP () (cons 1 (null int)))").isDefined)
    }

    // ------------------------------------------------------------------
    // Universal polymorphism (Figure 12.9)
    // ------------------------------------------------------------------

    "EpolyId (book Figure 12.10)" should "type-check to int" in {
        "(flexk/SP () (let ((id (pabs (t) (abs ((x t)) x))))" +
            " (if ((pcall id bool) #t)" +
            " 1" +
            " (((pcall id (-> (int) int)) (pcall id int)) 2))))" shouldFlexSPCheckTo (FlexOk("int"))
    }

    "a polymorphic value projected onto an enclosing pabs variable" should "type-check" in {
        "(flexk/SP () (pabs (t) (let ((id (pabs (u) (abs ((x u)) x))))" +
            " ((pcall id (-> (t) t)) (pcall id t) (abs ((x t)) x)))))" shouldFlexSPCheckTo
            (FlexOk("(forall (t) (-> (t) t))"))
    }

    "pcall (Figure 12.9)" should "reject a wrong number of type arguments" in {
        flexspErr("(flexk/SP () (pcall (pabs (t u) (abs ((x t)) x)) int))")
        // A monomorphic value is not a polymorphic value.
        flexspErr("(flexk/SP () (pcall (abs ((x int)) x) int))")
    }

    "the import restriction (book p.732)" should "reject polytest" in {
        // The inner pabs would capture the outer pabs' t (used in x's
        // type), so polytest cannot have the type (forall (t) (-> (t)
        // (forall (t) t))).
        val prog =
            "(flex/SP () #u (def polytest (forall (t) (-> (t) (forall (t) t)))" +
                " (pabs (t) (abs ((x t)) (pabs (t) x)))))"
        assert(flexspErr(prog).contains("import restriction"))
    }

    "the purity restriction (Figure 12.9)" should "reject a pabs body that mutates" in {
        val prog = "(flexk/SP () (let ((c (cell 1))) (pabs (t) (:= c 2))))"
        assert(flexspErr(prog).contains("purity restriction"))
        // set! is rejected too.
        flexspErr("(flexk/SP () (let ((x 1)) (pabs (t) (set! x 2))))")
    }

    // ------------------------------------------------------------------
    // The [forall-≈] / [forall-≤] type rules (Figure 12.9)
    // ------------------------------------------------------------------

    "forall types (Figure 12.9)" should "compare up to alpha-renaming" in {
        // [forall-≤] at a the-ascription.
        "(flexk/SP () (the (forall (t) (-> (t) t)) (pabs (u) (abs ((x u)) x))))" shouldFlexSPCheckTo
            (FlexOk("(forall (t) (-> (t) t))"))
        // ... in the other direction as well.
        "(flexk/SP () (the (forall (u) (-> (u) u)) (pabs (t) (abs ((x t)) x))))" shouldFlexSPCheckTo
            (FlexOk("(forall (u) (-> (u) u))"))
        // [forall-approx] at the def match point: the declared type binds
        // t, the body binds u — accepted up to alpha-renaming. (The def's
        // value is applied only after a pcall projection, per FLEX/SP.)
        "(flex/SP () ((pcall id int) 3)" +
            " (def id (forall (t) (-> (t) t)) (pabs (u) (abs ((x u)) x))))" shouldFlexSPCheckTo
            (FlexOk("int"))
        // A body that is not a subtype is rejected.
        flexspErr(
            "(flexk/SP () (the (forall (t) (-> (t) (trec x (pairof t x))))" +
                " (pabs (t) (abs ((x t)) (pair x (abs ((y t)) y))))))")
    }

    "subtyping through forall (Figure 12.9 + 12.2)" should "be contravariant in the arguments" in {
        // The definition takes a record with FEWER fields than the declared
        // formal type: a procedure taking a narrower record is a subtype of
        // one taking a wider record.
        "(flex/SP () ((pcall pick int) (record (a 3) (b 4)))" +
            " (def pick (forall (t) (-> ((recordof (a t) (b t))) t))" +
            " (pabs (t) (abs ((r (recordof (a t)))) (select a r)))))" shouldFlexSPCheckTo
            (FlexOk("int"))
        // ... but the other direction is not safe, and is rejected.
        flexspErr(
            "(flex/SP () ((pcall pick int) (record (a 3)))" +
                " (def pick (forall (t) (-> ((recordof (a t))) t))" +
                " (pabs (t) (abs ((r (recordof (a t) (b t)))) (select a r)))))")
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
        "(flex/SP () ((pcall cons int) 1 (null int)))" shouldFlexSPCheckTo
            (FlexOk("(listof int)"))
        "(flex/SP () ((pcall car int) ((pcall cons int) 1 (null int))))" shouldFlexSPCheckTo
            (FlexOk("int"))
        // The monomorphic kernel forms remain accepted alongside.
        "(flexk/SP () (car (cons 1 (null int))))" shouldFlexSPCheckTo (FlexOk("int"))
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
        prog shouldFlexSPCheckTo (FlexOk("(listof bool)"))
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
        ("(flex/SP () (icons 1 (inull)) " + intlistDecl + ")") shouldFlexSPCheckTo
            (FlexOk("(trec intlist (oneof (inull (prodof)) (icons (prodof int intlist))))"))
        // The deconstructor, projected onto int.
        ("(flex/SP () ((pcall icons~ int) (icons 1 (inull))" +
            " (abs ((n int) (ms intlist)) n)" +
            " (abs () 0)) " + intlistDecl + ")") shouldFlexSPCheckTo (FlexOk("int"))
        // A deconstructor argument of the wrong type is rejected.
        flexspErr(
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
            ")") shouldFlexSPCheckTo (FlexOk("int"))
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
            ")") shouldFlexSPCheckTo (FlexOk("bool"))
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
            ")") shouldFlexSPCheckTo
            (FlexOk("(trec intlist (oneof (inull (prodof)) (icons (prodof int intlist))))"))
    }

    // ------------------------------------------------------------------
    // FLEX/S regression: FLEX/SP is a superset of FLEX/S
    // ------------------------------------------------------------------

    "FLEX/S programs (superset property)" should "still type-check under FLEX/SP" in {
        // get-age with a superset record (book p.702).
        "(flex/SP () (get-age (record (name (sym Polly_Morwicz)) (age 35) (student? #f)))" +
            " (def get-age (-> ((recordof (age int))) int)" +
            " (abs ((r (recordof (age int)))) (select age r))))" shouldFlexSPCheckTo (FlexOk("int"))
        // The pos?/even? FLEX example (book p.636) under the FLEX/SP tag.
        "(flex/SP ((b bool) (i int)) (if b (pos? i) (even? i))" +
            " (def-type intfun (-> (int) int))" +
            " (def-type intpred (-> (int) bool))" +
            " (def dec intfun (abs ((x int)) (- x 1)))" +
            " (def pos? intpred (abs ((y int)) (> y 0)))" +
            " (def even? intpred (abs ((x int)) (if (= x 0) #t (odd? (dec x)))))" +
            " (def odd? intpred (abs ((y int)) (if (= y 0) #f (even? (dec y))))))" shouldFlexSPCheckTo
            (FlexOk("(=> (bool int) bool)"))
    }
}
