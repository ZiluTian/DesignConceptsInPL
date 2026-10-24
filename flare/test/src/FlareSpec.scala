package DSL.flare

import org.scalatest.flatspec.AnyFlatSpecLike
import DSL.flex.{FlexOk, FlexErr}

class FlareSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flareErr(input: String): String = {
        flareRecon(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Parsing
    // ------------------------------------------------------------------

    "A valid FLARE program" should "parse" in {
        assert(FlareProgram("(flarek () 3)").isDefined)
        assert(FlareProgram("(flare () 3)").isDefined)
        assert(FlareProgram("(flare () 3 (def x 5))").isDefined)
        assert(FlareProgram("(flare () 3 (def (f a b) 0))").isDefined)
        assert(FlareProgram("(flarek (n) (abs (x) (prim + x n)))").isDefined)
        assert(FlareProgram("(foo () 3)").isEmpty) // unknown program tag
        assert(FlareProgram("(flarek ()").isEmpty) // malformed s-expression
    }

    "A malformed program" should "be a parse error" in {
        "(flarek () (let ((if 3)) if))" shouldFlareReconFail("parse error")
        "(flarek () (@bogus 1))" shouldFlareReconFail("parse error")
        "(flarek () (if #t 1))" shouldFlareReconFail("parse error")
        "(flarek () (prim bogus 1))" shouldFlareReconFail("parse error")
        "(flarek () (abs x x))" shouldFlareReconFail("parse error")
        "(flare () (def x 3))" shouldFlareReconFail("parse error")
        "(flarek () (let ((x 3)) x)" shouldFlareReconFail("parse error")
    }

    // ------------------------------------------------------------------
    // Literals, procedures, and program types
    // ------------------------------------------------------------------

    "A literal program" should "report the literal's type" in {
        "(flarek () 3)" shouldFlareReconTo (FlexOk("int"))
        "(flarek () #t)" shouldFlareReconTo (FlexOk("bool"))
        "(flarek () #u)" shouldFlareReconTo (FlexOk("unit"))
        "(flarek () (sym a))" shouldFlareReconTo (FlexOk("symb"))
    }

    "An abstraction" should "have an arrow type" in {
        "(flarek () (abs (x) x))" shouldFlareReconTo (FlexOk("(-> (T1) T1)"))
        "(flarek () (abs (x y) x))" shouldFlareReconTo (FlexOk("(-> (T1 T2) T1)"))
        "(flarek () (abs () #u))" shouldFlareReconTo (FlexOk("(-> () unit)"))
    }

    "A program with formal parameters" should "report the full program type (=> ...)" in {
        "(flarek (x) x)" shouldFlareReconTo (FlexOk("(=> (T1) T1)"))
        "(flarek (x y) (abs (a b) a))" shouldFlareReconTo (FlexOk("(=> (T1 T2) (-> (T3 T4) T3))"))
        "(flarek (n) (prim + n 1))" shouldFlareReconTo (FlexOk("(=> (int) int)"))
    }

    "An error expression" should "be assigned a fresh type" in {
        "(flare () (error boom))" shouldFlareReconTo (FlexOk("T1"))
    }

    // ------------------------------------------------------------------
    // Conditionals
    // ------------------------------------------------------------------

    "An if expression" should "require a bool test and matching branches" in {
        "(flarek () (if #t 1 2))" shouldFlareReconTo (FlexOk("int"))
        "(flarek () (if #f #t #f))" shouldFlareReconTo (FlexOk("bool"))
        "(flarek () (if 1 #t #f))" shouldFlareReconFail("type reconstruction failed")
        "(flarek () (if #t 1 #f))" shouldFlareReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // let / letrec
    // ------------------------------------------------------------------

    "A let expression" should "bind names for the body (parallel definitions)" in {
        "(flarek () (let ((x 3)) x))" shouldFlareReconTo (FlexOk("int"))
        "(flarek () (let ((x 3) (y 4)) (prim + x y)))" shouldFlareReconTo (FlexOk("int"))
    }

    "A let definition" should "not see other let-bound names" in {
        "(flarek () (let ((x 3) (y x)) y))" shouldFlareReconFail("unbound variable: x")
    }

    "A letrec" should "support recursion" in {
        // Ppow (page 775 of the book)
        "(flarek (n) (let ((dbl (abs (x) (prim * x 2)))) (letrec ((loop (abs (i) (if (prim >= i n) i (loop (dbl i)))))) (loop 1))))" shouldFlareReconTo (FlexOk("(=> (int) int)"))
        // A factorial defined by self-reference.
        "(flarek (n) (letrec ((fact (abs (x) (if (prim = x 0) 1 (prim * x (fact (prim - x 1))))))) (fact n)))" shouldFlareReconTo (FlexOk("(=> (int) int)"))
    }

    // ------------------------------------------------------------------
    // Let polymorphism (Figures 13.20 / 13.26)
    // ------------------------------------------------------------------

    "A polymorphic let binding" should "generalize the definition's type" in {
        // Eid (page 778 of the book): `id` generalizes to (generic (?a) (-> (?a) ?a)).
        "(flare () (let ((id (abs (x) x))) (if (id #t) 1 ((id id) 2))))" shouldFlareReconTo (FlexOk("int"))
    }

    "A let-polymorphism limitation" should "reject Econst" in {
        // Econst (page 804): the free variable `c` (abs-bound, not let-bound) is
        // not generalized, so `const` is forced to one type and the program fails.
        "(flare () (abs (c) (let ((const (abs (x) c))) (if (const #t) 1 ((const const) 2)))))" shouldFlareReconFail("type reconstruction failed")
    }

    "abs-bound names are monomorphic" should "reject EabsR" in {
        // EabsR (page 807): `f` is bound by abs, so it is a plain type and cannot
        // be instantiated twice.
        "(flare () (abs (f) (if (f #t) 1 ((f f) 2))))" shouldFlareReconFail("type reconstruction failed")
    }

    "letrec-bound names are monomorphic inside definitions" should "reject the p.806 example" in {
        "(flare () (letrec ((id (abs (x) x)) (inc (abs (y) (+ 1 (id y))))) (if (id #t) (id 1) (inc 2))))" shouldFlareReconFail("type reconstruction failed")
    }

    "genPure restricts generalization to pure definitions" should "reject EpolyCell" in {
        // EpolyCell (page 815): the definition of `c` is impure (cell allocation),
        // so it is not generalized; both uses of `c` must share one content type.
        "(flare () (let ((c (cell (null)))) (begin (:= c (cons 1 (null))) (not (car (^ c))))))" shouldFlareReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // Standard library (Figure 13.23)
    // ------------------------------------------------------------------

    "The standard library" should "bind the primitive operators as procedures" in {
        "(flare () (+ 1 4))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (= 1 2))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (not #t))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (bool=? #t #t))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (sym=? (sym a) (sym b)))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (> 3 2))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (and #t #f))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () true)" shouldFlareReconTo (FlexOk("bool"))
        // In the kernel language, + is just an unbound variable.
        assert(flareErr("(flarek () (+ 1 4))").contains("unbound variable: +"))
    }

    "Relational, arithmetic, and logical primops" should "type-check" in {
        "(flare () (< 1 2))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (<= 1 1))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (>= 2 3))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (!= 1 2))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (- 5 3))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (* 4 5))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (/ 6 2))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (% 7 3))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (or #f #t))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (and (and (bool=? #t #f) (< 1 2)) (and (sym=? (sym a) (sym a)) (not #t))))" shouldFlareReconTo (FlexOk("bool"))
    }

    // ------------------------------------------------------------------
    // Pairs
    // ------------------------------------------------------------------

    "Pairs" should "support pair/fst/snd" in {
        "(flare () (pair 1 #t))" shouldFlareReconTo (FlexOk("(pairof int bool)"))
        "(flare () (fst (pair 1 #t)))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (snd (pair 1 #t)))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (let ((p (pair #t 1))) (if (fst p) (snd p) 0)))" shouldFlareReconTo (FlexOk("int"))
    }

    // ------------------------------------------------------------------
    // Lists
    // ------------------------------------------------------------------

    "Lists" should "support cons/car/cdr/null/null?" in {
        "(flare () (cons 1 (null)))" shouldFlareReconTo (FlexOk("(listof int)"))
        "(flare () (car (cons 1 (cons 2 (null)))))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (cdr (cons 1 (cons 2 (null)))))" shouldFlareReconTo (FlexOk("(listof int)"))
        "(flare () (null))" shouldFlareReconTo (FlexOk("(listof T1)"))
        "(flare () (null? (null)))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (cons #t (cons 1 (null))))" shouldFlareReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // Cells
    // ------------------------------------------------------------------

    "Cells" should "support cell/^/:=/cell=?" in {
        "(flare () (let ((c (cell 10))) (^ c)))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (let ((c (cell 1))) (cell=? c c)))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (let ((c (cell 1))) (let ((d (^ c))) d)))" shouldFlareReconTo (FlexOk("int"))
    }

    "a cell assignment" should "return the unit value" in {
        "(flare () (let ((c (cell 1))) (:= c 2)))" shouldFlareReconTo (FlexOk("unit"))
        "(flare () (let ((c (cell 1))) (list (:= c 2) #u)))" shouldFlareReconTo (FlexOk("(listof unit)"))
        "(flare () (let ((c (cell 1))) (:= c #t)))" shouldFlareReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // Syntactic sugar
    // ------------------------------------------------------------------

    "Syntactic sugar" should "desugar cond/scand/scor/begin/list" in {
        "(flare () (cond (#t 1) (else 2)))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (scand #t #t))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (scor #f #t))" shouldFlareReconTo (FlexOk("bool"))
        "(flare () (begin 1 2))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (list 1 2 3))" shouldFlareReconTo (FlexOk("(listof int)"))
        "(flare () (list))" shouldFlareReconTo (FlexOk("(listof T1)"))
    }

    "def definitions" should "be available in the body" in {
        "(flare () (+ 1 (double 5)) (def double (abs (x) (* 2 x))))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (f (abs (a) a) 3) (def (f x y) (x y)))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (even 4) (def even (abs (n) (if (= n 0) #t (odd (- n 1))))) (def odd (abs (n) (if (= n 0) #f (even (- n 1))))))" shouldFlareReconTo (FlexOk("bool"))
    }

    "The recur sugar" should "define and invoke a recursive procedure" in {
        "(flare () (recur fact ((n 5)) (if (= n 0) 1 (* n (fact (- n 1))))))" shouldFlareReconTo (FlexOk("int"))
    }

    // ------------------------------------------------------------------
    // Higher-order procedures
    // ------------------------------------------------------------------

    "Higher-order procedures" should "type-check" in {
        "(flare () (let ((twice (abs (f x) (f (f x))))) (twice (abs (y) (+ y 1)) 3)))" shouldFlareReconTo (FlexOk("int"))
        "(flare () (let ((compose (abs (f g x) (f (g x))))) (compose (abs (a) (+ a 1)) (abs (b) (* b 2)) 3)))" shouldFlareReconTo (FlexOk("int"))
    }

    // ------------------------------------------------------------------
    // Ill-typed programs
    // ------------------------------------------------------------------

    "An ill-typed program" should "produce a type error" in {
        assert(flareErr("(flarek () y)").contains("unbound variable: y"))
        assert(flareErr("(flare () (+ #t 1))").startsWith("type reconstruction failed"))
        assert(flareErr("(flare () (car 5))").startsWith("type reconstruction failed"))
        assert(flareErr("(flare () (fst 5))").startsWith("type reconstruction failed"))
        assert(flareErr("(flarek () (prim + 1 2 3))").startsWith("type reconstruction failed"))
        assert(flareErr("(flare () (let ((x 3)) (x 4)))").startsWith("type reconstruction failed"))
    }
}
