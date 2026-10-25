package DSL.flare_e

import org.scalatest.flatspec.AnyFlatSpecLike
import DSL.flex.{FlexOk, FlexErr}

class FlareESpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flareErrE(input: String): String = {
        flareReconE(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Parsing (FLARE/E's concrete syntax is identical to FLARE's)
    // ------------------------------------------------------------------

    "A valid FLARE/E program" should "parse" in {
        assert(DSL.flare.FlareProgram("(flarek () 3)").isDefined)
        assert(DSL.flare.FlareProgram("(flare () 3)").isDefined)
        assert(DSL.flare.FlareProgram("(flare () 3 (def x 5))").isDefined)
        assert(DSL.flare.FlareProgram("(flarek (n) (abs (x) (prim + x n)))").isDefined)
        assert(DSL.flare.FlareProgram("(foo () 3)").isEmpty)
        assert(DSL.flare.FlareProgram("(flarek ()").isEmpty)
    }

    "A malformed program" should "be a parse error" in {
        "(flarek () (let ((if 3)) if))" shouldFlareEReconFail("parse error")
        "(flarek () (@bogus 1))" shouldFlareEReconFail("parse error")
        "(flarek () (if #t 1))" shouldFlareEReconFail("parse error")
        "(flarek () (prim bogus 1))" shouldFlareEReconFail("parse error")
        "(flarek () (abs x x))" shouldFlareEReconFail("parse error")
        "(flare () (def x 3))" shouldFlareEReconFail("parse error")
        "(flarek () (let ((x 3)) x)" shouldFlareEReconFail("parse error")
    }

    // ------------------------------------------------------------------
    // Literals, procedures, and program types
    //   The program type is always (=> (Targ*) Fbody Tbody); a pure body has
    //   effect `pure`, and a program with no formals is (=> () Fbody Tbody).
    // ------------------------------------------------------------------

    "A literal program" should "report the literal's type with a pure effect" in {
        "(flarek () 3)" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flarek () #t)" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flarek () #u)" shouldFlareEReconTo (FlexOk("(=> () pure unit)"))
        "(flarek () (sym a))" shouldFlareEReconTo (FlexOk("(=> () pure symb)"))
    }

    "An abstraction" should "have an arrow type with a pure latent effect" in {
        "(flarek () (abs (x) x))" shouldFlareEReconTo (FlexOk("(=> () pure (-> (T1) pure T1))"))
        "(flarek () (abs (x y) x))" shouldFlareEReconTo (FlexOk("(=> () pure (-> (T1 T2) pure T1))"))
        "(flarek () (abs () #u))" shouldFlareEReconTo (FlexOk("(=> () pure (-> () pure unit))"))
    }

    "A program with formal parameters" should "report the full program type (=> ...)" in {
        "(flarek (x) x)" shouldFlareEReconTo (FlexOk("(=> (T1) pure T1)"))
        "(flarek (x y) (abs (a b) a))" shouldFlareEReconTo (FlexOk("(=> (T1 T2) pure (-> (T3 T4) pure T3))"))
        "(flarek (n) (prim + n 1))" shouldFlareEReconTo (FlexOk("(=> (int) pure int)"))
    }

    "An error expression" should "be assigned a fresh type" in {
        "(flare () (error boom))" shouldFlareEReconTo (FlexOk("(=> () pure T1)"))
    }

    // ------------------------------------------------------------------
    // Conditionals
    // ------------------------------------------------------------------

    "An if expression" should "require a bool test and matching branches" in {
        "(flarek () (if #t 1 2))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flarek () (if #f #t #f))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flarek () (if 1 #t #f))" shouldFlareEReconFail("type reconstruction failed")
        "(flarek () (if #t 1 #f))" shouldFlareEReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // let / letrec
    // ------------------------------------------------------------------

    "A let expression" should "bind names for the body (parallel definitions)" in {
        "(flarek () (let ((x 3)) x))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flarek () (let ((x 3) (y 4)) (prim + x y)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
    }

    "A let definition" should "not see other let-bound names" in {
        "(flarek () (let ((x 3) (y x)) y))" shouldFlareEReconFail("unbound")
    }

    "A letrec" should "support recursion" in {
        // Ppow (page 775 of the book)
        "(flarek (n) (let ((dbl (abs (x) (prim * x 2)))) (letrec ((loop (abs (i) (if (prim >= i n) i (loop (dbl i)))))) (loop 1))))" shouldFlareEReconTo (FlexOk("(=> (int) pure int)"))
        // A factorial defined by self-reference.
        "(flarek (n) (letrec ((fact (abs (x) (if (prim = x 0) 1 (prim * x (fact (prim - x 1))))))) (fact n)))" shouldFlareEReconTo (FlexOk("(=> (int) pure int)"))
    }

    // ------------------------------------------------------------------
    // Let polymorphism (mirrors FLARE; Figures 16.8 / 13.26)
    // ------------------------------------------------------------------

    "A polymorphic let binding" should "generalize the definition's type" in {
        // Eid (page 778 of the book)
        "(flare () (let ((id (abs (x) x))) (if (id #t) 1 ((id id) 2))))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
    }

    "A let-polymorphism limitation" should "reject Econst" in {
        "(flare () (abs (c) (let ((const (abs (x) c))) (if (const #t) 1 ((const const) 2)))))" shouldFlareEReconFail("type reconstruction failed")
    }

    "abs-bound names are monomorphic" should "reject EabsR" in {
        "(flare () (abs (f) (if (f #t) 1 ((f f) 2))))" shouldFlareEReconFail("type reconstruction failed")
    }

    "letrec-bound names are monomorphic inside definitions" should "reject the p.806 example" in {
        "(flare () (letrec ((id (abs (x) x)) (inc (abs (y) (+ 1 (id y))))) (if (id #t) (id 1) (inc 2))))" shouldFlareEReconFail("type reconstruction failed")
    }

    "genPureSP restricts generalization to pure definitions" should "reject EpolyCell" in {
        // EpolyCell (page 815): the definition of `c` is impure (cell
        // allocation), so it is not generalized; both uses of `c` must share
        // one content type.
        "(flare () (let ((c (cell (null)))) (begin (:= c (cons 1 (null))) (not (car (^ c))))))" shouldFlareEReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // Standard library and base primops (pure effects)
    // ------------------------------------------------------------------

    "The standard library" should "bind the primitive operators as procedures" in {
        "(flare () (+ 1 4))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (= 1 2))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (not #t))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (bool=? #t #t))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (sym=? (sym a) (sym b)))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (> 3 2))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (and #t #f))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () true)" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
    }

    "Relational, arithmetic, and logical primops" should "type-check with pure effects" in {
        "(flare () (< 1 2))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (<= 1 1))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (>= 2 3))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (!= 1 2))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (- 5 3))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (* 4 5))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (/ 6 2))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (% 7 3))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (or #f #t))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
    }

    // ------------------------------------------------------------------
    // Pairs and lists (pure effects)
    // ------------------------------------------------------------------

    "Pairs" should "support pair/fst/snd" in {
        "(flare () (pair 1 #t))" shouldFlareEReconTo (FlexOk("(=> () pure (pairof int bool))"))
        "(flare () (fst (pair 1 #t)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (snd (pair 1 #t)))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (let ((p (pair #t 1))) (if (fst p) (snd p) 0)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
    }

    "Lists" should "support cons/car/cdr/null/null?" in {
        "(flare () (cons 1 (null)))" shouldFlareEReconTo (FlexOk("(=> () pure (listof int))"))
        "(flare () (car (cons 1 (cons 2 (null)))))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (cdr (cons 1 (cons 2 (null)))))" shouldFlareEReconTo (FlexOk("(=> () pure (listof int))"))
        "(flare () (null))" shouldFlareEReconTo (FlexOk("(=> () pure (listof T1))"))
        "(flare () (null? (null)))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (cons #t (cons 1 (null))))" shouldFlareEReconFail("type reconstruction failed")
    }

    // ------------------------------------------------------------------
    // Cells (the store effects: init / read / write)
    // ------------------------------------------------------------------

    "A cell allocation" should "have type (cellof T R) and effect (init R)" in {
        "(flare () (cell 5))" shouldFlareEReconTo (FlexOk("(=> () (init R1) (cellof int R1))"))
        "(flare () (let ((c (cell 10))) c))" shouldFlareEReconTo (FlexOk("(=> () (init R1) (cellof int R1))"))
    }

    "A cell read" should "have effect (read R)" in {
        "(flare () (let ((c (cell 10))) (^ c)))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (read R1)) int)"))
    }

    "A cell assignment" should "return unit and have effect (write R)" in {
        "(flare () (let ((c (cell 1))) (:= c 2)))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (write R1)) unit)"))
        "(flare () (let ((c (cell 1))) (list (:= c 2) #u)))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (write R1)) (listof unit))"))
        "(flare () (let ((c (cell 1))) (:= c #t)))" shouldFlareEReconFail("type reconstruction failed")
    }

    "cell=?" should "compare two cells of the same content type" in {
        "(flare () (let ((c (cell 1))) (cell=? c c)))" shouldFlareEReconTo (FlexOk("(=> () (init R1) bool)"))
        "(flare () (let ((c (cell 1)) (d (cell 2))) (cell=? c d)))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (init R2)) bool)"))
    }

    // Eboolcell (page 946 of the book):
    //   (let ((b (cell #f))) (begin (:= b #t) (^ b)))
    //   : bool ! (maxeff (init R1) (read R1) (write R1))
    "Eboolcell" should "combine init/write/read effects on one region" in {
        "(flare () (let ((b (cell #f))) (begin (:= b #t) (^ b))))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (read R1) (write R1)) bool)"))
    }

    // Einc-c! (page 948 of the book):
    //   (let ((c (cell 0)))
    //     (let ((inc-c! (abs () (begin (:= c (+ 1 (^ c))) (^ c))))))
    //       (pair (inc-c!) (inc-c!))))
    //   : (pairof int int) ! (maxeff (init R1) (read R1) (write R1))
    "Einc-c!" should "generalize the procedure's latent effect but keep the region fixed" in {
        "(flare () (let ((c (cell 0))) (let ((inc-c! (abs () (begin (:= c (+ 1 (^ c))) (^ c))))) (pair (inc-c!) (inc-c!)))))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (read R1) (write R1)) (pairof int int))"))
    }

    // Etwice (page 949 of the book): dup! generalizes over the element type,
    // the cell region, and the latent effect; apply-twice inherits f's effect.
    //   : (pairof (listof bool) (listof int))
    //     ! (maxeff (init R1) (read R1) (write R1) (init R2) (read R2) (write R2))
    "Etwice" should "generalize over type, region, and effect" in {
        "(flare () (let ((bools (cell (list #t #f))) (ints (cell (list 1 2 3))) (dup! (abs (c) (begin (:= c (cons (car (^ c)) (^ c))) (^ c)))) (apply-twice (abs (f x) (begin (f x) (f x))))) (pair (apply-twice dup! bools) (apply-twice dup! ints))))" shouldFlareEReconTo (FlexOk("(=> () (maxeff (init R1) (read R1) (write R1) (init R2) (read R2) (write R2)) (pairof (listof bool) (listof int)))"))
    }

    // Eifproc (page 955 of the book): the two procedure bodies have different
    // effects, so the latent effects must be unified (the [does] rule). Here the
    // read-only branch and the read+write branch are forced to share one
    // (inflated) latent effect.
    "Eifproc" should "unify the latent effects of the two branches" in {
        "(flare () (let ((c (cell 1))) (if #t (abs () (^ c)) (abs () (begin (:= c 2) (^ c))))))" shouldFlareEReconTo (FlexOk("(=> () (init R1) (-> () (maxeff (read R1) (write R1)) int))"))
    }

    // ------------------------------------------------------------------
    // Syntactic sugar
    // ------------------------------------------------------------------

    "Syntactic sugar" should "desugar cond/scand/scor/begin/list" in {
        "(flare () (cond (#t 1) (else 2)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (scand #t #t))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (scor #f #t))" shouldFlareEReconTo (FlexOk("(=> () pure bool)"))
        "(flare () (begin 1 2))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (list 1 2 3))" shouldFlareEReconTo (FlexOk("(=> () pure (listof int))"))
        "(flare () (list))" shouldFlareEReconTo (FlexOk("(=> () pure (listof T1))"))
    }

    "def definitions" should "be available in the body" in {
        "(flare () (+ 1 (double 5)) (def double (abs (x) (* 2 x))))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (f (abs (a) a) 3) (def (f x y) (x y)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
    }

    "The recur sugar" should "define and invoke a recursive procedure" in {
        "(flare () (recur fact ((n 5)) (if (= n 0) 1 (* n (fact (- n 1))))))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
    }

    // ------------------------------------------------------------------
    // Higher-order procedures (pure)
    // ------------------------------------------------------------------

    "Higher-order procedures" should "type-check" in {
        "(flare () (let ((twice (abs (f x) (f (f x))))) (twice (abs (y) (+ y 1)) 3)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
        "(flare () (let ((compose (abs (f g x) (f (g x))))) (compose (abs (a) (+ a 1)) (abs (b) (* b 2)) 3)))" shouldFlareEReconTo (FlexOk("(=> () pure int)"))
    }

    // ------------------------------------------------------------------
    // Ill-typed programs
    // ------------------------------------------------------------------

    "An ill-typed program" should "produce a type error" in {
        assert(flareErrE("(flarek () y)").contains("unbound"))
        assert(flareErrE("(flare () (+ #t 1))").startsWith("type reconstruction failed"))
        assert(flareErrE("(flare () (car 5))").startsWith("type reconstruction failed"))
        assert(flareErrE("(flare () (fst 5))").startsWith("type reconstruction failed"))
        assert(flareErrE("(flarek () (prim + 1 2 3))").startsWith("type reconstruction failed"))
        assert(flareErrE("(flare () (let ((x 3)) (x 4)))").startsWith("type reconstruction failed"))
    }

    // ------------------------------------------------------------------
    // Theorem 16.1: a program is typable in FLARE iff it is typable in
    // FLARE/E. The accept/reject decision must match the FLARE module exactly;
    // only the *displayed* types differ (effects and regions are added).
    // ------------------------------------------------------------------

    "Theorem 16.1" should "agree with FLARE on which programs type-check" in {
        val programs = List(
            "(flarek () 3)",
            "(flarek () (abs (x) x))",
            "(flarek (x) x)",
            "(flarek (n) (prim + n 1))",
            "(flarek () (if #t 1 2))",
            "(flarek () (if 1 #t #f))",
            "(flarek () (let ((x 3) (y x)) y))",
            "(flare (n) (letrec ((fact (abs (x) (if (prim = x 0) 1 (prim * x (fact (prim - x 1))))))) (fact n)))",
            "(flare () (let ((id (abs (x) x))) (if (id #t) 1 ((id id) 2))))",
            "(flare () (abs (c) (let ((const (abs (x) c))) (if (const #t) 1 ((const const) 2)))))",
            "(flare () (abs (f) (if (f #t) 1 ((f f) 2))))",
            "(flare () (let ((c (cell (null)))) (begin (:= c (cons 1 (null))) (not (car (^ c))))))",
            "(flare () (cell 5))",
            "(flare () (let ((c (cell 10))) (^ c)))",
            "(flare () (let ((c (cell 1))) (:= c 2)))",
            "(flare () (let ((c (cell 1))) (:= c #t)))",
            "(flare () (cons #t (cons 1 (null))))",
            "(flare () (car 5))",
            "(flarek () y)"
        )
        programs.foreach { input =>
            val inFlare = DSL.flare.flareRecon(input).isInstanceOf[FlexOk]
            val inFlareE = flareReconE(input).isInstanceOf[FlexOk]
            assert(inFlare == inFlareE,
                s"acceptance mismatch for: $input (flare=${DSL.flare.flareRecon(input)}, flare_e=${flareReconE(input)})")
        }
    }
}
