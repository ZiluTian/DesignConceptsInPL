package DSL.flex

import org.scalatest.flatspec.AnyFlatSpecLike

class FlexSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexErr(input: String): String = {
        flexCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Parsing
    // ------------------------------------------------------------------

    "A valid FLEX program" should "parse" in {
        assert(FlexProgram("(flexk () 3)").isDefined)
        assert(FlexProgram("(flex () 3)").isDefined)
        assert(FlexProgram("(flexk ((x int)) (abs ((y int)) x))").isDefined)
        assert(FlexProgram("(flex () 3 (def x int 5))").isDefined)
        assert(FlexProgram("(flex () 3 (def-type t int) (def x t 5))").isDefined)
        assert(FlexProgram("(foo () 3)").isEmpty) // unknown program tag
        assert(FlexProgram("(flexk ()").isEmpty) // malformed s-expression
    }

    "A malformed program" should "be a parse error" in {
        assert(flexCheck("(flexk () (get n (prod 1 2)))") == FlexErr("parse error")) // non-literal get index
        assert(flexCheck("(flex () 3 (def x int 5) (def-type t int))") == FlexErr("parse error")) // def-type after def
        assert(flexCheck("(flexk () (the -> 1))") == FlexErr("parse error")) // type keyword as type identifier
        assert(flexCheck("(flexk () (abs (x int) if))") == FlexErr("parse error")) // keyword as value identifier
        assert(flexCheck("(flexk () (the (pairof int) 1))") == FlexErr("parse error")) // malformed type
    }

    // ------------------------------------------------------------------
    // flexk: literals, procedures, conditionals
    // ------------------------------------------------------------------

    "A literal program" should "report the literal's type" in {
        "(flexk () 3)" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () #t)" shouldFlexCheckTo (FlexOk("bool"))
        "(flexk () #u)" shouldFlexCheckTo (FlexOk("unit"))
    }

    "An abstraction" should "have an arrow type" in {
        "(flexk () (abs ((x int)) x))" shouldFlexCheckTo (FlexOk("(-> (int) int)"))
        "(flexk () (abs ((x int) (y bool)) x))" shouldFlexCheckTo (FlexOk("(-> (int bool) int)"))
    }

    "A program with formal parameters" should "report the full program type (=> ...)" in {
        "(flexk ((x int)) x)" shouldFlexCheckTo (FlexOk("(=> (int) int)"))
        "(flexk ((x int) (y bool)) (pair x y))" shouldFlexCheckTo (FlexOk("(=> (int bool) (pairof int bool))"))
    }

    "An if expression" should "require a bool test and matching branches" in {
        "(flexk () (if #t 1 2))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (if #f #t #f))" shouldFlexCheckTo (FlexOk("bool"))
        assert(flexErr("(flexk () (if 1 2 3))").contains("the if test must have type bool"))
        assert(flexErr("(flexk () (if #t 1 #t))").contains("the if branches have different types"))
    }

    "The kernel let form" should "bind variables without types" in {
        "(flexk () (let ((x 3) (y x)) y))" shouldFlexCheckTo (FlexOk("int"))
    }

    "Mutually recursive letrec definitions" should "type-check" in {
        "(flexk () (letrec ((even? (-> (int) bool) (abs ((n int)) (if (prim = n 0) #t (odd? (prim - n 1))))) (odd? (-> (int) bool) (abs ((n int)) (if (prim = n 0) #f (even? (prim - n 1)))))) (odd? 3)))" shouldFlexCheckTo (FlexOk("bool"))
    }

    "A the ascription" should "check the expression against the declared type" in {
        "(flexk () (the int 3))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (the (pairof int bool) (pair 1 #t)))" shouldFlexCheckTo (FlexOk("(pairof int bool)"))
        assert(flexErr("(flexk () (the int #t))").contains("the type ascription says"))
    }

    "An error expression" should "have its declared type" in {
        """(flexk () (error "boom" int))""" shouldFlexCheckTo (FlexOk("int"))
        """(flexk () (error "bad" (-> (int) bool)))""" shouldFlexCheckTo (FlexOk("(-> (int) bool)"))
    }

    "Primitive applications" should "check argument types" in {
        "(flexk () (prim + 1 2))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (prim not #t))" shouldFlexCheckTo (FlexOk("bool"))
        "(flexk () (@+ 1 2))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (@not #f))" shouldFlexCheckTo (FlexOk("bool"))
        "(flexk () (prim = 1 2))" shouldFlexCheckTo (FlexOk("bool"))
        assert(flexErr("(flexk () (prim + 1 #t))").contains("the primitive expects"))
        assert(flexErr("(flexk () (prim + 1))").contains("expected 2 argument(s)"))
    }

    "N-ary application" should "apply a procedure to all its arguments" in {
        "(flexk () (let ((add (abs ((x int) (y int)) (prim + x y)))) (add 1 2)))" shouldFlexCheckTo (FlexOk("int"))
        assert(flexErr("(flexk () (3 4))").contains("the rator has type"))
    }

    "Cond, scand, and scor sugar" should "desugar to if-expressions" in {
        "(flexk () (cond (#f 1) (#t 2) (else 3)))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (scand #t #t))" shouldFlexCheckTo (FlexOk("bool"))
        "(flexk () (scor #f #t))" shouldFlexCheckTo (FlexOk("bool"))
        assert(flexErr("(flexk () (cond (#t 1) (#f #t)))").contains("the if branches have different types"))
        // A cond without an else desugars to an error of type unit in the
        // fall-through, so the branches no longer match.
        assert(flexErr("(flexk () (cond (#t 1)))").contains("the if branches have different types"))
    }

    // ------------------------------------------------------------------
    // flexk: pairof, prodof, seqof
    // ------------------------------------------------------------------

    "Pair formation and elimination" should "work" in {
        "(flexk () (pair 1 #t))" shouldFlexCheckTo (FlexOk("(pairof int bool)"))
        "(flexk () (fst (pair 1 #t)))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (snd (pair 1 #t)))" shouldFlexCheckTo (FlexOk("bool"))
        assert(flexErr("(flexk () (fst 3))").contains("requires a pairof type"))
    }

    "Product formation and elimination" should "work" in {
        "(flexk () (prod 1 2 3))" shouldFlexCheckTo (FlexOk("(prodof int int int)"))
        "(flexk () (get 2 (prod 1 2)))" shouldFlexCheckTo (FlexOk("int"))
        assert(flexErr("(flexk () (get 3 (prod 1 2)))").contains("out of range"))
        assert(flexErr("(flexk () (get 1 3))").contains("requires a prodof type"))
    }

    "Sequences" should "be homogeneous" in {
        "(flexk () (seq 1 2 3))" shouldFlexCheckTo (FlexOk("(seqof int)"))
        "(flexk () (seq-get 1 (seq 1 2 3)))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (seq-size (seq 1 2)))" shouldFlexCheckTo (FlexOk("int"))
        assert(flexErr("(flexk () (seq 1 #t))").contains("sequence components must all have the same type"))
        assert(flexErr("(flexk () (seq))").contains("an empty sequence"))
        assert(flexErr("(flexk () (seq-get #t (seq 1 2)))").contains("the sequence index must have type int"))
    }

    // ------------------------------------------------------------------
    // flexk: recordof
    // ------------------------------------------------------------------

    "Record formation and elimination" should "work" in {
        "(flexk () (record (x 1) (y #t)))" shouldFlexCheckTo (FlexOk("(recordof (x int) (y bool))"))
        "(flexk () (select x (record (x 1) (y #t))))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (with (record (x 1) (y #t)) x))" shouldFlexCheckTo (FlexOk("int"))
        assert(flexErr("(flexk () (select y (record (x 1))))").contains("no field named y"))
        assert(flexErr("(flexk () (with 3 x))").contains("requires a recordof type"))
    }

    // ------------------------------------------------------------------
    // flexk: oneof (one / tagcase)
    // ------------------------------------------------------------------

    "Oneof introduction" should "check the payload against the tag's type" in {
        "(flexk () (one (oneof (square int) (rect bool)) square 3))" shouldFlexCheckTo (FlexOk("(oneof (square int) (rect bool))"))
        assert(flexErr("(flexk () (one (oneof (square int)) square #t))").contains("the payload has type"))
        assert(flexErr("(flexk () (one (oneof (square int)) rect 3))").contains("is not in the oneof type"))
    }

    "Tagcase" should "require complete, ordered, same-typed clauses" in {
        "(flexk () (tagcase (one (oneof (square int) (rect int)) square 3) v (square v) (rect v)))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (tagcase (one (oneof (square int) (rect int) (tri bool)) square 3) v (square #t) (else #f)))" shouldFlexCheckTo (FlexOk("bool"))
        assert(flexErr("(flexk () (tagcase (one (oneof (square int) (rect int)) square 3) v (rect v) (square v)))").contains("must follow the oneof type's tag order"))
        assert(flexErr("(flexk () (tagcase (one (oneof (square int) (rect int)) square 3) v (square v)))").contains("but the oneof type has 2 tag(s)"))
        assert(flexErr("(flexk () (tagcase (one (oneof (square int) (rect int)) square 3) v (square v) (rect v) (else #t)))").contains("the tagcase else body has type"))
        // The payload name is not in scope in the else clause.
        assert(flexErr("(flexk () (tagcase (one (oneof (square int) (rect int)) square 3) v (square v) (rect v) (else v)))").contains("unbound variable: v"))
    }

    // ------------------------------------------------------------------
    // flexk: listof (null / cons / car / cdr / null?)
    // ------------------------------------------------------------------

    "Typed lists" should "be homogeneous" in {
        "(flexk () (null int))" shouldFlexCheckTo (FlexOk("(listof int)"))
        "(flexk () (cons 1 (null int)))" shouldFlexCheckTo (FlexOk("(listof int)"))
        "(flexk () (car (cons 1 (null int))))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (cdr (cons 1 (cons 2 (null int)))))" shouldFlexCheckTo (FlexOk("(listof int)"))
        "(flexk () (null? (null int)))" shouldFlexCheckTo (FlexOk("bool"))
        "(flexk () (list int 1 2 3))" shouldFlexCheckTo (FlexOk("(listof int)"))
        "(flexk () (list int))" shouldFlexCheckTo (FlexOk("(listof int)"))
        assert(flexErr("(flexk () (cons #t (null int)))").contains("(cons ...) expects a head"))
        assert(flexErr("(flexk () (cons 1 2))").contains("must have a listof type"))
        assert(flexErr("(flexk () (car 3))").contains("requires a listof type"))
        assert(flexErr("(flexk () (null? 3))").contains("requires a listof type"))
    }

    // ------------------------------------------------------------------
    // flexk: mutable data (cell / deref / := / cell=? / set!)
    // ------------------------------------------------------------------

    "Cells" should "type-check" in {
        "(flexk () (cell 3))" shouldFlexCheckTo (FlexOk("(cellof int)"))
        "(flexk () (^ (cell 3)))" shouldFlexCheckTo (FlexOk("int"))
        "(flexk () (:= (cell 3) 5))" shouldFlexCheckTo (FlexOk("unit"))
        "(flexk () (cell=? (cell 3) (cell 4)))" shouldFlexCheckTo (FlexOk("bool"))
        assert(flexErr("(flexk () (cell=? (cell 3) (cell #t)))").contains("cell=? requires cells with the same content type"))
        assert(flexErr("(flexk () (:= (cell 3) #t))").contains("(:= ...) expects a value of type"))
        assert(flexErr("(flexk () (^ 3))").contains("requires a cellof type"))
    }

    "Mutable variables" should "support set! and begin sugar" in {
        "(flexk ((x int)) (begin (set! x 5) x))" shouldFlexCheckTo (FlexOk("(=> (int) int)"))
        assert(flexErr("(flexk ((x int)) (begin (set! x #t) x))").contains("set! of x expects type"))
        assert(flexErr("(flexk () (set! x 5))").contains("unbound variable: x"))
    }

    // ------------------------------------------------------------------
    // flexk: let-type / let-type*
    // ------------------------------------------------------------------

    "Type abbreviations" should "substitute into type positions" in {
        "(flexk () (let-type ((myint int)) (the myint 3)))" shouldFlexCheckTo (FlexOk("int"))
        // Sequential substitution: b is substituted into a's definition.
        "(flexk () (let-type* ((a (-> (int) b)) (b int)) (abs ((x a)) x)))" shouldFlexCheckTo (FlexOk("(-> ((-> (int) int)) (-> (int) int))"))
    }

    // ------------------------------------------------------------------
    // flexk: recursive types (trec)
    // ------------------------------------------------------------------

    "Recursive types" should "unwind for the elimination rules" in {
        // Exercise 11.24: a self-applicable procedure type.
        "(flexk () (let ((f (the (trec s (-> (s) bool)) (error \"f\" (trec s (-> (s) bool)))))) (f f)))" shouldFlexCheckTo (FlexOk("bool"))
        "(flexk () (the (trec s (-> (s) bool)) (error \"x\" (trec s (-> (s) bool)))))" shouldFlexCheckTo (FlexOk("(trec s (-> (s) bool))"))
    }

    // ------------------------------------------------------------------
    // The book's FLEX examples
    // ------------------------------------------------------------------

    "The let-type* example (book p.635)" should "type-check to the transform-apply type" in {
        """(flexk () (let-type* ((intfun (-> (int) int)) (transform (-> (intfun) intfun))) (the (-> (transform transform) transform) (abs ((t1 transform) (t2 transform)) (abs ((f intfun)) (t1 (t2 f)))))))""" shouldFlexCheckTo (FlexOk("(-> ((-> ((-> (int) int)) (-> (int) int)) (-> ((-> (int) int)) (-> (int) int))) (-> ((-> (int) int)) (-> (int) int)))"))
    }

    "The pos?/even? example (book p.636)" should "have program type (=> (bool int) bool)" in {
        "(flex ((b bool) (i int)) (if b (pos? i) (even? i)) (def-type intfun (-> (int) int)) (def-type intpred (-> (int) bool)) (def dec intfun (abs ((x int)) (- x 1))) (def pos? intpred (abs ((y int)) (> y 0))) (def even? intpred (abs ((x int)) (if (= x 0) #t (odd? (dec x))))) (def odd? intpred (abs ((y int)) (if (= y 0) #f (even? (dec y))))))" shouldFlexCheckTo (FlexOk("(=> (bool int) bool)"))
    }

    "The int-tree def-type (book Fig. 12.15)" should "simplify recursive tree types" in {
        "(flex () (make-int-node (one int-tree leaf 3) (one int-tree leaf 4)) (def-type int-tree (trec tr (oneof (leaf int) (node (prodof tr tr))))) (def make-int-node (-> (int-tree int-tree) int-tree) (abs ((l int-tree) (r int-tree)) (one int-tree node (prod l r)))))" shouldFlexCheckTo (FlexOk("(trec tr (oneof (leaf int) (node (prodof tr tr))))"))
    }

    "The shape/perim/scale example (book p.682-684)" should "type-check" in {
        "(flex () (scale (one shape square 3) 2) (def-type shape (oneof (square int) (rectangle (pairof int int)) (triangle (prodof int int int)))) (def perim (-> (shape) int) (abs ((sh shape)) (tagcase sh v (square (* 4 v)) (rectangle (* 2 (+ (fst v) (snd v)))) (triangle (+ (get 1 v) (+ (get 2 v) (get 3 v))))))) (def scale (-> (shape int) shape) (abs ((sh shape) (n int)) (tagcase sh v (square (one shape square (* n v))) (rectangle (one shape rectangle (pair (* n (fst v)) (* n (snd v))))) (triangle (one shape triangle (prod (* n (get 1 v)) (* n (get 2 v)) (* n (get 3 v)))))))))" shouldFlexCheckTo (FlexOk("(oneof (square int) (rectangle (pairof int int)) (triangle (prodof int int int)))"))
    }

    "The map-shape-int example (book p.687)" should "map a list of shapes to a list of ints" in {
        "(flex () (map-shape-int perim (list shape (one shape triangle (prod 7 8 9)))) (def-type shape (oneof (square int) (rectangle (pairof int int)) (triangle (prodof int int int)))) (def perim (-> (shape) int) (abs ((sh shape)) (tagcase sh v (square (* 4 v)) (rectangle (* 2 (+ (fst v) (snd v)))) (triangle (+ (get 1 v) (+ (get 2 v) (get 3 v))))))) (def map-shape-int (-> ((-> (shape) int) (listof shape)) (listof int)) (abs ((f (-> (shape) int)) (ss (listof shape))) (if (null? ss) (null int) (cons (f (car ss)) (map-shape-int f (cdr ss)))))))" shouldFlexCheckTo (FlexOk("(listof int)"))
    }

    "The equirecursively equivalent types Tib1-Tib4 (book Fig. 11.26)" should "accept a the-chain across all four" in {
        "(flex () (the Tib1 (the Tib2 (the Tib3 (the Tib4 (error done Tib1))))) (def-type Tib1 (trec iblist (pairof int (pairof bool iblist)))) (def-type Tib2 (trec int-bool-list (pairof int (pairof bool int-bool-list)))) (def-type Tib3 (pairof int (pairof bool (trec iblist (pairof int (pairof bool iblist)))))) (def-type Tib4 (pairof int (trec bilist (pairof bool (pairof int bilist))))))" shouldFlexCheckTo (FlexOk("(trec iblist (pairof int (pairof bool iblist)))"))
    }

    // ------------------------------------------------------------------
    // The flex sugar language: def, def-type, and the standard library
    // ------------------------------------------------------------------

    "A def" should "declare the type of a top-level definition" in {
        "(flex () (square 6) (def square (-> (int) int) (abs ((n int)) (* n n))))" shouldFlexCheckTo (FlexOk("int"))
        "(flex () (square 6) (def square (-> (int) int) (abs ((n int)) (prim * n n))))" shouldFlexCheckTo (FlexOk("int"))
        assert(flexErr("(flex () #t (def x bool 5))").contains("but is declared to have type bool"))
    }

    "The procedure-defining sugar" should "build an arrow type and an abstraction" in {
        "(flex () (square 6) (def (square int (n int)) (* n n)))" shouldFlexCheckTo (FlexOk("int"))
        // The book's alternative even? definition (p.636).
        "(flex () (even? 4) (def-type intfun (-> (int) int)) (def dec intfun (abs ((x int)) (- x 1))) (def (even? bool (x int)) (if (= x 0) #t (odd? (dec x)))) (def (odd? bool (y int)) (if (= y 0) #f (even? (dec y)))))" shouldFlexCheckTo (FlexOk("bool"))
    }

    "The standard library" should "bind the primitive operators as procedures" in {
        "(flex () (+ 1 4) (def x int 5))" shouldFlexCheckTo (FlexOk("int"))
        "(flex () (= 1 2))" shouldFlexCheckTo (FlexOk("bool"))
        "(flex () (not #t))" shouldFlexCheckTo (FlexOk("bool"))
        "(flex () (bool=? #t #t))" shouldFlexCheckTo (FlexOk("bool"))
        "(flex () (sym=? (sym a) (sym b)))" shouldFlexCheckTo (FlexOk("bool"))
        "(flex () (> 3 2))" shouldFlexCheckTo (FlexOk("bool"))
        "(flex () true)" shouldFlexCheckTo (FlexOk("bool"))
        // In the kernel language, + is just an unbound variable.
        assert(flexErr("(flexk () (+ 1 4))").contains("unbound variable: +"))
    }

    "A def-type" should "be usable in later def-types, defs, and the body" in {
        "(flex () (apply (abs ((n int)) n) 3) (def-type intfun (-> (int) int)) (def apply (-> (intfun int) int) (abs ((f intfun) (x int)) (f x))))" shouldFlexCheckTo (FlexOk("int"))
    }

    // ------------------------------------------------------------------
    // Ill-typed programs
    // ------------------------------------------------------------------

    "An ill-typed program" should "produce a type error" in {
        assert(flexErr("(flexk () y)").contains("unbound variable: y"))
        assert(flexErr("(flexk () (the foo 1))").contains("malformed type in a (the ...) expression"))
        assert(flexErr("(flexk () (the t 3))").contains("malformed type in a (the ...) expression"))
        assert(flexErr("(flexk () (letrec ((f (-> (int) bool) (abs ((n int)) n))) #t))").contains("but is declared to have type"))
        assert(flexErr("(flexk () (letrec ((f foo (abs ((n int)) n))) #t))").contains("malformed type in letrec binding f"))
        assert(flexErr("(flexk () (the (pairof int bool) 3))").contains("the type ascription says"))
    }
}
