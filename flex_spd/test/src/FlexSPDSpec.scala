package DSL.flex_spd

import DSL.flex._
import org.scalatest.flatspec.AnyFlatSpecLike

class FlexSPDSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexspdErr(input: String): String = {
        flexspdCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // The standard-library list type of element type t, as the checker
    // displays it (Figure 12.19 of the book):
    private def listOf(t: String): String =
        s"(tletrec ((listof-t (oneof (null unit) (cons (prodof $t listof-t))))) listof-t)"

    // ------------------------------------------------------------------
    // Parsing (Figure 12.18: the FLEX/SP syntax in which every type
    // position is a description, plus dabs / dletrec / plet / pletrec)
    // ------------------------------------------------------------------

    "A valid FLEX/SPD program" should "parse" in {
        assert(FlexSPDProgram("(flexk/SPD () 3)").isDefined)
        assert(FlexSPDProgram("(flex/SPD () 3)").isDefined)
        assert(FlexSPDProgram("(flex/SPD () ((pcall (pabs (t) (abs ((x t)) x)) int) 3))").isDefined)
        assert(FlexSPDProgram("(flex/SPD () (the (drec t (oneof (a unit))) #u))").isDefined)
        assert(FlexSPDProgram("(flex/SPD () (plet ((a int)) (the a 3)))").isDefined)
        assert(FlexSPDProgram("(flex/SPD () (pletrec ((a int) (b a)) (the b 3)))").isDefined)
        // FLEX / FLEX/SP tags are not FLEX/SPD tags.
        assert(FlexSPDProgram("(flex () 3)").isEmpty)
        assert(FlexSPDProgram("(flex/SP () 3)").isEmpty)
        assert(FlexSPDProgram("(flexk/SP () 3)").isEmpty)
        assert(FlexSPDProgram("(foo () 3)").isEmpty) // unknown program tag
    }

    "a bare pair / list keyword" should "name a standard-library value in a value position" in {
        // cons / car / cdr / null / null? / pair / fst / snd are polymorphic
        // standard-library values in FLEX/SPD (book p.755, Figure 12.19), so
        // they parse as value identifiers, not as kernel constructs.
        assert(FlexSPDProgram("(flexk/SPD () ((pcall (pcall cons int) 1) (pcall null int)))").isDefined)
        assert(FlexSPDProgram("(flexk/SPD () ((pcall (pcall null? int)) (pcall null int)))").isDefined)
        assert(FlexSPDProgram("(flexk/SPD () (cons 1 2))").isDefined) // parses; rejected at check
    }

    // ------------------------------------------------------------------
    // Description binding in expressions: plet / pletrec (Figure 12.18)
    // ------------------------------------------------------------------

    "the plet example (book p.755)" should "type-check" in {
        // (plet ((pairof (dabs (s t) (prodof s t))))
        //   (the (pairof int (pairof bool symb))
        //         (prod 3 (prod #f (sym Abby)))))
        "(flex/SPD () (plet ((pairof (dabs (s t) (prodof s t))))" +
            " (the (pairof int (pairof bool symb))" +
            "      (prod 3 (prod #f (sym Abby))))))" shouldFlexSPDCheckTo
            (FlexOk("(prodof int (prodof bool symb))"))
    }

    "the plet transparency example (book p.757)" should "type-check" in {
        // A plet-bound description is equivalent to its definition:
        // (plet ((s int) (t int)) (abs ((b bool) (x s) (y t)) (if b x y)))
        "(flex/SPD () (plet ((s int) (t int))" +
            " (abs ((b bool) (x s) (y t)) (if b x y))))" shouldFlexSPDCheckTo
            (FlexOk("(-> (bool int int) int)"))
    }

    "a pletrec binding" should "be usable in the body" in {
        "(flex/SPD () (pletrec ((tr (drec tr (oneof (leaf int) (node (prodof tr tr))))))" +
            " (the tr (one tr leaf 5))))" shouldFlexSPDCheckTo
            (FlexOk("(tletrec ((tr (oneof (leaf int) (node (prodof tr tr))))) tr)"))
    }

    "mutually recursive pletrec bindings" should "resolve through the sibling scope" in {
        // a's payload (tag x) is b's type; the expression must have b's type
        // to be accepted under the ascription to a.
        "(flex/SPD () (pletrec ((a (drec a (oneof (x b))))" +
            " (b (drec b (oneof (y int)))))" +
            " (the a (one a x (one b y 3)))))" shouldFlexSPDCheckTo
            (FlexOk("(tletrec ((a (oneof (x (tletrec ((b (oneof (y int)))) b))))) a)"))
    }

    "a pletrec cycle used as a type" should "be rejected" in {
        // a and b are mutually aliasing; neither denotes a type.
        flexspdErr("(flex/SPD () (pletrec ((a b) (b a)) (the a #u)))")
    }

    // ------------------------------------------------------------------
    // Description application and beta-equivalence (Figure 12.20)
    // ------------------------------------------------------------------

    "a description application" should "normalize to its beta-equivalent type" in {
        // ((dabs (s t) (prodof s t)) int bool)  ≈  (prodof int bool)  [dabs-beta-≈]
        "(flex/SPD () (the A (the B (prod 1 #t)))" +
            " (def-desc A ((dabs (s t) (prodof s t)) int bool))" +
            " (def-desc B (prodof int bool)))" shouldFlexSPDCheckTo
            (FlexOk("(prodof int bool)"))
    }

    "the book's def-desc examples (p.755)" should "type-check" in {
        // (def-desc intlist (listof int)) and
        // (def-desc twiceof (dabs (t) (prodof t t)))
        "(flex/SPD () (the (twiceof int) (prod 3 4))" +
            " (def-desc intlist (listof int))" +
            " (def-desc twiceof (dabs (t) (prodof t t))))" shouldFlexSPDCheckTo
            (FlexOk("(prodof int int)"))
        "(flex/SPD () (the intlist ((pcall cons int) 1 ((pcall null int))))" +
            " (def-desc intlist (listof int)))" shouldFlexSPDCheckTo
            (FlexOk(listOf("int")))
    }

    "a base type in rator position (safe nonsense, p.757)" should "parse but fail the check" in {
        flexspdErr("(flexk/SPD () (the (int bool) #u))")
        flexspdErr("(flexk/SPD () (the cellof #u))")
        flexspdErr("(flexk/SPD () (the (dabs (t) t) #u))")
        flexspdErr("(flexk/SPD () (abs ((x cellof) (y (dabs (t) t))) (prod x y)))")
    }

    "the book's looping description (p.758)" should "not hang and should be rejected" in {
        // ((dabs (d) (d d)) (dabs (d) (d d))) is non-normalizing; the
        // trampoline normalizer cuts it off at the step bound.
        val m = flexspdErr("(flexk/SPD () (the ((dabs (d) (d d)) (dabs (d) (d d))) #u))")
        assert(m.contains("malformed description"))
    }

    "trec / tletrec are no longer type spellings (Figure 12.18)" should "be rejected" in {
        // trec is parsed as a description identifier (an application rator),
        // which is unbound and hence not a type.
        flexspdErr("(flexk/SPD () (the (trec tr (oneof (a unit))) #u))")
        flexspdErr("(flexk/SPD () (the (tletrec ((tr (oneof (a unit)))) tr) #u))")
    }

    "an arity-mismatched description application" should "be rejected" in {
        flexspdErr("(flexk/SPD () (the (pairof int) (prod 1 2)))")
    }

    // ------------------------------------------------------------------
    // The standard-library list and pair values (book p.755, Figure 12.19)
    // ------------------------------------------------------------------

    "the polymorphic list and pair values" should "work through pcall" in {
        "(flex/SPD () ((pcall cons int) 1 ((pcall null int))))" shouldFlexSPDCheckTo
            (FlexOk(listOf("int")))
        "(flex/SPD () ((pcall car int) ((pcall cons int) 1 ((pcall null int)))))" shouldFlexSPDCheckTo
            (FlexOk("int"))
        "(flex/SPD () ((pcall cdr int) ((pcall cons int) 1 ((pcall null int)))))" shouldFlexSPDCheckTo
            (FlexOk(listOf("int")))
        "(flex/SPD () ((pcall null? int) ((pcall cons int) 1 ((pcall null int)))))" shouldFlexSPDCheckTo
            (FlexOk("bool"))
        "(flex/SPD () ((pcall pair int bool) 1 #t))" shouldFlexSPDCheckTo
            (FlexOk("(prodof int bool)"))
        "(flex/SPD () ((pcall fst int bool) ((pcall pair int bool) 1 #t)))" shouldFlexSPDCheckTo
            (FlexOk("int"))
        "(flex/SPD () ((pcall snd int bool) ((pcall pair int bool) 1 #t)))" shouldFlexSPDCheckTo
            (FlexOk("bool"))
        // A polymorphic standard-library value used without a pcall is rejected.
        flexspdErr("(flexk/SPD () (cons 1 2))")
        flexspdErr("(flexk/SPD () (pair 1 #t))")
    }

    "a formal parameter typed with a description" should "display the description as written" in {
        "(flex/SPD ((p (pairof int bool))) ((pcall fst int bool) p))" shouldFlexSPDCheckTo
            (FlexOk("(=> ((pairof int bool)) int)"))
    }

    // ------------------------------------------------------------------
    // The higher-order description operator mapperof (book pp.755-756)
    // ------------------------------------------------------------------

    private val mapperofDecl =
        "(def-desc mapperof (dabs (type-constructor)" +
        " (forall (in-type out-type)" +
        " (-> ((-> (in-type) out-type) (type-constructor in-type))" +
        "     (type-constructor out-type)))))"

    "the list-map procedure (book p.755, via mapperof)" should "type-check" in {
        val prog =
            "(flex/SPD ()" +
            " ((pcall list-map int bool)" +
            " (abs ((x int)) (prim = x 0))" +
            " ((pcall cons int) 23" +
            " ((pcall cons int) 13" +
            " ((pcall cons int) 29 ((pcall null int))))))" +
            " " + mapperofDecl +
            " (def list-map (mapperof listof)" +
            " (pabs (in-type out-type)" +
            " (abs ((f (-> (in-type) out-type)) (xs (listof in-type)))" +
            " (if ((pcall null? in-type) xs)" +
            " ((pcall null out-type))" +
            " ((pcall cons out-type)" +
            " (f ((pcall car in-type) xs))" +
            " ((pcall list-map in-type out-type)" +
            " f ((pcall cdr in-type) xs))))))))"
        prog shouldFlexSPDCheckTo (FlexOk(listOf("bool")))
    }

    "the seq-map procedure (book p.755, via mapperof seqof)" should "type-check" in {
        // The declared type (mapperof seqof) is a description application
        // whose operator is a base type constructor (seqof, Figure 12.18).
        val prog =
            "(flex/SPD ()" +
            " ((pcall seq-map int bool)" +
            " (abs ((x int)) (prim = x 0))" +
            " (seq 1 2 3))" +
            " " + mapperofDecl +
            " (def seq-map (mapperof seqof)" +
            " (pabs (in-type out-type)" +
            " (abs ((f (-> (in-type) out-type)) (xs (seqof in-type)))" +
            " (error todo (seqof out-type))))))"
        prog shouldFlexSPDCheckTo (FlexOk("(seqof bool)"))
    }

    // ------------------------------------------------------------------
    // Type constructors: make-node (book Figure 12.17)
    // ------------------------------------------------------------------

    "make-node (book Figure 12.17)" should "type-check" in {
        // (pcall make-node int) projects make-node to
        // (-> ((treeof int) (treeof int)) (treeof int)); applying it to two
        // int-trees yields the (treeof int) type constructor's type.
        val prog =
            "(flex/SPD ()" +
            " ((pcall make-node int)" +
            " (one (treeof int) leaf 1)" +
            " (one (treeof int) node (prod (one (treeof int) leaf 2) (one (treeof int) leaf 3))))" +
            " (def-desc treeof" +
            " (dabs (leaf-type)" +
            " (drec tr (oneof (leaf leaf-type) (node (prodof tr tr))))))" +
            " (def make-node (forall (t) (-> ((treeof t) (treeof t)) (treeof t)))" +
            " (pabs (t)" +
            " (abs ((l (treeof t)) (r (treeof t)))" +
            " (one (treeof t) node (prod l r))))))"
        prog shouldFlexSPDCheckTo
            (FlexOk("(tletrec ((tr (oneof (leaf int) (node (prodof tr tr))))) tr)"))
    }

    // ------------------------------------------------------------------
    // Universal polymorphism (Figure 12.9): FLEX/SP regression
    // ------------------------------------------------------------------

    "EpolyId (book Figure 12.10)" should "type-check to int" in {
        "(flexk/SPD () (let ((id (pabs (t) (abs ((x t)) x))))" +
            " (if ((pcall id bool) #t)" +
            " 1" +
            " (((pcall id (-> (int) int)) (pcall id int)) 2))))" shouldFlexSPDCheckTo (FlexOk("int"))
    }

    "a polymorphic value projected onto an enclosing pabs variable" should "type-check" in {
        "(flexk/SPD () (pabs (t) (let ((id (pabs (u) (abs ((x u)) x))))" +
            " ((pcall id (-> (t) t)) (pcall id t) (abs ((x t)) x)))))" shouldFlexSPDCheckTo
            (FlexOk("(forall (t) (-> (t) t))"))
    }

    "pcall (Figure 12.9)" should "reject a wrong number of type arguments" in {
        flexspdErr("(flexk/SPD () (pcall (pabs (t u) (abs ((x t)) x)) int))")
        // A monomorphic value is not a polymorphic value.
        flexspdErr("(flexk/SPD () (pcall (abs ((x int)) x) int))")
    }

    "the import restriction (book p.732)" should "reject polytest" in {
        val prog =
            "(flex/SPD () #u (def polytest (forall (t) (-> (t) (forall (t) t)))" +
                " (pabs (t) (abs ((x t)) (pabs (t) x)))))"
        assert(flexspdErr(prog).contains("import restriction"))
    }

    "the purity restriction (Figure 12.9)" should "reject a pabs body that mutates" in {
        val prog = "(flexk/SPD () (let ((c (cell 1))) (pabs (t) (:= c 2))))"
        assert(flexspdErr(prog).contains("purity restriction"))
        // set! is rejected too.
        flexspdErr("(flexk/SPD () (let ((x 1)) (pabs (t) (set! x 2))))")
    }

    "forall types (Figure 12.9)" should "compare up to alpha-renaming" in {
        // [forall-≤] at a the-ascription.
        "(flexk/SPD () (the (forall (t) (-> (t) t)) (pabs (u) (abs ((x u)) x))))" shouldFlexSPDCheckTo
            (FlexOk("(forall (t) (-> (t) t))"))
        // ... in the other direction as well.
        "(flexk/SPD () (the (forall (u) (-> (u) u)) (pabs (t) (abs ((x t)) x))))" shouldFlexSPDCheckTo
            (FlexOk("(forall (u) (-> (u) u))"))
        // [forall-approx] at the def match point: the declared type binds
        // t, the body binds u — accepted up to alpha-renaming.
        "(flex/SPD () ((pcall id int) 3)" +
            " (def id (forall (t) (-> (t) t)) (pabs (u) (abs ((x u)) x))))" shouldFlexSPDCheckTo
            (FlexOk("int"))
        // A body that is not a subtype is rejected (the FLEX/SP test's
        // (trec x ...) description is spelled with the FLEX/SPD drec).
        flexspdErr(
            "(flexk/SPD () (the (forall (t) (-> (t) (drec x (pairof t x))))" +
                " (pabs (t) (abs ((x t)) (pcall (pcall pair t t) x (abs ((y t)) y))))))")
    }

    "subtyping through forall (Figure 12.9 + 12.2)" should "be contravariant in the arguments" in {
        // The definition takes a record with FEWER fields than the declared
        // formal type: a procedure taking a narrower record is a subtype of
        // one taking a wider record.
        "(flex/SPD () ((pcall pick int) (record (a 3) (b 4)))" +
            " (def pick (forall (t) (-> ((recordof (a t) (b t))) t))" +
            " (pabs (t) (abs ((r (recordof (a t)))) (select a r)))))" shouldFlexSPDCheckTo
            (FlexOk("int"))
        // ... but the other direction is not safe, and is rejected.
        flexspdErr(
            "(flex/SPD () ((pcall pick int) (record (a 3)))" +
                " (def pick (forall (t) (-> ((recordof (a t))) t))" +
                " (pabs (t) (abs ((r (recordof (a t) (b t)))) (select a r)))))")
    }

    // ------------------------------------------------------------------
    // Deconstructible data types (Figures 12.11, 12.12, 12.13), with the
    // recursive description spelling (dletrec) of Figure 12.18
    // ------------------------------------------------------------------

    private val intlistDecl = "(def-datatype intlist (inull) (icons int intlist))"

    "def-datatype intlist (book Figure 12.11)" should "define a constructor and a deconstructor" in {
        // The constructor.
        ("(flex/SPD () (icons 1 (inull)) " + intlistDecl + ")") shouldFlexSPDCheckTo
            (FlexOk("(tletrec ((intlist (oneof (inull (prodof)) (icons (prodof int intlist))))) intlist)"))
        // The deconstructor, projected onto int.
        ("(flex/SPD () ((pcall icons~ int) (icons 1 (inull))" +
            " (abs ((n int) (ms intlist)) n)" +
            " (abs () 0)) " + intlistDecl + ")") shouldFlexSPDCheckTo (FlexOk("int"))
        // A deconstructor argument of the wrong type is rejected: the
        // inull~ success continuation must have type (-> () int), but is
        // given (-> () bool).
        flexspdErr(
            "(flex/SPD () (bad (inull))" +
                " " + intlistDecl +
                " (def bad (-> (intlist) int)" +
                " (abs ((ns intlist))" +
                " ((pcall inull~ int) ns (abs () #t) (abs () 1)))))")
    }

    "the intlist procedures (book Figure 12.12)" should "type-check" in {
        // sum
        ("(flex/SPD () (sum (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def sum (-> (intlist) int)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ int) ns (abs () 0)" +
            " (abs ()" +
            " ((pcall icons~ int) ns" +
            " (abs ((n int) (ms intlist)) (+ n (sum ms)))" +
            " (abs () (error shouldnt-happen int)))))))" +
            ")") shouldFlexSPDCheckTo (FlexOk("int"))
        // all-positive?
        ("(flex/SPD () (all-positive? (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def all-positive? (-> (intlist) bool)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ bool) ns (abs () #t)" +
            " (abs ()" +
            " ((pcall icons~ bool) ns" +
            " (abs ((n int) (ms intlist)) (scand (> n 0) (all-positive? ms)))" +
            " (abs () (error shouldnt-happen bool)))))))" +
            ")") shouldFlexSPDCheckTo (FlexOk("bool"))
        // map-square (the book's Figure 12.12 writes (cons ...), which is a
        // typo: building an intlist out of an int and an intlist is the
        // data-type constructor (icons ...), not the list cons).
        ("(flex/SPD () (map-square (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def map-square (-> (intlist) intlist)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ intlist) ns (abs () (inull))" +
            " (abs ()" +
            " ((pcall icons~ intlist) ns" +
            " (abs ((n int) (ms intlist)) (icons (* n n) (map-square ms)))" +
            " (abs () (error shouldnt-happen intlist)))))))" +
            ")") shouldFlexSPDCheckTo
            (FlexOk("(tletrec ((intlist (oneof (inull (prodof)) (icons (prodof int intlist))))) intlist)"))
    }

    // ------------------------------------------------------------------
    // FLEX/SP regression: FLEX/SPD is a superset of FLEX/SP (modulo the
    // trec / tletrec spellings, replaced by drec / dletrec)
    // ------------------------------------------------------------------

    "FLEX/SP programs (superset property)" should "still type-check under FLEX/SPD" in {
        // get-age with a superset record (book p.702).
        "(flex/SPD () (get-age (record (name (sym Polly_Morwicz)) (age 35) (student? #f)))" +
            " (def get-age (-> ((recordof (age int))) int)" +
            " (abs ((r (recordof (age int)))) (select age r))))" shouldFlexSPDCheckTo (FlexOk("int"))
        // The pos?/even? FLEX example (book p.636) under the FLEX/SPD tag,
        // with the def-type items accepted as def-desc aliases.
        "(flex/SPD ((b bool) (i int)) (if b (pos? i) (even? i))" +
            " (def-type intfun (-> (int) int))" +
            " (def-type intpred (-> (int) bool))" +
            " (def dec intfun (abs ((x int)) (- x 1)))" +
            " (def pos? intpred (abs ((y int)) (> y 0)))" +
            " (def even? intpred (abs ((x int)) (if (= x 0) #t (odd? (dec x)))))" +
            " (def odd? intpred (abs ((y int)) (if (= y 0) #f (even? (dec y))))))" shouldFlexSPDCheckTo
            (FlexOk("(=> (bool int) bool)"))
    }
}
