package DSL.flex_spdk

import DSL.flex._
import org.scalatest.flatspec.AnyFlatSpecLike

class FlexSPDKSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexspdkErr(input: String): String = {
        flexspdkCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // The standard-library list type of element type t, as the checker
    // displays it (Figure 12.19 of the book):
    private def listOf(t: String): String =
        s"(tletrec ((listof-t (oneof (null unit) (cons (prodof $t listof-t))))) listof-t)"

    // ------------------------------------------------------------------
    // Parsing (Figure 12.21: the FLEX/SPD syntax with kind-annotated
    // pabs / forall / dabs binders; K ::= type | (->> (K*) K))
    // ------------------------------------------------------------------

    "A valid FLEX/SPDK program" should "parse" in {
        assert(FlexSPDKProgram("(flexk/SPDK () 3)").isDefined)
        assert(FlexSPDKProgram("(flex/SPDK () 3)").isDefined)
        assert(FlexSPDKProgram("(flex/SPDK () ((pcall (pabs (t type) (abs ((x t)) x)) int) 3))").isDefined)
        assert(FlexSPDKProgram("(flex/SPDK () (pletrec ((a int) (b a)) (the b 3)))").isDefined)
        // An empty kinded binder list is allowed.
        assert(FlexSPDKProgram("(flexk/SPDK () (pabs () 3))").isDefined)
        assert(FlexSPDKProgram("(flexk/SPDK () (the (forall (t type) (-> (t) t)) (pabs (t type) (abs ((x t)) x))))").isDefined)
        // The kind keywords type and ->> are NOT descriptions: (type ...)
        // and (->> ...) do not parse in description position, and a bare
        // type / ->> is not a description identifier.
        assert(FlexSPDKProgram("(flexk/SPDK () (the (type int) 3))").isEmpty)
        assert(FlexSPDKProgram("(flexk/SPDK () (the (->> (type) type) 3))").isEmpty)
        assert(FlexSPDKProgram("(flexk/SPDK () (the type 3))").isEmpty)
        // An unkinded or odd-length binder list does not parse.
        assert(FlexSPDKProgram("(flexk/SPDK () (pabs (t) (abs ((x t)) x)))").isEmpty)
        assert(FlexSPDKProgram("(flexk/SPDK () (pabs (t type t) (abs ((x t)) x)))").isEmpty)
        assert(FlexSPDKProgram("(flexk/SPDK () (the (forall (t) (-> (t) t)) 3))").isEmpty)
        // FLEX / FLEX/SP / FLEX/SPD tags are not FLEX/SPDK tags.
        assert(FlexSPDKProgram("(flexk/SPD () 3)").isEmpty)
        assert(FlexSPDKProgram("(flex () 3)").isEmpty)
    }

    // ------------------------------------------------------------------
    // Kind checking (Figure 12.22): which descriptions have kind type
    // ------------------------------------------------------------------

    "the kind-type examples (book p.759)" should "have kind type" in {
        "(flexk/SPDK () (the int 3))" shouldFlexSPDKCheckTo (FlexOk("int"))
        "(flexk/SPDK () (the (-> (int) bool) (abs ((x int)) #t)))" shouldFlexSPDKCheckTo
            (FlexOk("(-> (int) bool)"))
        "(flexk/SPDK () (the (recordof (name symb) (age int))" +
            " (record (name (sym a)) (age 3))))" shouldFlexSPDKCheckTo
            (FlexOk("(recordof (name symb) (age int))"))
        // (drec intlist ...) is a def-desc spelling: the recursive data type
        // is well kinded (kind type) and denotes the tletrec type.
        "(flex/SPDK () (the (drec intlist (oneof (inull unit) (icons (prodof int intlist))))" +
            " (one intlist inull #u))" +
            " (def-desc intlist (drec intlist (oneof (inull unit) (icons (prodof int intlist))))))" shouldFlexSPDKCheckTo
            (FlexOk("(tletrec ((intlist (oneof (inull unit) (icons (prodof int intlist))))) intlist)"))
    }

    "description operators are not types (book p.759)" should "be rejected in type position" in {
        val m = flexspdkErr("(flexk/SPDK () (the cellof #u))")
        assert(m.contains("has kind (->> (type) type), not kind type"))
        flexspdkErr("(flexk/SPDK () (the (dabs (t type) t) #u))")
        flexspdkErr("(flexk/SPDK () (abs ((x cellof) (y (dabs (t type) t))) (prod x y)))")
    }

    "ill-kinded description applications" should "be rejected" in {
        // (int bool): a base type is not a description operator.
        flexspdkErr("(flexk/SPDK () (the (int bool) #u))")
        // (pairof int): one argument, but pairof takes two.
        flexspdkErr("(flexk/SPDK () (the (pairof int) (prod 1 2)))")
        // (listof int bool): two arguments, but listof takes one.
        flexspdkErr("(flexk/SPDK () (the (listof int bool) ((pcall null int))))")
    }

    "the book's looping description (p.758)" should "not hang and should be rejected" in {
        // ((dabs (d) (d d)) (dabs (d) (d d))) needs kind-level recursion to
        // be well kinded; kind checking (unlike normalization) decides it
        // in one step: the argument has an arrow kind, not kind type.
        val m = flexspdkErr("(flexk/SPDK () (the ((dabs (d type) (d d)) (dabs (d type) (d d))) #u))")
        assert(m.contains("is not well kinded"))
    }

    "an ill-kinded def-desc used as a type" should "be rejected" in {
        // The def-desc's definition (a dletrec whose binding has an arrow
        // kind) is not of kind type, so the alias is not well kinded.
        val m = flexspdkErr(
            "(flex/SPDK () (the listof ((pcall null int)))" +
            " (def-desc listof (dletrec ((listof (dabs (t type) (listof t)))) listof)))")
        assert(m.contains("is not well kinded"))
    }

    // ------------------------------------------------------------------
    // Description binding in expressions: plet / pletrec (Figure 12.18)
    // with the kind-at-use rule of Section 12.3.2
    // ------------------------------------------------------------------

    "the plet example (book p.755)" should "type-check" in {
        // (plet ((pairof (dabs (s t) (prodof s t))))
        //   (the (pairof int (pairof bool symb))
        //         (prod 3 (prod #f (sym Abby)))))
        "(flexk/SPDK () (plet ((pairof (dabs (s type t type) (prodof s t))))" +
            " (the (pairof int (pairof bool symb))" +
            "      (prod 3 (prod #f (sym Abby))))))" shouldFlexSPDKCheckTo
            (FlexOk("(prodof int (prodof bool symb))"))
    }

    "a plet-bound name with an arrow kind" should "be rejected as a type" in {
        // The plet name's kind is the kind of its definition (an arrow
        // kind here), computed at the use position, so (the f ...) fails.
        val m = flexspdkErr("(flexk/SPDK () (plet ((f (dabs (t type) t))) (the f 3)))")
        assert(m.contains("has kind (->> (type) type), not kind type"))
    }

    "a pletrec binding" should "be usable in the body" in {
        "(flexk/SPDK () (pletrec ((tr (drec tr (oneof (leaf int) (node (prodof tr tr))))))" +
            " (the tr (one tr leaf 5))))" shouldFlexSPDKCheckTo
            (FlexOk("(tletrec ((tr (oneof (leaf int) (node (prodof tr tr))))) tr)"))
    }

    "mutually recursive pletrec bindings" should "resolve through the sibling scope" in {
        // a's payload (tag x) is b's type; the expression must have b's type
        // to be accepted under the ascription to a.
        "(flexk/SPDK () (pletrec ((a (drec a (oneof (x b))))" +
            " (b (drec b (oneof (y int)))))" +
            " (the a (one a x (one b y 3)))))" shouldFlexSPDKCheckTo
            (FlexOk("(tletrec ((a (oneof (x (tletrec ((b (oneof (y int)))) b))))) a)"))
    }

    "a pletrec cycle used as a type" should "be rejected" in {
        // a and b are mutually aliasing; the alias chain does not terminate
        // in a kind, so neither is well kinded.
        val m = flexspdkErr("(flexk/SPDK () (pletrec ((a b) (b a)) (the a #u)))")
        assert(m.contains("is not well kinded"))
    }

    // ------------------------------------------------------------------
    // Description application and beta-equivalence (Figure 12.20)
    // ------------------------------------------------------------------

    "a description application" should "normalize to its beta-equivalent type" in {
        // ((dabs (s t) (prodof s t)) int bool)  ≈  (prodof int bool)  [dabs-beta-≈]
        "(flex/SPDK () (the A (the B (prod 1 #t)))" +
            " (def-desc A ((dabs (s type t type) (prodof s t)) int bool))" +
            " (def-desc B (prodof int bool)))" shouldFlexSPDKCheckTo
            (FlexOk("(prodof int bool)"))
    }

    "the book's def-desc examples (p.755)" should "type-check" in {
        // (def-desc intlist (listof int)) and
        // (def-desc twiceof (dabs (t) (prodof t t)))
        "(flex/SPDK () (the (twiceof int) (prod 3 4))" +
            " (def-desc intlist (listof int))" +
            " (def-desc twiceof (dabs (t type) (prodof t t))))" shouldFlexSPDKCheckTo
            (FlexOk("(prodof int int)"))
        "(flex/SPDK () (the intlist ((pcall cons int) 1 ((pcall null int))))" +
            " (def-desc intlist (listof int)))" shouldFlexSPDKCheckTo
            (FlexOk(listOf("int")))
        // twiceof is a type CONSTRUCTOR, not a type: rejected as a type.
        val m = flexspdkErr(
            "(flex/SPDK () (the twiceof #u)" +
            " (def-desc twiceof (dabs (t type) (prodof t t))))")
        assert(m.contains("has kind (->> (type) type), not kind type"))
    }

    "the well-kinded Dlistof def-desc (dabs over dletrec)" should "denote a type" in {
        // (def-desc Dlistof (dabs (t) (dletrec ((listof-t (oneof (null unit)
        //     (cons (prodof t listof-t))))) listof-t)))  — the book's
        // reordered spelling (p.759); (Dlistof int) denotes the int list type.
        "(flex/SPDK () (the (Dlistof int) ((pcall null int)))" +
            " (def-desc Dlistof (dabs (t type)" +
            "  (dletrec ((listof-t (oneof (null unit) (cons (prodof t listof-t)))))" +
            "            listof-t))))" shouldFlexSPDKCheckTo
            (FlexOk(listOf("int")))
    }

    // ------------------------------------------------------------------
    // The standard-library list and pair values (book p.755, Figure 12.19)
    // ------------------------------------------------------------------

    "the polymorphic list and pair values" should "work through pcall" in {
        "(flex/SPDK () ((pcall cons int) 1 ((pcall null int))))" shouldFlexSPDKCheckTo
            (FlexOk(listOf("int")))
        "(flex/SPDK () ((pcall car int) ((pcall cons int) 1 ((pcall null int)))))" shouldFlexSPDKCheckTo
            (FlexOk("int"))
        "(flex/SPDK () ((pcall cdr int) ((pcall cons int) 1 ((pcall null int)))))" shouldFlexSPDKCheckTo
            (FlexOk(listOf("int")))
        "(flex/SPDK () ((pcall null? int) ((pcall cons int) 1 ((pcall null int)))))" shouldFlexSPDKCheckTo
            (FlexOk("bool"))
        "(flex/SPDK () ((pcall pair int bool) 1 #t))" shouldFlexSPDKCheckTo
            (FlexOk("(prodof int bool)"))
        "(flex/SPDK () ((pcall fst int bool) ((pcall pair int bool) 1 #t)))" shouldFlexSPDKCheckTo
            (FlexOk("int"))
        "(flex/SPDK () ((pcall snd int bool) ((pcall pair int bool) 1 #t)))" shouldFlexSPDKCheckTo
            (FlexOk("bool"))
        // A polymorphic standard-library value used without a pcall is rejected.
        flexspdkErr("(flexk/SPDK () (cons 1 2))")
        flexspdkErr("(flexk/SPDK () (pair 1 #t))")
    }

    "a formal parameter typed with a description" should "display the description as written" in {
        "(flex/SPDK ((p (pairof int bool))) ((pcall fst int bool) p))" shouldFlexSPDKCheckTo
            (FlexOk("(=> ((pairof int bool)) int)"))
    }

    // ------------------------------------------------------------------
    // The higher-order description operator mapperof (book pp.755-756)
    // ------------------------------------------------------------------

    private val mapperofDecl =
        "(def-desc mapperof (dabs (type-constructor (->> (type) type))" +
        " (forall (in-type type out-type type)" +
        " (-> ((-> (in-type) out-type) (type-constructor in-type))" +
        "     (type-constructor out-type)))))"

    "the list-map procedure (book p.755, via mapperof)" should "type-check" in {
        val prog =
            "(flex/SPDK ()" +
            " ((pcall list-map int bool)" +
            " (abs ((x int)) (prim = x 0))" +
            " ((pcall cons int) 23" +
            " ((pcall cons int) 13" +
            " ((pcall cons int) 29 ((pcall null int))))))" +
            " " + mapperofDecl +
            " (def list-map (mapperof listof)" +
            " (pabs (in-type type out-type type)" +
            " (abs ((f (-> (in-type) out-type)) (xs (listof in-type)))" +
            " (if ((pcall null? in-type) xs)" +
            " ((pcall null out-type))" +
            " ((pcall cons out-type)" +
            " (f ((pcall car in-type) xs))" +
            " ((pcall list-map in-type out-type)" +
            " f ((pcall cdr in-type) xs))))))))"
        prog shouldFlexSPDKCheckTo (FlexOk(listOf("bool")))
    }

    "the seq-map procedure (book p.755, via mapperof seqof)" should "type-check" in {
        // The declared type (mapperof seqof) is a description application
        // whose operator is a base type constructor (seqof, Figure 12.18).
        val prog =
            "(flex/SPDK ()" +
            " ((pcall seq-map int bool)" +
            " (abs ((x int)) (prim = x 0))" +
            " (seq 1 2 3))" +
            " " + mapperofDecl +
            " (def seq-map (mapperof seqof)" +
            " (pabs (in-type type out-type type)" +
            " (abs ((f (-> (in-type) out-type)) (xs (seqof in-type)))" +
            " (error todo (seqof out-type))))))"
        prog shouldFlexSPDKCheckTo (FlexOk("(seqof bool)"))
    }

    // ------------------------------------------------------------------
    // Type constructors: make-node (book Figure 12.17)
    // ------------------------------------------------------------------

    "make-node (book Figure 12.17)" should "type-check" in {
        // (pcall make-node int) projects make-node to
        // (-> ((treeof int) (treeof int)) (treeof int)); applying it to two
        // int-trees yields the (treeof int) type constructor's type.
        val prog =
            "(flex/SPDK ()" +
            " ((pcall make-node int)" +
            " (one (treeof int) leaf 1)" +
            " (one (treeof int) node (prod (one (treeof int) leaf 2) (one (treeof int) leaf 3))))" +
            " (def-desc treeof" +
            " (dabs (leaf-type type)" +
            " (drec tr (oneof (leaf leaf-type) (node (prodof tr tr))))))" +
            " (def make-node (forall (t type) (-> ((treeof t) (treeof t)) (treeof t)))" +
            " (pabs (t type)" +
            " (abs ((l (treeof t)) (r (treeof t)))" +
            " (one (treeof t) node (prod l r))))))"
        prog shouldFlexSPDKCheckTo
            (FlexOk("(tletrec ((tr (oneof (leaf int) (node (prodof tr tr))))) tr)"))
    }

    // ------------------------------------------------------------------
    // Universal polymorphism with explicit kinds (Figure 12.23)
    // ------------------------------------------------------------------

    "EpolyId (book Figure 12.10)" should "type-check to int" in {
        "(flexk/SPDK () (let ((id (pabs (t type) (abs ((x t)) x))))" +
            " (if ((pcall id bool) #t)" +
            " 1" +
            " (((pcall id (-> (int) int)) (pcall id int)) 2))))" shouldFlexSPDKCheckTo (FlexOk("int"))
    }

    "a polymorphic value projected onto an enclosing pabs variable" should "type-check" in {
        "(flexk/SPDK () (pabs (t type) (let ((id (pabs (u type) (abs ((x u)) x))))" +
            " ((pcall id (-> (t) t)) (pcall id t) (abs ((x t)) x)))))" shouldFlexSPDKCheckTo
            (FlexOk("(forall (t type) (-> (t) t))"))
    }

    "pcall (Figure 12.23)" should "reject a wrong number of type arguments" in {
        flexspdkErr("(flexk/SPDK () (pcall (pabs (t type u type) (abs ((x t)) x)) int))")
        // A monomorphic value is not a polymorphic value.
        flexspdkErr("(flexk/SPDK () (pcall (abs ((x int)) x) int))")
    }

    "pcall (Figure 12.23)" should "check the argument kinds in the caller's environment" in {
        // The binder m has an arrow kind; the argument int has kind type.
        val m = flexspdkErr(
            "(flexk/SPDK () (pcall (pabs (m (->> (type) type)) (abs ((x int)) x)) int))")
        assert(m.contains("has kind type, but the binder m has kind (->> (type) type)"))
        // A vacuous arrow-kind binder: its argument must be well kinded, but
        // the substitution is a no-op (the binder does not occur in the body).
        "(flexk/SPDK () (pcall (pabs (m (->> (type) type) t type) (abs ((x t)) x))" +
            " (dabs (s type) s) int))" shouldFlexSPDKCheckTo
            (FlexOk("(-> (int) int)"))
    }

    "the import restriction (book p.732)" should "reject polytest" in {
        val prog =
            "(flex/SPDK () #u (def polytest (forall (t type) (-> (t) (forall (t type) t)))" +
                " (pabs (t type) (abs ((x t)) (pabs (t type) x)))))"
        assert(flexspdkErr(prog).contains("import restriction"))
    }

    "the purity restriction (Figure 12.9)" should "reject a pabs body that mutates" in {
        val prog = "(flexk/SPDK () (let ((c (cell 1))) (pabs (t type) (:= c 2))))"
        assert(flexspdkErr(prog).contains("purity restriction"))
        // set! is rejected too.
        flexspdkErr("(flexk/SPDK () (let ((x 1)) (pabs (t type) (set! x 2))))")
    }

    "forall types (Figure 12.9)" should "compare up to alpha-renaming" in {
        // [forall-≤] at a the-ascription.
        "(flexk/SPDK () (the (forall (t type) (-> (t) t)) (pabs (u type) (abs ((x u)) x))))" shouldFlexSPDKCheckTo
            (FlexOk("(forall (t type) (-> (t) t))"))
        // ... in the other direction as well.
        "(flexk/SPDK () (the (forall (u type) (-> (u) u)) (pabs (t type) (abs ((x t)) x))))" shouldFlexSPDKCheckTo
            (FlexOk("(forall (u type) (-> (u) u))"))
        // [forall-approx] at the def match point: the declared type binds
        // t, the body binds u — accepted up to alpha-renaming.
        "(flex/SPDK () ((pcall id int) 3)" +
            " (def id (forall (t type) (-> (t) t)) (pabs (u type) (abs ((x u)) x))))" shouldFlexSPDKCheckTo
            (FlexOk("int"))
        // A body that is not a subtype is rejected (the FLEX/SP test's
        // (trec x ...) description is spelled with the FLEX/SPD drec).
        flexspdkErr(
            "(flexk/SPDK () (the (forall (t type) (-> (t) (drec x (pairof t x))))" +
                " (pabs (t type) (abs ((x t)) (pcall (pcall pair t t) x (abs ((y t)) y))))))")
    }

    "subtyping through forall (Figure 12.9 + 12.2)" should "be contravariant in the arguments" in {
        // The definition takes a record with FEWER fields than the declared
        // formal type: a procedure taking a narrower record is a subtype of
        // one taking a wider record.
        "(flex/SPDK () ((pcall pick int) (record (a 3) (b 4)))" +
            " (def pick (forall (t type) (-> ((recordof (a t) (b t))) t))" +
            " (pabs (t type) (abs ((r (recordof (a t)))) (select a r)))))" shouldFlexSPDKCheckTo
            (FlexOk("int"))
        // ... but the other direction is not safe, and is rejected.
        flexspdkErr(
            "(flex/SPDK () ((pcall pick int) (record (a 3)))" +
                " (def pick (forall (t type) (-> ((recordof (a t))) t))" +
                " (pabs (t type) (abs ((r (recordof (a t) (b t)))) (select a r)))))")
    }

    "forall binder kinds (Section 12.3.2)" should "must agree" in {
        // An arrow-kind binder, used where the declaration names an
        // arrow-kind binder: accepted.
        "(flexk/SPDK () (the (forall (f (->> (type) type)) (-> (int) int))" +
            " (pabs (f (->> (type) type)) (abs ((x int)) x))))" shouldFlexSPDKCheckTo
            (FlexOk("(forall (f (->> (type) type)) (-> (int) int))"))
        // ... but a type-kind binder where an arrow-kind binder is declared
        // is not a subtype (the binder kinds do not agree).
        flexspdkErr(
            "(flexk/SPDK () (the (forall (f (->> (type) type)) (-> (int) int))" +
                " (pabs (g type) (abs ((x int)) x))))")
    }

    // ------------------------------------------------------------------
    // Deconstructible data types (Figures 12.11, 12.12, 12.13), with the
    // kind-annotated deconstructor of Figure 12.21
    // ------------------------------------------------------------------

    private val intlistDecl = "(def-datatype intlist (inull) (icons int intlist))"

    "def-datatype intlist (book Figure 12.11)" should "define a constructor and a deconstructor" in {
        // The constructor.
        ("(flex/SPDK () (icons 1 (inull)) " + intlistDecl + ")") shouldFlexSPDKCheckTo
            (FlexOk("(tletrec ((intlist (oneof (inull (prodof)) (icons (prodof int intlist))))) intlist)"))
        // The deconstructor, projected onto int.
        ("(flex/SPDK () ((pcall icons~ int) (icons 1 (inull))" +
            " (abs ((n int) (ms intlist)) n)" +
            " (abs () 0)) " + intlistDecl + ")") shouldFlexSPDKCheckTo (FlexOk("int"))
        // A deconstructor argument of the wrong type is rejected: the
        // inull~ success continuation must have type (-> () int), but is
        // given (-> () bool).
        flexspdkErr(
            "(flex/SPDK () (bad (inull))" +
                " " + intlistDecl +
                " (def bad (-> (intlist) int)" +
                " (abs ((ns intlist))" +
                " ((pcall inull~ int) ns (abs () #t) (abs () 1)))))")
    }

    "the intlist procedures (book Figure 12.12)" should "type-check" in {
        // sum
        ("(flex/SPDK () (sum (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def sum (-> (intlist) int)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ int) ns (abs () 0)" +
            " (abs ()" +
            " ((pcall icons~ int) ns" +
            " (abs ((n int) (ms intlist)) (+ n (sum ms)))" +
            " (abs () (error shouldnt-happen int)))))))" +
            ")") shouldFlexSPDKCheckTo (FlexOk("int"))
        // all-positive?
        ("(flex/SPDK () (all-positive? (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def all-positive? (-> (intlist) bool)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ bool) ns (abs () #t)" +
            " (abs ()" +
            " ((pcall icons~ bool) ns" +
            " (abs ((n int) (ms intlist)) (scand (> n 0) (all-positive? ms)))" +
            " (abs () (error shouldnt-happen bool)))))))" +
            ")") shouldFlexSPDKCheckTo (FlexOk("bool"))
        // map-square (the book's Figure 12.12 writes (cons ...), which is a
        // typo: building an intlist out of an int and an intlist is the
        // data-type constructor (icons ...), not the list cons).
        ("(flex/SPDK () (map-square (icons 3 (icons 4 (inull))))" +
            " " + intlistDecl +
            " (def map-square (-> (intlist) intlist)" +
            " (abs ((ns intlist))" +
            " ((pcall inull~ intlist) ns (abs () (inull))" +
            " (abs ()" +
            " ((pcall icons~ intlist) ns" +
            " (abs ((n int) (ms intlist)) (icons (* n n) (map-square ms)))" +
            " (abs () (error shouldnt-happen intlist)))))))" +
            ")") shouldFlexSPDKCheckTo
            (FlexOk("(tletrec ((intlist (oneof (inull (prodof)) (icons (prodof int intlist))))) intlist)"))
    }

    // ------------------------------------------------------------------
    // FLEX/SPD regression: FLEX/SPDK is a superset of FLEX/SPD (modulo the
    // kind annotations, which FLEX/SPDK requires on pabs / forall / dabs)
    // ------------------------------------------------------------------

    "FLEX/SPD programs (superset property)" should "still type-check under FLEX/SPDK" in {
        // get-age with a superset record (book p.702).
        "(flex/SPDK () (get-age (record (name (sym Polly_Morwicz)) (age 35) (student? #f)))" +
            " (def get-age (-> ((recordof (age int))) int)" +
            " (abs ((r (recordof (age int)))) (select age r))))" shouldFlexSPDKCheckTo (FlexOk("int"))
        // The pos?/even? FLEX example (book p.636) under the FLEX/SPDK tag,
        // with the def-type items accepted as def-desc aliases.
        "(flex/SPDK ((b bool) (i int)) (if b (pos? i) (even? i))" +
            " (def-type intfun (-> (int) int))" +
            " (def-type intpred (-> (int) bool))" +
            " (def dec intfun (abs ((x int)) (- x 1)))" +
            " (def pos? intpred (abs ((y int)) (> y 0)))" +
            " (def even? intpred (abs ((x int)) (if (= x 0) #t (odd? (dec x)))))" +
            " (def odd? intpred (abs ((y int)) (if (= y 0) #f (even? (dec y))))))" shouldFlexSPDKCheckTo
            (FlexOk("(=> (bool int) bool)"))
    }
}
