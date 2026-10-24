package DSL.flex_m

import DSL.flex._
import org.scalatest.flatspec.AnyFlatSpecLike

class FlexMSpec extends AnyFlatSpecLike {

    // Reports the error message of an ill-typed (or unparsable) program,
    // failing if the program actually type-checks.
    private def flexmErr(input: String): String = {
        flexmCheck(input) match {
            case FlexErr(m) => m
            case FlexOk(t) => fail(s"expected an error but got FlexOk($t) for: $input")
        }
    }

    // ------------------------------------------------------------------
    // Shared constants (book figures, verbatim)
    // ------------------------------------------------------------------

    // Figure 15.5: TlistModule, the type of ElistModule (Figure 15.3).
    private val T_LIST =
        "(moduleof ((listof t))" +
        " (null (forall (t) (-> () (listof t))))" +
        " (null~ (forall (r t) (-> ((listof t) (-> () r) (-> () r)) r)))" +
        " (cons (forall (t) (-> (t (listof t)) (listof t))))" +
        " (cons~ (forall (r t) (-> ((listof t) (-> (t (listof t)) r) (-> () r)) r)))" +
        " (null? (forall (t) (-> ((listof t)) bool)))" +
        " (car (forall (t) (-> ((listof t)) t)))" +
        " (cdr (forall (t) (-> ((listof t)) (listof t)))))"

    // Exercise 15.1: the pairof module signature (same shape as TlistModule).
    private val T_PAIR =
        "(moduleof ((pairof a b))" +
        " (pair (forall (a b) (-> (a b) (pairof a b))))" +
        " (pair~ (forall (r a b) (-> ((pairof a b) (-> (a b) r) (-> () r)) r))))"

    // Figure 15.7: TenvModule.
    private val T_ENV =
        "(moduleof ((envof t))" +
        " (empty (forall (t) (-> () (envof t))))" +
        " (bind (forall (t) (-> (symb t (envof t)) (envof t))))" +
        " (lookup (forall (t) (-> (symb (envof t)) t))))"

    // Figure 15.10: Topen, the signature of Eopen (Figure 15.9) opened
    // over the list module.
    private val T_OPEN =
        "(moduleof ((entryof t) (envof t))" +
        " (entry (forall (t) (-> (symb t) (entryof t))))" +
        " (entry~ (forall (r t) (-> ((entryof t) (-> (symb t) r) (-> () r)) r)))" +
        " (list-env (forall (t) (-> (((dselect listof list-module) (entryof t))) (envof t))))" +
        " (list-env~ (forall (r t) (-> ((envof t) (-> (((dselect listof list-module) (entryof t))) r) (-> () r)) r)))" +
        " (empty (forall (t) (-> () (envof t))))" +
        " (bind (forall (t) (-> (symb t (envof t)) (envof t))))" +
        " (lookup (forall (t) (-> (symb (envof t)) t))))"

    // A module providing both a list module and a pair module (Figure 15.6).
    private val T_MODS =
        "(moduleof () (list-module " + T_LIST + ") (pair-module " + T_PAIR + "))"

    // The return type of make-polymod, with the dselect module
    // expressions written as (open mm ...) (mm is the functor parameter).
    private val T_POLYMOD_MM =
        "(moduleof ((polyof))" +
        " (poly (-> (((dselect listof (open mm list-module))" +
        " ((dselect pairof (open mm pair-module)) int int))) (polyof)))" +
        " (poly~ (forall (r) (-> ((polyof)" +
        " (-> (((dselect listof (open mm list-module))" +
        " ((dselect pairof (open mm pair-module)) int int))) r)" +
        " (-> () r)) r)))" +
        " (empty (-> () (polyof)))" +
        " (add-point (-> (int int (polyof)) (polyof))))"

    // Figure 15.3: ElistModule.
    private val E_LIST =
        "(module" +
        " (def-datatype (listof t) (null) (cons t (listof t)))" +
        " (def null? (forall (t) (-> ((listof t)) bool))" +
        "   (pabs (t) (abs ((xs (listof t)))" +
        "     (match xs ((null) #t) ((cons _ _) #f)))))" +
        " (def car (forall (t) (-> ((listof t)) t))" +
        "   (pabs (t) (abs ((xs (listof t)))" +
        "     (match xs" +
        "       ((null) (error car-of-empty-list t))" +
        "       ((cons a _) a)))))" +
        " (def cdr (forall (t) (-> ((listof t)) (listof t)))" +
        "   (pabs (t) (abs ((xs (listof t)))" +
        "     (match xs" +
        "       ((null) (error cdr-of-empty-list (listof t)))" +
        "       ((cons _ d) d))))))"

    // Figure 15.9: Eopen, an environment module represented as a list of
    // entries, opened over the list module.
    private val E_OPEN =
        "(open list-module" +
        " (module" +
        "  (def-datatype (entryof t) (entry symb t))" +
        "  (def-datatype (envof t) (list-env (listof (entryof t))))" +
        "  (def empty (forall (t) (-> () (envof t)))" +
        "   (pabs (t) (abs () (list-env ((pcall null (entryof t)))))))" +
        "  (def bind (forall (t) (-> (symb t (envof t)) (envof t)))" +
        "   (pabs (t) (abs ((name symb) (val t) (env (envof t)))" +
        "    (match env" +
        "     ((list-env entries)" +
        "      (list-env (cons (entry name val) entries)))))))" +
        "  (def lookup (forall (t) (-> (symb (envof t)) t))" +
        "   (pabs (t) (abs ((name symb) (env (envof t)))" +
        "    (match env" +
        "     ((list-env entries)" +
        "      (letrec ((loop (-> ((listof (entryof t))) t)" +
        "               (abs ((ents (listof (entryof t))))" +
        "                (match ents" +
        "                 ((null) (error unbound t))" +
        "                 ((cons (entry n v) rest)" +
        "                  (if (sym=? name n) v (loop rest)))))))" +
        "       (loop entries)))))))))"

    // Figure 15.11: EprocEnvModule (without the outer the), an
    // environment module represented as a procedure from symbols to
    // values.
    private val E_PROC_ENV =
        "(module" +
        " (def-datatype (envof t) (proc-env (-> (symb) t)))" +
        " (def empty (forall (t) (-> () (envof t)))" +
        "  (pabs (t) (abs () (proc-env (abs ((n symb)) (error unbound t))))))" +
        " (def bind (forall (t) (-> (symb t (envof t)) (envof t)))" +
        "  (pabs (t) (abs ((name symb) (val t) (env (envof t)))" +
        "   (proc-env (abs ((n symb))" +
        "    (if (sym=? n name) val (lookup n env)))))))" +
        " (def lookup (forall (t) (-> (symb (envof t)) t))" +
        "  (pabs (t) (abs ((name symb) (env (envof t)))" +
        "   (match env ((proc-env proc) (proc name)))))))"

    // Figure 15.8: the body of EenvTest, inside (abs ((envmod ...)) ...).
    private val EENVT_BODY =
        "(open envmod" +
        " (let ((e0 ((pcall empty int))))" +
        "  (let ((e1 (bind (sym a) 1 e0)))" +
        "   (let ((e2 (bind (sym b) 2 e1)))" +
        "    (let ((e3 (bind (sym a) 3 e2)))" +
        "     (prim + (prim * 1000 (lookup (sym a) e3))" +
        "      (prim + (prim * 100 (lookup (sym b) e3))" +
        "       (prim + (prim * 10 (lookup (sym a) e2))" +
        "        (lookup (sym b) e2)))))))))"

    // Figure 15.8: the body of EenvSwap, inside (abs ((envmod ...)) ...).
    private val EENVS_BODY =
        "(open envmod" +
        " (pabs (t)" +
        "  (abs ((s1 symb) (s2 symb) (env (envof t)))" +
        "   (let ((v1 (lookup s1 env)) (v2 (lookup s2 env)))" +
        "    (bind s1 v2 (bind s2 v1 env))))))"

    // The p.912 Tmod example, realized with xof / zof as opened modules.
    private val TXOF =
        "(moduleof ((xof s))" +
        " (make-x (forall (s) (-> (s) (xof s))))" +
        " (make-x~ (forall (r s) (-> ((xof s) (-> (s) r) (-> () r)) r))))"

    private val TZOF =
        "(moduleof ((zof b))" +
        " (z-node (forall (b) (-> (b) (zof b))))" +
        " (z-node~ (forall (r b) (-> ((zof b) (-> (b) r) (-> () r)) r))))"

    // The p.912 module M1: its own xof and yof type constructors, with a
    // and b of types (xof (yof int)) and (yof (zof bool)).
    private val M_MOD1 =
        "(module" +
        " (def-datatype (xof s) (x-node s))" +
        " (def-datatype (yof t) (y-node t))" +
        " (def a (xof (yof int)) (x-node (y-node 3)))" +
        " (def b (yof (zof bool)) (y-node (z-node #t))))"

    // Figure 15.8: the type of EenvSwap, with the module type of the
    // parameter written as `inner` (a def-type name in the source, or the
    // full moduleof in the expected display).
    private def tswap(inner: String): String =
        "(-> ((envmod " + inner + "))" +
        " (forall (t) (-> (symb symb ((dselect envof envmod) t))" +
        " ((dselect envof envmod) t))))"

    // ------------------------------------------------------------------
    // Parsing (Figure 15.1 / 15.2: the program forms flex/M and flex/Mk)
    // ------------------------------------------------------------------

    "A valid FLEX/M program" should "parse" in {
        assert(FlexMProgram("(flex/M () 3)").isDefined)
        assert(FlexMProgram("(flex/Mk () 3)").isDefined)
        assert(FlexMProgram("(flex/M ((m (moduleof () (x (-> (int) int))))) (mselect x m))").isDefined)
        assert(FlexMProgram("(flex/M () (module (def-datatype (tof t) (c t)) (def f (-> (int) (tof int)) (abs ((x int)) (c x)))))").isDefined)
    }

    it should "reject other program tags" in {
        assert(FlexMProgram("(flex/SP () 3)").isEmpty)
        assert(FlexMProgram("(flex () 3)").isEmpty)
        assert(FlexMProgram("(foo () 3)").isEmpty)
    }

    it should "reject a malformed type in a formal parameter" in {
        // A free type-constructor name in a formal type is not declared
        // in the program context (moduleof abstract types bind only in
        // their own signatures).
        assert(flexmErr("(flex/M ((x (moduleof () (f (-> (int) (tof int)))))) 1)").contains(
            "malformed type in formal parameter x: the type constructor tof is not declared in this context"))
    }

    // ------------------------------------------------------------------
    // Figure 15.3 / 15.5: ElistModule : TlistModule
    // ------------------------------------------------------------------

    "ElistModule (Figure 15.3)" should "have type TlistModule (Figure 15.5)" in {
        "(flex/M () " + E_LIST + ")" shouldFlexMCheckTo(FlexOk(T_LIST))
    }

    // ------------------------------------------------------------------
    // p.898: EdblProc, the integer-list doubling procedure
    // ------------------------------------------------------------------

    "EdblProc (p.898)" should "have a dependent type over the list module" in {
        val prog =
            "(flex/M ((list-module " + T_LIST + "))" +
            " (open list-module" +
            "  (letrec ((dbl (-> ((listof int)) (listof int))" +
            "   (abs ((xs (listof int)))" +
            "    (match xs" +
            "     ((null) ((pcall null int)))" +
            "     ((cons y ys) (cons (prim * 2 y) (dbl ys)))))))" +
            "  dbl)))"
        prog shouldFlexMCheckTo(
            FlexOk("(=> (" + T_LIST +
                ") (-> (((dselect listof list-module) int))" +
                " ((dselect listof list-module) int)))"))
    }

    // ------------------------------------------------------------------
    // Figure 15.6: make-polymod, a functor built from list and pair
    // modules
    // ------------------------------------------------------------------

    "make-polymod (Figure 15.6)" should "build a polygon module from a module of modules" in {
        val declType =
            "(-> ((mm (moduleof () (list-module TlistModule) (pair-module TpairModule)))) " + T_POLYMOD_MM + ")"
        val body =
            "(abs ((mm (moduleof () (list-module TlistModule) (pair-module TpairModule))))" +
            " (open mm" +
            "  (open list-module" +
            "   (open pair-module" +
            "    (module" +
            "     (def-datatype (polyof) (poly (listof (pairof int int))))" +
            "     (def empty (-> () (polyof))" +
            "      (abs () (poly ((pcall null (pairof int int))))))" +
            "     (def add-point (-> (int int (polyof)) (polyof))" +
            "      (abs ((x int) (y int) (p (polyof)))" +
            "       (match p ((poly points) (poly (cons (pair x y) points)))))))))))"
        val prog =
            "(flex/M ((mod-of-mods " + T_MODS + "))" +
            " (make-polymod mod-of-mods)" +
            " (def-type TlistModule " + T_LIST + ")" +
            " (def-type TpairModule " + T_PAIR + ")" +
            " (def make-polymod " + declType + " " + body + "))"
        val expectedRet =
            "(moduleof ((polyof))" +
            " (poly (-> (((dselect listof (open mod-of-mods list-module))" +
            " ((dselect pairof (open mod-of-mods pair-module)) int int))) (polyof)))" +
            " (poly~ (forall (r) (-> ((polyof)" +
            " (-> (((dselect listof (open mod-of-mods list-module))" +
            " ((dselect pairof (open mod-of-mods pair-module)) int int))) r)" +
            " (-> () r)) r)))" +
            " (empty (-> () (polyof)))" +
            " (add-point (-> (int int (polyof)) (polyof))))"
        prog shouldFlexMCheckTo(FlexOk("(=> (" + T_MODS + ") " + expectedRet + ")"))
    }

    // ------------------------------------------------------------------
    // Figure 15.9 / 15.10: Eopen : Topen
    // ------------------------------------------------------------------

    "Eopen (Figure 15.9)" should "have type Topen (Figure 15.10)" in {
        val prog = "(flex/M ((list-module " + T_LIST + ")) " + E_OPEN + ")"
        prog shouldFlexMCheckTo(FlexOk("(=> (" + T_LIST + ") " + T_OPEN + ")"))
    }

    // ------------------------------------------------------------------
    // Figure 15.8: EenvSwap
    // ------------------------------------------------------------------

    "EenvSwap (Figure 15.8)" should "have a dependent arrow type over the environment module" in {
        val prog =
            "(flex/M ()" +
            " (the " + tswap("TenvModule") + " (abs ((envmod TenvModule)) " + EENVS_BODY + "))" +
            " (def-type TenvModule " + T_ENV + "))"
        prog shouldFlexMCheckTo(FlexOk(tswap(T_ENV)))
    }

    // ------------------------------------------------------------------
    // Figure 15.8: EenvTest, applied to the two environment modules
    // ------------------------------------------------------------------

    "EenvTest (Figure 15.8)" should "apply to a formal environment module" in {
        val prog =
            "(flex/M ((env-mod " + T_ENV + "))" +
            " (the (-> (TenvModule) int)" +
            "  (abs ((envmod TenvModule)) " + EENVT_BODY + "))" +
            " (def-type TenvModule " + T_ENV + "))"
        prog shouldFlexMCheckTo(FlexOk("(=> (" + T_ENV + ") (-> (" + T_ENV + ") int))"))
    }

    it should "apply to the list-based environment module (the Topen <= TenvModule)" in {
        val prog =
            "(flex/M ((list-module " + T_LIST + "))" +
            " (env-test (the TenvModule " + E_OPEN + "))" +
            " (def-type TenvModule " + T_ENV + ")" +
            " (def env-test (-> (TenvModule) int)" +
            "  (abs ((envmod TenvModule)) " + EENVT_BODY + ")))"
        prog shouldFlexMCheckTo(FlexOk("(=> (" + T_LIST + ") int)"))
    }

    // ------------------------------------------------------------------
    // Figure 15.13: the table-module functor with raw symbols as keys
    // ------------------------------------------------------------------

    "the table functor of Figure 15.13" should "instantiate over symbols and build a table" in {
        val tmake =
            "(forall (key)" +
            " (-> ((-> (key key) bool))" +
            "  (moduleof ((tableof t))" +
            "   (empty (forall (t) (-> () (tableof t))))" +
            "   (bind (forall (t) (-> (key t (tableof t)) (tableof t))))" +
            "   (lookup (forall (t) (-> (key (tableof t)) t))))))"
        val tableModule =
            "(module" +
            " (def-datatype (entryof t) (entry key t))" +
            " (def-datatype (tableof t) (list-env (listof (entryof t))))" +
            " (def empty (forall (t) (-> () (tableof t)))" +
            "  (pabs (t) (abs () (list-env ((pcall null (entryof t)))))))" +
            " (def bind (forall (t) (-> (key t (tableof t)) (tableof t)))" +
            "  (pabs (t) (abs ((name key) (val t) (env (tableof t)))" +
            "   (match env ((list-env entries)" +
            "    (list-env (cons (entry name val) entries)))))))" +
            " (def lookup (forall (t) (-> (key (tableof t)) t))" +
            "  (pabs (t) (abs ((name key) (env (tableof t)))" +
            "   (match env ((list-env entries)" +
            "    (letrec ((loop (-> ((listof (entryof t))) t)" +
            "             (abs ((ents (listof (entryof t))))" +
            "              (match ents" +
            "               ((null) (error unbound t))" +
            "               ((cons (entry n v) rest)" +
            "                (if (key=? name n) v (loop rest)))))))" +
            "     (loop entries))))))))"
        val prog =
            "(flex/M ((list-module " + T_LIST + "))" +
            " (let ((env-table-mod ((pcall EmakeTableModule symb) sym=?)))" +
            "  (open env-table-mod" +
            "   (let ((env (bind (sym a) 1 (bind (sym b) 2 ((pcall empty int))))))" +
            "    (prim + (prim * 10 (lookup (sym a) env)) (lookup (sym b) env)))))" +
            " (def-type TmakeTableModule " + tmake + ")" +
            " (def EmakeTableModule TmakeTableModule" +
            "  (the TmakeTableModule" +
            "   (pabs (key)" +
            "    (abs ((key=? (-> (key key) bool)))" +
            "     (open list-module " + tableModule + "))))))"
        prog shouldFlexMCheckTo(FlexOk("(=> (" + T_LIST + ") int)"))
    }

    // ------------------------------------------------------------------
    // p.906: environments from different modules do not interoperate
    // ------------------------------------------------------------------

    "an environment from the list module" should "not be usable with the procedure-module swap" in {
        val prog =
            "(flex/M ((list-module " + T_LIST + "))" +
            " (let ((env (open list-env-mod" +
            "  (bind (sym c) 4 (bind (sym d) 5 ((pcall empty int)))))))" +
            "  ((pcall (env-swap proc-env-mod) int) (sym c) (sym d) env))" +
            " (def-type TenvModule " + T_ENV + ")" +
            " (def list-env-mod TenvModule (the TenvModule " + E_OPEN + "))" +
            " (def proc-env-mod TenvModule (the TenvModule " + E_PROC_ENV + "))" +
            " (def env-swap " + tswap("TenvModule") +
            "  (the " + tswap("TenvModule") + " (abs ((envmod TenvModule)) " + EENVS_BODY + "))))"
        assert(flexmErr(prog).contains("the 3th argument of the application"))
    }

    // ------------------------------------------------------------------
    // Soundness and restriction checks
    // ------------------------------------------------------------------

    "the pabs import restriction (p.732)" should "reject the polytest" in {
        assert(flexmErr("(flex/Mk () (pabs (t) (abs ((x t)) (pabs (t) x))))").contains(
            "import restriction (pabs): the type identifier t would capture the reference in the type of the value x"))
    }

    "pcall" should "reject too many type arguments" in {
        assert(flexmErr("(flex/Mk () (pcall (pabs (t) (abs ((x t)) x)) int bool))").contains(
            "pcall: the polymorphic value binds 1 type identifier(s), but 2 type argument(s) were given"))
    }

    "pcall" should "reject a non-polymorphic value" in {
        assert(flexmErr("(flex/Mk () (pcall (abs ((x int)) x) int))").contains(
            "pcall: the value has type (-> (int) int), which is not a forall type"))
    }

    "let" should "not permit rebinding" in {
        assert(flexmErr("(flex/Mk () (let ((a 1)) (let ((a 2)) a)))").contains(
            "the binding name a of (let ...) is already bound in this environment (FLEX/M does not permit rebinding)"))
    }

    "abs" should "not permit rebinding a formal parameter" in {
        assert(flexmErr("(flex/Mk () (let ((f (abs ((x int)) x))) (abs ((f int)) f)))").contains(
            "the formal parameter name f is already bound in this environment (FLEX/M does not permit rebinding)"))
    }

    "an arrow parameter" should "not mention a later parameter name" in {
        assert(flexmErr("(flex/Mk () (abs ((x ((dselect envof y) int)) (y int)) x))").contains(
            "the type of parameter x mentions the not-yet-bound parameter name y"))
    }

    "match" should "reject a non type-constructor-application discriminant" in {
        assert(flexmErr("(flex/Mk () (match 5 (_ (sym a))))").contains(
            "match: the discriminant must have a type-constructor-application type, but it has type int"))
    }

    "match" should "reject a pattern variable that is already bound" in {
        val m1 = "(module (def-datatype (tof t) (c t)))"
        // x is bound by the outer let; the pattern also tries to bind x.
        assert(flexmErr("(flex/Mk () (let ((x 5) (m " + m1 + ")) (open m (match (c 1) ((c x) x)))))").contains(
            "the pattern variable x is already bound in this environment"))
    }

    "implicit projection (p.920)" should "fail the locality restriction on (null)" in {
        val prog = "(flex/M ((list-module " + T_LIST + ")) (open list-module (null)))"
        assert(flexmErr(prog).contains("still contains unresolved type variable(s)"))
    }

    "an open" should "require a pure module expression" in {
        assert(flexmErr("(flex/Mk () (open (module (def c unit (:= (cell 1) 2))) (sym done)))").contains(
            "(open ...) requires a pure module expression, but this module expression contains a mutation"))
    }

    "the moduleof subtyping (p.912)" should "reject Tmod1 <= Tmod2" in {
        val prog =
            "(flex/M ((xof-mod " + TXOF + ") (zof-mod " + TZOF + "))" +
            " (open xof-mod (open zof-mod" +
            "  (the (moduleof ((yof t)) (a (xof (yof int)))) " + M_MOD1 + "))))"
        assert(flexmErr(prog).contains("the component a"))
    }

    it should "accept Tmod1 <= Tmod3" in {
        val prog =
            "(flex/M ((xof-mod " + TXOF + ") (zof-mod " + TZOF + "))" +
            " (open xof-mod (open zof-mod" +
            "  (the (moduleof ((yof t)) (b (yof (zof bool)))) " + M_MOD1 + "))))"
        prog shouldFlexMCheckTo(
            FlexOk("(=> (" + TXOF + " " + TZOF +
                ") (moduleof ((yof t)) (b (yof ((dselect zof zof-mod) bool)))))"))
    }

    "the" should "fail when the subtype relation does not hold" in {
        assert(flexmErr("(flex/Mk () (the (-> (bool) int) (abs ((x int)) x)))").contains(
            "(the ...): the type (-> (int) int) is not a subtype of (-> (bool) int)"))
    }

    "cellof" should "be invariant in its content type" in {
        assert(flexmErr("(flex/Mk () (let ((c (cell 1))) (:= c #t)))").contains(
            "(:= ...) the value:"))
    }

    // ------------------------------------------------------------------
    // FLEX/M sugar: letrec / mselect / let-type / load
    // ------------------------------------------------------------------

    "mselect" should "select a module component" in {
        val prog = "(flex/M ((list-module " + T_LIST + ")) (mselect null list-module))"
        prog shouldFlexMCheckTo(
            FlexOk("(=> (" + T_LIST + ") (forall (t) (-> () ((dselect listof list-module) t))))"))
    }

    "let-type" should "substitute a type definition" in {
        val prog = "(flex/Mk () (let-type ((T (-> (int) bool))) (abs ((f T)) f)))"
        prog shouldFlexMCheckTo(FlexOk("(-> ((-> (int) bool)) (-> (int) bool))"))
    }

    "load" should "have the type given in the load construct" in {
        val prog = "(flex/Mk () (load m.flxm (moduleof () (x (-> (int) int)))))"
        prog shouldFlexMCheckTo(FlexOk("(moduleof () (x (-> (int) int)))"))
    }

    // ------------------------------------------------------------------
    // Records, oneofs, cells (inherited from FLEX)
    // ------------------------------------------------------------------

    "records" should "select and with fields" in {
        val r1 = "(flex/Mk () (with (record (f (abs ((z int)) (prim + z 10))) (y 2)) (f 5)))"
        r1 shouldFlexMCheckTo(FlexOk("int"))
        val r2 = "(flex/Mk () (let ((r (record (x 1) (y 2)))) (select x r)))"
        r2 shouldFlexMCheckTo(FlexOk("int"))
    }

    "oneofs" should "construct and tagcase" in {
        val prog = "(flex/Mk () (let ((o (one (oneof (ok int err symb)) ok 5))) (tagcase o v (ok v) (err 0))))"
        prog shouldFlexMCheckTo(FlexOk("int"))
    }

    "cells" should "store and deref" in {
        val prog = "(flex/Mk () (let ((c (cell 1))) (let ((x (:= c 2))) (^ c))))"
        prog shouldFlexMCheckTo(FlexOk("int"))
    }
}
