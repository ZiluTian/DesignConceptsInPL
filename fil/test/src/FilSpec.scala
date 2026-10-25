package DSL.fil

import DSL.fl._
import DSL.flare.FlarePrim
import org.scalatest.flatspec.AnyFlatSpecLike

class FilSpec extends AnyFlatSpecLike {

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    def parse(input: String): FilProgram =
        FilProgram(input) match {
            case Some(p) => p
            case None => throw new AssertionError(s"parse failed: $input")
        }

    def parseFails(input: String): Unit =
        assert(FilProgram(input).isEmpty, s"expected parse failure: $input")

    def run(input: String, args: Int*): Result =
        filRun(input, args: _*)

    // Collect every subexpression of a FIL tree (preorder).
    def collect(e: Exp): List[Exp] = e match {
        case _: UnitLit | _: BoolLit | _: IntLit | _: Sym | _: Var | _: ErrorExpr => List(e)
        case If(t, th, el) => e +: (collect(t) ++ collect(th) ++ collect(el))
        case FilPrim(_, args) => e +: args.flatMap(collect)
        case FilApp(r, rands) => e +: (collect(r) ++ rands.flatMap(collect))
        case Abs(_, b) => e +: collect(b)
        case Let(bs, b) => e +: (bs.flatMap { case (_, d) => collect(d) } ++ collect(b))
        case LetStar(bs, b) => e +: (bs.flatMap { case (_, d) => collect(d) } ++ collect(b))
        case other => throw new AssertionError(s"unexpected node in collection: $other")
    }

    // ------------------------------------------------------------------
    // Parsing
    // ------------------------------------------------------------------

    "the parser" should "parse a minimal program and evaluate it" in {
        val p = parse("(fil () (@+ 1 2))")
        assert(p.body == FilPrim("+", List(IntLit(1), IntLit(2))))
        assert(run("(fil () (@+ 1 2))") == Val(IntValue(3)))
    }

    it should "reject the fl program tag" in {
        parseFails("(fl () 1)")
    }

    it should "reject a keyword in a binding position" in {
        parseFails("(fil () (let ((if 1)) 2))")
    }

    it should "reject an @-prefixed identifier as a formal" in {
        parseFails("(fil (@x) 1)")
    }

    it should "parse @-sugared indexed operators" in {
        assert(parse("(fil () (@mget 1 c))").body == FilPrim("mget 1", List(Var("c"))))
        assert(parse("(fil () (@mset! 2 c 5))").body == FilPrim("mset! 2", List(Var("c"), IntLit(5))))
    }

    it should "reject a non-literal index in @-sugar" in {
        parseFails("(fil () (@mget x c))")
    }

    it should "parse parenthesized indexed prim operators" in {
        assert(parse("(fil () (prim (mget 2) c))").body == FilPrim("mget 2", List(Var("c"))))
        assert(parse("(fil () (prim (mset! 1) c 5))").body == FilPrim("mset! 1", List(Var("c"), IntLit(5))))
    }

    it should "reject an indexed prim operator missing its index" in {
        parseFails("(fil () (prim (mget) c))")
    }

    it should "reject an unknown @-operator" in {
        parseFails("(fil () (@bogus 1))")
    }

    it should "desugar an empty let* to its body" in {
        assert(parse("(fil () (let* () 7))").body == IntLit(7))
        assert(run("(fil () (let* () 7))") == Val(IntValue(7)))
    }

    it should "desugar let* to nested single-binding lets" in {
        val p = parse("(fil () (let* ((x 1) (y 2)) x))")
        assert(p.body == Let(List(("x", IntLit(1))), Let(List(("y", IntLit(2))), Var("x"))))
    }

    it should "simplify an empty let" in {
        assert(parse("(fil () (let () 1))").body == IntLit(1))
    }

    it should "simplify an application of an abstraction to an implicit let" in {
        val p = parse("(fil () (app (abs (x) (prim + x 1)) 2))")
        assert(p.body == Let(List(("x", IntLit(2))), FilPrim("+", List(Var("x"), IntLit(1)))))
        assert(run("(fil () (app (abs (x) (prim + x 1)) 2))") == Val(IntValue(3)))
    }

    // ------------------------------------------------------------------
    // The Figure 17.15 simplifications
    // ------------------------------------------------------------------

    it should "perform copy propagation of a variable definition" in {
        val p = parse("(fil () (let ((x y)) (prim + x 1)))")
        assert(p.body == FilPrim("+", List(Var("y"), IntLit(1))))
    }

    it should "rename to avoid capture when copying" in {
        val body = parse("(fil () (let ((x y)) (let ((y 7)) x)))").body
        body match {
            case Let(List((n, IntLit(7))), Var("y")) if n.startsWith("@@fil_fresh_") =>
            case other => throw new AssertionError(s"unexpected: $other")
        }
    }

    it should "perform eta reduction" in {
        assert(parse("(fil () (abs (a b) (app f a b)))").body == Var("f"))
    }

    it should "block eta reduction when the rator's free identifiers overlap the formals" in {
        val body = parse("(fil () (abs (x) (app (abs (a b) (app f x)) x)))").body
        assert(body == Abs(List("x"), FilApp(Abs(List("a", "b"), FilApp(Var("f"), List(Var("x")))), List(Var("x")))))
    }

    it should "resolve the Eambig example bottom-up" in {
        val body = parse("(fil () (app (abs (x) (app g x)) e))").body
        assert(body == FilApp(Var("g"), List(Var("e"))))
    }

    it should "simplify the book's eta example through implicit-let and copy-prop" in {
        val body = parse("(fil () (abs (a) (app (abs (b) (prim + a b)) a)))").body
        assert(body == Abs(List("a"), FilPrim("+", List(Var("a"), Var("a")))))
    }

    it should "eta-reduce when the rator is an abstraction" in {
        val body = parse("(fil () (abs (x y) (app (abs (w) (prim + w 1)) x y)))").body
        assert(body == Abs(List("w"), FilPrim("+", List(Var("w"), IntLit(1)))))
    }

    it should "not eta-reduce a primop rator" in {
        val body = parse("(fil () (abs (a) (app (@mprod #u) a)))").body
        assert(body == Abs(List("a"), FilApp(FilPrim("mprod", List(UnitLit())), List(Var("a")))))
    }

    // ------------------------------------------------------------------
    // The evaluator
    // ------------------------------------------------------------------

    "the evaluator" should "evaluate a program with formals" in {
        assert(run("(fil (x y) (@+ x y))", 3, 4) == Val(IntValue(7)))
    }

    it should "evaluate a program with a single formal" in {
        assert(run("(fil (x) x)", 9) == Val(IntValue(9)))
    }

    it should "apply multi-formal closures" in {
        assert(run("(fil () (let ((f (abs (x y) (@+ x y)))) (app f 3 4)))") == Val(IntValue(7)))
    }

    it should "read a mutable-product slot" in {
        assert(run("(fil () (@mget 2 (@mprod 10 20)))") == Val(IntValue(20)))
    }

    it should "write a mutable-product slot and yield unit" in {
        assert(run("(fil () (let ((c (@mprod 1))) (let* ((r (@mset! 1 c 2))) (@mget 1 c))))") == Val(IntValue(2)))
    }

    it should "compare mutable products by store location" in {
        assert(run("(fil () (let ((c (@mprod 1))) (@mprod=? c c)))") == Val(BoolValue(true)))
        assert(run("(fil () (@mprod=? (@mprod 1) (@mprod 1)))") == Val(BoolValue(false)))
    }

    it should "reject a let definition that references a sibling binding" in {
        assert(run("(fil () (let ((a (@mprod 1)) (b (@mget 1 a))) b))") == Err("unbound variable: a"))
    }

    it should "evaluate nested lets sequentially" in {
        assert(run("(fil () (let ((a (@mprod 1))) (let ((b (@mget 1 a))) b)))") == Val(IntValue(1)))
    }

    it should "evaluate let definitions left to right" in {
        assert(run("(fil () (let ((c (@mprod 0))) (let ((a (@mset! 1 c 1)) (b (@mset! 1 c 2))) (@mget 1 c))))") == Val(IntValue(2)))
    }

    it should "branch on a boolean test" in {
        assert(run("(fil () (if (@> 2 3) 1 2))") == Val(IntValue(2)))
    }

    it should "reject a non-boolean if test" in {
        assert(run("(fil () (if 1 2 3))") == Err("if: test expression is not a boolean"))
    }

    it should "construct and inspect lists" in {
        assert(run("(fil () (@car (@cons 1 (@cons 2 (@null)))))") == Val(IntValue(1)))
        assert(run("(fil () (@null? (@null)))") == Val(BoolValue(true)))
        assert(run("(fil () (@null? (@cons 1 (@null))))") == Val(BoolValue(false)))
        assert(run("(fil () (@car (@cdr (@cons 1 (@cons 2 (@null))))))") == Val(IntValue(2)))
    }

    it should "report dynamic type errors" in {
        assert(run("(fil () (@+ #t 1))") == Err("+: arguments are not integers"))
        assert(run("(fil () (@/ 1 0))") == Err("divide-by-zero"))
        assert(run("(fil () (@mget 2 (@mprod 1)))") == Err("mget: index 2 out of range (product has 1 slot(s))"))
    }

    it should "report an unbound variable" in {
        assert(run("(fil () zzz)") == Err("unbound variable: zzz"))
    }

    it should "check arity in both directions" in {
        assert(run("(fil () (app (abs () 1) 2))") == Err("arity mismatch: procedure takes 0 argument(s), got 1"))
        assert(run("(fil () (app (abs (x y) x)))") == Err("arity mismatch: procedure takes 2 argument(s), got 0"))
        assert(run("(fil () (app 1 2))") == Err("app: rator is not a procedure"))
    }

    it should "evaluate an error expression" in {
        assert(run("(fil () (error boom))") == Err("boom"))
    }

    it should "evaluate logical, relational, and symbol operators" in {
        assert(run("(fil () (@and #t #f))") == Val(BoolValue(false)))
        assert(run("(fil () (@not #t))") == Val(BoolValue(false)))
        assert(run("(fil () (@sym=? (sym a) (sym b)))") == Val(BoolValue(false)))
        assert(run("(fil () (@bool=? #t #t))") == Val(BoolValue(true)))
        assert(run("(fil () (@<= 2 2))") == Val(BoolValue(true)))
    }

    it should "let closures capture the defining environment" in {
        assert(run("(fil () (let ((x 5)) (let ((g (abs (y) (@+ x y)))) (app g 10))))") == Val(IntValue(15)))
    }

    it should "call a nullary procedure" in {
        assert(run("(fil () (app (abs () 42)))") == Val(IntValue(42)))
    }

    // ------------------------------------------------------------------
    // The FLARE-to-FIL translation (Figure 17.16)
    // ------------------------------------------------------------------

    "the translation" should "map applications to the explicit app keyword" in {
        assert(Translate.Texp(MultiApp(Var("g"), List(Var("x")))) == FilApp(Var("g"), List(Var("x"))))
    }

    it should "be the identity on literals and variables" in {
        assert(Translate.Texp(Var("x")) == Var("x"))
        assert(Translate.Texp(IntLit(7)) == IntLit(7))
        assert(Translate.Texp(BoolLit(true)) == BoolLit(true))
        assert(Translate.Texp(Sym("s")) == Sym("s"))
        assert(Translate.Texp(UnitLit()) == UnitLit())
    }

    it should "map the cell and pair operators to mutable products" in {
        assert(Translate.Texp(FlarePrim("cell", List(UnitLit()))) == FilPrim("mprod", List(UnitLit())))
        assert(Translate.Texp(FlarePrim("^", List(Var("c")))) == FilPrim("mget 1", List(Var("c"))))
        assert(Translate.Texp(FlarePrim(":=", List(Var("c"), IntLit(5)))) == FilPrim("mset! 1", List(Var("c"), IntLit(5))))
        assert(Translate.Texp(FlarePrim("cell=?", List(Var("a"), Var("b")))) == FilPrim("mprod=?", List(Var("a"), Var("b"))))
        assert(Translate.Texp(FlarePrim("pair", List(Var("a"), Var("b")))) == FilPrim("mprod", List(Var("a"), Var("b"))))
        assert(Translate.Texp(FlarePrim("fst", List(Var("p")))) == FilPrim("mget 1", List(Var("p"))))
        assert(Translate.Texp(FlarePrim("snd", List(Var("p")))) == FilPrim("mget 2", List(Var("p"))))
    }

    it should "translate a letrec into mutable-product knot tying" in {
        val in = "(flarek () (letrec ((f (abs (x) x))) (f 41)))"
        val prog = Translate.translate(in).get
        prog.body match {
            case Let(List(("f", FilPrim("mprod", List(UnitLit())))), _) =>
            case other => throw new AssertionError(s"unexpected top shape: $other")
        }
        assert(collect(prog.body).forall(n => !n.isInstanceOf[LetRec]))
        assert(DSL.fil.Evaluator.run(prog, Nil) == Val(IntValue(41)))
    }

    it should "translate a kernel factorial program" in {
        val in = "(flarek () (letrec ((fact (abs (n) (if (prim = n 1) 1 (prim * (fact (prim - n 1)) n))))) (fact 4)))"
        val prog = Translate.translate(in).get
        assert(DSL.fil.Evaluator.run(prog, Nil) == Val(IntValue(24)))
    }

    it should "translate the revmap example" in {
        val in = "(flarek (a b) (let ((revmap (abs (f elts) (let ((ans (prim cell (prim null)))) (letrec ((loop (abs (xs) (if (prim null? xs) (prim ^ ans) (let ((_ (prim := ans (prim cons (f (prim car xs)) (prim ^ ans))))) (loop (prim cdr xs))))))) (loop elts)))))) (revmap (abs (x) (prim > x b)) (prim cons a (prim cons (prim * a 7) (prim null))))))"
        val prog = Translate.translate(in).get
        assert(DSL.fil.Evaluator.run(prog, List(IntValue(3), IntValue(10))) ==
            Val(PairValue(BoolValue(true), PairValue(BoolValue(false), UnitValue))))
    }

    it should "translate a sugared FLARE program through the stdlib wrapper" in {
        val prog = Translate.translate("(flare () (add1 41) (def add1 (abs (x) (+ x 1))))").get
        assert(DSL.fil.Evaluator.run(prog, Nil) == Val(IntValue(42)))
    }

    it should "change the program tag from flarek to fil" in {
        assert(Translate.translate("(flarek (x) x)") == Some(FilProgram(List("x"), Var("x"))))
    }

    it should "reject non-FLARE input" in {
        assert(Translate.translate("(fil () 1)").isEmpty)
    }
}
