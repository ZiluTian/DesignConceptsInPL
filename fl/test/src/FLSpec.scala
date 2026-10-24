package DSL.fl

import org.scalatest.flatspec.AnyFlatSpecLike

class flSpec extends AnyFlatSpecLike {
    import DSL.fl.{ Val, Err }

    "A valid FL program" should "parse" in {
        assert(FlProgram("(fl (x y) (@+ x y))").isDefined)
        assert(FlProgram("(flk (x) x)").isDefined)
        assert(FlProgram("(fl () (app (lam n n) 3))").isDefined)
        assert(FlProgram("(fl () (let ((a 1) (b 2)) (@+ a b)))").isDefined)
    }

    "Literals" should "evaluate to their values" in {
        "(fl () 42)"            shouldFlEvalTo (Nil, Val(IntValue(42)))
        "(fl () #t)"            shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () #f)"            shouldFlEvalTo (Nil, Val(BoolValue(false)))
        "(fl () #u)"            shouldFlEvalTo (Nil, Val(UnitValue))
        "(fl () (sym foo))"     shouldFlEvalTo (Nil, Val(SymValue("foo")))
    }

    "Arithmetic over inputs" should "evaluate (sugared @-primops)" in {
        "(fl (x y) (@+ x y))"   shouldFlEvalTo (List(3, 4), Val(IntValue(7)))
        "(fl (x y) (@- x y))"   shouldFlEvalTo (List(10, 4), Val(IntValue(6)))
        "(fl (x y) (@* x y))"   shouldFlEvalTo (List(6, 7), Val(IntValue(42)))
        "(fl (x y) (@/ x y))"   shouldFlEvalTo (List(17, 3), Val(IntValue(5)))
        "(fl (x y) (@% x y))"   shouldFlEvalTo (List(17, 3), Val(IntValue(2)))
        "(fl (x) (@* x (@+ x 1)))" shouldFlEvalTo (List(5), Val(IntValue(30)))
    }

    "Arithmetic with kernel prim" should "evaluate" in {
        "(fl (x y) (prim + x y))" shouldFlEvalTo (List(3, 4), Val(IntValue(7)))
        "(fl () (prim + 1 2 3))"  shouldFlEvalTo (Nil, Err("arity mismatch: expected 2 arguments, got 3"))
    }

    "Conditionals" should "select a branch" in {
        "(fl (x) (if (@> x 0) x 0))"  shouldFlEvalTo (List(-4), Val(IntValue(0)))
        "(fl (x) (if (@> x 0) x 0))"  shouldFlEvalTo (List(4), Val(IntValue(4)))
        "(fl (x) (if (@not (@> x 0)) 1 0))" shouldFlEvalTo (List(5), Val(IntValue(0)))
    }

    "Procedures (lam / app)" should "curry and apply" in {
        "(fl (x) (app (lam y (@+ y 1)) x))" shouldFlEvalTo (List(5), Val(IntValue(6)))
        "(fl () (app (app (lam a (lam b (@+ a b))) 1) 2))" shouldFlEvalTo (Nil, Val(IntValue(3)))
        "(fl () (@proc? (lam x x)))" shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@int? (lam x x)))" shouldFlEvalTo (Nil, Val(BoolValue(false)))
    }

    "Pairs" should "build and select" in {
        "(fl () (pair 1 2))"       shouldFlEvalTo (Nil, Val(PairValue(IntValue(1), IntValue(2))))
        "(fl () (@fst (pair 1 2)))" shouldFlEvalTo (Nil, Val(IntValue(1)))
        "(fl () (@snd (pair 1 2)))" shouldFlEvalTo (Nil, Val(IntValue(2)))
        "(fl () (@pair? (pair 1 2)))" shouldFlEvalTo (Nil, Val(BoolValue(true)))
    }

    "Type predicates" should "classify values" in {
        "(fl () (@unit? #u))"       shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@bool? #t))"       shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@sym? (sym a)))"   shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@pair? (pair #t #f)))" shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@int? 3))"         shouldFlEvalTo (Nil, Val(BoolValue(true)))
    }

    "Boolean connectives" should "evaluate" in {
        "(fl () (@not #t))"          shouldFlEvalTo (Nil, Val(BoolValue(false)))
        "(fl () (@and #t #t))"       shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@and #t #f))"       shouldFlEvalTo (Nil, Val(BoolValue(false)))
        "(fl () (@or #f #t))"        shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (@bool=? #t #t))"    shouldFlEvalTo (Nil, Val(BoolValue(true)))
    }

    "Kernel recursion (rec)" should "compute factorials" in {
        "(fl (n) (app (rec fact (lam m (if (@= m 0) 1 (@* m (app fact (@- m 1)))))) n))" shouldFlEvalTo (List(5), Val(IntValue(120)))
        "(fl (n) (app (rec fact (lam m (if (@= m 0) 1 (@* m (app fact (@- m 1)))))) n))" shouldFlEvalTo (List(0), Val(IntValue(1)))
    }

    "let (local binding)" should "evaluate in the bound scope" in {
        "(fl () (let ((x 5) (y 6)) (@+ x y)))" shouldFlEvalTo (Nil, Val(IntValue(11)))
        "(fl (n) (let ((sq (@* n n))) (@+ sq n)))" shouldFlEvalTo (List(4), Val(IntValue(20)))
    }

    "letrec (mutual recursion)" should "compute Fibonacci" in {
        "(fl (n) (letrec ((fib (lam m (if (@< m 2) m (@+ (app fib (@- m 1)) (app fib (@- m 2))))))) (app fib n)))" shouldFlEvalTo (List(6), Val(IntValue(8)))
        "(fl (n) (letrec ((fib (lam m (if (@< m 2) m (@+ (app fib (@- m 1)) (app fib (@- m 2))))))) (app fib n)))" shouldFlEvalTo (List(10), Val(IntValue(55)))
    }

    "Multi-abstraction (abs) and tagless application" should "curry" in {
        "(fl () ((abs (a b) (@+ a b)) 3 4))" shouldFlEvalTo (Nil, Val(IntValue(7)))
        "(fl () (app (abs () 99) #u))"       shouldFlEvalTo (Nil, Val(IntValue(99)))
    }

    "list" should "build a unit-terminated chain of pairs" in {
        "(fl () (list))"       shouldFlEvalTo (Nil, Val(UnitValue))
        "(fl () (list 1))"     shouldFlEvalTo (Nil, Val(PairValue(IntValue(1), UnitValue)))
        "(fl () (list 1 2 3))" shouldFlEvalTo (Nil, Val(PairValue(IntValue(1),
                                    PairValue(IntValue(2), PairValue(IntValue(3), UnitValue)))))
    }

    "quote" should "produce s-expression values" in {
        "(fl () (quote foo))"    shouldFlEvalTo (Nil, Val(SymValue("foo")))
        "(fl () (quote 42))"     shouldFlEvalTo (Nil, Val(IntValue(42)))
        "(fl () (quote #u))"     shouldFlEvalTo (Nil, Val(UnitValue))
        "(fl () (quote (a b)))"  shouldFlEvalTo (Nil, Val(PairValue(SymValue("a"),
                                    PairValue(SymValue("b"), UnitValue))))
    }

    "cond (n-way conditional)" should "pick the first true branch" in {
        "(fl (x) (cond ((@> x 0) 1) ((@< x 0) -1) (else 0)))"  shouldFlEvalTo (List(5),  Val(IntValue(1)))
        "(fl (x) (cond ((@> x 0) 1) ((@< x 0) -1) (else 0)))"  shouldFlEvalTo (List(-3), Val(IntValue(-1)))
        "(fl (x) (cond ((@> x 0) 1) ((@< x 0) -1) (else 0)))"  shouldFlEvalTo (List(0),  Val(IntValue(0)))
    }

    "Short-circuit connectives" should "evaluate" in {
        "(fl () (scand #t #t #t))"  shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (scand #t #f #t))"  shouldFlEvalTo (Nil, Val(BoolValue(false)))
        "(fl () (scor #f #f #t))"   shouldFlEvalTo (Nil, Val(BoolValue(true)))
        "(fl () (scor #f #f))"      shouldFlEvalTo (Nil, Val(BoolValue(false)))
    }

    "recur (recursive function call)" should "compute factorials" in {
        "(fl () (recur fact ((n 5)) (if (@= n 0) 1 (@* n (app fact (@- n 1))))))" shouldFlEvalTo (Nil, Val(IntValue(120)))
    }

    "Top-level definitions (def)" should "bind values and functions" in {
        "(fl (x) (@+ x one) (def one 1))"  shouldFlEvalTo (List(41), Val(IntValue(42)))
        "(fl (x) (app double x) (def (double m) (@* 2 m)))" shouldFlEvalTo (List(21), Val(IntValue(42)))
    }

    "Errors" should "return Err" in {
        "(fl (x y) (@/ x y))"  shouldFlEvalTo (List(5, 0), Err("divide-by-zero"))
        "(fl () (app (lam y z) 5))" shouldFlEvalTo (Nil, Err("unbound variable: z"))
        "(fl (x) (@+ x))"      shouldFlEvalTo (List(1), Err("arity mismatch: expected 2 arguments, got 1"))
        "(fl (x) (@+ #t 1))"   shouldFlEvalTo (List(1), Err("+: arguments are not integers"))
        "(fl () (@fst 3))"      shouldFlEvalTo (Nil, Err("fst: argument is not a pair"))
        "(fl () (@sym=? (sym a) 3))" shouldFlEvalTo (Nil, Err("sym=?: arguments are not symbols"))
    }

    "Argument-count mismatches" should "return Err" in {
        "(fl (x y) (@+ x y))"  shouldFlEvalTo (List(1), Err("expected 2 argument(s), got 1"))
        "(fl (x) x)"           shouldFlEvalTo (List(1, 2), Err("expected 1 argument(s), got 2"))
    }
}
