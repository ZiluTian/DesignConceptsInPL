package DSL.elm

// Reference big-step operational semantics for ELM (Exercise 3.10a of the
// book).
//
//   (elm k e)          a program taking k integer arguments
//   (arg i)           reads the i-th argument (1-indexed)
//   <int>             an integer literal
//   (op e1 e2)        a binary arithmetic operation (op ∈ {+,-,*,/,%})
//
// ELM has no conditionals or boolean expressions. A program evaluates to an
// integer, or errors (None) when it divides or mods by zero, or reads an
// argument that was not supplied.
object Evaluator {
    type Env = Map[Int, Int]

    def eval(exp: NumExp, env: Env): Option[Int] = exp match {
        case IntLit(n) => Some(n)
        case Input(k)  => env.get(k.n)
        case ArithmeticOperation(op, e1, e2) =>
            for {
                x <- eval(e1, env)
                y <- eval(e2, env)
                s <- arith(op, x, y)
            } yield s
    }

    private def arith(op: ArithmeticOperator, x: Int, y: Int): Option[Int] = op match {
        case ADD  => Some(x + y)
        case SUB  => Some(x - y)
        case MULT => Some(x * y)
        case DIV  => if (y == 0) None else Some(x / y)
        case MOD  => if (y == 0) None else Some(x % y)
    }
}

/** Parse and run an ELM program text with the given integer arguments. */
def elmRun(input: String, args: Int*): Option[Int] =
    ELMProgram(input) match {
        case Some(Program(numArgs, body)) =>
            if (numArgs.n != args.size) None
            else {
                val env: Evaluator.Env = args.zipWithIndex.map { case (a, i) => (i + 1, a) }.toMap
                Evaluator.eval(body, env)
            }
        case _ => None
    }

// Test helper:  "(elm 2 (+ (arg 1) (arg 2)))" shouldEvaluateTo (List(3, 4), Some(7))
// (args, expected result) are passed as a single tuple for infix use.
extension (input: String)
    def shouldEvaluateTo(argsAndResult: (Seq[Int], Option[Int])): Unit = {
        val (args, expected) = argsAndResult
        val got = elmRun(input, args: _*)
        assert(got == expected, s"expected $expected but got $got for $input with args $args")
    }
