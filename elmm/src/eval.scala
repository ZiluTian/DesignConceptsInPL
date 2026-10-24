package DSL.elmm

// Reference big-step operational semantics for ELMM (Figure 3.7 of the book).
//
//   (elmm e)          a program: a single numerical expression
//   <int>             an integer literal
//   (op e1 e2)        a binary arithmetic operation (op ∈ {+,-,*,/,%})
//
// A program evaluates to an integer, or errors (None) when it divides or
// mods by zero.
object Evaluator {
    def eval(exp: NumExp): Option[Int] = exp match {
        case IntLit(n) => Some(n)
        case ArithmeticOperation(op, e1, e2) =>
            for {
                x <- eval(e1)
                y <- eval(e2)
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

/** Parse and run an ELMM program text. */
def elmmRun(input: String): Option[Int] =
    ELMMProgram(input) match {
        case Some(Program(body)) => Evaluator.eval(body)
        case _ => None
    }

// Test helper:  "(elmm (- 10 4))" shouldEvaluateTo Some(6)
extension (input: String)
    def shouldEvaluateTo(expected: Option[Int]): Unit = {
        val got = elmmRun(input)
        assert(got == expected, s"expected $expected but got $got for $input")
    }
