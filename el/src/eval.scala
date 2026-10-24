package DSL.el

// Reference big-step operational semantics for EL.
//
//   (el k e)          a program taking k integer arguments
//   (arg i)           reads the i-th argument (1-indexed)
//   <int>             an integer literal
//   (+ e1 e2 ...)     n-ary, left-associative arithmetic (also -, *, /, %)
//   (= e1 e2) < ...   relational tests producing a boolean
//   (and b1 b2)       logical connectives (also or)
//   (if b t e)        conditional: evaluate b, then t or e
//
// Evaluation is deterministic. A program errors (evaluates to None) when it
// divides or mods by zero, or reads an argument that was not supplied.
object Evaluator {
    type Env = Map[Int, Int]

    def eval(exp: NumExp, env: Env): Option[Int] = exp match {
        case IntLit(n) => Some(n)
        case Input(k)  => env.get(k.n)
        case ArithmeticOperation(op, e1, e2, rest @ _*) =>
            val es = List(e1, e2) ++ rest.toList
            es match {
                case Nil => None
                case h :: t =>
                    for {
                        a0 <- eval(h, env)
                        a  <- t.foldLeft(Option(a0): Option[Int]) { (acc, e) =>
                                 for {x <- acc; y <- eval(e, env); s <- arith(op, x, y)} yield s
                             }
                    } yield a
            }
        case Conditional(test, t, e) =>
            evalBool(test, env) match {
                case Some(true)  => eval(t, env)
                case Some(false) => eval(e, env)
                case None        => None
            }
    }

    def evalBool(exp: BoolExp, env: Env): Option[Boolean] = exp match {
        case BoolLit(b) => Some(b)
        case RelationalOperation(op, e1, e2) =>
            for {a <- eval(e1, env); b <- eval(e2, env)} yield rel(op, a, b)
        case LogicalOperation(op, b1, b2) =>
            for {x <- evalBool(b1, env); y <- evalBool(b2, env)} yield logic(op, x, y)
    }

    private def arith(op: ArithmeticOperator, x: Int, y: Int): Option[Int] = op match {
        case ADD  => Some(x + y)
        case SUB  => Some(x - y)
        case MULT => Some(x * y)
        case DIV  => if (y == 0) None else Some(x / y)
        case MOD  => if (y == 0) None else Some(x % y)
    }

    private def rel(op: RelationalOperator, a: Int, b: Int): Boolean = op match {
        case EQ => a == b
        case LT => a < b
        case GT => a > b
    }

    private def logic(op: LogicalOperator, x: Boolean, y: Boolean): Boolean = op match {
        case AND => x && y
        case OR  => x || y
    }
}

/** Parse and run an EL program text with the given integer arguments. */
def elRun(input: String, args: Int*): Option[Int] =
    ELProgram(input) match {
        case Some(Program(numArgs, body)) =>
            if (numArgs.n != args.size) None
            else {
                val env: Evaluator.Env = args.zipWithIndex.map { case (a, i) => (i + 1, a) }.toMap
                Evaluator.eval(body, env)
            }
        case _ => None
    }

// Test helper:  "(el 2 (+ (arg 1) (arg 2)))" shouldEvaluateTo (List(3, 4), Some(7))
// (args, expected result) are passed as a single tuple for infix use.
extension (input: String)
    def shouldEvaluateTo(argsAndResult: (Seq[Int], Option[Int])): Unit = {
        val (args, expected) = argsAndResult
        val got = elRun(input, args: _*)
        assert(got == expected, s"expected $expected but got $got for $input with args $args")
    }
