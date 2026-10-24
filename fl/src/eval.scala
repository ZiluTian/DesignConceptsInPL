package DSL.fl

// Reference big-step operational semantics for FL (Chapter 6 of the book).
//
// A program is run with `flRun(text, args*)` (or `FlProgram(text)` for the AST,
// then `Evaluator.run`). The evaluator:
//   1. desugars the FL expression to the FLK kernel (Desugar), and
//   2. evaluates the kernel with a call-by-value, lexical-scope semantics.
//
// Results are `Val(value)` or `Err(message)`; the latter signals a type error,
// a divide-by-zero, an unbound variable, or an arity mismatch.
object Evaluator {

    def run(program: FL, args: List[Value]): Result = program match {
        case UnsugaredProgram(formals, body) => runProgram(formals, body, Nil, args)
        case SugaredProgram(formals, body, defs) => runProgram(formals, body, defs, args)
        case _ => Err("not a program")
    }

    private def runProgram(formals: List[String], body: Exp, defs: List[Def], args: List[Value]): Result = {
        if (args.size != formals.size)
            Err(s"expected ${formals.size} argument(s), got ${args.size}")
        else {
            val env = new Env()
            formals.zip(args).foreach { case (f, a) => env.update(f, a) }
            buildDefEnv(defs, env) match {
                case Some(defEnv) => eval(Desugar(body), defEnv)
                case None         => Err("error in top-level definition")
            }
        }
    }

    // Install top-level definitions (value and function defs), supporting
    // mutual recursion among function definitions. Returns None if a
    // definition evaluates to an error.
    private def buildDefEnv(defs: List[Def], base: Env): Option[Env] = {
        val cell = new Env(); cell.bindings = base.bindings
        // Pass 1: bind function (procedure) definitions so they can recurse.
        defs.foreach {
            case FunctionDef(name, formal, body) =>
                cell.update(name, Closure(formal, Desugar(body), cell))
            case _: ValueDef => () // handled in pass 2
        }
        // Pass 2: compute and bind value definitions (short-circuit on error).
        val installed: Result = defs.foldLeft[Result](Val(UnitValue)) { (prev, d) =>
            prev match {
                case _: Err => prev
                case _ => d match {
                    case ValueDef(name, exp) => eval(Desugar(exp), cell) match {
                        case Val(v)    => { cell.update(name, v); prev }
                        case err: Err  => err
                    }
                    case _: FunctionDef => prev // already bound in pass 1
                }
            }
        }
        installed match {
            case _: Err => None
            case _      => Some(cell)
        }
    }

    // ------------------------------------------------------------------
    // Expression evaluation
    // ------------------------------------------------------------------

    def eval(e: Exp, env: Env): Result = e match {
        case UnitLit()          => Val(UnitValue)
        case BoolLit(b)         => Val(BoolValue(b))
        case IntLit(n)          => Val(IntValue(n))
        case Sym(s)             => Val(SymValue(s))
        case Var(name) => env.lookup(name) match {
            case Some(v) => Val(v)
            case None    => Err(s"unbound variable: $name")
        }
        case ErrorExpr(msg) => Err(msg)

        case If(test, th, el) => eval(test, env) match {
            case Val(BoolValue(true))  => eval(th, env)
            case Val(BoolValue(false)) => eval(el, env)
            case Val(_)                => Err("if: test expression is not a boolean")
            case e: Err                => e
        }

        // Primitive application: arguments are evaluated strictly (the book's
        // `and`/`or` are explicitly "not short-circuit").
        case PrimOp(op, argExps) => {
            val argResults: List[Result] = argExps.map(a => eval(a, env))
            argResults.find(_.isInstanceOf[Err]) match {
                case Some(e: Err) => e
                case None =>
                    val values = argResults.collect { case Val(v) => v }
                    applyPrim(op, values)
            }
        }

        case Lam(formal, body) => Val(Closure(formal, body, env))

        case App(rator, rand) => eval(rator, env) match {
            case Val(p: Proc) => eval(rand, env) match {
                case Val(av) => applyProc(p, av)
                case e: Err  => e
            }
            case Val(_) => Err("app: rator is not a procedure")
            case e: Err => e
        }

        case Pair(f, s) => (eval(f, env), eval(s, env)) match {
            case (Val(fv), Val(sv)) => Val(PairValue(fv, sv))
            case (e: Err, _) => e
            case (_, e: Err) => e
        }

        // (rec name body) evaluates to a procedure that, when applied,
        // evaluates `body` in an environment where `name` is bound to itself.
        case Rec(name, body) => Val(RecClosure(name, body, env))

        // letrec — native mutual-recursion binding (see the note in Desugar).
        case LetRec(binds, body) => evalLetRec(binds, body, env)

        // Any sugar form that survived desugaring is an internal error.
        case _ => Err("internal error: un-desugared expression")
    }

    private def evalLetRec(binds: List[(String, Exp)], body: Exp, env: Env): Result = {
        val cell = new Env(); cell.bindings = env.bindings
        // Pass 1: bind procedure (lam) definitions into the live cell.
        binds.foreach { case (n, e) => e match {
            case Lam(formal, b) => cell.update(n, Closure(formal, b, cell))
            case _ => () // a value definition; computed in pass 2
        } }
        // Pass 2: compute and bind value definitions (short-circuit on error).
        val installed: Result = binds.foldLeft[Result](Val(UnitValue)) { (prev, b) =>
            val (n, e) = b
            prev match {
                case _: Err => prev
                case _ => e match {
                    case _: Lam => prev // already bound in pass 1
                    case _ => eval(e, cell) match {
                        case Val(v)    => { cell.update(n, v); prev }
                        case err: Err  => err
                    }
                }
            }
        }
        installed match {
            case err: Err => err
            case _        => eval(body, cell)
        }
    }

    // ------------------------------------------------------------------
    // Procedure application
    // ------------------------------------------------------------------

    private def applyProc(p: Proc, arg: Value): Result = p match {
        case Closure(formal, body, env) =>
            eval(body, env.extended(formal, arg))
        case RecClosure(name, body, env) =>
            val cell = new Env(); cell.bindings = env.bindings.updated(name, p)
            eval(body, cell) match {
                case Val(q: Proc) => applyProc(q, arg)
                case Val(_)      => Err("rec: body did not evaluate to a procedure")
                case e: Err      => e
            }
    }

    // ------------------------------------------------------------------
    // Primitive operators (Figure 6.2)
    // ------------------------------------------------------------------

    private def applyPrim(op: PrimOpTag, vs: List[Value]): Result = op match {
        // Unary type predicates
        case UnitQ => un(vs)(v => v match { case UnitValue => Val(BoolValue(true)); case _ => Val(BoolValue(false)) })
        case BoolQ => un(vs)(v => v match { case _: BoolValue => Val(BoolValue(true)); case _ => Val(BoolValue(false)) })
        case IntQ  => un(vs)(v => v match { case _: IntValue => Val(BoolValue(true)); case _ => Val(BoolValue(false)) })
        case SymQ  => un(vs)(v => v match { case _: SymValue => Val(BoolValue(true)); case _ => Val(BoolValue(false)) })
        case ProcQ => un(vs)(v => v match { case _: Proc => Val(BoolValue(true)); case _ => Val(BoolValue(false)) })
        case PairQ => un(vs)(v => v match { case _: PairValue => Val(BoolValue(true)); case _ => Val(BoolValue(false)) })
        // not
        case Not => un(vs)(v => v match {
            case BoolValue(b) => Val(BoolValue(!b))
            case _ => Err("not: argument is not a boolean")
        })
        // Boolean connectives (binary, not short-circuit)
        case And => bi(vs)((a, b) => (a, b) match {
            case (BoolValue(x), BoolValue(y)) => Val(BoolValue(x && y))
            case _ => Err("and: arguments are not booleans")
        })
        case Or => bi(vs)((a, b) => (a, b) match {
            case (BoolValue(x), BoolValue(y)) => Val(BoolValue(x || y))
            case _ => Err("or: arguments are not booleans")
        })
        case BoolEq => bi(vs)((a, b) => (a, b) match {
            case (BoolValue(x), BoolValue(y)) => Val(BoolValue(x == y))
            case _ => Err("bool=?: arguments are not booleans")
        })
        // Integer arithmetic (binary)
        case Plus => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(IntValue(x + y))
            case _ => Err("+: arguments are not integers")
        })
        case Minus => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(IntValue(x - y))
            case _ => Err("-: arguments are not integers")
        })
        case Star => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(IntValue(x * y))
            case _ => Err("*: arguments are not integers")
        })
        case Slash => bi(vs)((a, b) => (a, b) match {
            case (IntValue(_), IntValue(0)) => Err("divide-by-zero")
            case (IntValue(x), IntValue(y)) => Val(IntValue(x / y))
            case _ => Err("/: arguments are not integers")
        })
        case Percent => bi(vs)((a, b) => (a, b) match {
            case (IntValue(_), IntValue(0)) => Err("divide-by-zero")
            case (IntValue(x), IntValue(y)) => Val(IntValue(x % y))
            case _ => Err("%: arguments are not integers")
        })
        // Integer comparison (binary)
        case Eq => bi(vs)((a, b) => (a, b) match { case (IntValue(x), IntValue(y)) => Val(BoolValue(x == y)); case _ => Err("=: arguments are not integers") })
        case Neq => bi(vs)((a, b) => (a, b) match { case (IntValue(x), IntValue(y)) => Val(BoolValue(x != y)); case _ => Err("!=: arguments are not integers") })
        case Lt => bi(vs)((a, b) => (a, b) match { case (IntValue(x), IntValue(y)) => Val(BoolValue(x < y)); case _ => Err("<: arguments are not integers") })
        case Le => bi(vs)((a, b) => (a, b) match { case (IntValue(x), IntValue(y)) => Val(BoolValue(x <= y)); case _ => Err("<=: arguments are not integers") })
        case Gt => bi(vs)((a, b) => (a, b) match { case (IntValue(x), IntValue(y)) => Val(BoolValue(x > y)); case _ => Err(">: arguments are not integers") })
        case Ge => bi(vs)((a, b) => (a, b) match { case (IntValue(x), IntValue(y)) => Val(BoolValue(x >= y)); case _ => Err(">=: arguments are not integers") })
        // Symbol equality (binary)
        case SymEq => bi(vs)((a, b) => (a, b) match {
            case (SymValue(x), SymValue(y)) => Val(BoolValue(x == y))
            case _ => Err("sym=?: arguments are not symbols")
        })
        // Pair selectors (unary)
        case Fst => un(vs)(v => v match {
            case PairValue(f, _) => Val(f)
            case _ => Err("fst: argument is not a pair")
        })
        case Snd => un(vs)(v => v match {
            case PairValue(_, s) => Val(s)
            case _ => Err("snd: argument is not a pair")
        })
    }

    // Helpers for arity checking and integer comparison.
    private def un(vs: List[Value])(f: Value => Result): Result = vs match {
        case List(v) => f(v)
        case _ => Err(s"arity mismatch: expected 1 argument, got ${vs.size}")
    }
    private def bi(vs: List[Value])(f: (Value, Value) => Result): Result = vs match {
        case List(a, b) => f(a, b)
        case _ => Err(s"arity mismatch: expected 2 arguments, got ${vs.size}")
    }
}

/** Parse and run an FL/FLK program text with the given integer arguments. */
def flRun(input: String, args: Int*): Result =
    FlProgram(input) match {
        case Some(prog) => Evaluator.run(prog, args.map(IntValue(_)).toList)
        case None        => Err("parse error")
    }

// Test helper:  "(fl (x y) (@+ x y))" shouldFlEvalTo(List(3, 4), Val(IntValue(7)))
extension (input: String)
    def shouldFlEvalTo(args: List[Int], expected: Result): Unit = {
        val got = flRun(input, args: _*)
        assert(got == expected, s"expected $expected but got $got for $input with args $args")
    }
