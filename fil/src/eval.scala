package DSL.fil

import DSL.fl._

// Reference big-step operational semantics for FIL (Section 17.7 of the
// book).
//
// FIL is a statically scoped, call-by-value language, and because it is
// stateful the order of evaluation matters: the subexpressions of an app,
// the arguments of a prim, and the definition expressions of a let are all
// evaluated from left to right (page 1035). A let is a parallel binding:
// the definition expressions are evaluated in the surrounding environment
// (a definition cannot refer to a let-bound name), and the body sees all of
// the bindings.
//
// FIL has no formal type system (page 1035); the evaluator nonetheless
// reports dynamic type errors (a non-boolean if test, non-integer
// arithmetic, an out-of-range mget, ...) as Err, mirroring the FL
// evaluator.
//
// A program is run with `filRun(text, args*)` (or `FilProgram(text)` for
// the AST, then `Evaluator.run`).

object Evaluator {

    def run(p: FilProgram, args: List[Value]): Result = {
        if (args.size != p.formals.size)
            Err(s"expected ${p.formals.size} argument(s), got ${args.size}")
        else {
            val env = new Env()
            p.formals.zip(args).foreach { case (f, a) => env.update(f, a) }
            eval(p.body, env)
        }
    }

    def eval(e: Exp, env: Env): Result = e match {
        case UnitLit() => Val(UnitValue)
        case BoolLit(b) => Val(BoolValue(b))
        case IntLit(n) => Val(IntValue(n))
        case Sym(s) => Val(SymValue(s))
        case Var(name) => env.lookup(name) match {
            case Some(v) => Val(v)
            case None => Err(s"unbound variable: $name")
        }
        case ErrorExpr(msg) => Err(msg)

        case If(test, th, el) => eval(test, env) match {
            case Val(BoolValue(true)) => eval(th, env)
            case Val(BoolValue(false)) => eval(el, env)
            case Val(_) => Err("if: test expression is not a boolean")
            case e: Err => e
        }

        // Primitive application: strict, left to right.
        case FilPrim(op, argExps) =>
            val argResults: List[Result] = argExps.map(a => eval(a, env))
            argResults.find(_.isInstanceOf[Err]) match {
                case Some(e: Err) => e
                case None =>
                    val values = argResults.collect { case Val(v) => v }
                    applyPrim(op, values)
            }

        case Abs(formals, body) => Val(FilClosure(formals, body, env))

        // Application: strict, left to right (rator first, then the
        // arguments).
        case FilApp(rator, rands) => eval(rator, env) match {
            case Val(c: FilClosure) => applyClosure(c, rands, env)
            case Val(_) => Err("app: rator is not a procedure")
            case e: Err => e
        }

        // let — parallel binding: the definition expressions are evaluated
        // left to right in the surrounding environment; the body sees all
        // of the bindings.
        case Let(binds, body) =>
            evalBinds(binds, env) match {
                case Left(err) => err
                case Right(vs) =>
                    val env2 = vs.foldLeft(env) { (e2, kv) => e2.extended(kv._1, kv._2) }
                    eval(body, env2)
            }

        case _ => Err("internal error: un-desugared or foreign expression")
    }

    // Apply a closure: evaluate the arguments left to right, extending the
    // closure's environment one formal at a time.
    private def applyClosure(c: FilClosure, rands: List[Exp], env: Env): Result =
        (c.formals.isEmpty, rands.isEmpty) match {
            case (true, true) => eval(c.body, c.env)
            case (true, false) =>
                Err(s"arity mismatch: procedure takes 0 argument(s), got ${rands.size}")
            case (false, true) =>
                Err(s"arity mismatch: procedure takes ${c.formals.size} argument(s), got 0")
            case (false, false) =>
                val f = c.formals.head
                val r = rands.head
                eval(r, env) match {
                    case Val(v) =>
                        applyClosure(
                            FilClosure(c.formals.tail, c.body, c.env.extended(f, v)),
                            rands.tail, env)
                    case e: Err => e
                }
        }

    // Evaluate the definition expressions of a let, left to right, in the
    // (unextended) surrounding environment — parallel binding.
    private def evalBinds(binds: List[(String, Exp)], env: Env): Either[Err, List[(String, Value)]] =
        binds.foldLeft[Either[Err, List[(String, Value)]]](Right(Nil)) {
            case (Left(err), _) => Left(err)
            case (Right(acc), (n, e)) => eval(e, env) match {
                case Val(v) => Right(acc :+ ((n, v)))
                case e: Err => Left(e)
            }
        }

    // ------------------------------------------------------------------
    // The FIL primitive operators (Figure 17.14)
    // ------------------------------------------------------------------

    private def applyPrim(op: String, vs: List[Value]): Result = op match {
        // Arithmetic operators
        case "+" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(IntValue(x + y))
            case _ => Err("+: arguments are not integers")
        })
        case "-" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(IntValue(x - y))
            case _ => Err("-: arguments are not integers")
        })
        case "*" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(IntValue(x * y))
            case _ => Err("*: arguments are not integers")
        })
        case "/" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(_), IntValue(0)) => Err("divide-by-zero")
            case (IntValue(x), IntValue(y)) => Val(IntValue(x / y))
            case _ => Err("/: arguments are not integers")
        })
        case "%" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(_), IntValue(0)) => Err("divide-by-zero")
            case (IntValue(x), IntValue(y)) => Val(IntValue(x % y))
            case _ => Err("%: arguments are not integers")
        })
        // Relational operators
        case "=" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(BoolValue(x == y))
            case _ => Err("=: arguments are not integers")
        })
        case "!=" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(BoolValue(x != y))
            case _ => Err("!=: arguments are not integers")
        })
        case "<" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(BoolValue(x < y))
            case _ => Err("<: arguments are not integers")
        })
        case "<=" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(BoolValue(x <= y))
            case _ => Err("<=: arguments are not integers")
        })
        case ">" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(BoolValue(x > y))
            case _ => Err(">: arguments are not integers")
        })
        case ">=" => bi(vs)((a, b) => (a, b) match {
            case (IntValue(x), IntValue(y)) => Val(BoolValue(x >= y))
            case _ => Err(">=: arguments are not integers")
        })
        // Logical operators
        case "bool=?" => bi(vs)((a, b) => (a, b) match {
            case (BoolValue(x), BoolValue(y)) => Val(BoolValue(x == y))
            case _ => Err("bool=?: arguments are not booleans")
        })
        case "sym=?" => bi(vs)((a, b) => (a, b) match {
            case (SymValue(x), SymValue(y)) => Val(BoolValue(x == y))
            case _ => Err("sym=?: arguments are not symbols")
        })
        case "not" => un(vs)(v => v match {
            case BoolValue(b) => Val(BoolValue(!b))
            case _ => Err("not: argument is not a boolean")
        })
        case "and" => bi(vs)((a, b) => (a, b) match {
            case (BoolValue(x), BoolValue(y)) => Val(BoolValue(x && y))
            case _ => Err("and: arguments are not booleans")
        })
        case "or" => bi(vs)((a, b) => (a, b) match {
            case (BoolValue(x), BoolValue(y)) => Val(BoolValue(x || y))
            case _ => Err("or: arguments are not booleans")
        })
        // List operators (a list is a unit-terminated chain of pairs, as in
        // FL; the book's lists are immutable).
        case "null" =>
            if (vs.isEmpty) Val(UnitValue)
            else Err(s"arity mismatch: null takes 0 argument(s), got ${vs.size}")
        case "null?" => un(vs)(v => v match {
            case UnitValue => Val(BoolValue(true))
            case _ => Val(BoolValue(false))
        })
        case "cons" => bi(vs)((a, b) => Val(PairValue(a, b)))
        case "car" => un(vs)(v => v match {
            case PairValue(f, _) => Val(f)
            case _ => Err("car: argument is not a list")
        })
        case "cdr" => un(vs)(v => v match {
            case PairValue(_, s) => Val(s)
            case _ => Err("cdr: argument is not a list")
        })
        // Mutable-product operators
        case "mprod" => Val(MProdValue.fresh(vs))
        case "mprod=?" => bi(vs)((a, b) => (a, b) match {
            case (x: MProdValue, y: MProdValue) => Val(BoolValue(x.loc == y.loc))
            case _ => Err("mprod=?: arguments are not mutable products")
        })
        case s if s.startsWith("mget ") =>
            s.drop("mget ".length).toIntOption match {
                case Some(j) if j >= 1 => un(vs)(v => v match {
                    case mp: MProdValue =>
                        if (j <= mp.slots.length) Val(mp.slots(j - 1))
                        else Err(s"mget: index $j out of range (product has ${mp.slots.length} slot(s))")
                    case _ => Err("mget: argument is not a mutable product")
                })
                case _ => Err("malformed mget operator: " + op)
            }
        case s if s.startsWith("mset! ") =>
            s.drop("mset! ".length).toIntOption match {
                case Some(j) if j >= 1 => bi(vs)((a, b) => (a, b) match {
                    case (mp: MProdValue, v) =>
                        if (j <= mp.slots.length) { mp.slots(j - 1) = v; Val(UnitValue) }
                        else Err(s"mset!: index $j out of range (product has ${mp.slots.length} slot(s))")
                    case _ => Err("mset!: first argument is not a mutable product")
                })
                case _ => Err("malformed mset! operator: " + op)
            }
        case other => Err(s"unknown FIL primitive operator: $other")
    }

    // Helpers for arity checking.
    private def un(vs: List[Value])(f: Value => Result): Result = vs match {
        case List(v) => f(v)
        case _ => Err(s"arity mismatch: expected 1 argument, got ${vs.size}")
    }
    private def bi(vs: List[Value])(f: (Value, Value) => Result): Result = vs match {
        case List(a, b) => f(a, b)
        case _ => Err(s"arity mismatch: expected 2 arguments, got ${vs.size}")
    }
}

/** Parse and run a FIL program text with the given integer arguments. */
def filRun(input: String, args: Int*): Result =
    FilProgram(input) match {
        case Some(prog) => Evaluator.run(prog, args.map(IntValue(_)).toList)
        case None => Err("parse error")
    }

// Test helper:  "(fil (x y) (@+ x y))" shouldFilEvalTo(List(3, 4), Val(IntValue(7)))
extension (input: String)
    def shouldFilEvalTo(args: List[Int], expected: Result): Unit = {
        val got = filRun(input, args: _*)
        assert(got == expected, s"expected $expected but got $got for $input with args $args")
    }
