package DSL.flavar

import DSL.fl._
import DSL.flic._

// Reference big-step operational semantics for FLAVAR (Section 8.4 of the
// book).
//
// A program is run with `flavarRun(text, args*)` (or `FlavarProgram(text)` for
// the AST, then `Evaluator.run`). The evaluator:
//   1. desugars the FLAVAR expression to the FLICK-kernel-plus-assignment
//      form (Desugar — Figure 8.9 + Figure 8.25), and
//   2. evaluates it with a call-by-value, lexical-scope semantics in which
//      every variable is a mutable location (a VarBox) and cells are
//      first-class values.
//
// Mutable variables (Figure 8.24):
//   I (as a Var)       reads the location named I (late: the current value)
//   (set! I E)         evaluates E, stores the result in the location named I;
//                      yields unit; an error if I is not a bound variable
//
// Cells (Figure 8.8) are unchanged from FLIC:
//   (cell E) / (@^ E) / (@:= E1 E2) / (@cell=? E1 E2) / (@cell? E)
//
// Parameter passing is call-by-value (Figure 8.26): an application allocates a
// fresh location for the formal parameter, seeded with the argument value.
//
// Results are `Val(value)` or `Err(message)`.
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
            val env = new FlavarEnv()
            formals.zip(args).foreach { case (f, a) => env.bindBox(f, new VarBox(a)) }
            buildDefEnv(defs, env) match {
                case Some(defEnv) => eval(DSL.flavar.Desugar(body), defEnv)
                case None         => Err("error in top-level definition")
            }
        }
    }

    // Install top-level definitions (value and function defs), supporting
    // mutual recursion among function definitions. Every name is bound to a
    // location; function defs get a location holding a closure (pass 1) so
    // they can recurse, and value defs are evaluated and stored (pass 2).
    // Returns None if a definition evaluates to an error.
    private def buildDefEnv(defs: List[Def], base: FlavarEnv): Option[FlavarEnv] = {
        val env = new FlavarEnv(); env.bindings = base.bindings
        // Pass 1: bind function (procedure) definitions so they can recurse.
        defs.foreach {
            case FunctionDef(name, formal, body) =>
                env.bindBox(name, new VarBox(FlavarClosure(formal, DSL.flavar.Desugar(body), env)))
            case _: ValueDef => () // handled in pass 2
        }
        // Pass 2: compute and store value definitions (short-circuit on error).
        val installed: Result = defs.foldLeft[Result](Val(UnitValue)) { (prev, d) =>
            prev match {
                case _: Err => prev
                case _ => d match {
                    case ValueDef(name, exp) => eval(DSL.flavar.Desugar(exp), env) match {
                        case Val(v)    => { env.update(name, v); prev }
                        case err: Err  => err
                    }
                    case _: FunctionDef => prev // already bound in pass 1
                }
            }
        }
        installed match {
            case _: Err => None
            case _      => Some(env)
        }
    }

    // ------------------------------------------------------------------
    // Expression evaluation
    // ------------------------------------------------------------------

    def eval(e: Exp, env: FlavarEnv): Result = e match {
        case UnitLit()          => Val(UnitValue)
        case BoolLit(b)         => Val(BoolValue(b))
        case IntLit(n)          => Val(IntValue(n))
        case Sym(s)             => Val(SymValue(s))
        // A variable reads the location it names (late binding).
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

        // Primitive application: arguments are evaluated strictly.
        case PrimOp(op, argExps) => {
            val argResults: List[Result] = argExps.map(a => eval(a, env))
            argResults.find(_.isInstanceOf[Err]) match {
                case Some(e: Err) => e
                case None =>
                    val values = argResults.collect { case Val(v) => v }
                    applyPrim(op, values)
            }
        }

        case Lam(formal, body) => Val(FlavarClosure(formal, body, env))

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
        case Rec(name, body) => Val(FlavarRecClosure(name, body, env))

        // ----------------------------------------------------------------
        // FLAVAR's assignment (Figure 8.24)
        // ----------------------------------------------------------------
        // (set! I E): evaluate E, then store the result in the location named
        // I. I is an L-value (a bound variable); E is an R-value.
        case SetBang(name, e) => eval(e, env) match {
            case Val(v) => env.lookupBox(name) match {
                case Some(box) => { box.value = v; Val(UnitValue) }
                case None      => Err(s"unbound variable: $name")
            }
            case err: Err => err
        }

        // ----------------------------------------------------------------
        // FLICK kernel (Figure 8.8) — cells, unchanged from FLIC
        // ----------------------------------------------------------------

        case CellExp(x) => eval(x, env) match {
            case Val(v)  => Val(CellValue.fresh(v))
            case e: Err  => e
        }

        // (begin E1 E2): evaluate E1 (discarding its value), then E2.
        case BeginExp(e1, e2) => eval(e1, env) match {
            case Val(_) => eval(e2, env)
            case e: Err => e
        }

        case CellFetchExp(x) => eval(x, env) match {
            case Val(c: CellValue) => Val(c.content)
            case Val(_)           => Err("error:not-a-cell")
            case e: Err           => e
        }

        case CellStoreExp(c, v) => (eval(c, env), eval(v, env)) match {
            case (Val(c: CellValue), Val(vv)) => { c.content = vv; Val(UnitValue) }
            case (Val(_), _)                  => Err("error:not-a-cell")
            case (e: Err, _)                 => e
            case (_, e: Err)                 => e
        }

        case CellEqExp(a, b) => (eval(a, env), eval(b, env)) match {
            case (Val(ca: CellValue), Val(cb: CellValue)) =>
                Val(BoolValue(ca.loc == cb.loc))
            case (Val(_), _) => Err("error:not-a-cell")
            case (_, Val(_)) => Err("error:not-a-cell")
            case (e: Err, _) => e
            case (_, e: Err) => e
        }

        case CellPredExp(x) => eval(x, env) match {
            case Val(_: CellValue) => Val(BoolValue(true))
            case Val(_)           => Val(BoolValue(false))
            case e: Err           => e
        }

        // Any form that survived desugaring is an internal error (letrec in
        // particular is desugared to set! by Figure 8.25 and never reaches
        // the evaluator).
        case _ => Err("internal error: un-desugared expression")
    }

    // ------------------------------------------------------------------
    // Procedure application (call-by-value, Figure 8.26)
    // ------------------------------------------------------------------

    private def applyProc(p: Proc, arg: Value): Result = p match {
        // A fresh location for the formal, seeded with the argument value.
        case FlavarClosure(formal, body, env) =>
            eval(body, env.extended(formal, arg))
        case FlavarRecClosure(name, body, env) =>
            val env2 = env.extended(name, p)
            eval(body, env2) match {
                case Val(q: Proc) => applyProc(q, arg)
                case Val(_)      => Err("rec: body did not evaluate to a procedure")
                case e: Err      => e
            }
        case _ => Err("app: rator is not a procedure")
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

/** Parse and run a FLAVAR/FLAVARK program text with the given integer arguments. */
def flavarRun(input: String, args: Int*): Result =
    FlavarProgram(input) match {
        case Some(prog) => Evaluator.run(prog, args.map(IntValue(_)).toList)
        case None        => Err("parse error")
    }

// Test helper:  "(flavar () (cell 5))" shouldFlavarEvalTo(Nil, ...)
extension (input: String)
    def shouldFlavarEvalTo(argsAndResult: (List[Int], Result)): Unit = {
        val (args, expected) = argsAndResult
        val got = flavarRun(input, args: _*)
        assert(got == expected, s"expected $expected but got $got for $input with args $args")
    }
