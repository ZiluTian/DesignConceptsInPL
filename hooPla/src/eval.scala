package DSL.hooPla

import DSL.fl._

// Reference big-step operational semantics for HOOK / HOOPLA (Section 7.3
// of the book).
//
// A program is run with `hooplaRun(text, args*)` (or `HooPlaProgram(text)`
// for the AST, then `Evaluator.run`). The evaluator:
//   1. desugars the HOOPLA expression to the HOOK kernel (Desugar, Figure
//      7.23), and
//   2. evaluates the kernel directly:
//        * integers, booleans, and symbols are full message-passing objects;
//        * user objects are tables of message -> method;
//        * compose merges two method tables (the first object's methods
//          take precedence over the second's);
//        * a send looks up the method in the receiver and invokes it with
//          the receiver (the *whole* object, if composed) and the arguments;
//        * top-level defs are installed sequentially into one shared
//          environment, so their method bodies have recursive scope (a body
//          may reference defs installed before it — and, because bodies are
//          evaluated at invocation time, even the def that created the
//          method, as in point's `move` calling `(send new point ...)`).
//
// The book instead defines the semantics by a translation into FL
// (Figure 7.25); the README describes the correspondence.
//
// Results are `HVal(value)` or `HErr(message)`.
object Evaluator {

    def run(program: FL, args: List[Int]): HResult = program match {
        case UnsugaredProgram(formals, body) => runProgram(formals, body, Nil, args)
        case SugaredProgram(formals, body, defs) => runProgram(formals, body, defs, args)
        case _ => HErr("not a program")
    }

    private def runProgram(formals: List[String], body: Exp, defs: List[Def], args: List[Int]): HResult = {
        if (args.size != formals.size)
            HErr(s"expected ${formals.size} argument(s), got ${args.size}")
        else {
            // Program arguments are integers; they are bound as integer
            // objects (the book's translation wraps them in $new-integer).
            val env = new HookEnv()
            formals.zip(args).foreach { case (f, a) => env.bind(f, IntObj(a)) }
            buildDefEnv(defs, env) match {
                case Some(defEnv) => eval(DSL.hooPla.Desugar(body), defEnv)
                case None         => HErr("error in top-level definition")
            }
        }
    }

    // Install top-level definitions sequentially: each def is evaluated in
    // the environment of the defs installed before it, and its value is
    // bound before the next def is evaluated. All defs share one HookEnv
    // instance, and method bodies capture that instance (not a snapshot), so
    // a body evaluated at invocation time sees every def that has been
    // installed by then — HOOK's recursive top-level scope.
    private def buildDefEnv(defs: List[Def], base: HookEnv): Option[HookEnv] = {
        val env = new HookEnv()
        env.bindings = base.bindings
        defs.foldLeft[Option[HookEnv]](Some(env)) { (prev, d) =>
            prev match {
                case Some(e) => d match {
                    case ValueDef(name, exp) => eval(DSL.hooPla.Desugar(exp), e) match {
                        case HVal(v)    => { e.bind(name, v); Some(e) }
                        case err: HErr  => None
                    }
                    case _ => None // HOOK has no function definitions
                }
                case None => None
            }
        }
    }

    // ------------------------------------------------------------------
    // Expression evaluation
    // ------------------------------------------------------------------

    def eval(e: Exp, env: HookEnv): HResult = e match {
        case BoolLit(b)      => HVal(BoolObj(b))
        case IntLit(n)       => HVal(IntObj(n))
        case Sym(s)          => HVal(SymObj(s))
        case Var(name)       => env.lookup(name) match {
            case Some(v) => HVal(v)
            case None    => HErr(s"unbound variable: $name")
        }

        // (method M (Ireceiver Iformal*) Ebody) evaluates to a user object
        // that responds to the single message M.
        case MethodExp(message, receiver, formals, body) =>
            HVal(new UserObject(Map(message -> HookMethod(receiver, formals, body, env))))

        // (compose E1 E2): both operands must be user objects; the methods
        // of the first take precedence over those of the second.
        case ComposeExp(o1, o2) => (eval(o1, env), eval(o2, env)) match {
            case (HVal(a: UserObject), HVal(b: UserObject)) =>
                HVal(new UserObject(b.methods ++ a.methods))
            case (HVal(a), HVal(b)) =>
                HErr(s"compose: arguments are not user objects (got $a and $b)")
            case (e: HErr, _) => e
            case (_, e: HErr) => e
        }

        // (null-object): the object with no methods.
        case NullObjectExp() => HVal(new UserObject(Map.empty))

        // (send M Ereceiver Earg*): evaluate the receiver, then the
        // arguments (left to right), then dispatch on the receiver's kind.
        case SendExp(message, receiverExp, argExps) => eval(receiverExp, env) match {
            case e: HErr => e
            case HVal(recv) =>
                val argResults: List[HResult] = argExps.map(a => eval(a, env))
                argResults.collectFirst { case e: HErr => e } match {
                    case Some(err) => err
                    case None =>
                        val args = argResults.collect { case HVal(v) => v }
                        sendTo(recv, message, args)
                }
        }

        // Any HOOPLA sugar that survived desugaring is an internal error.
        case _ => HErr("internal error: un-desugared expression")
    }

    // ------------------------------------------------------------------
    // Message dispatch
    // ------------------------------------------------------------------

    private def sendTo(recv: HookValue, message: String, args: List[HookValue]): HResult = recv match {
        case IntObj(n)  => intSend(n, message, args)
        case BoolObj(b) => boolSend(b, message, args)
        case SymObj(s)  => symSend(s, message, args)
        case uo: UserObject => uo.methods.get(message) match {
            case None => HErr(s"error:no-such-method: $message")
            case Some(HookMethod(receiver, formals, body, env)) =>
                if (formals.size != args.size)
                    HErr(s"arity mismatch: method for '$message' expects ${formals.size} argument(s), got ${args.size}")
                else {
                    // The receiver parameter is bound to the whole receiver
                    // object (the result of a compose, if the method comes
                    // from a composed component).
                    val env2 = env.extended((receiver -> recv) +: formals.zip(args): _*)
                    eval(body, env2)
                }
        }
    }

    // The integer object's methods (the $new-integer record, Figure 7.25).
    // = / != compare across kinds and return false / true on a mismatch
    // (book p.373); the other operations require an integer argument.
    private def intSend(n: Int, message: String, args: List[HookValue]): HResult = {
        def bin(f: (Int, Int) => Int, op: String): HResult = args match {
            case List(IntObj(m)) => HVal(IntObj(f(n, m)))
            case List(_)        => HErr(s"$op: argument is not an integer")
            case _              => HErr(s"arity mismatch: '$op' expects 1 argument(s), got ${args.size}")
        }
        def rel(f: Int => Boolean, op: String): HResult = args match {
            case List(IntObj(m)) => HVal(BoolObj(f(m)))
            case List(_)        => HErr(s"$op: argument is not an integer")
            case _              => HErr(s"arity mismatch: '$op' expects 1 argument(s), got ${args.size}")
        }
        message match {
            case "+"  => bin(_ + _, "+")
            case "-"  => bin((a, b) => a - b, "-")
            case "*"  => bin(_ * _, "*")
            case "/"  => if (args == List(IntObj(0))) HErr("divide-by-zero") else bin(_ / _, "/")
            case "%"  => if (args == List(IntObj(0))) HErr("divide-by-zero") else bin(_ % _, "%")
            case "="  => args match {
                case List(IntObj(m)) => HVal(BoolObj(n == m))
                case _               => HVal(BoolObj(false))
            }
            case "!=" => args match {
                case List(IntObj(m)) => HVal(BoolObj(n != m))
                case _               => HVal(BoolObj(true))
            }
            case "<"  => rel(m => n < m, "<")
            case "<=" => rel(m => n <= m, "<=")
            case ">"  => rel(m => n > m, ">")
            case ">=" => rel(m => n >= m, ">=")
            case _ => HErr(s"error:no-such-method: $message")
        }
    }

    // The boolean object's methods: if-true is the target of the desugaring
    // of `if` (it sends `call` to the chosen thunk); = / != compare across
    // kinds as for integers; not / and / or mirror FL's boolean primops.
    private def boolSend(b: Boolean, message: String, args: List[HookValue]): HResult = message match {
        case "if-true" => args match {
            case List(thenT, elseT) => sendTo(if (b) thenT else elseT, "call", Nil)
            case _ => HErr("if-true: expected 2 arguments")
        }
        case "="  => args match {
            case List(BoolObj(m)) => HVal(BoolObj(b == m))
            case _               => HVal(BoolObj(false))
        }
        case "!=" => args match {
            case List(BoolObj(m)) => HVal(BoolObj(b != m))
            case _               => HVal(BoolObj(true))
        }
        case "not" => if (args.isEmpty) HVal(BoolObj(!b)) else HErr("not: expected 0 arguments")
        case "and" => args match {
            case List(BoolObj(m)) => HVal(BoolObj(b && m))
            case _               => HErr("and: argument is not a boolean")
        }
        case "or"  => args match {
            case List(BoolObj(m)) => HVal(BoolObj(b || m))
            case _               => HErr("or: argument is not a boolean")
        }
        case _ => HErr(s"error:no-such-method: $message")
    }

    // The symbol object's methods: = / != over the symbol names, comparing
    // across kinds as above.
    private def symSend(s: String, message: String, args: List[HookValue]): HResult = message match {
        case "="  => args match {
            case List(SymObj(m)) => HVal(BoolObj(s == m))
            case _              => HVal(BoolObj(false))
        }
        case "!=" => args match {
            case List(SymObj(m)) => HVal(BoolObj(s != m))
            case _              => HVal(BoolObj(true))
        }
        case _ => HErr(s"error:no-such-method: $message")
    }
}

/** Parse and run a HOOK/HOOPLA program text with the given integer arguments. */
def hooplaRun(input: String, args: Int*): HResult =
    HooPlaProgram(input) match {
        case Some(prog) => Evaluator.run(prog, args.toList)
        case None       => HErr("parse error")
    }

// Test helper:  "(hoopla () ...)" shouldHooPlaEvalTo(Nil, HVal(IntObj(5)))
extension (input: String)
    def shouldHooPlaEvalTo(argsAndResult: (List[Int], HResult)): Unit = {
        val (args, expected) = argsAndResult
        val got = hooplaRun(input, args: _*)
        assert(got == expected, s"expected $expected but got $got for $input with args $args")
    }
