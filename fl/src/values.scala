package DSL.fl

// Runtime values of the FL evaluator.
//
//   unit        the unique unit value (#u)
//   true/false  booleans (#t / #f)
//   integer     an integer
//   sym(...)    a symbol
//   procedure   a (first-class) procedure: a closure or a recursive closure
//   (a, b)      a pair
//
// Value is (deliberately) not sealed: stateful extensions of FL (FLIC adds
// mutable cells, FLAVAR adds mutable-variable closures) introduce new value
// types that mix with these.
trait Value

case object UnitValue extends Value
final case class BoolValue(b: Boolean) extends Value
final case class IntValue(n: Int) extends Value
final case class SymValue(s: String) extends Value

// A procedure is a first-class value. FLK abstractions have exactly one formal
// parameter; RecClosure is the value produced by the kernel (rec ...) form and
// supports self-reference for recursion.
//
// (Not sealed: FLAVAR introduces its own closure types, which capture a
// mutable-variable environment.)
trait Proc extends Value
final case class Closure(formal: String, body: Exp, env: Env) extends Proc
final case class RecClosure(name: String, body: Exp, env: Env) extends Proc

final case class PairValue(first: Value, second: Value) extends Value

// A lexical environment. Environments are reference objects so that
// mutually-recursive bindings (letrec / top-level def) can share one live
// environment that grows as bindings are installed. `extended` produces a new
// environment for ordinary (shadowing) scoping.
final class Env {
    var bindings: Map[String, Value] = Map.empty
    def lookup(name: String): Option[Value] = bindings.get(name)
    def update(name: String, v: Value): Unit = { bindings = bindings.updated(name, v) }
    def extended(name: String, v: Value): Env = {
        val e = new Env(); e.bindings = bindings.updated(name, v); e
    }
}

// The outcome of evaluating an expression: either a value or an error.
// (Non-termination — an infinite loop — is not representable by a total
// evaluator and simply does not return.)
sealed trait Result
case class Val(value: Value) extends Result
case class Err(msg: String) extends Result

object FLValue {
    // Render a runtime value in the book's outcome notation.
    def show(v: Value): String = v match {
        case UnitValue         => "unit"
        case BoolValue(b)      => b.toString
        case IntValue(n)       => n.toString
        case SymValue(s)       => s"sym($s)"
        case _: Proc           => "<procedure>"
        case PairValue(f, s)   => s"(${show(f)}, ${show(s)})"
        case other             => other.toString
    }
}
