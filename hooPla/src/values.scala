package DSL.hooPla

import DSL.fl._

// HOOK's runtime values (Section 7.3.3 of the book). The book defines the
// semantics of HOOK by translating it into FL (Figure 7.25), where objects
// are records that bind message names to procedures and a message send is a
// lookup + application in the receiver record. This module instead gives a
// direct reference evaluator of the same semantics:
//
//   IntObj / BoolObj / SymObj   the built-in "literals as objects": every
//                               integer, boolean, and symbol is a full-fledged
//                               message-passing object (in the spirit of
//                               Smalltalk, book p.363)
//   UserObject                  a user object: a table of message -> method,
//                               created by (method ...), (compose ...), or
//                               (null-object)
//
// When a message is sent to the result of a compose, the receiver parameter
// of the invoked method is bound to the *whole* composed object (book
// p.368: "the receiver parameter of the invoked method is bound to the
// result of the compose").

sealed trait HookValue {
    override def toString: String
}

// An integer object: responds to + - * / % and to the comparisons
// = != < <= > >= (and, as in the FL translation, = / != compare across
// kinds and return false on a kind mismatch).
final case class IntObj(n: Int) extends HookValue {
    override def toString: String = n.toString
}

// A boolean object: responds to if-true (the target of the desugaring of
// `if`), to = / != (cross-kind, as above), and — mirroring FL's boolean
// primops — to not / and / or. (The book leaves the $new-boolean record as
// an exercise; this is the corresponding choice for the direct evaluator.)
final case class BoolObj(b: Boolean) extends HookValue {
    override def toString: String = if (b) "#t" else "#f"
}

// A symbol object: responds to = / != (structural over the symbol names).
final case class SymObj(s: String) extends HookValue {
    override def toString: String = "(sym " + s + ")"
}

// A user object: a table of message -> method. (Equality is by reference:
// two compose results are distinct objects even when their tables coincide —
// the book's translation gives the same behavior, since FL records are
// compared by the equality of their contents at the $val level, and user
// objects carry no comparable payload here.)
final class UserObject(val methods: Map[String, HookMethod]) extends HookValue {
    override def toString: String = "(object " + methods.keys.mkString(" ") + ")"
}

// A HOOK method: the message it handles, its receiver parameter, its formal
// parameters, its body, and the lexical environment in which the
// (method ...) expression was evaluated (it captures the top-level
// definitions, which have recursive scope).
case class HookMethod(receiver: String, formals: List[String], body: Exp, env: HookEnv)

// A lexical environment for HOOK: names -> HookValue. The environment is
// deliberately a mutable shared object: a method captures the *instance* of
// the environment in which it was created, so when it is later invoked it
// reads the current bindings of that instance. Because every top-level def
// is installed into the same top-level instance, a method body may reference
// a def that was installed after the method was created (the book's
// "recursive scope" for top-level definitions, p.373) — this matters for
// self-referencing classes such as point's `move`.
final class HookEnv {
    var bindings: Map[String, HookValue] = Map.empty

    def lookup(name: String): Option[HookValue] = bindings.get(name)
    def bind(name: String, v: HookValue): Unit   = bindings = bindings.updated(name, v)

    // A new environment with a (snapshot of the) current bindings plus the
    // given pairs. Used for method invocation: the receiver and the actual
    // arguments are bound here, on top of the captured environment.
    def extended(pairs: (String, HookValue)*): HookEnv = {
        val e = new HookEnv()
        e.bindings = bindings ++ pairs
        e
    }
}

// Results of evaluating a HOOK/HOOPLA expression.
sealed trait HResult
final case class HVal(v: HookValue) extends HResult
final case class HErr(msg: String) extends HResult
