package DSL.fil

import DSL.fl._
import DSL.sexp._

// AST of FIL (Section 17.7 of the book), the intermediate language of the
// Tortoise transformation-based compiler. FIL is a stateful, call-by-value,
// statically scoped, function-oriented language.
//
// Kernel grammar (Figure 17.14):
//   P ∈ ProgFIL ::= (fil (Iformal*) Ebody)
//   E ∈ ExpFIL  ::= L | I | (error Ymessage)
//               | (if Etest Ethen Eelse)
//               | (prim Oprimop Earg*)
//               | (abs (Iformal*) Ebody)
//               | (app Erator Erand*)
//               | (let ((Iname Edefn)*) Ebody)
//   L ∈ LitFIL  ::= #u | B | N | (sym Y)
//
// Multi-argument abstractions and applications are kernel forms (as in
// FLARE), but unlike FLARE, a FIL application carries an explicit `app`
// keyword. Multibinding `let` is a kernel form; it is a PARALLEL binding:
// the definition expressions are evaluated in the surrounding environment
// (left to right — a definition cannot refer to a let-bound name), and the
// body sees all of the bindings.
//
// Unlike FLARE, FIL has no letrec and no set! (the "knot-tying" of recursion
// is done by storing closures in mutable products); no cells and no pairs
// (both are represented as mutable products); no globally bound standard
// identifiers (all valid FIL programs are closed). And unlike FLARE, FIL
// has no formal type system — the reference semantics of this module is a
// big-step evaluator (see eval.scala).
//
// The new AST nodes are:
//   FilPrim   (prim O E*)  — the FIL primop set: FLARE's arithmetic,
//                            relational, logical, and list primops plus the
//                            mutable-product operators mprod, (mget J),
//                            (mset! J), mprod=?; the index J of the last two
//                            is part of the operator name (a positive
//                            integer literal, enforced by the parser);
//   FilApp    (app E E*)   — the explicit-keyword application;
//   LetStar   (let* ... E) — syntactic sugar: a sequence of nested
//                            single-binding lets (Figure 17.14).
// All other kernel forms reuse the DSL.fl nodes: the literals, Var,
// ErrorExpr, If, Abs, and Let.
//
// There is a single program tag: (fil (Iformal*) Ebody) — kernel and sugar
// forms are both admitted in the body; desugaring and the Figure 17.15
// simplifications are performed when FIL ASTs are constructed, i.e. by the
// parser and by Translate (both route their output through Desugar).

// ---------------------------------------------------------------------------
// FIL expression nodes (new to this module)
// ---------------------------------------------------------------------------

// (prim O E*) — a primitive application. O is a base primop name ("+",
// "cons", "mprod", ...) or an indexed operator name ("mget 1", "mset! 2") —
// the operator includes the index J of the component slot manipulated, which
// is why the book writes (prim (mget Jindex) Emp) rather than (prim mget
// Eindex Emp) (page 1031).
case class FilPrim(op: String, args: List[Exp]) extends INode with Exp {
    label = "FilPrim"
    children = SymbolicToken(op) :: args
}

// (app Erator Erand*) — an application with the explicit app keyword (the
// only application form in FIL; Erand* may be empty).
case class FilApp(rator: Exp, rands: List[Exp]) extends INode with Exp {
    label = "FilApp"
    children = rator :: rands
}

// (let* ((I E)*) E) — a sequence of nested single-binding lets (sugar,
// Figure 17.14).
case class LetStar(binds: List[(String, Exp)], body: Exp) extends INode with Exp {
    label = "LetStar"
    children = binds.map { case (n, e) => INode(List(SymbolicToken(n), e)) } :+ body
}

// ---------------------------------------------------------------------------
// Identifiers (Figure 17.14):
//   KeywordFIL = {abs, app, error, fil, if, let, let*, prim, sym}
//   I ∈ IdentFIL = SymLit − ({Y | Y begins with @} ∪ KeywordFIL)
// ---------------------------------------------------------------------------

object FilIdent {
    val keywords: Set[String] =
        Set("abs", "app", "error", "fil", "if", "let", "let*", "prim", "sym")

    def valid(name: String): Boolean =
        name.nonEmpty && !name.startsWith("@") && !keywords.contains(name)
}

// ---------------------------------------------------------------------------
// Primitive operators (Figure 17.14: "other primitives will be added as
// needed")
// ---------------------------------------------------------------------------

object FilPrimop {
    // The base operators: arithmetic, relational, logical, and list
    // primops (FLARE's set, minus the cell/pair operators, which FIL
    // represents as mutable products) plus the mutable-product operators
    // mprod and mprod=?.
    val baseOps: Set[String] = Set(
        "+", "-", "*", "/", "%",
        "=", "!=", "<", "<=", ">", ">=", "bool=?", "sym=?",
        "not", "and", "or",
        "cons", "car", "cdr", "null", "null?",
        "mprod", "mprod=?"
    )

    // A valid FIL primop name: a base operator, or the indexed operators
    // "mget J" / "mset! J" with J a positive integer literal.
    def valid(name: String): Boolean = name match {
        case n if baseOps.contains(n) => true
        case s if s.startsWith("mget ")  => isPosLit(s.drop("mget ".length))
        case s if s.startsWith("mset! ") => isPosLit(s.drop("mset! ".length))
        case _ => false
    }

    // J ∈ PosLit = {1, 2, 3, ...}
    def isPosLit(s: String): Boolean =
        s.nonEmpty && s.forall(_.isDigit) && s.toIntOption.exists(_ >= 1)
}
