package DSL.flavar

import DSL.fl._
import DSL.sexp._

// AST of FLAVAR ("FL And mutable VARiables"), Chapter 8 of the book.
//
// FLAVAR is a dialect of FLIC in which *every variable* is a mutable location,
// in addition to (orthogonal) mutable cells. It is built in two stages:
//
//   FLAVARK — the kernel: FLICK plus
//     (set! I E)          [Assignment]
//
//   FLAVAR — the kernel plus all of FL's sugar (as in FLIC, Figure 8.9).
//
// All FLK / FL / FLIC nodes (literals, Var, If, PrimOp, Lam, App, Pair, Rec,
// the FL sugar, and FLIC's cell/begin constructs) are reused from DSL.fl and
// DSL.flic; only the mutable-variable construct (set!) lives here.
//
// Semantically, a variable is an L-value (a location) that can be read (as a
// Var expression) or written (as the target of set!). Cells remain first-class
// values that can be written with :=; set! targets a named variable, not an
// arbitrary expression.

// (set! I E) — assign the value of E to the variable I; yields unit.
// I must be a variable bound in the current scope (an L-value); E is the
// value to store (an R-value).
case class SetBang(name: String, e: Exp) extends INode with Exp {
    label = "Assignment"
    children = List(SymbolicToken(name), e)
}

extension (c: FL)
    def show(): Unit = {
        val printTree = new PrintFLAVAR()
        c.accept(printTree)
    }
