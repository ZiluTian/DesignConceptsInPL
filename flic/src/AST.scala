package DSL.flic

import DSL.fl._
import DSL.sexp._

// AST of FLIC ("FL Including mutable Cells"), Chapter 8 of the book.
//
// FLIC is built in two stages:
//
//   FLICK (Figure 8.8) — the kernel: FLK plus
//     (cell E)            [CellCreation]
//     (begin E1 E2)       [SimpleSequencing]
//     and the primops  ^  :=  cell=?  cell?
//
//   FLIC (Figure 8.9) — the kernel plus FL's sugar, plus new sugar:
//     (begin E*)          [ExtendedSequencing]
//     (if Etest Ethen)    [ElselessIf]
//     (while Etest Ebody) [WhileLoop]
//
// All FLK/FL nodes (literals, Var, If, PrimOp, Lam, App, Pair, Rec, and the
// FL sugar constructs) are reused from DSL.fl; only the stateful constructs
// live here.

// ---------------------------------------------------------------------------
// FLICK kernel (Figure 8.8)
// ---------------------------------------------------------------------------

// (cell E) — allocate a new mutable cell whose initial content is the value of E
case class CellExp(content: Exp) extends INode with Exp {
    label = "CellCreation"
    children = List(content)
}

// (begin E1 E2) — evaluate E1, discard its value, then evaluate E2
case class BeginExp(sequent1: Exp, sequent2: Exp) extends INode with Exp {
    label = "SimpleSequencing"
    children = List(sequent1, sequent2)
}

// The four FLICK primops (Figure 8.8). They are written with the @-sugar in
// concrete syntax (@^, @:=, @cell=?, @cell?) and desugared to these kernel
// nodes by DSL.flic.Desugar.
case class CellFetchExp(e: Exp) extends INode with Exp {
    label = "CellFetch"          // (^ E)
    children = List(e)
}
case class CellStoreExp(cell: Exp, value: Exp) extends INode with Exp {
    label = "CellStore"          // (:= Ecell Evalue)  -> unit
    children = List(cell, value)
}
case class CellEqExp(e1: Exp, e2: Exp) extends INode with Exp {
    label = "CellEq"             // (cell=? E1 E2)
    children = List(e1, e2)
}
case class CellPredExp(e: Exp) extends INode with Exp {
    label = "CellPred"           // (cell? E)
    children = List(e)
}

// ---------------------------------------------------------------------------
// FLIC sugar (Figure 8.9)
// ---------------------------------------------------------------------------

// (begin E*) — extended sequencing (the kernel begin has exactly two sequents)
case class BeginListExp(sequents: List[Exp]) extends INode with Exp {
    label = "ExtendedSequencing"
    children = sequents
}

// (if Etest Ethen) — an if without an else (the else is #u)
case class ElselessIfExp(test: Exp, thenExp: Exp) extends INode with Exp {
    label = "ElselessIf"
    children = List(test, thenExp)
}

// (while Etest Ebody) — loop while the test is true
case class WhileExp(test: Exp, body: Exp) extends INode with Exp {
    label = "WhileLoop"
    children = List(test, body)
}

extension (c: FL)
    def show(): Unit = {
        val printTree = new PrintFLIC()
        c.accept(printTree)
    }
