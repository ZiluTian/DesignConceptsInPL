package DSL.flare

import DSL.fl._
import DSL.sexp._

// AST of the full FLARE language (Chapter 13 of the book).
//
// Full FLARE (Figure 13.23) extends μFLARE with immutable pairs,
// homogeneous immutable lists, and mutable cells. Its kernel grammar is the
// μFLARE kernel (Figure 13.1):
//
//   P ∈ Prog ::= (flarek (Iformal*) Ebody)
//   E ∈ Exp  ::= L | I | (error Y) | (if E E E)
//               | (prim O E*) | (abs (I*) E) | (E0 E1 ... En)
//               | (let ((I E)*) E) | (letrec ((I E)*) E)
//
// Multi-parameter abstractions and multi-argument applications are KERNEL
// forms in FLARE (unlike FL, where they are sugar), so the shared DSL.fl
// nodes Abs / MultiApp are used directly for them, and DSL.fl's single-
//parameter Lam / App are never produced by the FLARE parser. All the other
// kernel and sugar forms reuse DSL.fl's nodes; the only new nodes are
// FlarePrim (the (prim O E*) kernel form over FLARE's extended primop set)
// and BeginExp (the begin sugar).
//
// Programs:
//   (flarek (I*) Ebody)                 — kernel program
//   (flare (I*) Ebody (def I E)*)       — sugar program; procedure defs are
//                                          assumed already desugared to value
//                                          defs by the def desugaring rule
//                                          inherited from FL (page 233)

// ---------------------------------------------------------------------------
// FLARE expression nodes (new to this module)
// ---------------------------------------------------------------------------

// (prim O E*) — a primitive application. O is a FLARE primop name
// (validated by the parser against TEPrim.primops).
case class FlarePrim(op: String, args: List[Exp]) extends INode with Exp {
    label = "Prim"
    children = SymbolicToken(op) :: args
}

// (begin E1 E2) — sequencing sugar (Figure 13.23); desugars to
// (let ((_ E1)) E2), where _ is a fresh, unreferenced identifier.
case class BeginExp(e1: Exp, e2: Exp) extends INode with Exp {
    label = "Begin"
    children = List(e1, e2)
}

// ---------------------------------------------------------------------------
// FLARE programs
// ---------------------------------------------------------------------------

sealed trait FlarePgm extends FL

// (flarek (I*) Ebody)
case class FlareKernelProgram(formals: List[String], body: Exp) extends INode with FlarePgm {
    label = "FlareProgram"
    children = INode(formals.map(s => SymbolicToken(s))) :: List(body)
}

// (flare (I*) Ebody (def I E)*) — defs are value definitions (the def
// desugaring rule has already been applied by the parser)
case class FlareSugarProgram(formals: List[String], body: Exp,
                             defs: List[(String, Exp)]) extends INode with FlarePgm {
    label = "FlareSugarProgram"
    children = INode(formals.map(s => SymbolicToken(s))) :: List(body)
}

// ---------------------------------------------------------------------------
// Identifiers (Figures 13.1 / 13.23):
//   I ∈ Ident = SymLit − ({Y | Y begins with @} ∪ Keyword ∪ SugarKeyword)
//   Keyword      = {abs, error, flarek, if, let, letrec, prim, sym}
//   SugarKeyword = {cond, def, flare, recur, scand, scor, begin, list}
// ---------------------------------------------------------------------------

object FlareIdent {
    val keywords: Set[String] =
        Set("abs", "error", "flarek", "if", "let", "letrec", "prim", "sym")
    val sugarKeywords: Set[String] =
        Set("cond", "def", "flare", "recur", "scand", "scor", "begin", "list")
    val tags: Set[String] = Set("flare", "flarek")

    def valid(name: String): Boolean =
        name.nonEmpty &&
            !name.startsWith("@") &&
            !keywords.contains(name) &&
            !sugarKeywords.contains(name) &&
            !tags.contains(name)
}
