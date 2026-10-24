package DSL.flex_spd

import DSL.fl._
import DSL.flex._
import DSL.sexp._

// AST additions for FLEX/SPD (Section 12.3.1 of the book).
//
// FLEX/SPD generalizes the type domain to *descriptions* (the description
// forms TBaseCtor / TDabs / TDApp / TDletrec live in DSL.flex.T) and adds two
// expression-sugar forms that name descriptions within expressions:
//
//   (plet    ((δ D)*) Ebody)   — bind descriptions, return a value
//   (pletrec ((δ D)*) Ebody)   — bind (mutually recursive) descriptions,
//                                 return a value
//
// Both desugar to description substitution into the body's type positions
// (Figure 12.18); the FLEX/SPD checker realizes them by extending the
// description environment with the bindings and checking the body (the
// bindings are transparent: a name is equivalent to its definition).
//
// The list / pair *expression* forms of FLEX (cons, car, cdr, null, null?,
// pair, fst, snd) are NOT part of the FLEX/SPD kernel: they are standard-
// library values (polymorphic procedures) bound by the program desugaring
// (Figure 12.19). The parser therefore treats those keywords as bare value
// identifiers, and the checker provides them in the standard-library value
// environment.

// (plet ((δ D)*) Ebody) — bind descriptions δ to D, transparently, in the
// body's type positions; the body is an expression (Figure 12.18).
case class PletExp(binds: List[(String, T)], body: Exp) extends INode with Exp {
    label = "Plet"
    children = binds.map { case (n, d) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(d)))) } :+ body
}

// (pletrec ((δ D)*) Ebody) — as plet, but the descriptions are mutually
// recursive (their scope includes all the other definitions) (Figure 12.18).
case class PletRecExp(binds: List[(String, T)], body: Exp) extends INode with Exp {
    label = "PletRec"
    children = binds.map { case (n, d) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(d)))) } :+ body
}

// ---------------------------------------------------------------------------
// Programs (Figure 12.18 / Figure 12.19 of the book)
//
//   (flexk/SPD ((I D)*) Ebody)
//   (flex/SPD  ((I D)*) Ebody (def-desc δ D)* (def I D E)*)
//
// A flex/SPD program desugars (Figure 12.19) to a flexk/SPD program whose
// body is wrapped in: a pletrec binding the standard-library DESCRIPTIONS
// (pairof, listof), a let binding the standard-library VALUES (the list /
// pair procedures and the primops), a pletrec binding the program's def-desc
// descriptions, and a letrec binding the program's value definitions.
// ---------------------------------------------------------------------------

sealed trait FlexSPDPgm extends FL

case class FlexSPDKernel(formals: List[(String, T)], body: Exp) extends INode with FlexSPDPgm {
    label = "FlexSPDKProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } :+ body
}

case class FlexSPDSugar(formals: List[(String, T)], body: Exp,
                        descDefs: List[(String, T)], defs: List[FlexDef]) extends INode with FlexSPDPgm {
    label = "FlexSPDProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } ++
        descDefs.map { case (n, d) => INode(List(SymbolicToken("def-desc " + n), SymbolicToken("::" + T.show(d)))) } ++
        defs :+ body
}
