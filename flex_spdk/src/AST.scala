package DSL.flex_spdk

import DSL.fl._
import DSL.flex._
import DSL.sexp._

// AST additions for FLEX/SPDK (Section 12.3.2 of the book, Figure 12.21).
//
// FLEX/SPDK is FLEX/SPD with explicit kinds: a kind annotation is required on
// every description identifier declared in pabs, forall, and dabs
//
//   (pabs ((δ K)*) E)       (forall ((δ K)*) D)       (dabs ((δ K)*) D)
//
// The kinds of the binders of dletrec / plet / pletrec are not spelled:
// dletrec-bound identifiers are required to be of kind type (footnote 10 of
// the book), and plet / pletrec names are description aliases whose kind is
// the kind of their definition.
//
// The kind domain (K ::= type | (->> (K*) K)) and the kind-annotated
// description forms (TForallK / TDabsK) live in DSL.flex (shared with the
// family). The kind-annotated polymorphic abstraction gets its own
// expression node, PabsExpK (the unkinded PabsExp of DSL.flex_sp is not part
// of the FLEX/SPDK kernel).

// (pabs (δ1 K1 ... δn Kn) E) — a polymorphic abstraction whose bound
// description identifiers carry kind annotations (Figure 12.21; [∀-intro] of
// Figure 12.23). The binder list is a flat alternating name / kind sequence.
case class PabsExpK(binds: List[(String, Kind)], e: Exp) extends INode with Exp {
    label = "PabsK"
    children =
        List(INode(binds.map { case (n, k) => SymbolicToken(n + " " + Kind.show(k)) })) :+ e
}

// ---------------------------------------------------------------------------
// Programs (Figure 12.21 / Figure 12.19 of the book): the FLEX/SPD program
// forms in the kind-annotated syntax.
//
//   (flexk/SPDK ((I D)*) Ebody)
//   (flex/SPDK  ((I D)*) Ebody (def-desc δ D)* (def I D E)*)
//
// A flex/SPDK program desugars (Figure 12.19) to a flexk/SPDK program whose
// body is wrapped in: a pletrec binding the standard-library DESCRIPTIONS
// (pairof, listof), a let binding the standard-library VALUES (the list /
// pair procedures and the primops), a pletrec binding the program's def-desc
// descriptions, and a letrec binding the program's value definitions.
// ---------------------------------------------------------------------------

sealed trait FlexSPDKPgm extends FL

case class FlexSPDKKernel(formals: List[(String, T)], body: Exp) extends INode with FlexSPDKPgm {
    label = "FlexKSPDKProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } :+ body
}

case class FlexSPDKSugar(formals: List[(String, T)], body: Exp,
                         descDefs: List[(String, T)], defs: List[FlexDef]) extends INode with FlexSPDKPgm {
    label = "FlexSPDKProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } ++
        descDefs.map { case (n, d) => INode(List(SymbolicToken("def-desc " + n), SymbolicToken("::" + T.show(d)))) } ++
        defs :+ body
}
