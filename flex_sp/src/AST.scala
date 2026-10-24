package DSL.flex_sp

import DSL.fl._
import DSL.sexp._
import DSL.flex._

// AST additions of FLEX/SP (Chapter 12.2 of the book): FLEX/S extended with
// universal (parametric) polymorphism. The two new expression forms:
//
//   (pabs (τ*) E)     — a polymorphic abstraction over the type
//                       identifiers τ* (Figure 12.9: [∀-intro]);
//   (pcall E T*)      — a polymorphic projection of the polymorphic value
//                       denoted by E onto the types T* (Figure 12.9:
//                       [∀-elim]).
//
// The polymorphic type form (forall (τ*) T) is represented by the TForall
// node of DSL.flex.Type (the type domain is shared with FLEX and FLEX/S).
// All other expression and type nodes are reused from DSL.flex (which
// extends the unsealed fl.Exp, so these nodes can inherit fl.Exp too).

// (pabs (τ1 ... τn) E) — creates a first-class polymorphic value
// parameterized over the type identifiers τ1 ... τn.
case class PabsExp(vars: List[String], e: Exp) extends INode with Exp {
    label = "Pabs"
    children = List(INode(vars.map(v => SymbolicToken(v)))) :+ e
}

// (pcall E T1 ... Tn) — projects the polymorphic value denoted by E onto
// the types T1 ... Tn, instantiating E's forall-bound type identifiers.
case class PcallExp(e: Exp, types: List[T]) extends INode with Exp {
    label = "Pcall"
    children = List(e) :+ INode(types.map(t => SymbolicToken("::" + T.show(t))))
}
