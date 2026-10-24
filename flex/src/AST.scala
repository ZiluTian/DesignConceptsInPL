package DSL.flex

import DSL.fl._
import DSL.sexp._

// AST of FLEX (Figures 11.1 and 11.31 of the book): the s-expression kernel
// of full FLEX, extended with the syntactic sugar of muFLEX (Figure 11.2)
// plus the begin sugar (Figure 11.21) and the list sugar (Figure 11.24).
//
// FLEX is FL with explicit types. Its reference semantics is the type
// checker (TypeChecker / ProgramChecker in check.scala); the sugar nodes
// below are removed by Desugar before checking.
//
// Reused from DSL.fl: the leaves (UnitLit, BoolLit, IntLit, Sym, Var), If,
// Let, Pair, PrimOp, and the sugar nodes Cond, Scand, Scor,
// SugaredPrimOp. All other expression nodes are defined here and extend
// fl.Exp (which is unsealed so that dialects can extend it).

sealed trait FlexPgm extends FL

// (error Ymessage Ttype) — an error that asserts its (annotated) type
case class FlexError(msg: String, t: T) extends INode with Exp {
    label = "Error"
    children = List(SymbolicToken(msg), SymbolicToken("::" + T.show(t)))
}

// (abs ((Iformal Tformal)*) Ebody) — an abstraction with explicitly typed
// formal parameters (the return type is inferred, not annotated)
case class AbsExp(params: List[(String, T)], body: Exp) extends INode with Exp {
    label = "Abs"
    children = params.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } :+ body
}

// (Erator Earg*) — an N-ary application. Unlike FL (where application is
// binary and multi-parameter procedures are curried), FLEX treats
// multi-argument application as a kernel form, because currying would not
// preserve expression types (book p.634).
case class AppExp(rator: Exp, args: List[Exp]) extends INode with Exp {
    label = "App"
    children = rator :: args
}

// (letrec ((I T E)*) Ebody) — a recursive binding with an explicit declared
// type (required for recursive procedures, book p.636)
case class LetRecExp(bindings: List[(String, T, Exp)], body: Exp) extends INode with Exp {
    label = "LetRec"
    children = bindings.map { case (n, t, e) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)), e)) } :+ body
}

// (the T E) — a type ascription: E must have type T (verified by the checker)
case class TheExp(t: T, e: Exp) extends INode with Exp {
    label = "The"
    children = List(SymbolicToken("::" + T.show(t)), e)
}

// Pairs (Figure 11.15). fst / snd are not primops in FLEX (the monomorphic
// type system cannot give them a single entry in TEprim).
case class FstExp(e: Exp) extends INode with Exp {
    label = "Fst"; children = List(e)
}
case class SndExp(e: Exp) extends INode with Exp {
    label = "Snd"; children = List(e)
}

// Tuples (Figure 11.16): positional products; get requires an explicit
// integer-literal index.
case class ProdExp(comps: List[Exp]) extends INode with Exp {
    label = "Prod"; children = comps
}
case class GetExp(index: Int, e: Exp) extends INode with Exp {
    label = "Get"
    children = List(SymbolicToken(index.toString), e)
}

// Sequences (Figure 11.17): homogeneous products with computable indices.
case class SeqExp(comps: List[Exp]) extends INode with Exp {
    label = "Seq"; children = comps
}
case class SeqGetExp(index: Exp, seq: Exp) extends INode with Exp {
    label = "SeqGet"; children = List(index, seq)
}
case class SeqSizeExp(e: Exp) extends INode with Exp {
    label = "SeqSize"; children = List(e)
}

// Records (Figure 11.18): named products. `with` evaluates the body in an
// environment extended with the record's fields.
case class RecordExp(fields: List[(String, Exp)]) extends INode with Exp {
    label = "Record"
    children = fields.map { case (n, e) => INode(List(SymbolicToken(n), e)) }
}
case class SelectExp(name: String, e: Exp) extends INode with Exp {
    label = "Select"
    children = List(SymbolicToken(name), e)
}
case class WithExp(rcd: Exp, body: Exp) extends INode with Exp {
    label = "With"
    children = List(rcd, body)
}

// Oneofs (Figure 11.22): named sums. `one` names the oneof type and the tag
// explicitly (needed to preserve monomorphism); `tagcase` clauses must
// follow the oneof type's tag order (with an optional else clause covering
// the remaining tags).
case class OneExp(oneofType: T, tag: String, payload: Exp) extends INode with Exp {
    label = "One"
    children = List(SymbolicToken("::" + T.show(oneofType)), SymbolicToken(tag), payload)
}
case class TagCaseExp(disc: Exp, payloadName: String,
                      clauses: List[(String, Exp)], elseExp: Option[Exp]) extends INode with Exp {
    label = "TagCase"
    children = List(disc, SymbolicToken(payloadName)) ++
        clauses.map { case (n, e) => INode(List(SymbolicToken(n), e)) } ++
        elseExp.map(e => INode(List(SymbolicToken("else"), e)))
}

// Lists (Figure 11.24): homogeneous lists; `null` names the element type of
// the empty list explicitly.
case class ConsExp(head: Exp, tail: Exp) extends INode with Exp {
    label = "Cons"; children = List(head, tail)
}
case class CarExp(e: Exp) extends INode with Exp {
    label = "Car"; children = List(e)
}
case class CdrExp(e: Exp) extends INode with Exp {
    label = "Cdr"; children = List(e)
}
case class NullExp(t: T) extends INode with Exp {
    label = "Null"
    children = List(SymbolicToken("::" + T.show(t)))
}
case class NullQExp(e: Exp) extends INode with Exp {
    label = "NullQ"; children = List(e)
}

// Mutable data (Figure 11.21): mutable variables (set!) and cells.
case class SetExp(name: String, e: Exp) extends INode with Exp {
    label = "Set"
    children = List(SymbolicToken(name), e)
}
case class CellExp(e: Exp) extends INode with Exp {
    label = "Cell"; children = List(e)
}
case class DerefExp(e: Exp) extends INode with Exp {
    label = "Deref"; children = List(e)
}
case class CellSetExp(cell: Exp, e: Exp) extends INode with Exp {
    label = "CellSet"; children = List(cell, e)
}
case class CellEqExp(e1: Exp, e2: Exp) extends INode with Exp {
    label = "CellEq"; children = List(e1, e2)
}

// ---------------------------------------------------------------------------
// Sugar nodes (removed by Desugar)
// ---------------------------------------------------------------------------

// (begin E1 E2) — Figure 11.21 presents begin as sugar; it desugars to a let
// over a fresh variable (the type of the let binding is inferred from E1).
case class BeginExp(e1: Exp, e2: Exp) extends INode with Exp {
    label = "Begin"; children = List(e1, e2)
}

// (list T E*) — Figure 11.24: the element type is explicit.
case class ListExp(t: T, elems: List[Exp]) extends INode with Exp {
    label = "List"
    children = SymbolicToken("::" + T.show(t)) :: elems
}

// (let-type ((tau T)*) Ebody) — simultaneous type substitution [Ti/tau]Ebody
case class LetTypeExp(binds: List[(String, T)], body: Exp) extends INode with Exp {
    label = "LetType"
    children = binds.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } :+ body
}
// (let-type* ((tau T)*) Ebody) — sequential (nested) type substitution
case class LetTypeStarExp(binds: List[(String, T)], body: Exp) extends INode with Exp {
    label = "LetTypeStar"
    children = binds.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } :+ body
}

// ---------------------------------------------------------------------------
// Programs (Figure 11.31 / Figure 11.2)
//
//   (flexk ((I T)*) Ebody)
//   (flex  ((I T)*) Ebody (def-type tau T)* (def I T E)*)
//
// A `flex` program desugars to a `flexk` program whose body is wrapped in
// the standard-library let, a let-type* over the def-types, and a letrec
// over the value definitions (Figure 11.2).
// ---------------------------------------------------------------------------

// A value definition (def I T E). The procedure-defining sugar
// (def (IprocName Treturn (I1 T1) ... (In Tn)) Ebody) — the formal pairs are
// direct elements of the head list — is converted to
// (def I (-> (T1 ... Tn) Treturn) (abs ((I1 T1) ... (In Tn)) Ebody)) at parse
// time.
case class FlexDef(name: String, t: T, e: Exp) extends INode with FL {
    label = "Def"
    children = List(SymbolicToken(name), SymbolicToken("::" + T.show(t)), e)
}

case class FlexKernelProgram(formals: List[(String, T)], body: Exp) extends INode with FlexPgm {
    label = "FlexKProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } :+ body
}

case class FlexSugarProgram(formals: List[(String, T)], body: Exp,
                            typeDefs: List[(String, T)], defs: List[FlexDef]) extends INode with FlexPgm {
    label = "FlexProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + T.show(t)))) } ++
        typeDefs.map { case (n, t) => INode(List(SymbolicToken("def-type " + n), SymbolicToken("::" + T.show(t)))) } ++
        defs :+ body
}

extension (c: FlexPgm)
    def show(): Unit = {
        val printTree = new PrintFlex()
        c.accept(printTree)
    }
