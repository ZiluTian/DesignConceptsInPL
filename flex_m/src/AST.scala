package DSL.flex_m

import DSL.fl._
import DSL.sexp._
import DSL.flex._

// AST of FLEX/M (Chapter 15.2, Figures 15.1 and 15.2 of the book).
//
// FLEX/M is FLEX/SP with a first-class module system and static dependent
// types. The expression nodes that carry a type position (abs, the, one,
// pcall, error, letrec, let-type) are given M-variants that hold the FLEX/M
// type domain (MT, defined in Type.scala) instead of the FLEX type domain
// (T). All type-free nodes are reused from DSL.flex (prod, get, seq, record,
// select, with, tagcase, set!, cell, ...) and DSL.fl (the leaves, if, prim,
// let, and the sugar cond / scand / scor / sugared-primop / begin).
//
// FLEX/M has NO pair / list / recursive-type kernel constructs: pair, fst,
// snd, cons, car, cdr, null, null? are ordinary *value* names (procedures
// that clients obtain from modules such as ElistModule), and all recursive
// types are abstracted inside modules via def-datatype. So there is no
// pairof / listof / trec / tletrec type syntax either.
//
// New FLEX/M kernel forms (Figure 15.1):
//
//   (module DD* VD*)        — a module expression (MModule);
//   (open Emod Ebody)       — a module open (MOpen);
//   (load Y T)              — loading a compiled module (MLoad);
//   (match Edisc (PT E)*)   — pattern matching (MMatch, with Mpat patterns).
//
// New FLEX/M sugar (Figure 15.2):
//
//   (letrec ((I T E)*) Ebody)  — typed recursive binding (MLetRec),
//                                desugars to (open (module (def I T E)*) Ebody);
//   (mselect I Emod)           — module selection (MMselect), desugars to
//                                (open Emod I);
//   (let-type ...), (let-type* ...) — type substitution (MLetType /
//   MLetTypeStar); the sugar arrow (-> (T*) T0).
//
// The program forms (Figure 15.2):
//
//   (flex/Mk ((I T)*) Ebody)                        — kernel program;
//   (flex/M  ((I T)*) Ebody (def-type τ T)* DD* VD*) — sugar program, where
//   DD = (def-datatype (θ τ*) (ctor T*)*) and VD = (def I T E).

// ---------------------------------------------------------------------------
// Kernel expression nodes that carry a type position (M-variants)
// ---------------------------------------------------------------------------

// (error Ymessage T) — an error that asserts its (annotated) type.
case class MError(msg: String, t: MT) extends INode with Exp {
    label = "Error"; children = List(SymbolicToken(msg), SymbolicToken("::" + MT.show(t)))
}

// (abs ((I T)*) Ebody) — an abstraction with explicitly typed formal
// parameters. The parameter names are value names that may occur (inside
// dselects) in the later parameter types and the result type.
case class MAbs(params: List[(String, MT)], body: Exp) extends INode with Exp {
    label = "Abs"
    children = params.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + MT.show(t)))) } :+ body
}

// (Erator Earg*) — an N-ary application. In FLEX/M an application of a
// polymorphic (forall-typed) rator performs the implicit projection
// (Figure 15.18) unless written explicitly as (pcall E T*).
case class MApp(rator: Exp, args: List[Exp]) extends INode with Exp {
    label = "App"; children = rator :: args
}

// (the T E) — a type ascription: E must have a type that is a subtype of T
// (the [the-inclusion] rule; FLEX/M has no implicit inclusion, so `the` is
// the only way to up-cast).
case class MThe(t: MT, e: Exp) extends INode with Exp {
    label = "The"; children = List(SymbolicToken("::" + MT.show(t)), e)
}

// (one T tag E) — a oneof value: T names the oneof type explicitly and tag
// names the payload tag (needed to preserve monomorphism).
case class MOne(oneofType: MT, tag: String, payload: Exp) extends INode with Exp {
    label = "One"
    children = List(SymbolicToken("::" + MT.show(oneofType)), SymbolicToken(tag), payload)
}

// (pabs (τ*) E) — a polymorphic abstraction over the type identifiers τ*
// (inherited from FLEX/SP, Figure 12.9).
case class MPabs(vars: List[String], e: Exp) extends INode with Exp {
    label = "Pabs"; children = List(INode(vars.map(v => SymbolicToken(v)))) :+ e
}

// (pcall E T*) — an explicit polymorphic projection of the polymorphic
// value denoted by E onto the types T* (inherited from FLEX/SP).
case class MPcall(e: Exp, types: List[MT]) extends INode with Exp {
    label = "Pcall"
    children = List(e) :+ INode(types.map(t => SymbolicToken("::" + MT.show(t))))
}

// ---------------------------------------------------------------------------
// Module constructs (Figure 15.1)
// ---------------------------------------------------------------------------

// A data-type declaration (def-datatype (θ τ*) (ctor Tcomp*)*). The θ is the
// abstract type-constructor name, τ* are dummy parameter names (their count
// is the arity; they have no binding power), and each ctor is a name with a
// list of component types.
case class MDtDef(name: String, params: List[String],
                  ctors: List[(String, List[MT])]) extends INode {
    label = "DefDatatype"
    children = INode(SymbolicToken(name) :: params.map(SymbolicToken(_))) ::
        ctors.map { case (c, ts) =>
            INode(List(SymbolicToken(c), INode(ts.map(t => SymbolicToken("::" + MT.show(t))))))
        }
}

// A value definition (def I T E) inside a module or program.
case class MValDef(name: String, t: MT, e: Exp) extends INode {
    label = "Def"
    children = List(SymbolicToken(name), SymbolicToken("::" + MT.show(t)), e)
}

// (module DD* VD*) — a module expression: abstract type components (DDs)
// plus value components (VDs). The VDs are mutually recursive: every value
// name (the def names and the ctor / dctor names introduced by the DDs) is
// in scope in every VD expression. There is no separate body.
case class MModule(dts: List[MDtDef], vds: List[MValDef]) extends INode with Exp {
    label = "Module"
    children = dts ++ vds
}

// (open Emod Ebody) — a module open: Ebody is checked in an environment
// extended with the value components of the module denoted by Emod (the
// [moduleof-elim] rule).
case class MOpen(emod: Exp, body: Exp) extends INode with Exp {
    label = "Open"; children = List(emod, body)
}

// (load Y T) — loading a compiled module from file Y, which is declared to
// have module type T (the [loadLTstat] rule; load is pure).
case class MLoad(file: String, t: MT) extends INode with Exp {
    label = "Load"
    children = List(SymbolicToken(file), SymbolicToken("::" + MT.show(t)))
}

// A pattern (Figure 15.2): PT ::= _ | I | L | (I PT*)
sealed trait Mpat extends INode
case class MpatWild() extends Mpat { label = "Wild"; children = List(SymbolicToken("_")) }
case class MpatVar(name: String) extends Mpat { label = "PatVar"; children = List(SymbolicToken(name)) }
case class MpatLit(e: Exp) extends Mpat { label = "PatLit"; children = List(e) }
case class MpatCons(head: String, subpats: List[Mpat]) extends Mpat {
    label = "PatCons"
    children = SymbolicToken(head) :: subpats
}

// (match Edisc (PT E)*) — pattern matching over a sum-of-products
// discriminant (Section 15.4.6).
case class MMatch(disc: Exp, clauses: List[(Mpat, Exp)]) extends INode with Exp {
    label = "Match"
    children = disc :: clauses.flatMap { case (p, b) => List(p, b) }
}

// ---------------------------------------------------------------------------
// Sugar nodes (removed by Desugar)
// ---------------------------------------------------------------------------

// (letrec ((I T E)*) Ebody) — a typed recursive binding (Figure 15.2);
// desugars to (open (module (def I T E)*) Ebody).
case class MLetRec(bindings: List[(String, MT, Exp)], body: Exp) extends INode with Exp {
    label = "LetRec"
    children = bindings.map { case (n, t, e) => INode(List(SymbolicToken(n), SymbolicToken("::" + MT.show(t)), e)) } :+ body
}

// (mselect I Emod) — module selection (Figure 15.2); desugars to
// (open Emod I).
case class MMselect(name: String, emod: Exp) extends INode with Exp {
    label = "Mselect"; children = List(SymbolicToken(name), emod)
}

// (let-type ((τ T)*) Ebody) — simultaneous type substitution [Ti/τi]Ebody.
case class MLetType(binds: List[(String, MT)], body: Exp) extends INode with Exp {
    label = "LetType"
    children = binds.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + MT.show(t)))) } :+ body
}

// (let-type* ((τ T)*) Ebody) — sequential (nested) type substitution.
case class MLetTypeStar(binds: List[(String, MT)], body: Exp) extends INode with Exp {
    label = "LetTypeStar"
    children = binds.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + MT.show(t)))) } :+ body
}

// ---------------------------------------------------------------------------
// Programs (Figure 15.2)
//
//   (flex/Mk ((I T)*) Ebody)
//   (flex/M  ((I T)*) Ebody (def-type τ T)* (def-datatype ...)* (def I T E)*)
//
// A flex/M program desugars to a flex/Mk program whose body is wrapped in a
// load of the standard library, a let-type* over the def-types, and an open
// of a module over the data-type and value definitions (Figure 15.2).
// ---------------------------------------------------------------------------

sealed trait FlexMPgm extends FL

case class FlexMKernelProgram(formals: List[(String, MT)], body: Exp) extends INode with FlexMPgm {
    label = "FlexMKernelProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + MT.show(t)))) } :+ body
}

case class FlexMSugarProgram(formals: List[(String, MT)], body: Exp,
                             typeDefs: List[(String, MT)],
                             dts: List[MDtDef], vds: List[MValDef]) extends INode with FlexMPgm {
    label = "FlexMProgram"
    children = formals.map { case (n, t) => INode(List(SymbolicToken(n), SymbolicToken("::" + MT.show(t)))) } ++
        typeDefs.map { case (n, t) => INode(List(SymbolicToken("def-type " + n), SymbolicToken("::" + MT.show(t)))) } ++
        dts ++ vds :+ body
}

// ---------------------------------------------------------------------------
// S-expression display of expressions
//
// Used to print the module expression (Emod) inside a dependent type
// constructor (dselect θ Emod) when displaying an MT (see MT.show). It
// renders the canonical s-expression form of any FLEX/M expression.
// ---------------------------------------------------------------------------

object FlexMExp {

    def show(e: Exp): String = e match {
        case UnitLit() => "#u"
        case BoolLit(b) => if (b) "#t" else "#f"
        case IntLit(n) => n.toString
        case Sym(s) => "(sym " + quote(s) + ")"
        case Var(n) => n
        case MError(msg, t) => "(error " + quote(msg) + " " + MT.show(t) + ")"
        case MAbs(params, body) =>
            "(abs (" + params.map { case (n, t) => n + " " + MT.show(t) }.mkString(" ") + ") " +
            show(body) + ")"
        case MApp(r, args) =>
            show(r) + " " + args.map(show).mkString(" ")
        case MThe(t, e2) => "(the " + MT.show(t) + " " + show(e2) + ")"
        case MOne(t, tag, p) => "(one " + MT.show(t) + " " + tag + " " + show(p) + ")"
        case MPabs(vars, e2) => "(pabs (" + vars.mkString(" ") + ") " + show(e2) + ")"
        case MPcall(e2, ts) => "(pcall " + show(e2) + " " + ts.map(MT.show).mkString(" ") + ")"
        case MModule(dts, vds) =>
            "(module " + dts.map(showDt).mkString(" ") + " " + vds.map(showVd).mkString(" ") + ")"
        case MOpen(emod, body) => "(open " + show(emod) + " " + show(body) + ")"
        case MLoad(file, t) => "(load " + file + " " + MT.show(t) + ")"
        case MMatch(disc, clauses) =>
            "(match " + show(disc) + " " +
            clauses.map { case (p, b) => showPat(p) + " " + show(b) }.mkString(" ") + ")"
        case MLetRec(bs, body) =>
            "(letrec (" + bs.map { case (n, t, e) => n + " " + MT.show(t) + " " + show(e) }.mkString(" ") + ") " +
            show(body) + ")"
        case MMselect(n, emod) => "(mselect " + n + " " + show(emod) + ")"
        case MLetType(bs, body) =>
            "(let-type (" + bs.map { case (n, t) => n + " " + MT.show(t) }.mkString(" ") + ") " + show(body) + ")"
        case MLetTypeStar(bs, body) =>
            "(let-type* (" + bs.map { case (n, t) => n + " " + MT.show(t) }.mkString(" ") + ") " + show(body) + ")"
        // Type-free nodes reused from DSL.flex / DSL.fl.
        case If(t1, t2, t3) => "(if " + show(t1) + " " + show(t2) + " " + show(t3) + ")"
        case PrimOp(op, args) => "(prim " + op.toString + " " + args.map(show).mkString(" ") + ")"
        case Let(bs, body) =>
            "(let (" + bs.map { case (n, e) => n + " " + show(e) }.mkString(" ") + ") " + show(body) + ")"
        case ProdExp(cs) => "(prod " + cs.map(show).mkString(" ") + ")"
        case GetExp(i, e2) => "(get " + i + " " + show(e2) + ")"
        case SeqExp(cs) => "(seq " + cs.map(show).mkString(" ") + ")"
        case SeqGetExp(i, s) => "(seq-get " + show(i) + " " + show(s) + ")"
        case SeqSizeExp(e2) => "(seq-size " + show(e2) + ")"
        case RecordExp(fs) =>
            "(record " + fs.map { case (n, e) => n + " " + show(e) }.mkString(" ") + ")"
        case SelectExp(n, e2) => "(select " + n + " " + show(e2) + ")"
        case WithExp(r, b) => "(with " + show(r) + " " + show(b) + ")"
        case TagCaseExp(d, pn, cs, el) =>
            "(tagcase " + show(d) + " " + pn + " (" +
            cs.map { case (n, e) => n + " " + show(e) }.mkString(" ") + ")" +
            (el.map(e => " (else " + show(e) + ")").getOrElse("")) + ")"
        case SetExp(n, e2) => "(set! " + n + " " + show(e2) + ")"
        case CellExp(e2) => "(cell " + show(e2) + ")"
        case DerefExp(e2) => "(^ " + show(e2) + ")"
        case CellSetExp(c, e2) => "(:= " + show(c) + " " + show(e2) + ")"
        case CellEqExp(e1, e2) => "(cell=? " + show(e1) + " " + show(e2) + ")"
        case BeginExp(e1, e2) => "(begin " + show(e1) + " " + show(e2) + ")"
        case SugaredPrimOp(op, args) =>
            "@" + op + " " + args.map(show).mkString(" ")
        case Cond(branches, d) =>
            "(cond (" + branches.map { case (t1, t2) => show(t1) + " " + show(t2) }.mkString(") (") + ")" +
            (d.map(e => " (else " + show(e) + ")").getOrElse("")) + ")"
        case Scand(es) => "(scand " + es.map(show).mkString(" ") + ")"
        case Scor(es) => "(scor " + es.map(show).mkString(" ") + ")"
        case _ => "?"
    }

    private def showDt(dt: MDtDef): String =
        "(def-datatype (" + dt.name + " " + dt.params.mkString(" ") + ") " +
        dt.ctors.map { case (c, ts) =>
            c + " (" + ts.map(MT.show).mkString(" ") + ")"
        }.mkString(" ") + ")"

    private def showVd(vd: MValDef): String =
        "(def " + vd.name + " " + MT.show(vd.t) + " " + show(vd.e) + ")"

    private def showPat(p: Mpat): String = p match {
        case MpatWild() => "_"
        case MpatVar(n) => n
        case MpatLit(e) => show(e)
        case MpatCons(h, subs) => "(" + h + " " + subs.map(showPat).mkString(" ") + ")"
    }

    // Quote a string literal for s-expression display.
    private def quote(s: String): String = "\"" + s + "\""
}
