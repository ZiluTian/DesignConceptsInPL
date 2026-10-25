package DSL.flare_v

import DSL.fl._
import DSL.sexp._

// AST of FLARE/V (Section 17.2.2 of the book): the full FLARE language (the
// AST, parser, and type domain of DSL.flare) extended with **mutable
// variables** via the `set!` construct (from FLAVAR, Section 8.4).
//
// The *expressions* of FLARE/V are the FLARE expressions plus one new kernel
// form:
//
//   (set! Ivar Eval)   — assign a new value to an in-scope variable Ivar.
//
// The book reuses the FLARE program tags (`flare` / `flarek`) for FLARE/V
// (footnote 1, p.1009), so the program node types are the same as FLARE's and
// are reused from DSL.flare. The only *new* AST node is SetBang (the set!
// kernel form). Every other FLARE node (FlarePrim, BeginExp, and the reused
// DSL.fl nodes Abs / MultiApp / Let / LetRec / ...) is unchanged.
//
// A FLARE/V program is a DSL.flare.FlareKernelProgram or
// DSL.flare.FlareSugarProgram whose body (and defs) may contain SetBang nodes.

// ---------------------------------------------------------------------------
// The mutable-variable assignment (set! I E), a FLARE/V kernel form
// (Figure 17.2)
// ---------------------------------------------------------------------------

// (set! I E) — assign E's value to the in-scope variable I. I must already be
// bound (a formal, a let/letrec binding, or a global procedure name); set!
// changes the *value* of an existing variable, it does not create one. The
// result of the assignment is unit (as in FLAVAR / FLICK).
case class SetBang(name: String, e: Exp) extends INode with Exp {
    label = "Assignment"
    children = SymbolicToken(name) :: List(e)
}

// ---------------------------------------------------------------------------
// Identifiers (Figures 17.2 / 17.3): same as FLARE's, plus the set! keyword.
//   I ∈ Ident = SymLit − ({Y | Y begins with @} ∪ Keyword ∪ SugarKeyword)
//   Keyword      = {abs, error, flarek, if, let, letrec, prim, set!, sym}
//   SugarKeyword = {begin, cond, def, flare, list, recur, scand, scor}
// ---------------------------------------------------------------------------

object FlareVIdent {
    // FLARE's keywords plus set! (the mutable-variable assignment is a
    // keyword in FLARE/V's kernel grammar, Figure 17.2).
    val keywords: Set[String] =
        DSL.flare.FlareIdent.keywords + "set!"
    val sugarKeywords: Set[String] = DSL.flare.FlareIdent.sugarKeywords
    val tags: Set[String] = DSL.flare.FlareIdent.tags

    def valid(name: String): Boolean =
        name.nonEmpty &&
            !name.startsWith("@") &&
            !keywords.contains(name) &&
            !sugarKeywords.contains(name) &&
            !tags.contains(name)
}
