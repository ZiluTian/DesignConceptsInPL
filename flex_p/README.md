# FLEX/P — FLEX with Universal Polymorphism (No Subtyping)

FLEX/P is the polymorphic FLEX variant defined in **footnote 4 of p.727** of
the book: *"FLEX/P is FLEX/SP without the [inclusion] type rule."* That is,
the type system of FLEX — **equirecursive type equivalence** (Figure 11.28)
— extended with the universal-polymorphism rules of Figure 12.9, with no
subtyping anywhere.

The book develops FLEX/P purely at the level of the type system and defines
**no `flex/P` program tag**: FLEX/P programs are written in the same
`flex/SP` (sugar) and `flexk/SP` (kernel) forms as FLEX/SP, and only the
static semantics differs. This module therefore reuses the FLEX/SP parser
(`DSL.flex_sp.FlexSPProgram`), the `PabsExp`/`PcallExp` AST nodes, and the
full binder-aware desugarer (`DSL.flex_sp.Desugar`), and replaces only the
checker.

## The type rules

- **[∀-intro]** (checking `(pabs (τ*) E)`): two side conditions, then check
  the body with the τ* in scope.
  - *import restriction* (p.732): a pabs-bound type identifier may not
    occur among the free type identifiers of the types of the free value
    identifiers of the body — otherwise the pabs would capture a type
    identifier a free value imports. The book's counterexample `polytest`
    is rejected for exactly this reason (tested).
  - *purity restriction*: the body must contain no mutation (`set!` / `:=`).
- **[∀-elim]** (checking `(pcall E T*)`): `E` must have a `forall` type with
  exactly as many bound identifiers as type arguments are given; each
  argument type is checked, then the body type is instantiated. A
  polymorphic value is **not a procedure** — it must be projected with
  `pcall` before it is applied.
- **[∀-≈]** (`CT.equiv`): `forall` types compare up to alpha-renaming of
  their bound identifiers (both sides freshened to the same fresh, rigid
  names, then the bodies compared).

At **every other decision point** the comparison is FLEX's equirecursive
equivalence, not subtyping: if branches, arrow arguments, `the`-ascriptions,
letrec/def declarations, oneof payloads, tagcase results, `set!`, `:=`,
`cell=?`/cellof (invariant), `cons` heads, and primitive arguments all
require **equal** types. Consequences tested in `FlexPSpec`:

| Program | FLEX/SP | FLEX/P |
|---|---|---|
| `(the (recordof (a int)) (record (a 3) (b 4)))` | accepted | **rejected** |
| `pick` — def with a wider record formal than its body (contravariant; accepted by FLEX/SP per `FlexSPSpec`) | accepted | **rejected** |
| `get-age` (p.702) applied to a record with extra fields | accepted | **rejected** |
| every monomorphic FLEX program (e.g. `pos?`/`even?`, p.636) | accepted | accepted |

The standard list procedures (`cons`/`car`/`cdr`/`null?`/`null`, p.728) are
**polymorphic standard-library values** under the `flex/SP` tag, exactly as
in FLEX/SP; the monomorphic kernel list forms remain accepted alongside.
`def-datatype` (Section 12.2.3, Figures 12.11–12.13) desugars at parse time
in the FLEX/SP parser (trec def-type + constructor defs + polymorphic
deconstructor defs) and type-checks under equivalence: all of a
deconstructor's tagcase clause results are the same rigid return-type
identifier.

## Implementation notes

- `PolyChecker` (in `check.scala`) is the FLEX/SP `SubtypeChecker` with all
  16 subtyping decision points replaced by FLEX's equirecursive
  `CT.equiv`, the Pabs/Pcall cases (which involve no subtyping) kept, and
  the `tyScope` threading (pabs-bound type identifiers are not put into
  `CT.env` — a self-mapping would break `CT.isRecursive`/`step`/`equiv` —
  so they travel as a scope set, and annotations are opened against it in
  `openIn`).
- `PolyProgramChecker` desugars with `DSL.flex_sp.Desugar` (the full,
  binder-aware FLEX/SP desugarer — a wrapper around `DSL.flex.Desugar`
  would turn nested pabs/pcall into unit-typed errors) and substitutes
  def-types with `DSL.flex_sp.Desugar.substTypeDefsExp`.
- Entry point: `flexpCheck(input)` → `FlexOk(str)` / `FlexErr(msg)` (the
  FLEX result types); test helper `shouldFlexPCheckTo`.

## Book errata and notation notes (documented in the tests)

- **Figure 12.12** (`map-square`) writes `(cons (* n n) (map-square ms))` —
  a typo: the data-type constructor is `(icons ...)`. The tests use `icons`.
- **Figures 12.11/12.12** write the data type's type identifier T-prefixed
  (`Tintlist`); Figure 12.13's formal desugaring names the def-type after
  the def-datatype (`intlist`), which is what the checker implements.

## Entry point and tests

`flexpCheck(input)` parses a `flex/SP`/`flexk/SP` program and returns
`FlexOk(str)` or `FlexErr(msg)`. `FlexPSpec.scala` (15 tests) covers:

- parsing (the reused FLEX/SP parser, including the tag restriction);
- `EpolyId` (book Figure 12.10) → `int`; pcall onto an enclosing pabs
  variable; pcall arity and non-forall rejections;
- the import restriction (`polytest`, p.732) and the purity restriction;
- [∀-≈] alpha-renaming at `the` and at the def match point, and a
  non-equivalent rejection;
- the three **discriminating tests** (accepted by FLEX/SP, rejected here):
  the `recordof`-subtype ascription, contravariant `pick`, and `get-age`
  (p.702);
- the polymorphic standard-library list procedures through pcall;
- the canonical FLEX/SP `map` (p.730) → `(listof bool)`;
- `def-datatype intlist` (Figure 12.11): constructor, deconstructor
  projection, wrong-type rejection;
- the `sum` / `all-positive?` / `map-square` procedures (Figure 12.12);
- FLEX regression (the p.636 `pos?`/`even?` program).

## Build & test

```bash
mill flex_p.test
```
