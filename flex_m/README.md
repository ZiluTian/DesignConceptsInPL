# FLEX/M — FLEX/SP with Modules

FLEX/M (Section 15.2 of the book) extends FLEX/SP with **first-class
modules**: values can be modules with typed components, and types can be
parameterized by *values* (dependent types). The module brings the last of
the book's static-semantic features to this repo:

- `module` / `open` / `mselect` / `load` — module construction, projection,
  component selection, and loading a module from a file;
- `def-datatype` with **constructor and deconstructor** procedures whose
  types follow Figure 15.4 (deconstructors take the data value, a success
  continuation of the component values, and a failure continuation);
- **dependent type constructors**: `(dselect θ Emod)` — a type whose
  parameters are instantiated with *values* from a module expression;
- `match` — pattern-matching case analysis over deconstructible data types
  (Section 15.4.6);
- `let-type` / `let-type*` and a typed `letrec` sugar;
- the book's canonical examples: the list module (Figure 15.3),
  `make-polymod` (Figure 15.6), `Eopen` (Figures 15.9–15.10), the
  environment examples of Figure 15.8 (including the
  `Topen ≤ TenvModule` information-hiding result), the table functor
  (Figure 15.13), and the module-capture counterexamples (p.912).

The module is self-contained: it defines its own type domain (`MT`, in
`Type.scala`) rather than reusing `DSL.flex.T` — dependent types make value
identifiers occur in types, so a separate domain is cleaner. The FL s-expr
lexer/parser (`DSL.fl`), the FLEX result types (`DSL.flex`), and the
FLEX/SP checker architecture (checking mode + a rigid `unify` for the
dependent positions) are reused.

## Programs

Programs use two tags:

- `flex/Mk (Tformals*) Ebody` — kernel: no sugar, no items;
- `flex/M (Tformals*) Ebody (def-type τ T)* (def-datatype θ (τ*) (I T*)*)* (def I T E)*`
  — sugar: typed formals, a body, and program items.

Formal parameters are typed (a program is a procedure over its module
arguments), and a program's type is displayed as
`(=> (T1 T2 ... Tn) Tbody)` — all formal types in one list. For the kernel
tag the formal list is usually `()`.

The sugar form desugars (Figure 15.2) to a program that opens a
**standard-library module** (the list procedures as polymorphic standard
values, `@@sl1`/`@@sl2`), applies a sequential `let-type*` over the
def-types, opens a module of the value definitions, and then evaluates the
body. Formal parameter types therefore cannot reference def-type names
(formals are bound outside the `let-type*`).

## The type domain (`MT`, `Type.scala`)

| Node | Form |
|---|---|
| `MTBase` / `MTVar` | `unit`, `int`, `bool`, `symb` / a type identifier |
| `MTUnif` | a unification variable (`?v…`) |
| `MTArrow(params, ret)` | `(-> (T*) T0)` sugar, or `(-> ((I T)*) T0)` when a later parameter's type (or the result) mentions an earlier parameter's *value* name (Figure 15.4, note 3, p.895) |
| `MTRecord(fields)` / `MTOneof(tags)` | `(recordof (I T I T …))` / `(oneof (I T I T …))` — flat field lists |
| `MTProd` / `MTSeq` / `MTCell` | `(prodof T*)`, `(seqof T)`, `(cellof T)` |
| `MTForall(vars, body)` | `(forall (τ*) T)` |
| `MTModuleof(ats, vals)` | `(moduleof ((θ τ*)*) (I T)*)` — abstract-type specs first, then value components as separate items |
| `MTyConApp(tc, args)` | `θ(τ*)` — a type-constructor application |
| `TyConName(θ)` / `TyConSelect(θ, emod)` | a type-constructor name / its projection onto a module value (the runtime form of `dselect`) |

Type-constructor names must end in `of` (p.895, note 4) — `envof`,
`listof`, `polyof`, … — and type keywords are not tycon names; this keeps
`dselect` disambiguation and `Idents.validValueIdent` sound. Tycon scope is
a checker-state stack of `ScopeDeclare`/`ScopeOpen` (innermost wins).

Because of dependent types, **value identifiers occur in types** (a
parameterized arrow's parameter names, a `TyConSelect`'s module expression).
The display convention: the sugar arrow `(-> (T*) T0)` is used only when no
parameter name occurs free in a later parameter's type or the result
(`Fr.valueRefs` decides); otherwise the parameterized form
`(-> ((I1 T1 … In Tn)) T0)` is shown, and `TyConSelect` prints as
`((dselect θ Emod) T*)`.

## The checker (`check.scala`)

A standard FLEX/SP-style checking checker over `MT`, plus:

- **[moduleof-intro]** (Figure 15.17): check a module definition against a
  `moduleof` type — abstract types declared (no rebinding), components
  checked with the tycon in scope, and an (structurally unreachable here)
  import restriction on the module's free value identifiers.
- **[moduleof-elim]**: projecting a `TyConName`/`TyConSelect` onto a module
  value — the module must have a `moduleof` type whose abstract-type specs
  and value components subsume the tycon's; the substitution
  `θi → TyConSelect(θi, emod)` is applied, the emod must be pure, and
  on the way out the component value names are rebound to
  `(open Emod I)` projections.
- **moduleof subtyping (p.912)**: structural — the candidate's abstract
  types must match and each component must be a subtype (with the
  candidate's tycon substituted into the source's tycon references). This
  gives both the module-capture counterexamples (`Tmod1 ≰ Tmod2`) and the
  `Topen ≤ TenvModule` information-hiding acceptance.
- **[implicit-projection]** (p.920): when a tycon name is used in a type
  position and the current environment module has a matching component,
  the component's type is *unified* (fresh `?v` per forall variable,
  rigid unification) rather than merely subtyped — deliberately weaker
  than pcall + subtyping (locality restriction; failure messages say to
  use an explicit pcall).
- **[the]** (p.917), **[→-elim]** (application, including dependent arrows
  where the result type is instantiated with the argument values),
  **[let]** / **[with]**, the **pabs** import restriction (p.732) and purity
  restriction (body has no mutation), **match** (Section 15.4.6: the
  discriminant must be a tycon application; patterns bind payload variables
  to the component types; no rebinding), and **[loadLTstat]**.
- **Unsoundness guards (tested)**: `cellof` is invariant in its content
  type (`:=` between different `cellof` types is rejected); there is no
  [inclusion] rule across distinct base types (the FLEX/SP join is absent).

Rebinding is forbidden everywhere: abs parameters, let names, pattern
variables, module names, open names.

## The data-type construct (Figure 15.4)

`(def-datatype θ (τ*) (Itag Tcomp*)*)` introduces, for each clause, a
**constructor** with arrow type over the components and the tycon
application, and a **polymorphic deconstructor** whose success
continuation receives the component values (for a nullary clause the
continuation's parameter list is the empty tuple — the components are
still the tycon's parameters, not dropped) and whose failure
continuation takes no arguments. `match` is desugared against these.

## Implementation notes

- `Type.scala` also holds `Open` (tycon + type-variable scopes), `Fr`
  (free *value* identifiers — the dependent-type workhorse), `Subst`
  (capture-avoiding substitution: the replacement is alpha-renamed against
  the target's *bound* type-identifier names; a free occurrence of the
  substituted name is never renamed), `alphaRenameTyVars` (renames only
  names that are both bound-bound-avoid and valid type identifiers), and
  `Fresh` (unification and fresh-name supply; bare number strings show up
  in some error-message displays — cosmetic).
- `program.scala` parses the two program tags and all expression forms
  (including `^` for deref, paired record fields `(record (I E)*)`, and
  two-item tagcase clauses `(Itag Ebody)`). A list-head rator such as
  `((pcall empty int))` is a zero-ary application.
- `Desugar.scala` carries the sugar desugarings and the binder-aware
  type-substitution walkers (`substTypeDefsExp` / `substSimTypeDefsExp`);
  a pabs-bound type identifier blocks substitution in its body.
- Every expression has a **unique** type (FLEX/M is explicitly typed), so
  the checker never infers — `unify` is used only to solve the fresh
  variables that implicit projection and dependent-arrow instantiation
  introduce.

## Entry point and tests

`flexmCheck(input)` (in `check.scala`) parses a `flex/M`/`flex/Mk` program
and returns `FlexOk(str)` or `FlexErr(msg)` (reusing the FLEX result
types). `FlexMSpec.scala` (32 tests) covers:

- parsing (valid program, tag rejection, malformed formal type);
- `ElistModule` (Figure 15.3) → `TlistModule` (Figure 15.5);
- `EdblProc` (p.898) — a dependent arrow over the list module;
- `make-polymod` (Figure 15.6) — a module functor over a module of
  modules;
- `Eopen` (Figure 15.9) → `Topen` (Figure 15.10);
- `EenvSwap` (Figure 15.8) and its rejection of the procedure-module swap
  (p.906);
- `EenvTest` (Figure 15.8) applied to the formal environment module and to
  the list-based one (`Topen ≤ TenvModule`);
- the table functor (Figure 15.13);
- the pabs import restriction (p.732, `polytest`);
- pcall arity and non-polymorphic rejections;
- no-rebinding (let, abs) and the arrow-parameter locality rule
  (a parameter's type may not mention a later parameter's name);
- `match` (non-tycon discriminant, pattern rebinding);
- implicit projection failing the locality restriction (p.920);
- open purity; moduleof subtyping (p.912, both directions);
- `the` failure; `cellof` invariance;
- `mselect`, `let-type`, `load`;
- records (`select`/`with`), oneofs (`one`/`tagcase`), cells
  (`cell`/`:=`/`^`).

## Build & test

```bash
mill flex_m.test
```
