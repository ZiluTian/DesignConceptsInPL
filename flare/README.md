# FLARE — FL with Type Reconstruction

FLARE (Chapter 13 of the book) is FL with **type reconstruction** (type
inference) instead of explicit type annotations. Every expression is assigned
a type by an algorithm rather than by the programmer, and the only types the
programmer writes are implicit. This module implements **full FLARE**
(Section 13.5.1): the μFLARE kernel (Section 13.2), let polymorphism
(Section 13.4), and the full-FLARE data constructs — immutable **pairs**,
homogeneous immutable **lists**, and mutable **cells**.

(Sections 13.5.2–13.5.4 — mutable variables, sum-of-products, oneofs, and
records — are *discussion* in the book, not part of full FLARE. Mutable
variables in particular live in FLARE/V, §17.2.2.)

## Programs

Programs use two tags:

- `(flarek (Iformal*) Ebody)` — **kernel**: no sugar, no items, no standard
  library. A bare primop name such as `+` is just an unbound variable; only
  `(prim + 1 2)` or `(@+ 1 2)` works here.
- `(flare (Iformal*) Ebody (def I E)*)` — **sugar**: a body plus top-level
  `def` definitions. This form desugars to a `flarek` program wrapped in a
  standard-library `letrec` (below) and a user `letrec` for the `def`s.

A program's type is displayed as `(=> (T1 ... Tn) Tbody)` when it has formals,
or as just `Tbody` when it has none (matching the FLEX convention). Any free
type identifiers left after reconstruction are canonicalized to `T1, T2, ...`
in order of first appearance.

## The type domain (`T`, `Type.scala`)

| Node | Form |
|---|---|
| `TBase` | `unit`, `int`, `bool`, `symb` |
| `TVar` | a (fresh) type identifier, displayed `?vN` while reconstructing |
| `TArrow(params, ret)` | `(-> (T*) T0)` |
| `TPair(fst, snd)` | `(pairof Tf Ts)` |
| `TList(elem)` | `(listof T)` |
| `TCell(elem)` | `(cellof T)` |

A **type schema** (`TS`) is either a closed type or `(generic (τ*) T)` — the
carrier of let polymorphism. Schemas occur only in type environments
(`TE: Ident → TypeSchema`); a reference to a name bound to
`(generic (τ*) T)` is *instantiated* with a fresh type identifier for each
`τi` at every use.

## Type reconstruction (`check.scala`)

The algorithm (Figures 13.14, 13.20, 13.26) walks the desugared kernel
expression, assigning each subexpression a type and accumulating a set of
**type constraints**. The constraints are solved once, at the top, by a lazy
left-to-right unifier (Figure 13.11) with an occurs check and
arrow-arity/structural agreement for `pairof`/`listof`/`cellof`.

The reconstruction rules:

- **[unitR] [intR] [boolR] [symR]** — the literal types.
- **[errorR]** — a fresh type identifier.
- **[varLPR] / [genvarLPR]** — a closed schema gives its type; a generic
  schema is freshened (a fresh identifier per bound `τ`). An unbound
  variable is an error.
- **[ifR]** — the result is the then-branch's type; the test is constrained to
  `bool` and the two branches to be equal.
- **[→-introR]** — a fresh identifier per formal (multi-parameter `abs` is a
  kernel form, so it is handled directly).
- **[→-elimR]** — a fresh result identifier; the rator is constrained to be an
  arrow from the argument types to that result (multi-argument application is
  a kernel form).
- **[primR]** — the operator type is looked up in `TEPrim`, instantiated with
  fresh identifiers, and constrained to an arrow over the actual arguments.
- **[letLPR]** — each definition is typed in the **outer** environment (a
  `let` is *parallel*: a definition cannot see the other let-bound names),
  and its schema is `rgenPure(Ti, TE, TCSi, Ei)` — generalized over its own
  constraints only.
- **[letrecLPR]** — a fresh identifier per name; each definition is typed with
  **all** the names (including its own) bound to their fresh identifiers
  (monomorphic inside the definitions). The constraint set is
  `(∪ TCSi) ∪ {τi = Ti}`; each schema is `rgenPure(Ti, TE, TCSdefns, Ei)` —
  over the *full* constraint set and the *outer* environment.

### Generalization: `rgen` and `genPure` (Figure 13.26)

`rgen(T, TE, TCS)` solves `TCS`, applies the substitution to `T`, and
generalizes over the identifiers free in the result but not in the
(substituted) environment. `rgenPure(T, TE, TCS, E)` is `rgen` when `E` is
**pure**, and the plain (closed) type `T` otherwise — the **value
restriction**: a definition that touches the store cannot be generalized,
because generalizing it would effectively *copy* a side-effecting
expression.

### Purity (Figure 13.25)

A conservative approximation of "does not touch the store":

- literals, variable references, and `error` are pure;
- an `abs` is **always** pure (creating a procedure does not touch the store,
  even if invoking it might);
- an `if` is pure iff all three subexpressions are pure;
- a `let`/`letrec` is pure iff all of its *definition* expressions are pure
  (the body is not required);
- a primitive application is pure iff the operator is **not** one of
  `{cell, ^, :=}` and all of its arguments are pure;
- a procedure application is **always** impure.

This is what makes `EpolyCell` (p.815) ill typed: the definition of `c`
(`(cell (null))`) is impure, so `c` is *not* generalized, and both uses of
`c` must share a single content type — which cannot be both `int` and `bool`.

### The primitive type environment (`TEPrim`, Figure 13.24)

The 15 μFLARE primops have closed arrow types. The pair / list / cell primops
have **generic** schemas:

| Primop | Schema |
|---|---|
| `pair` | `(generic (?a ?b) (-> (?a ?b) (pairof ?a ?b)))` |
| `fst` / `snd` | `(generic (?a ?b) (-> (pairof ?a ?b) ?a))` / `(?b)` |
| `cons` | `(generic (?a) (-> (?a (listof ?a)) (listof ?a)))` |
| `car` / `cdr` | `(generic (?a) (-> (listof ?a) ?a))` / `(-> (listof ?a) (listof ?a))` |
| `null` | `(generic (?a) (-> () (listof ?a)))` |
| `null?` | `(generic (?a) (-> (listof ?a) bool))` |
| `cell` | `(generic (?a) (-> (?a) (cellof ?a)))` |
| `^` | `(generic (?a) (-> (cellof ?a) ?a))` |
| `:=` | `(generic (?a) (-> ((cellof ?a) ?a) unit))` — **returns `unit`** |
| `cell=?` | `(generic (?a) (-> ((cellof ?a) (cellof ?a)) bool))` — shared content type |

`:=` returns the **unit** value (not the cell): this matches the FLEX
`[cell-set]` rule (Figure 11.21) and the FLICK value of a cell assignment
(p.399). `cell=?` uses a *shared* content type (the FLEX `[cell-eq]` rule).

### The standard library (Figure 13.23)

A `flare` (sugar) program desugars to a `flarek` program wrapped in a
**standard-library `letrec`** of 29 bindings: one wrapper procedure per
primop (e.g. `(+ 1 2)` is `app`-ing the `+` wrapper, which is
`(abs (x y) (prim + x y))`), plus `true`/`false` as synonyms for the boolean
literals. Because that `letrec` is subject to `[letrecLPR]` with `genPure`,
the stdlib names carry exactly their `TEPrim` generic schemas in the body's
type environment (so `pair`, `cons`, `cell`, … are polymorphic, while `+`,
`=`, … are monomorphic). A `flarek` program gets **no** stdlib.

## The AST and parser

- **AST reuse**: the FL expression nodes are reused (`DSL.fl.Exp` is unsealed,
  the `flic` precedent). `abs`/multi-application are the FL `Abs`/`MultiApp`
  kernel nodes (they are *kernel* forms in FLARE, unlike FL where they are
  sugar). The only new nodes are `FlarePrim(op, args)` (the `(prim O E*)`
  kernel form over FLARE's extended primop set) and `BeginExp(e1, e2)` (the
  `begin` sugar).
- **Programs**: `FlareKernelProgram(formals, body)` and
  `FlareSugarProgram(formals, body, defs)`.
- **Parser** (`program.scala`): reuses the FL s-expr lexer; the
  interpretation is *fallible* (`Option`), so a keyword in the wrong arity, an
  identifier in a binding position, or an unknown primop rejects the whole
  program as a parse error. Binding/formal names are validated against the
  `Ident` domain (Figure 13.1/13.23: `SymLit` minus `@`-prefixed names,
  keywords, and sugar keywords); primop names against `TEPrim.primops`.
- **Desugaring** (`Desugar.scala`): `@O` → `(prim O …)`, `cond` → nested `if`,
  `scand`/`scor` → short-circuit, `recur` → `letrec`, `begin` →
  `let`-fresh, `list` → `null`/`cons`, and the program-level stdlib + user
  `letrec` wrapper. `abs`/`MultiApp`/`let`/`letrec` pass through unchanged
  (they are kernel forms).

## Entry point and tests

`flareRecon(input)` (in `check.scala`) parses a `flarek`/`flare` program and
returns `FlexOk(str)` or `FlexErr(msg)` (reusing the `DSL.flex` result types).
`FlareSpec.scala` (26 tests) covers:

- parsing (valid programs, malformed programs → parse error);
- literals, abstractions (incl. multi-parameter and zero-parameter), and
  program formals;
- `if` (bool test, matching branches);
- `let` (parallel definitions) and `letrec` (recursion — the book's `Ppow`,
  p.775, and a factorial);
- **let polymorphism**: `Eid` (p.778) accepted; `Econst` (p.804), `EabsR`
  (p.807), the p.806 letrec-monomorphism example, and `EpolyCell` (p.815)
  rejected;
- the standard library (primops as procedures; `flarek` has no stdlib);
- relational/arithmetic/logical primops;
- pairs (`pair`/`fst`/`snd`), lists (`cons`/`car`/`cdr`/`null`/`null?`,
  homogeneous), cells (`cell`/`^`/`:=`/`cell=?`, `:=` returns `unit`);
- syntactic sugar (`cond`/`scand`/`scor`/`begin`/`list`/`def`/`recur`);
- higher-order procedures;
- ill-typed programs (unbound variable, wrong argument type, arity mismatch,
  applying a non-procedure).

## Build & test

```bash
mill flare.test
```
