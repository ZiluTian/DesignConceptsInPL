# FLARE/E — FLARE with a Simple Effect System

FLARE/E (Section 16.2 of the book) extends implicitly typed FLARE with a
**simple effect system** over **store effects**: every expression is
assigned not just a type but also an *effect* — the set of store operations
(`init`, `read`, `write`) it may perform — and every procedure type carries a
**latent effect** (the effect the procedure is *allowed* to perform when
invoked). The *expressions* of FLARE/E are exactly those of FLARE, so the AST,
parser, desugaring, and syntactic-purity test are all reused from
`DSL.flare`; what is new is the type domain (latent effects, regions, effect
constraints) and **Algorithm Z**, the type/effect reconstruction algorithm
(Figures 16.4–16.9).

The reference FLARE/E system of this section (Figures 16.2–16.3) uses a
**syntactic** purity test (the same one as FLARE, Figure 13.25) and does not
implement [effect-masking] (§16.2.4) nor the effect-based purity variant
(§16.2.5); those are discussed in the book as extensions.

## Programs and program types

Programs use the same two tags as FLARE: `(flarek (Iformal*) Ebody)` (kernel)
and `(flare (Iformal*) Ebody (def I E)*)` (sugar). A program's type/effect is
always displayed in the full arrow form

```
(=> (Targ*) Fbody Tbody)
```

even when there are no formals (`(=> () Fbody Tbody)`). `Fbody` is the effect
the whole program performs; a purely functional body displays as `pure`.
Free type identifiers are canonicalized to `T1, T2, ...` and free region
identifiers to `R1, R2, ...` in order of first appearance.

## The type/effect domain (`Type.scala`)

Descriptions (Figure 16.1) all draw their variables from a **single** fresh
`?vN` supply, so one unifier and one substitution handle types, effects, and
regions together:

| Node | Form |
|---|---|
| `TBase` | `unit`, `int`, `bool`, `symb` |
| `TVar` | a (fresh) type identifier `δ` |
| `TArrow(params, latent, ret)` | `(-> (T*) Flatent T0)` — the arrow carries a *latent* effect |
| `TPair` / `TList` | `(pairof T T)` / `(listof T)` |
| `TCell(elem, region)` | `(cellof T R)` — the cell carries a *region* |
| `EPure` / `EVar` / `EMax` / `EBase(ctor, region)` | `pure` / `δ` / `(maxeff F*)` / `(FCR R)` |
| `EffCon(delta, f)` | `(>= δ F)` — the effect named by `δ` must be at least as large as `F` |
| `TS` | `T` (closed) or `(generic (δ*) T FCS)` — an **algebraic** type schema that also carries an effect-constraint set |

Effects are combined with `maxeff`, which is ACUI (associative, commutative,
unit `pure`, idempotent), so an effect is treated as a *set* of base effects.

## Type/effect reconstruction (Algorithm Z, `check.scala`)

The signature (Figure 16.6) is

```
Z : Exp -> TypeEnvironment
       -> (Type × TypeConstraintSet × Effect × EffectConstraintSet)
```

expressed as `recon(e, te) = Right((T, TCS, F, FCS))`. The rules:

- **[unitZ] [intZ] [boolZ] [symZ]** — the literal types, effect `pure`.
- **[errorZ]** — a fresh type identifier.
- **[varZ] / [genvarZ]** — a closed schema gives its type; a generic (algebraic)
  schema is freshened (a fresh description identifier per bound `δ`, plus the
  instantiated effect constraints). An unbound variable is an error.
- **[ifZ]** — the result is the then-branch's type; the test is constrained to
  `bool`, the branches to be equal; the effects are `maxeff`-ed.
- **[→-introZ]** — a fresh type identifier per formal and a **fresh latent
  effect identifier** `δlat`; the constraint `(>= δlat Fbody)` is added.
- **[→-elimZ]** — a fresh result type and a fresh latent effect; the rator is
  constrained to `(-> (Targs) δlat δres)`; the result effect is the `maxeff`
  of the argument effects and `δlat`.
- **[primZ]** — the operator's algebraic schema is freshened, then the same
  constraint pattern as `[→-elimZ]`.
- **[letSPZ]** — each definition is reconstructed in the **outer**
  environment (parallel `let`); its algebraic schema is
  `zgenPureSP(Tdef, TE, TCSdef, FCSdef, Edef)`.
- **[letrecSPZ]** — a fresh type identifier per name; each definition is
  reconstructed with all the names bound to their fresh identifiers
  (monomorphic inside the definitions); the equation constraints
  `δi = Ti` tie those identifiers to the definitions' types.

### Generalization: `zgen` / `zgenPureSP` (Figure 16.8)

`zgenPureSP` generalizes only when the definition expression is **syntactically
pure** (the Figure 13.25 test, reused from `DSL.flare`); otherwise the
definition is kept monomorphic (a closed schema). `zgen` solves the type
constraints, applies the substitution to the type *and* the effect constraints,
and generalizes over the description identifiers that are free in the
(substituted) type and constraints but **not** in the (substituted)
environment. This is why, in the book's `Einc-c!` example, the *region* of the
cell `c` stays **fixed** (not generalized) while the procedure `inc-c!`
generalizes over its content type and its latent effect: `c` is in the *outer*
let's environment when the inner let is generalized.

### Constraint solving

- **Type constraints** (`TCS`) are solved once at the top by the lazy
  left-to-right unifier of Figure 13.11, extended with an **occurs check** and
  structural agreement for `pairof`/`listof`/`cellof`, plus unification of
  arrow **latent effects** (always effect variables by construction) and of
  cell **regions** (always region variables).
- **Effect constraints** (`FCS`) are solved to their **least solution** by the
  least-fixed-point iteration of Figure 16.4: starting from `σ(δ) = pure`,
  iterate `σ'(δ) = maxeff(σ(δ), σ(F1), ..., σ(Fn))` over the constraints
  `(>= δ Fi)` until no set grows. Every latent-effect variable introduced by
  `[→-introZ]` is tied to its body's effect by an `(>= δlat Fbody)` constraint,
  so by the time the FCS is solved no effect identifier is left free.

## The primitive type/effect environment (`TEPrimE`, Figure 16.2)

The non-cell primops have **pure** latent effects (exactly the FLARE
`TEPrim` schemas). The cell operators carry **base-effect** latents,
parameterized by the cell's region:

| Primop | Schema |
|---|---|
| `cell` | `(generic (?t ?r) (-> (?t) (init ?r) (cellof ?t ?r)))` |
| `^` | `(generic (?t ?r) (-> ((cellof ?t ?r)) (read ?r) ?t))` |
| `:=` | `(generic (?t ?r) (-> ((cellof ?t ?r) ?t) (write ?r) unit))` — **returns `unit`** |
| `cell=?` | `(generic (?t ?r1 ?r2) (-> ((cellof ?t ?r1) (cellof ?t ?r2)) pure bool))` |

In **sugar mode** these primops are stdlib procedures (pure abstractions over
the `prim` form), so the store effects surface through the wrapper's latent
effect rather than through a `prim` application — the effect analysis is
identical to kernel `prim` use.

## Theorem 16.1 (page 956)

> A program is typable in FLARE **if and only if** it is typable in FLARE/E.

The two systems make the **same** accept/reject decision; only the *displayed*
types differ (FLARE/E adds the latent effects and regions). A cross-check test
asserts this on a representative battery of programs (well-typed and
ill-typed).

## The AST and parser

All reused from `DSL.flare` (the `flarek`/`flare` parser, `Desugar`,
`FlarePrim`/`BeginExp`, and the 29-binding standard library). This module adds
no AST or parser code — only the new type/effect domain and Algorithm Z.

## Entry point and tests

`flareReconE(input)` (in `check.scala`) parses a `flarek`/`flare` program and
returns `FlexOk(str)` or `FlexErr(msg)` (reusing the `DSL.flex` result types).
`FlareESpec.scala` (33 tests) covers:

- parsing (valid programs, malformed programs → parse error);
- literals, abstractions, and program formals (always `(=> ...)` form);
- `if` (bool test, matching branches);
- `let` (parallel definitions) and `letrec` (recursion — the book's `Ppow`);
- **let polymorphism**: `Eid` accepted; `Econst`, `EabsR`, the p.806
  letrec-monomorphism example, and `EpolyCell` rejected (mirrors FLARE);
- the standard library and all pure primops;
- pairs, lists, and **cells** (`cell` → `(init R)`, `^` → `(read R)`,
  `:=` → `(write R)`, `cell=?`);
- the book's effect examples: `Eboolcell` (p.946), `Einc-c!` (p.948, region
  stays fixed while the latent effect generalizes), `Etwice` (p.949,
  generalizes over type, region, and effect), `Eifproc` (p.955, latent-effect
  unification via `[does]`);
- syntactic sugar (`cond`/`scand`/`scor`/`begin`/`list`/`def`/`recur`);
- higher-order procedures;
- ill-typed programs;
- **Theorem 16.1** (acceptance matches the FLARE module exactly).

## Build & test

```bash
mill flare_e.test
```
