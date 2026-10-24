# FLEX/SPD — FLEX/SP with Descriptions

FLEX/SPD (Section 12.3.1 of the book; the D stands for Descriptions) extends
FLEX/SP so that **every type position is a description**: an expression
language over types, in which types are first-class values that can be
bound, passed as arguments, and computed. The book's motivation: type
constructors such as `(treeof int)` (book Figure 12.17) and higher-order
operators such as `mapperof` (pp.755–756) let one write a single def whose
type mentions *type parameters* as ordinary description variables.

Because descriptions are just an expression language that evaluates to
types, the module **normalizes descriptions to types** and then reuses
FLEX/SP's equirecursive subtyping checker unmodified (threaded with a
description environment, so description-bound names open to their
definitions). There is no separate description-equivalence relation.

## Description syntax (Figure 12.18)

| Form | Meaning |
|---|---|
| base types, `τ` (type identifier) | as before — also the leaves of a description |
| `(dabs (δ*) D)` | a description procedure (a δ-binding) |
| `(Drator Drand*)` | description application (≥1 argument; a 1-element list is *not* an application) |
| `(dletrec ((δ D)*) D)` / `(drec δ D)` | recursive description bindings; `drec` is the single-binding sugar |
| `(plet ((δ D)*) E)` / `(pletrec ((δ D)*) E)` | description bindings **in expressions** (Figure 12.18, p.755) |
| `def-desc δ D` | program-level description binding (`def-type` is accepted as an alias) |

`listof` and `pairof` are **standard-library description identifiers**
(pre-bound `dabs`es), not keywords. `trec`/`tletrec` are no longer type
spellings in FLEX/SPD (Figure 12.18 drops them); the book's examples spell
recursive types with `drec`/`dletrec`. `def-datatype` desugars exactly as in
FLEX/SP, except the generated def-desc is `dletrec`-based (a `TDletrec`
normalizes to a `TTletrec` type at check time).

## The normalization-to-type design

- Descriptions parse into the four new `T` nodes: `TBaseCtor` (the 1-arg
  base type constructors `cellof`/`seqof`), `TDabs`, `TDApp`, `TDletrec`
  (in `DSL.flex.Type`, shared with the family).
- `DescEval.normalize` β-reduces a description to a type with a step-bounded
  trampoline (`MaxSteps = 10000`): `TDletrec` becomes a `TTletrec` (its
  bindings are rigid, never followed as aliases); alias-following is guarded
  by a `visiting` set so that the book's **looping description**
  `((dabs (d) (d d)) (dabs (d) (d d)))` (p.758) terminates and is rejected
  as "malformed description" instead of hanging.
- A description-bound name (def-desc, plet/pletrec bind) enters the checker
  as a raw `δ → D` entry (`descEnv`); every type position opens names
  through `openDesc`. Mutual recursion works through sibling alias-following;
  a cycle among *aliases* (with no `dletrec` to rigidify it) bottoms out in
  a rigid `TVar` and fails `T.wellFormed`.
- **plet scope** (p.755): a `plet` bind is in scope only in the body —
  each bind's definition must be well formed relative to the *outer*
  description environment. `pletrec` binds see all sibling names.
- Standard library (book p.755, Figure 12.19): the FLEX/SPD kernel **drops
  the list/pair expression forms** — `null`, `cons`, `car`, `cdr`, `null?`,
  `pair`, `fst`, `snd` are polymorphic **stdlib values** of `forall` types,
  projected at use sites with `pcall`. In particular `null` is a 0-ary
  procedure: the empty list of type `T` is `((pcall null T))`, and
  `listof T` normalizes to the book's `TTletrec` spelling
  `(tletrec ((listof-t (oneof (null unit) (cons (prodof T listof-t)))))
  listof-t)`.

## Book examples covered by the tests (28)

- plet transparency (p.755, p.757) and pletrec, incl. mutually recursive
  binds and a rejected alias cycle;
- description β-equivalence (`((dabs (s t) (prodof s t)) int bool) ≈
  (prodof int bool)`, Figure 12.20), the p.755 `def-desc` examples
  (`intlist`, `twiceof`), safe nonsense (a base type in rator position,
  p.757), the looping description (p.758), and `trec`/`tletrec` rejection;
- the polymorphic list/pair stdlib through `pcall`;
- **`mapperof`** (pp.755–756) driving the book's `list-map` and `seq-map`
  (the declared types are description applications whose operator is a
  stdlib δ or a base type constructor);
- **`make-node`** (Figure 12.17): `(pcall make-node int)` *projects* the
  polymorphic value to the monomorphic arrow
  `(-> ((treeof int) (treeof int)) (treeof int))` — applying it to two
  int-trees yields the `treeof int` type;
- the FLEX/SP regression set (EpolyId, pcall arity, import/purity
  restrictions, forall alpha-renaming, contravariance, `def-datatype
  intlist` + `sum`/`all-positive?`/`map-square`, the p.702 `get-age` and
  p.636 `pos?`/`even?` programs, `def-type` accepted as a `def-desc` alias).

FLEX/SPD is a superset of FLEX/SP modulo the `trec`/`tletrec` spellings.

## Syntax traps (hit while writing the tests)

- the program body comes **before** the items: `(flex/SPD (formals) Ebody
  items*)`;
- `pcall` is `(pcall E T*)` with `E` a *value* and the T* *descriptions*:
  `((pcall cons int) 1 …)`, never `(pcall (pcall cons int) 1)`;
- stdlib `null`/`pair` are procedures: zero-arg application `((pcall null
  int))` gets the value;
- projecting a polymorphic value yields a monomorphic arrow — apply it to
  get the result type;
- a `seqof`-typed def body is `(error todo (seqof out-type))` — the `seq`
  wrapper would raise one level.

## Implementation notes

- `SPDChecker` is a copy of FLEX/SP's `SubtypeChecker` threaded with
  `descEnv: Map[String, T]` as a fourth environment; `openDesc` runs at
  every type position. The `PletExp`/`PletRecExp` cases well-form the
  binds (with the pling scope above), then check the body with the binds
  added to `descEnv`. The list/pair kernel cases of FLEX/SP are removed.
- `FlexSPDProgramChecker` pre-loads `StdDescs` (`pairof`, `listof` as
  `TDabs`es) and the polymorphic stdlib values; its Fig-12.19 desugaring
  wraps `pletrec` in a `LetRecExp` and `def-datatype` in a `TDletrec`
  def-desc.
- **Known conservative gap**: `DescEval.evalRator` does not unwrap a
  `TDletrec`-shaped definition used in rator position (e.g. `(l x)` where
  `l` is a `dletrec`), so such an application is rejected where
  unfold-to-definition would accept it. No book example needs it.

## Entry point and tests

`flexspdCheck(input)` (in `check.scala`) parses a `flex/SPD`/`flexk/SPD`
program and returns `FlexOk(str)` or `FlexErr(msg)` (reusing the FLEX
result types). `FlexSPDSpec.scala` (28 tests) is listed above.

## Build & test

```bash
mill flex_spd.test
```
