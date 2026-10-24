# FLEX/SPDK — FLEX/SPD with Kinds

FLEX/SPDK (Section 12.3.2 of the book; the K stands for Kinds) is FLEX/SPD
with **explicit kinds**: a kind annotation is required on every description
identifier declared in `pabs`, `forall`, and `dabs`. The kind domain is

```
K ::= type | (->> (Karg*) Kresult)
```

where `type` is the kind of descriptions that denote types and
`(->> (K*) K)` the kind of a description operator (type constructor). The
book's examples: `cellof`, `seqof`, `listof` have kind `(->> (type) type)`;
`pairof` has kind `(->> (type type) type)`; the higher-order `mapperof`
(p.755) has kind `(->> ((->> (type) type)) type)`. (In the literature, `type`
is often written `•` or `*` and `->>` as an infix `⇒`.)

Kinds play for descriptions the role that types play for values: the
kind-checking rules of **Figure 12.22** are enforced as *kind premises* in
the type rules of **Figure 12.23**. This carves out a restricted (System
Fω-style) subset of descriptions on which equivalence is decidable — just as
a simple type system carves a strongly normalizing subset of FL (book
p.760).

## Syntax (Figure 12.21)

| Form | Meaning |
|---|---|
| `(pabs ((δ K)*) E)` | kind-annotated polymorphic abstraction (replaces the FLEX/SPD unkinded `pabs`) |
| `(forall ((δ K)*) D)` | kind-annotated polymorphic type |
| `(dabs ((δ K)*) D)` | kind-annotated description abstraction |

The binder list is a **flat alternating name/kind sequence**:
`(pabs (t type f (->> (type) type)) E)`. `dletrec`, `plet`, and `pletrec`
binder lists are *unchanged* (no kinds): dletrec-bound identifiers are
required to be of kind `type` (book footnote 10), and plet/pletrec names
take the kind of their definition. The kind keywords `type` and `->>` are
not descriptions: `(type …)` and `(->> …)` do not parse in description
position.

## Kind checking (Figure 12.22)

`KindCheck.kindOf(d, descEnv, KE, visiting)` computes the kind of a
description `d` relative to the kind environment `KE` (kind name → kind,
starting from `KEbase`: the base types have kind `type`; `cellof`/`seqof`
have kind `(->> (type) type)`), or `None` if `d` is not well kinded:

- **[→] / [prodof] / [recordof] / [oneof]**: kind `type` iff every component
  description has kind `type`;
- **[forall]**: kind `type` iff the body has kind `type` under the binder
  kinds;
- **[->>-intro]** (a `dabs`): kind `(->> (K1 … Kn) Kbody)` where `Kbody` is
  the body's kind under the binder kinds;
- **[->>-elim]** (an application): the rator must have an arrow kind of
  exactly the application's arity, and each argument must have the
  corresponding argument kind;
- **[dletrec]**: the binders are kind `type`, each *definition* must have
  kind `type`, and the result is the *body's* kind.

A named description's kind is computed **lazily at its use positions**
(def-descs, plet/pletrec binds, stdlib names): the [var] rule looks the
name up in `descEnv` and kind-checks the definition, with a `visiting`
cycle guard. Consequences:

- a `def-desc` may name a **type constructor** (book p.755: `twiceof`,
  `mapperof`) — its kind is checked only where it is used;
- the book's **looping description** `((dabs (d) (d d)) (dabs (d) (d d)))`
  (p.758) is rejected by kind checking in one step (the argument has an
  arrow kind, not `type`) — no trampoline cutoff needed;
- two *mutually aliasing* pletrec/def-desc names with no enclosing dletrec
  are conservatively rejected by the cycle guard (the book's intended
  spelling for mutual recursion is a single `dletrec`, whose binders are
  kind-checked simultaneously).

## Type checking (Figure 12.23)

`SPDKChecker` is the FLEX/SPD checker threaded with the kind environment
`KE`. Before a description is normalized to a type (`DescEval.normalize`,
inherited from FLEX/SPD), it must be **well kinded and of kind `type`**
(`descAsType`); the kind premises of Figure 12.23:

- **[→-intro]**: the formal descriptions must have kind `type`;
- **[letrec]**: the declared descriptions must have kind `type`;
- **[the] / [error] / [oneof-intro]**: as above;
- **[∀-intro]**: the binder kinds are taken from the syntax and enter `KE`
  for the body (the FLEX/SP import and purity restrictions are unchanged);
- **[∀-elim]** (a `pcall`): each argument must have the kind of the
  corresponding `forall` binder, **checked in the caller's kind
  environment**; the argument descriptions are then substituted for the
  binders in the forall body (a *vacuous* binder makes the substitution a
  no-op — its argument need only be well kinded, not denote a type) and the
  result normalized to a type.

`TForallK`/`TDabsK` (kind-annotated `forall`/`dabs`) live in
`DSL.flex.Type` with the family-shared machinery (`wellFormed`, `show` —
displayed as `(forall (t type) …)` / `(dabs (t type) …)` — substitution,
`CT.structural`'s [forall-≤]/[forall-approx] with a binder-kind-agreement
premise, and `flex_sp.Subtype`'s [forall-≤] likewise).

## Standard library (Figure 12.19, kind-annotated)

The stdlib descriptions `pairof`/`listof` are `TDabsK`s and the polymorphic
list/pair values (`null`, `cons`, `car`, `cdr`, `null?`, `pair`, `fst`,
`snd`) have `TForallK` types — everything else is as in FLEX/SPD
(`listof T` normalizes to the book's `TTletrec` spelling).

## Book examples covered by the tests (31)

- parsing: the `flex/SPDK`/`flexk/SPDK` tags, kind-annotated forms, the
  empty binder list `()`, `type`/`->>` rejected in description position,
  unkinded/odd-length binder lists rejected;
- the kind-type examples of p.759 (`int`, `(-> (int) bool)`,
  `(recordof …)`, a `drec intlist`) and the rejection of description
  operators as types (`cellof`, a `dabs`);
- ill-kinded applications (`(int bool)`, `(pairof int)`, `(listof int
  bool)`), the looping description, and an ill-kinded `def-desc`;
- the well-kinded **`Dlistof`** def-desc (dabs over dletrec, the book's
  reordered spelling);
- plet (p.755) and a plet-bound arrow-kind name rejected as a type; pletrec
  binds (incl. mutually recursive ones and a rejected alias cycle);
- description β-equivalence and the p.755 def-desc examples (`intlist`,
  `twiceof` — the latter rejected *as a type*, accepted *applied*);
- the polymorphic list/pair stdlib through `pcall`;
- **`mapperof`** (pp.755–756) with its arrow-kind binder driving
  `list-map` and `seq-map`;
- **`make-node`** (Figure 12.17);
- the FLEX/SPD regression set, now kind-annotated: EpolyId, projection onto
  an enclosing pabs variable, pcall arity/monomorphic-rator/argument-kind
  errors (incl. a vacuous arrow-kind binder), import/purity restrictions,
  forall alpha-renaming, contravariance through forall, binder-kind
  agreement, `def-datatype intlist` + `sum`/`all-positive?`/`map-square`,
  the p.702 `get-age` and p.636 `pos?`/`even?` programs.

FLEX/SPDK is a superset of FLEX/SPD modulo the kind annotations, which
FLEX/SPDK *requires*.

## Syntax traps (hit while writing the tests)

- the program body comes **before** the items: `(flex/SPDK (formals) Ebody
  items*)`;
- `pcall` is `(pcall E D*)` with `E` a *value*;
- every `pabs`/`forall`/`dabs` binder needs its kind (`t type`,
  `f (->> (type) type)`); `dletrec`/`plet`/`pletrec` binders are unkinded;
- `(type …)` and `(->> …)` in description position are parse errors;
- a `drec` binds its name **only in its own description** — use a
  `def-desc` for a recursive data type that sibling expressions name.

## Implementation notes

- `KindCheck` (Figure 12.22) plus the kind premises in `SPDKChecker`
  (Figure 12.23); `descAsType` = well-kinded + kind `type` → normalize →
  well-formed. The `pcall` case checks argument kinds in the *caller's* `KE`
  before substituting the raw argument descriptions (T-level
  `Subst.substType`, so a vacuous binder is a no-op).
- `def-datatype` desugars to the kind-annotated deconstructor
  (`TForallK` declared type, `PabsExpK` body, binder `t_ret type`), as
  Figure 12.21 requires.
- **Known conservative gap** (no book example needs it): a `forall` body
  that *uses* an arrow-kind binder as a description operator (e.g. the
  type `(f int)` inside a `pabs (f (->> (type) type))` body) does not
  normalize (the application is stuck at the binder variable) and is
  rejected; full Fω higher-order type substitution is not represented.

## Entry point and tests

`flexspdkCheck(input)` (in `check.scala`) parses a `flex/SPDK`/`flexk/SPDK`
program and returns `FlexOk(str)` or `FlexErr(msg)` (reusing the FLEX
result types). `FlexSPDKSpec.scala` (31 tests) is listed above.

## Build & test

```bash
mill flex_spdk.test
```
