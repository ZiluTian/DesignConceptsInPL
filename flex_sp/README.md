# FLEX/SP — FLEX/S with Universal Polymorphism

FLEX/SP (Section 12.2.2 of the book; the P stands for Polymorphism) extends
FLEX/S with **universal (parametric) polymorphism**: values can be created
polymorphic over type identifiers and later specialized at their use sites.
Because universal polymorphism does not depend on subtyping, the book also
defines **FLEX/P** as "FLEX/SP without the [inclusion] type rule" (footnote 4,
p.727) — that variant is the `flex_p` module.

The module reuses the FLEX parser/AST from `DSL.flex` (plus the two new
kernel forms, `PabsExp`/`PcallExp`, in `AST.scala`) and the FLEX/S equirecursive
subtyping (the self-contained `Subtype.scala` copy, extended with the
[∀-≤] rule). Only the static semantics and the program grammar change.

## The three new constructs (Figure 12.9)

| Construct | Meaning |
|---|---|
| `(pabs (τ*) E)` | creates a first-class polymorphic value parameterized over the type identifiers τ* |
| `(pcall E T*)` | projects the polymorphic value denoted by E onto the types T*, instantiating E's type identifiers |
| `(forall (τ*) T)` | a polymorphic type — T parameterized over τ* |

A polymorphic value is **not a procedure**: it must be projected with
`pcall` before it is applied. `(pcall id int)` is the function; `(id ...)`
where `id` still has a `forall` type is rejected by the checker (the book's
examples always project first, e.g. `((pcall id bool) #t)`).

Programs use the `flex/SP` (sugar) and `flexk/SP` (kernel) tags, with the
body before the items, as in FLEX. The standard list procedures become
**polymorphic standard-library values** (book p.728) — `cons`, `car`, `cdr`,
`null?`, `null` (a 0-ary procedure) — and are available in the sugar form
(the kernel list forms `(cons h t)`, `(car e)`, … remain accepted as a
permissive superset).

## The [∀-intro] / [∀-elim] rules

- **[∀-intro]** (checking `(pabs (τ*) Ebody)`): two side conditions, then
  check the body with the τ* in scope.
  - *import restriction* (p.732): a pabs-bound type identifier may not
    occur among the free type identifiers of the types of the free value
    identifiers of the body — otherwise the pabs would capture a type
    identifier a free value imports. The book's counterexample `polytest`
    is rejected for exactly this reason (tested).
  - *purity restriction*: the body must contain no mutation (`set!` / `:=`).
- **[∀-elim]** (checking `(pcall E T*)`): `E` must have a `forall` type with
  exactly as many bound identifiers as type arguments are given; each
  argument type is checked, then the body type is instantiated.
- **[∀-≈] / [∀-≤]** (`Subtype.scala`): `forall` types compare up to
  alpha-renaming of their bound identifiers (both sides freshened to the
  same fresh names, then the bodies compared), matching the book's
  two-finger style.

## Deconstructible data types (Section 12.2.3, Figures 12.11–12.13)

`(def-datatype τdata (Itag T*)*)` desugars at parse time, per Figure 12.13,
into:

- a def-type `τdata = (trec τdata (oneof (Itag (prodof T*))*))`;
- one **constructor** per clause:
  `(def Itag (-> (T* τdata)) (abs ((x1 T1) ...) (one τdata Itag (prod x1 ...))))`;
- one **polymorphic deconstructor** per clause:
  `(def Itag~ (forall (τret) (-> (τdata (-> (T*) τret) (-> () τret)) τret))
   (pabs (τret) (abs ((val τdata) (succ (-> (T*) τret)) (fail (-> () τret)))
     (tagcase val payload (Itag (succ (get 1 payload) ...)) (else (fail))))))`.

Program items are normalized to all def-types first, then all defs
(Figure 12.13's footnote 6).

## Book errata and notation notes (documented in the tests)

- **Figure 12.12** (`map-square`) writes `(cons (* n n) (map-square ms))` —
  a typo: building an `intlist` out of an `int` and an `intlist` is the
  data-type constructor `(icons ...)`, not list `cons`. The tests use
  `icons`.
- **Figure 12.11**'s `icons~` writes `(pabs (t) (forall (t) ...))` — the pabs
  variable shadows the forall variable; the deconstructor the parse-time
  expansion generates binds a distinct return-type identifier instead.
- **Figure 12.11/12.12** write the data type's type identifier with a T
  prefix (`Tintlist`); Figure 12.13's formal desugaring names the def-type
  after the def-datatype (`intlist`), which is what the checker implements.
- The book's [oneof-elim1/2] rules (Figure 11.22) require tagcase clauses to
  follow the oneof type's tag order ("for simplicity"), but [oneof-≈] makes
  oneof tag order irrelevant. This module checks tagcase **order-independently**
  (each clause's payload type is looked up by tag; duplicate or unknown tags
  are rejected; without an `else` the clauses must cover every tag) —
  required because a generated deconstructor's single clause need not be the
  oneof's first tag. `flex`/`flex_s` keep the stricter prefix-order
  approximation.

## Implementation notes

- `TForall` and the `forall` keyword live in `DSL.flex.T` (with
  `T.parseForall`, an opt-in parse that accepts the forall form at every
  nesting position; the plain `T.parse` keeps FLEX itself forall-free).
  `CT.equiv` handles `forall` by freshening both sides to the same fresh
  names.
- pabs-bound type identifiers are **not** put into `CT.env` (a self-mapping
  would break `isRecursive`/`step`/`equiv`); they are threaded through the
  checker as a scope set (`tyScope`) and checked open via
  `T.wellFormed(t, tyScope)`.
- Type substitution must be binder-aware: a pabs variable shadows the
  substituted identifier in the pabs body. `DSL.flex.Subst` therefore
  exposes `substType`/`substSim` overloads taking a `shadowed` set.
- `Desugar.scala` is a **full** desugarer (the FLEX desugaring plus the
  pabs/pcall cases, with its own binder-aware expression substitution
  walkers). A wrapper that delegated to `DSL.flex.Desugar` is **not**
  sufficient: its catch-all turns any nested pabs/pcall into
  `FlexError("internal error: non-FLEX expression node", unit)`, whose
  symptom is the cryptic "the rator has type unit, which is not a procedure
  type" at the application site.

## Entry point and tests

`flexspCheck(input)` (in `check.scala`) parses a `flex/SP`/`flexk/SP`
program and returns `FlexOk(str)` or `FlexErr(msg)` (reusing the FLEX
result types). `FlexSPSpec.scala` (14 tests) covers:

- parsing of the new forms, and that `cons`/`car`/… are value identifiers;
- `EpolyId` (book Figure 12.10) → `int`; pcall onto an enclosing pabs
  variable; pcall arity and non-forall rejections;
- the import restriction (`polytest`, p.732) and the purity restriction;
- [∀-≈]/[∀-≤] alpha-renaming at `the` and at the def match point, and a
  non-subtype rejection;
- contravariance through `forall` (narrower-record def accepted, wider
  rejected);
- the polymorphic standard-library list procedures through pcall;
- the canonical FLEX/SP `map` (p.730) → `(listof bool)`;
- `def-datatype intlist` (Figure 12.11): constructor, deconstructor
  projection, wrong-type rejection;
- the `sum` / `all-positive?` / `map-square` procedures (Figure 12.12);
- FLEX/S regression under the `flex/SP` tag (the p.702 `get-age` program and
  the p.636 `pos?`/`even?` program).

## Build & test

```bash
mill flex_sp.test
```
