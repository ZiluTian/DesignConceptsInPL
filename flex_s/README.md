# FLEX/S — FLEX with Subtyping

FLEX/S (Chapter 12.1 of the book) is FLEX with a subtype relation: the
type rules are **those of FLEX extended with the single [inclusion] rule**
(Figure 12.1) — an expression of type T' can be used anywhere an expression
of type T is expected, provided T' ≤ T. The concrete syntax is unchanged
(same `flexk` / `flex` program forms), so this module reuses the FLEX
parser, AST, and substitution machinery from `DSL.flex` and replaces only
the static semantics.

Because every FLEX equivalence is a FLEX/S subtype relation (the
[equiv-≤] rule), FLEX/S is a strict superset of FLEX: every FLEX program
type-checks under FLEX/S (regression-tested in `FlexSSpec`).

## The subtype relation (Figures 12.2 and 12.4)

`Subtype.subtype(p, q)` in `Subtype.scala` computes the equirecursive
two-finger judgment p ≤ q:

- **[assumed-≤AS]** — an already-assumed pair (the cycle guard for
  recursive types);
- **[equiv-≤]** — the FLEX equirecursive equivalence (`CT.equiv`);
- **structural rules** (both sides non-recursive, Figure 12.2):

  | Construct | Direction |
  |---|---|
  | base types, unbound identifiers | equality |
  | `pairof`, `prodof`, `seqof`, `listof` | covariant in the components |
  | `recordof` | the subtype has **all** supertype fields; common fields covariant (subtypes have more fields) |
  | `oneof` | the subtype has **fewer** tags; common tags covariant |
  | `->` | equal arity; **contravariant** in the arguments, covariant in the result |
  | `cellof` | **invariant** in the content (the content types must be equivalent) |

- **[trec-left-≤AS] / [trec-right-≤AS]** — if exactly one side is
  recursive (a `trec`, a `tletrec`, or a type identifier with a
  definition), step that side, record the pair as an assumption, and
  continue. This is what establishes the book's p.706 judgments
  `Trs ≤ Trt` and `Tru ≤ Trv` over infinite recursive unwoundings.

**Why cellof is invariant (book p.705):** a covariant cellof rule would be
unsound — the book's counterexample

```
(let ((stuffit (abs ((r (cellof (recordof (a int))))) (:= r (record (a 2)))))
      (c (cell (record (a 1) (b #t)))))
  (begin (stuffit c) (select b (^ c))))
```

would type-check with covariance but crash at run time (`stuffit` shrinks
the record stored in `c`, after which `(select b ...)` fails). With
invariance, the call `(stuffit c)` is ill-typed. This module rejects it.

## Directional subtyping at the checker match points

The FLEX/S checker (`SubtypeChecker` in `check.scala`) is the FLEX checker
with each "the types must be equivalent" test replaced by a directional
test (`T'` is inferred, `T` the expected one):

| Match point | Rule |
|---|---|
| if-branches, seq components, tagcase results | a **common supertype** (T1 ≤ T2 or T2 ≤ T1) |
| procedure application | argument ≤ formal parameter |
| `letrec` bindings / top-level `def` | inferred ≤ declared |
| `the` | inferred ≤ ascribed |
| `one` payload | inferred ≤ tag type |
| `cons` head | head ≤ list element type |
| `set!` | value ≤ variable's declared type |
| `:=` | value ≤ cell content type |
| primop arguments | argument ≤ declared argument type |
| `cell=?` | content types **equivalent** (invariance kept exact) |
| if-test / sequence index | exact base type (`bool` / `int`) |

## Entry point and tests

`flexsCheck(input)` (in `check.scala`) parses a `flexk`/`flex` program and
returns `FlexOk(str)` or `FlexErr(msg)` (reusing the FLEX result types).
`FlexSSpec.scala` (15 tests) covers the book's examples:

- the `get-age` record with extra fields, p.702 (rejected by FLEX, accepted
  by FLEX/S — cross-checked against `DSL.flex.flexCheck`);
- recordof / pairof / listof / oneof covariance and its failures, p.703;
- arrow contravariance and result covariance, p.704;
- cellof invariance and the p.705 soundness counterexample;
- the `Trs ≤ Trt` and `Tru ≤ Trv` recursive-type judgments, p.706, plus the
  reversed (rejected) direction;
- the inclusion rule at the `if` / `seq` / `tagcase` / `set!` / `def` match
  points;
- the FLEX superset regression (the p.636 `pos?`/`even?` program and the
  Figure 11.26 `Tib1`–`Tib4` equivalence chain still type-check).

## Build & test

```bash
mill flex_s.test
```
