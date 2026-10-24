# FLEX — FL with Explicit Types

FLEX (Chapter 11) is the book's typed version of FL: it adds a type system to
FL's expressions so that the **type checker** (not an evaluator) becomes the
language's reference semantics. The module implements two dialects:

- **flexk** — the kernel language (Figure 11.31), typed s-expressions with
  explicit types at every binding and at every type-constructing form.
- **flex** — the kernel plus the μFLEX sugar (Figure 11.2): top-level `def`
  and `def-type` items and the standard library, which the program checker
  desugars to a `letrec` over the definitions with the standard-library
  bindings underneath.

Because the book presents FLEX as a *type system*, this module has no
evaluator: `flexCheck` (in `check.scala`) parses a program and runs the
equirecursive type checker, reporting either the program's type
(`FlexOk`) or the first type error (`FlexErr`).

## Types (Figure 11.31)

```
T ::= unit | int | bool | symb                 ; base types
    | τ                                        ; type identifier
    | (-> (Targ*) Tresult)                     ; procedure type
    | (pairof T T)
    | (prodof T*)                              ; positional product (tuple)
    | (seqof T)                                ; immutable sequence
    | (recordof (I T)*)                        ; record
    | (oneof (I T)*)                           ; tagged union (sum)
    | (listof T)                               ; typed list
    | (cellof T)                               ; mutable cell
    | (trec τ Tbody)                           ; recursive type
    | (tletrec ((τ T)*) Tbody)                 ; mutually recursive types
```

Value identifiers and type identifiers live in **separate namespaces**
(book p.635). A type annotation must be *closed* (no free type identifiers)
at its top level; free type identifiers inside a `trec`/`tletrec` body refer
to its binders.

## flexk kernel (Figure 11.31)

A program has the form `(flexk ((I T)*) Ebody)`. Expressions:

```
L            ::= #u | #t | #f | N | (sym Y) I
(error Y T)   ; an error that asserts its (annotated) type T
(if E E E)
(prim O E*)   ; primitive application (16 primops, below)
(abs ((I T)*) E)
(let ((I E)*) E)          ; untyped let (book p.632)
(letrec ((I T E)*) E)     ; mutually recursive, declared types
(the T E)
(pair E E) (fst E) (snd E)
(prod E*) (get N E)       ; N must be an integer literal
(seq E*) (seq-get E E) (seq-size E)
(record (I E)*) (select I E) (with E I)
(one T I E) (tagcase E I (I E)* (else E)?)
(null T) (cons E E) (car E) (cdr E) (null? E)
(cell E) (^ E) (:= E E) (cell=? E E)
(E E*)                   ; N-ary application
```

The 16 primitive operators are the FL primops **minus** the type predicates
and the pair selectors (Figure 11.1: `fst`/`snd` are kernel forms in full
FLEX, Figure 11.15): `not and or bool=?` `= != < <= > >=` `+ - * / %`
`sym=?`.

## flex sugar (Figure 11.2, 11.21, 11.24)

A program has the form

```
(flex ((I T)*) Ebody (def-type τ T)* (def I T E)*)
```

with the body expression **second**, and all `def-type` items before all
`def` items (enforced at parse time). The sugar:

```
(@O E*)                     ; primop sugar
(cond (T E)* (else E)?) (scand E*) (scor E*)
(set! I E) (begin E1 E2)    ; mutable variables / sequencing (Figure 11.21)
(list T E*)                 ; list construction sugar (Figure 11.24)
(let-type ((τ T)*) E)       ; simultaneous type abbreviation
(let-type* ((τ T)*) E)      ; sequential (nested) type abbreviation
```

plus the top-level forms:

```
(def I T E)                 ; value definition, declared type T
(def (Iproc Tret (I1 T1) … (In Tn)) E)   ; procedure-defining sugar
(def-type τ T)              ; type definition
```

The procedure sugar is converted at parse time to
`(def Iproc (-> (T1 … Tn) Tret) (abs ((I1 T1) … (In Tn)) E))`. The
`def`/`def-type` items desugar (Figure 11.2) to

```
(let StdLib (letrec defs body))
```

where `StdLib` binds a procedure for each of the 16 primops plus `true` and
`false` — that is why `(+ 1 4)` works in `flex` but is an unbound variable in
`flexk`.

## Semantics notes

- **Equirecursive type equivalence** (Figure 11.28) is used everywhere the
  book has an exact match (if-branches, arrow elimination, `the`, letrec
  declared types, oneof payload vs tag, tagcase clause results, `:=`,
  `cell=?`): a two-finger step-through with an assumption set of types
  already judged equal; `recordof`/`oneof` are permutation-insensitive;
  `trec`/`tletrec` pointers are followed with a cycle guard. This is what
  makes the book's Figure 11.26 chain
  `(the Tib1 (the Tib2 (the Tib3 (the Tib4 …))))` type-check.
- **Substitution** (Section 11.4.4 / Figure 11.3) is simultaneous for
  `let-type` and *sequential* for `let-type*` (the last def-type is the
  innermost, so its substitution is applied first).
- A `cond` without branches and without `else` desugars to a `unit`-typed
  `error`, so a `cond` whose branches do not all match `unit` is a type
  error — the typed counterpart of FL's runtime error.

## Book examples (all in `FlexSpec.scala`)

- the `let-type*` example, p.635
- `pos?`/`even?` with `def-type` + `def`, p.636 → program type
  `(=> (bool int) bool)`
- the `shape` oneof + `perim`/`scale`, p.682–684
- `map-shape-int` (recursive list processing), p.687
- the int-tree `trec` def-type, Figure 12.15
- `Tib1`–`Tib4`, Figure 11.26 (equirecursive equivalence)
- the self-applicable procedure of Exercise 11.24

## Build & test

```bash
mill flex.test
```
