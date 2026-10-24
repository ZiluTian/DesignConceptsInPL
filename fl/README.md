# FL — Functional Language

FL is the book's core functional language (Chapter 6). It is a kernel language
— **FLK** (Figure 6.1) — extended with **syntactic sugar** (Figure 6.3) that is
removed by the desugaring function **DS** (Figure 6.4). Everything else in the
book's static- and dynamic-semantics chapters builds on FL, so this is the most
capable module in the family.

## FLK kernel (Figure 6.1)

A program has the form `(flk (I…) Ebody)`. Expressions:

```
L            ::= #u | #t | #f | N | (sym Y)      ; unit / bool / int / symbol
I            ::= identifier                       ; variable reference
(error Y)     ; signal an error
(if E E E)    ; conditional
(prim O E…)   ; primitive application (O ∈ Figure 6.2)
(lam I E)     ; abstraction (exactly one formal parameter)
(app E E)     ; application
(pair E E)    ; pair creation
(rec I E)     ; simple (named) recursion
```

The 24 primitive operators (Figure 6.2) are: the type predicates
`unit? bool? int? sym? proc? pair?`, the boolean `not` / `and` / `or` /
`bool=?`, the integer arithmetic `+ - * / %` and comparisons `= != < <= > >=`,
the symbol test `sym=?`, and the pair selectors `fst snd`.

## FL sugar (Figure 6.3)

A program has the form `(fl (I…) Ebody D*)`. On top of the kernel, FL adds:

| Construct | Meaning | Desugars to |
|-----------|---------|-------------|
| `(@O E…)` | abbreviated primitive application | `(prim O E…)` |
| `(abs (I…) E)` | multi-parameter abstraction | nested `(lam …)` |
| `(E E…)` | tagless multi-application | nested `(app …)` |
| `(list E…)` | a unit-terminated chain of pairs | nested `(pair …)` |
| `(quote SX)` | a quoted s-expression value | `sym` / literals / `list` |
| `(cond …)` | n-way conditional | nested `(if …)` |
| `(scand E…)` / `(scor E…)` | short-circuit and / or | nested `(if …)` |
| `(let ((I E)…) E)` | local binding | `((abs (I…) E) E…)` |
| `(letrec ((I E)…) E)` | mutually-recursive binding | *(native — see below)* |
| `(recur I ((I E)…) E)` | recursive function call | `(letrec …)` |
| `(def I E)` / `(def (Iproc Iformal) E)` | top-level value / function definition | program-level binding |

## Semantics

`DSL.fl.Evaluator` gives a reference big-step, call-by-value, lexical-scope
semantics:

1. `Desugar` maps an FL expression to the FLK kernel (the book's DS function,
   Figure 6.4).
2. The kernel evaluator evaluates the result, producing a `Val(value)` or an
   `Err(message)`.

Values are `unit`, booleans, integers, symbols, **pairs**, and **procedures**
(first-class closures). `rec`, `letrec`, and top-level `def` support
self/mutual recursion through a shared live environment.

> **Note on `letrec`:** the book desugars `letrec` to a Church-tuple encoding
> (Figure 6.4). This reference implementation instead supports `letrec`
> natively in the evaluator (with true mutual recursion), which is
> behaviourally equivalent and clearer. All other sugar is desugared exactly as
> in the book.

A program is run with `flRun(text, args*)` (or `FlProgram(text)` for the AST,
then `Evaluator.run`). `None`-style failures are represented as `Err(msg)`.

## Examples

```
(fl (x y) (@+ x y))                       with 3, 4  ; => 7
(fl () (app (app (lam a (lam b (@+ a b))) 1) 2))     ; => 3  (currying)
(fl (n) (app (rec fact (lam m (if (@= m 0) 1
             (@* m (app fact (@- m 1)))))) n))       with 5  ; => 120
(fl () (list 1 2 3))                              ; => (1, (2, (3, unit)))
(fl (x) (cond ((@> x 0) 1) ((@< x 0) -1) (else 0)))  with -3  ; => -1
```

## Build & test

```bash
mill fl.test
```
