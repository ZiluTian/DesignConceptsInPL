# ELMM — EL Minus Minus

ELMM is the most restricted stage of the EL family, introduced in the book as
the simplest language to develop operational semantics on (§3.2.6, §4.2.3;
Figures 3.6–3.7). A program is a **single numerical expression** — there are
no program inputs, no boolean expressions, and no conditionals.

## Concrete syntax

```
program      ::= ( elmm num-exp )
num-exp      ::= <int>
              | ( <arith-op> num-exp num-exp )   ; binary
arith-op     ::= + | - | * | / | %
```

## Abstract syntax

Defined in `AST.scala` over the [`sexp`](../sexp/) base types:

- `NumExp`: `IntLit` (a leaf) and `ArithmeticOperation` (a binary interior
  node, matching the production `(Arator NE rand1 NE rand2)` in Figure 3.6).
- `Program(body)` ties a program to its single body expression (ELMM takes no
  arguments, so there is no `num_args` field, unlike `el`/`elm`).

## Semantics

`DSL.elmm.Evaluator` gives a reference big-step semantics (the transition
relation of Figure 3.7). A program is run with `elmmRun(text)` (or
`ELMMProgram(text).get` for the AST, then `Evaluator.eval`). Evaluation is
deterministic; it returns `None` on a division/modulo by zero.

## Examples

```
(elmm 5)                          ; => 5
(elmm (- 10 4))                  ; => 6
(elmm (+ (* (- 5 1) 2) (/ 21 7))) ; => 11   (book, Figure 3.9)
(elmm (/ 100 (* (- 7 4) (+ 5 6)))) ; => 3    (book, Figure 3.9)
```

## Build & test

```bash
mill elmm.test
```
