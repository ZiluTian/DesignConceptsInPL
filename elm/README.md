# ELM — EL Minus

ELM ("EL Minus") is **ELMM extended with indexed references to program
inputs** — it is EL without conditionals and boolean expressions
(Exercise 3.10a of the book). Compared with [`elmm`](../elmm/), a program
declares how many arguments it takes and its numerical expressions may read
them with `(arg N)` (indices start at 1).

## Concrete syntax

```
program      ::= ( elm <num-args> num-exp )
num-exp      ::= <int>
              | ( arg <index> )
              | ( <arith-op> num-exp num-exp )   ; binary
arith-op     ::= + | - | * | / | %
```

`<num-args>` is the number of integer arguments the program expects.

## Abstract syntax

Defined in `AST.scala` over the [`sexp`](../sexp/) base types:

- `NumExp`: `IntLit`, `Input` (`(arg N)`), and the binary
  `ArithmeticOperation`.
- `Program(num_args, body)` ties a program to its argument count and body.

## Semantics

`DSL.elm.Evaluator` gives a reference big-step semantics. A program is run
with `elmRun(text, args*)` (or `ELMProgram(text).get` for the AST, then
`Evaluator.eval(body, env)`). Evaluation is deterministic; it returns `None`
on a division/modulo by zero, when a referenced argument was not supplied, or
when the number of supplied arguments does not match the declared count.

## Examples

```
(elm 2 (+ (arg 1) (arg 2)))      with 3, 4   ; => 7
(elm 1 (* (arg 1) (arg 1)))      with 11     ; => 121  (square)
(elm 2 (- (* (arg 1) (arg 2)) (+ (arg 1) (arg 2)))) with 6, 3 ; => 9
```

## Build & test

```bash
mill elm.test
```
