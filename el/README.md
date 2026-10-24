# EL — Expression Language

EL is a small arithmetic/boolean expression language used to develop the
operational and denotational semantics in the book (§2.1, §4.2). A program
takes integer arguments and evaluates to an integer.

## Concrete syntax

```
program   ::= ( el <num-args> num-exp )
num-exp   ::= <int>
            | ( arg <index> )
            | ( <arith-op> num-exp num-exp num-exp* )   ; n-ary, left-associative
            | ( if bool-exp num-exp num-exp )
bool-exp  ::= true | false
            | ( <rel-op> num-exp num-exp )
            | ( <logic-op> bool-exp bool-exp )
arith-op  ::= + | - | * | / | %
rel-op    ::= = | < | >
logic-op  ::= and | or
```

`(arg i)` reads the `i`‑th (1‑based) program argument.

## Abstract syntax

Defined in `AST.scala` over the [`sexp`](../sexp/) base types:

- `NumExp`: `IntLit`, `Input`, `ArithmeticOperation` (n‑ary), `Conditional`
- `BoolExp`: `BoolLit`, `RelationalOperation`, `LogicalOperation`
- `Program(num_args, body)` ties a program to its argument count and body.

## Semantics

`DSL.el.Evaluator` gives a reference big‑step semantics. A program is run with
`elRun(text, args*)` (or `ELProgram(text).get` to get the AST, then
`Evaluator.eval`). Evaluation is deterministic; it returns `None` on a
division/modulo by zero or when a referenced argument was not supplied.

## Examples

```
(el 2 (+ (arg 1) (arg 2)))     with 3, 4    ; => 7
(el 2 (/ (arg 1) (arg 2)))     with 17, 3   ; => 5
(el 2 (if (= (arg 1) (arg 2)) 1 0)) with 5, 5 ; => 1
(el 1 (if (> (arg 1) 0) (arg 1) 0)) with -4  ; => 0
```

## Build & test

```bash
mill el.test
```
