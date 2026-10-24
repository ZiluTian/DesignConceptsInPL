# PostFix

A simple stack language, used in the book to introduce syntax, semantics, and
pragmatics (§1.4). A PostFix program manipulates an **implicit stack of
integers**: commands are executed left‑to‑right, each popping and/or pushing
values.

## Concrete syntax

A program is a parenthesized sequence:

```
program      ::= ( postfix <num-args> command* )
command      ::= <integer>
              | add | sub | mul | div | rem
              | eq  | lt  | gt
              | pop | swap | sel | nget | exec
              | ( command* )          ; an executable sequence
```

`<num-args>` is the number of integer arguments the program takes; they are
pushed onto the stack at the start, **the first argument on top**.

| command | effect (top of stack first)            |
|---------|---------------------------------------|
| `add`   | pop two, push their sum               |
| `sub`   | pop two, push `second − first`        |
| `mul`   | pop two, push their product           |
| `div`   | pop two, push integer quotient (÷0 ⇒ error) |
| `rem`   | pop two, push remainder (mod 0 ⇒ error)   |
| `eq`/`lt`/`gt` | pop two, push `1` if true else `0` |
| `pop`   | discard the top value                 |
| `swap`  | exchange the top two values           |
| `sel`   | pop `c, b, a`; push `a` if `c≠0` else `b` |
| `nget`  | pop index `i`; copy the `i`‑th (1‑based) stack element to the top |
| `exec`  | pop an executable sequence and splice its commands ahead of the rest |

## Semantics

Execution is a left‑to‑right pass over the command list on an integer stack.
A program **errors** when any of these hold: a command needs more values than
are on the stack, a division/modulo by zero occurs, the final stack is empty, or
the top of the final stack is not an integer. `DSL.postfix.PostfixProgram#run`
returns `Some(n)` for a successful result or `None` for an error.

## Examples

```
(postfix 0 4 7 sub)                 ; => -3
(postfix 1 3 div)   with arg 17     ; => 5
(postfix 1 1 nget mul) with arg 11  ; => 121  (square)
(postfix 1 (2 mul) exec) with 7     ; => 14
(postfix 1 1 nget 0 lt (0 swap sub) () sel exec) with -7 ; => 7 (abs)
```

## Build & test

```bash
mill postfix.test
```
