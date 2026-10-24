# FLIC — FL Including mutable Cells

FLIC (Chapter 8 of the book) extends [`fl`](../fl/) with **mutable cells**, the
simplest form of mutable data: a one-slot container whose content can change
over time. It is presented in two stages:

- **FLICK** (Figure 8.8) — the kernel: FLK plus
  `(cell E)` (cell creation), `(begin E1 E2)` (simple sequencing), and four
  new primitive operators `^` (fetch), `:=` (store), `cell=?` (identity),
  `cell?` (predicate).
- **FLIC** (Figure 8.9) — the kernel plus all of FL's sugar, plus new sugar:
  extended sequencing `(begin E*)`, elseless `if` `(if Etest Ethen)`, and
  the `while` loop `(while Etest Ebody)`.

Cells are first-class values (written `loc$val` in the book): they can be
created, passed to procedures, stored in pairs, and compared for identity.

## Concrete syntax

```
program      ::= ( flick <formals> expr )          ; FLICK
               | ( flic  <formals> expr <def>* )   ; FLIC
expr (new)   ::= ( cell <expr> )                   ; allocate a cell
               | ( begin <expr>* )                 ; sequencing
               | ( while <test> <body> )           ; loop
               | ( if <test> <then> )              ; elseless if
primops      ::= @^ E            ; fetch content
               | @:= Ecell Eval  ; store; yields unit
               | @cell=? E1 E2   ; same cell?
               | @cell? E        ; is it a cell?
```

(The `@` prefix for primitive operators is FL's convention — the book's
p.400 examples are written in a looser bare-operator style; the strict
`@`-style is what this implementation parses.)

## Semantics

`DSL.flic.Evaluator` gives a reference big-step, call-by-value,
lexical-scope semantics (CBV is the book's default strategy for stateful
languages):

1. `DSL.flic.Desugar` removes the FLIC/FL sugar (Figure 8.9 + Figure 6.4).
   `while` desugars exactly as in the book, via a fresh local recursive
   procedure:
   `(while Etest Ebody) ⇝ (letrec ((Iloop (abs () (if Etest (begin Ebody (Iloop)) #u)))) (Iloop))`
2. The FLICK kernel evaluator runs over a shared lexical environment; cells
   are heap objects whose content may change, so a procedure's closure sees
   the current (late) content whenever it fetches a cell it captured.

Errors: fetching/storing/identity-testing a non-cell signals
`error:not-a-cell` (the book's wording); all other errors are as in FL.

## Examples

```
(flic () (let ((c (cell 1))) (list (@^ c) (@:= c 4) (@^ c))))
    ; => (1, unit, 4)                       (book, p.398)

(flic (n) (let ((num (cell n)) (ans (cell 1)))
           (begin (while (@> (@^ num) 0)
                    (begin (@:= ans (@* (@^ num) (@^ ans)))
                           (@:= num (@- (@^ num) 1))))
                  (@^ ans))))
    ; iterative factorial; with 5 => 120     (book, p.400)
```

## Build & test

```bash
mill flic.test
```
