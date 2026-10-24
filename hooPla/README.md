# HOOPLA — Humble Object-Oriented Programming Language

HOOPLA (Chapter 7, Section 7.3 of the book) is the book's object-oriented
language, designed by Jonathan Rees. It is presented in two stages:

- **HOOK** (Humble Object-Oriented Kernel, Figure 7.22) — messages, objects,
  and composition.
- **HOOPLA** (HOOK + syntactic sugar, Figure 7.23) — adds `object`, `class`,
  `abs`, tagless application, `let`, and `if`.

The principal idea is that **everything is an object**: integers, booleans,
and symbols are full-fledged message-passing objects (in the spirit of
Smalltalk, unlike Java/C++/C#, book p.363), and user objects are just tables
of message → method.

## Concrete syntax

```
program      ::= ( hook  <formals> expr <def>* )    ; HOOK's tag
               | ( hoopla <formals> expr <def>* )  ; HOOPLA's tag
def          ::= ( def <ident> expr )
expr (HOOK)  ::= ( method <msg> (<receiver> <formals>*) <expr> )   ; simple object
               | ( compose <expr> <expr> )                       ; composition
               | ( null-object )                                  ; no methods
               | ( send <msg> <receiver> <expr>* )                ; message send
               | <bool> | <int> | ( sym <lit> ) | <ident>
expr (sugar) ::= ( object <expr>* )                    ; compose any number
               | ( class <inits> <expr>* )             ; responds to `new`
               | ( abs <formals> <expr> )              ; responds to `call`
               | ( <rator> <expr>* )                   ; (send call <rator> …)
               | ( let (<name> <expr>)* <expr> )
               | ( if <test> <then> <else> )
```

Identifiers and messages cannot begin with `$` (reserved by the book's
HOOK-to-FL translation for `$val` / `$new-integer`, Figure 7.25). By
convention, `_` names an ignored receiver parameter.

## Semantics

The book defines HOOK's semantics by **translation into FL** (Figure 7.25):
an object is an FL record binding message names to procedures, `compose` is
record overriding (the first object's methods take precedence), and a `send`
is a method lookup + application. This module instead gives a **direct
reference evaluator** (`DSL.hooPla.Evaluator`) of the same semantics:

1. `DSL.hooPla.Desugar` removes the HOOPLA sugar per Figure 7.23.
2. The evaluator runs over a small runtime:
   - `IntObj` / `BoolObj` / `SymObj` — the built-in literal objects
     (integers respond to `+ - * / % = != < <= > >=`; booleans to
     `if-true not and or = !=` — `if-true` is the target of the desugaring
     of `if`; symbols to `= !=`; `=` / `!=` compare across kinds and return
     false/true on a kind mismatch, as in the book's `$new-integer`);
   - `UserObject` — a table of message → method, created by `method`,
     `compose`, or `null-object`.
3. A `send` evaluates the receiver and the arguments, looks up the method in
   the receiver's table, and invokes it. The **receiver parameter is bound
   to the whole receiver object** (the result of a compose, if the method
   came from a composed component) — this is what makes mixins and
   "inheritance" work (book p.368).
4. Top-level `def`s are installed sequentially into one shared environment,
   giving HOOK's **recursive top-level scope** (book p.373): a method body
   may reference a def installed before it — and, since bodies are evaluated
   at invocation time, even the def that created the method (this is how
   `point`'s `move` can call `(send new point …)`).

### Deviations from the book's translation (documented)

The direct evaluator is stricter in a few places the book's translation is
loose (the book itself flags these in Exercises 7.34/7.35):

- **Arity is checked**: a send whose argument count does not match the
  invoked method's formal parameters is an error (the translation does not
  flag this).
- **`compose` requires user objects**: composing a built-in (e.g.
  `(compose 3 (method side (_) 5))`) is an error here, whereas the
  translation would override the integer's record. No example in the book
  composes a built-in.
- **`$new-boolean` / `$new-symbol` are "left as an exercise"** in the book;
  this evaluator gives booleans `not and or = !=` (mirroring FL's boolean
  primops) and symbols `= !=`.

## Examples

```
; the book's square5 (p.365)
(hook () (send + (send side s5) (send area s5))
  (def s5 (compose (method side (_) 5)
                   (method area (_) 25))))
    ; => 30

; a class and an instance (p.369)
(hoopla () (send area (send new square 9))
  (def square (class (s)
                (method side (self) s)
                (method area (self)
                  (send * (send side self) (send side self))))))
    ; => 81

; colored turtles (Figure 7.24, p.370) — see HooPlaSpec
(hoopla () (send x t2)
  (def point (class (init-x init-y)
                (method x (self) init-x)
                (method y (self) init-y)
                (method move (self dx dy)
                  (object (send new point
                                (send + (send x self) dx)
                                (send + (send y self) dy))
                          self))))
  ...
  (def t1 (send new colored-turtle 0 0 0 (sym green)))
  (def t2 (send move (send turn t1 45) 17 23)))
    ; => 17
```

## Build & test

```bash
mill hooPla.test
```
