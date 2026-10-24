# FLAVAR — FL And mutable VARiables

FLAVAR (Chapter 8 of the book) is a dialect of [`flic`](../flic/) in which
**every variable is a mutable location**, in addition to the (orthogonal)
mutable cells. It is presented in two stages:

- **FLAVARK** (Figure 8.24) — the kernel: FLICK plus one new construct,
  `(set! I E)` (variable assignment).
- **FLAVAR** — the kernel plus all of FL's sugar (as in FLIC, Figure 8.9).

The principal feature of FLAVARK is that variables, like mutable cells, are
represented as **locations in the store**: an environment binding associates a
name `I` with a location, and the location holds the current value. The
indirection allows the value associated with a name to be changed.

## Concrete syntax

```
program      ::= ( flavark <formals> expr )         ; FLAVARK
               | ( flavar  <formals> expr <def>* ) ; FLAVAR
expr (new)   ::= ( set! <ident> <expr> )           ; variable assignment
```

Everything else (cells, `begin`, `while`, `let`, `letrec`, the `@`-primops,
…) is exactly as in FLIC. The `@` prefix for primitive operators is FL's
convention (the book's examples are written in a looser bare-operator style;
the strict `@`-style is what this implementation parses).

> **`set!` vs `:=`.** `:=` changes the content of a *first-class cell*
> (its target is an expression that evaluates to a cell); `set!` changes the
> value of a *variable* (its target must be an identifier visible in the
> current scope). They are orthogonal: FLAVAR has both.

## Semantics

`DSL.flavar.Evaluator` gives a reference big-step, call-by-value,
lexical-scope semantics:

1. `DSL.flavar.Desugar` removes the FLAVAR/FLIC/FL sugar. Notably,
   **`letrec` desugars per Figure 8.25** — it is *not* native, as in FL/FLIC:
   `(letrec ((Ii Ei)…) Ebody) ⇝ (let ((Ii #u)…) (begin (set! I1 E1) … Ebody))`.
   Each `set!` right-hand side is evaluated in an environment where all the
   bound names already exist (seeded with `unit`), so mutually-recursive
   definitions read the locations that earlier `set!`s have filled.
2. The evaluator runs over a **Box-based environment**: every name is bound to
   a `VarBox` (a one-slot location). Reading a variable (`Var`) fetches the
   box's current value (late binding); `set!` writes into the box and yields
   `unit` (an error if the name is not bound).
3. **Parameter passing is call-by-value** (Figure 8.26): an application
   allocates a fresh location for the formal parameter, seeded with the
   argument value. Closures capture the environment (the map of names to
   locations), so a closed-over variable reflects later mutations.

Mutable cells (`cell`, `^`, `:=`, `cell=?`, `cell?`) behave exactly as in
FLIC and are independent of variable mutation.

## Examples

```
(flavar () (let ((a 3)) (list a (set! a 4) a)))
    ; => (3, unit, 4)                    (book, p.430)

(flavar () (let ((n 1))
            (let ((incr (lam _ (begin (set! n (@+ n 1)) n))))
              (list (app incr #u) (app incr #u) n))))
    ; => (2, (3, (3, unit)))  — one location n, shared by the closure

(flavar (n) (letrec ((even? (lam k (if (@= k 0) #t (odd? (@- k 1)))))
                     (odd?  (lam k (if (@= k 0) #f (even? (@- k 1))))))
               (app even? n)))
    ; with 10 => true ; with 7 => false  (mutual recursion via Figure 8.25)
```

## Build & test

```bash
mill flavar.test
```
