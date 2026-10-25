# FLARE/V — FLARE with Mutable Variables

FLARE/V (Section 17.2.2 of the book) is the source language of the Tortoise
compiler: full FLARE extended with **mutable variables** via the `set!`
construct (from FLAVAR, Section 8.4). It is a stateful, call-by-value,
statically scoped, statically typed language with type reconstruction,
supporting mutable cells, mutable variables, pairs, and homogeneous immutable
lists.

The *expressions* of FLARE/V are the FLARE expressions plus one new kernel
form — the assignment

```
(set! Ivar Eval)    — assign a new value to an in-scope variable Ivar
```

— so the module adds: one AST node (`SetBang`), a parser that recognizes the
`set!` keyword, a desugaring that passes `set!` through (it is a **kernel**
form, Figure 17.2), and a type checker with a `set!` rule and the soundness
restriction of Section 13.5.2 / Exercise 13.11. The type domain, program
node types, standard library, and display machinery are all reused from
`DSL.flare`.

## Programs

The book reuses the FLARE program tags for FLARE/V (footnote 1, p. 1009):

- `(flarek (Iformal*) Ebody)` — kernel: no sugar, no items, no standard
  library (a bare `+` is an unbound variable; use `(prim + 1 2)` or `(@+ 1 2)`).
- `(flare (Iformal*) Ebody (def I E)*)` — sugar: a body plus top-level `def`
  definitions, with the standard library opened around the program.

A program's type is displayed as in FLARE: the body type when there are no
formals, and `(=> (Targ*) Tresult)` otherwise, with free type identifiers
canonicalized to `T1, T2, ...` in first-appearance order.

## The `set!` type rule

A `set!` targets an **in-scope variable** — a formal, a `let` / `letrec`
binding, or a global (standard-library) name — and changes the *value* held
by that binding; it does not create a binding.

- the target must be bound (otherwise `unbound variable: <name>`);
- the value must have **exactly** the target's type (`Tvalue = Ttarget`);
- the result of the assignment is `unit`;
- the target must be **monomorphic**: assignment to a generic (polymorphic)
  schema is rejected with `cannot assign to a polymorphic variable: <name>`.
  With the soundness restriction below, every binding a `set!` can actually
  reach is already closed, so this branch is purely defensive — it guards the
  invariant rather than rejecting any program the restriction allows.

## The soundness restriction (Section 13.5.2, Exercise 13.11)

Just as it is unsound to generalize the type of a definition that touches the
store, it is unsound to **generalize the type of a definition whose associated
name is assigned via `set!` in its scope** (Section 13.5.2, consequence 1;
Exercise 13.11b–e). The generalization step (`rgenPureV`) therefore keeps a
definition monomorphic when it is impure (FLARE's value restriction, Figure
13.25) **or** when its name is assigned in the binding's scope. The
assignment set is computed by `findAssigned(e, name)` (cf. the `MutIds`
function, Figure 17.10), a scope-respecting walk: a `set!` targets the
*innermost* binding of its name, so

- an inner `Abs` / `Lam` / `LetRec` that rebinds the name **shadows** it
  (nothing in its subtree targets the enclosing binding);
- a parallel-`let` rebinds the name in its *body* but not in its own
  *definitions* (definitions see the outer environment), so a `set!` in an
  inner let's definitions still targets the enclosing binding;
- `letrec` definitions see all the letrec names (including their own), so a
  `set!` anywhere inside a letrec that binds the name targets the letrec's
  own binding.

This is exactly what rejects the Exercise 13.11b counterexample, which is
well typed under the original (unsound) rule but dynamically errors:

```
(let ((f (abs (x) x)))
  (begin (set! f (abs (y) (prim + y 1)))
         (if (f #t) 1 (f 2))))
```

Because `f` is assigned, it must stay monomorphic: `set!` unifies `f`'s type
with `(-> (int) int)`, so `(f #t)` has type `int` and the `if`'s test is not
a `bool` — the program is rejected. (Under the original rule `f` would be
generalized to `(generic (?v) (-> (?v) ?v))`, making the program well typed
as `int` while `(f #t)` evaluates to `(+ #t 1)` — a dynamic error.)

### Purity

FLARE's syntactic purity test (Figure 13.25) is reused as-is, with `SetBang`
impure. The book notes (Section 13.5.2, consequence 2) that in a stateful
language a variable reference is no longer *pure* in the general sense (it
reads the mutable store), and Exercise 13.11f–h explores the consequences of
a naive (all-`Var`-impure) purity versus a set-tracking one. The reference
FLARE/V system keeps FLARE's syntactic purity: assignment mutates *bindings*,
not *values*, so a let definition that is a variable reference keeps its
value no matter what the aliased variable is later set to, and generalizing
it remains sound. (Consequently the Exercise 13.11f program — which a naive
purity would reject — is accepted here, as it is in FLARE; Exercise 13.11h's
set-tracking refinement is a possible extension, not part of the reference
system.)

### Book vs. module: globalization

The book says FLARE/V's *desugaring* does **not** bind the standard
identifiers — that is done by the separate **globalization** compiler
transformation (Section 17.4) instead. For the type checker (this module's
reference static semantics) it is equivalent to open the standard library up
front, so the desugarer folds that step into the program wrapper (reusing
FLARE's stdlib), keeping the type system identical to FLARE's for every
program that does not use `set!`.

## Theorem: FLARE/V extends FLARE

A program **without** `set!` is typable in FLARE **if and only if** it is
typable in FLARE/V: the accept/reject decision — and, for accepted programs,
the displayed type — is identical (the `set!` rule and the restriction are
inactive). FLARE/V additionally accepts `set!` programs. A cross-check test
against `DSL.flare.flareRecon` locks this in on a representative battery of
well- and ill-typed programs.

## The running example (Figure 17.4)

The book's `revmap` program (p. 1011) exercises numbers, booleans, lists, a
locally defined recursive procedure (`recur`), a higher-order argument, and a
mutable variable:

```
(flare (a b)
  (let ((revmap (abs (f elts)
                  (let ((ans (null)))
                    (recur loop ((xs elts))
                      (if (null? xs)
                          ans
                          (begin (set! ans (cons (f (car xs)) ans))
                                 (loop (cdr xs)))))))))
    (revmap (abs (x) (> x b)) (list a (* a 7)))))
```

`ans` is a let-bound name assigned via `set!`, so the restriction keeps it
monomorphic; the program's type is `(=> (int int) (listof bool))`.

## Entry point and tests

`flareVRecon(input)` (in `check.scala`) parses a `flarek` / `flare` program
and returns `FlexOk(str)` or `FlexErr(msg)` (reusing the `DSL.flex` result
types). `FlareVSpec.scala` (21 tests) covers:

- parsing (a valid `set!` program; wrong arity; `set!` as a binding name);
- `set!` on a let variable, a formal, a standard-library name, and a top-level
  `def` name — each yielding `unit` / the program type;
- type-mismatch, unbound-target, and dead-branch `set!` rejections;
- the soundness restriction: the Ex 13.11b counterexample rejected, its
  corrected variant accepted; assignment through inner-let definitions and
  letrec definitions targeting the right binding; shadowing;
- `def` and `letrec` in sugar contexts;
- the Fig 17.4 revmap program → `(=> (int int) (listof bool))`;
- the extension theorem (accept/reject — and displayed types — agree with
  `DSL.flare.flareRecon` on every `set!`-free program; FLARE/V additionally
  accepts `set!` programs).

## Build & test

```bash
mill flare_v.test
```
