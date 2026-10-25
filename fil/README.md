# FIL — Functional Intermediate Language

FIL (Section 17.7 of the book) is the intermediate language of the Tortoise
transformation-based compiler: a **stateful**, call-by-value, statically
scoped, function-oriented language into which typed source languages (FLARE,
FLARE/V, ...) are translated. Multi-argument abstractions and applications are
kernel forms (as in FLARE), but — unlike FLARE — a FIL application carries an
explicit `app` keyword.

FIL has no formal type system (page 1035): type and effect information is
assumed to be *preserved* by the translation but is not described in FIL. The
reference semantics of this module is therefore a **big-step evaluator**
(`eval.scala`) rather than a type checker, mirroring the FL/FLIC/FLAVAR
modules.

## Kernel grammar (Figure 17.14)

```
P ∈ ProgFIL ::= (fil (Iformal*) Ebody)
E ∈ ExpFIL  ::= L | I | (error Ymessage)
            | (if Etest Ethen Eelse)
            | (prim Oprimop Earg*)
            | (abs (Iformal*) Ebody)
            | (app Erator Erand*)
            | (let ((Iname Edefn)*) Ebody)
L ∈ LitFIL  ::= #u | B | N | (sym Y)
```

Notable differences from FLARE:

- **no `letrec` and no `set!`** — the "knot-tying" of recursion is performed
  by storing closures in the slots of mutable products (the letrec
  translation, below);
- **no cells and no pairs** — both are represented as mutable products
  (footnote 4, page 1032): a cell is a one-slot product, a pair a two-slot one;
- **all valid FIL programs are closed** — there are no globally bound
  standard identifiers.

### Primitive operators

The primop set is FLARE's arithmetic, relational, logical, and list primops
(`+ - * / %  = != < <= > >=  not and or  bool=? sym=?  null null? cons car
cdr`) plus the **mutable-product** operators:

```
mprod      (mprod E*)          — a fresh product, one slot per argument
(mget J)   (prim (mget J) Emp) — read slot J (1-based); J is a literal
(mset! J)  (prim (mset! J) Emp Enew) — write slot J; yields unit
mprod=?    (mprod=? E1 E2)    — true iff E1 and E2 are the same location
```

The index `J` of the indexed operators is **part of the operator name** (a
positive integer literal, page 1031), which is why the book writes
`(prim (mget Jindex) Emp)` rather than `(prim mget Eindex Emp)`. The parser
enforces the literalness of `J`; `mget 0`, a variable index, or a missing
index are parse errors.

### Syntactic sugar

```
(@O E*)    — abbreviation for (prim O E*) (base and indexed operators:
             (@mget J Emp), (@mset! J Emp Enew))
(let* ((I E)*) E)  — a sequence of nested single-binding lets
```

There is a **single program tag**: `(fil (Iformal*) Ebody)` — kernel and sugar
forms are both admitted in the body.

## Desugaring and the Figure 17.15 simplifications

Desugaring removes the sugar (`@`-operators → `prim`, `let*` → nested
single-binding `let`s). In addition, four simplification rules (Figure 17.15)
are performed **when FIL ASTs are constructed** — by the parser and by the
translation (`Translate`), both of which route their output through
`DSL.fil.Desugar`:

```
(let () E)                    -> E                     [empty-let]
(app (abs (I*) E) E1* ... En*) -> (let ((I1 E1) ... (In En*)) E)   [implicit-let]
(abs (I*) (app Erator I*))    -> Erator                [eta]
let Erator is a variable or an abstraction, and
FrIds[Erator] ∩ {I1, ..., In} = {}
(let ((I I')) E)              -> [I'/I]E               [copy-prop]
with capture-free substitution
```

The rules are **not confluent**: the book's `Eambig` example,
`(app (abs (I) (app Irator I)) E)` with `I ≠ Irator`, can simplify either to
`(let ((I E)) (app Irator I))` (via `[implicit-let]` on the outer app) or to
`(app Irator E)` (via `[eta]` on the rator), and the two results do not in
general simplify to a common expression. The book resolves the ambiguity by a
**bottom-up** application discipline — a rule may be applied to an expression
only if no rule applies to any of its subexpressions — so `Eambig`
unambiguously simplifies to `(app Irator E)`. `Desugar.simp` implements
exactly that: simplify the children (to fixpoint), then try the rules at this
node, then re-simplify the result. The process terminates because every rule
application removes a `let`, an `abs`, or an `app`.

`[copy-prop]` is safe in FIL precisely because FIL has **no mutable
variables** (page 1033; Exercise 17.7 shows it is unsafe in a language with
assignments, where an assignment to `I` or `I'` can alias).

## Evaluation semantics (`eval.scala`)

A reference big-step, call-by-value, lexical-scope semantics:

- subexpressions of an `app`, the arguments of a `prim`, and the definition
  expressions of a `let` are evaluated **left to right** (page 1035);
- a `let` is a **parallel** binding: the definitions are evaluated in the
  surrounding environment (a definition cannot refer to a let-bound name),
  and the body sees all of the bindings;
- `mget` / `mset!` are 1-based and bounds-checked; `mprod=?` compares store
  locations;
- dynamic type errors (a non-boolean `if` test, non-integer arithmetic,
  divide-by-zero, an out-of-range `mget`, an arity mismatch, an unbound
  variable) are reported as `Err(message)`, mirroring the FL evaluator.

A program is run with `filRun(text, args*)` or `FilProgram(text)` +
`Evaluator.run`.

## The FLARE-to-FIL translation (Figure 17.16, `Translate.scala`)

`Tprog` and `Texp` translate a kernel FLARE program into a FIL program.
**Precondition:** the input is a valid, **closed, assignment-free** kernel
FLARE program — the output of the desugaring stage after the
assignment-conversion stage has run (`set!` has no `Texp` case; the
assignment conversion — turning every name assigned via `set!` into a cell —
is documented as an out-of-scope pre-stage). The translation is structural
except for:

1. `Tprog` changes the program tag from `flarek` to `fil`;
2. `Texp` adds the explicit `app` keyword to applications:
   `(Erator E1 ... En)  ->  (app Texp[Erator] (Texp[Ei])*)`;
3. `Texp` transforms each `letrec` into a `let` that binds each name to a
   one-slot mutable product (a cell) and rewrites every reference to a
   letrec-bound name `I` through `(mget 1) I`:

   ```
   (letrec ((I1 E1) ... (In En)) Ebody)
     -> (let ((I1 (prim mprod #u)) ... (In (prim mprod #u)))
            (let* (($_i (prim (mset! 1) Ii (msubst Texp[Ei])))* )
               (msubst Texp[Ebody]))),
        where msubst E = ([(prim (mget 1) Ii)/Ii]*)E
   ```

   One rule that performs three conceptually distinct steps (page 1037):
   (1) the FLAVAR letrec desugaring (bind each name to `#u` and set the
   definition expression into it), (2) the assignment conversion (turn the
   mutable names into cells), and (3) the representation of those cells as
   one-slot mutable products. Step 1 is not well-typedness-preserving as a
   FLARE/V-to-FLARE/V transformation — one of several cases that is simpler
   to express in FIL, without a formal type system, which is the main reason
   the compiler uses FIL;
4. `Texp` translates FLARE's cells and immutable pairs to FIL mutable
   products:

   ```
   (prim cell E)     -> (prim mprod Texp[E])
   (prim ^ E)        -> (prim (mget 1) Texp[E])
   (prim := E Enew)  -> (prim (mset! 1) Texp[E] Texp[Enew])
   (prim cell=? E E) -> (prim mprod=? Texp[E1] Texp[E2])
   (prim pair E E)   -> (prim mprod Texp[E1] Texp[E2])
   (prim fst E)      -> (prim (mget 1) Texp[E])
   (prim snd E)      -> (prim (mget 2) Texp[E])
   ```

The output is run through `Desugar`, so the result never contains the trivial
lets / eta-expandable abstractions the translation can introduce.
`Translate.translate(input)` parses a `flarek` program (desugared) or a
`flare` program (the full-FLARE program desugaring, Figure 13.23 — the
standard-library wrapper and the top-level defs become explicit letrecs,
exactly as the book's desugaring + globalization produce before the
Translation) and returns the FIL program.

## Entry point and tests

`filRun(input, args*)` parses and runs a FIL program. `FilSpec.scala`
(49 tests) covers:

- parsing: the `fil` tag; `@`-sugar (base and indexed operators); the
  parenthesized `(prim (mget J) ...)` form; `let*` desugaring to nested
  single-binding lets; rejection of a wrong tag, a keyword in a binding
  position, an `@`-prefixed formal, a non-literal index, a missing index,
  and an unknown operator;
- the Figure 17.15 simplifications: `[empty-let]`, `[implicit-let]`,
  `[copy-prop]` (including the capture-avoiding rename), `[eta]` (including
  the FrIds side-condition negative case and the abstraction-rator case), the
  `Eambig` bottom-up resolution, and the book's own example
  `(abs (a) (app (abs (b) (+ a b)) a))` → `(abs (a) (+ a a))`;
- the evaluator: multi-formal closures, `mprod`/`mget`/`mset!`/`mprod=?`,
  parallel-let semantics (a sibling reference is a runtime error; left-to-right
  definition evaluation), list construction, `if` branching, and dynamic
  errors (type errors, divide-by-zero, out-of-range `mget`, unbound variables,
  arity mismatches in both directions, `error` expressions);
- the translation: the explicit-`app` mapping, the seven cell/pair primop
  mappings, the letrec → mutable-product encoding (structure: top `let` binds
  the name to `(mprod #u)`; no `LetRec` remains; behavior preserved), the
  factorial and revmap examples (page 1037: revmap's type after translation is
  `(=> (int int) (listof bool))`), a sugared FLARE program through the
  standard-library wrapper, the `flarek` → `fil` tag change, and rejection of
  non-FLARE input.

## Build & test

```bash
mill fil.test
```
