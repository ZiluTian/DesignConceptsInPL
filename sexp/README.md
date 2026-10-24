# S‑Expression

The syntactic foundation of the whole family (Ch. 2). Every other language in
this repository represents its programs as **s‑expression trees** built from the
base types defined here, and parses the book's s‑expression concrete syntax with
the parser here.

## The three base types

| Type               | Role                                        |
|--------------------|-------------------------------------------|
| `SPTree`           | Common supertype of every AST node.       |
| `SymbolicToken`    | A **leaf**: a single token (a value).     |
| `INode`            | An **interior node**: a parenthesized list of child `SPTree`s. |
| `PhraseTag`        | A `SymbolicToken` that is a keyword (e.g. `if`, `arg`, `el`). |

Every node carries a `label` (its syntactic domain) and an optional
`edgeLabel` (the role of a child, e.g. `num_args`, `body`).

## Parsing

`DSL.sexp.SParser` is a `RegexParsers` grammar. A token is any run of
non‑whitespace, non‑parenthesis characters; an `INode` is `(` `<node>*` `)`.
`DSL.sexp.SExpression.apply(text)` returns `Some(tree)` or `None` (malformed /
unbalanced parentheses).

## Visiting & printing

`SPTreeVisitor` is a simple visitor interface. `PrintTree` renders a tree with
one node per indented line — `(SToken …)` for leaves and `INode` for interior
nodes. The `show` extension on `SPTree` prints a tree to stdout.

## Example

```scala
import DSL.sexp._

val t = SExpression("(if (= (arg 1) 3) (arg 2) 4)").get
t.show()
// INode
//     INode
//         (SToken =)
//         INode
//             (SToken arg)
//             (SToken 1)
//         (SToken 3)
//     (SToken if)
//     INode
//         (SToken arg)
//         (SToken 2)
//     (SToken 4)
```

## Build & test

```bash
mill sexp.test
```
