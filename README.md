# LeanMirror

Readable, executable mathematics with Lean-checked definitions, statements, and proof steps.

LeanMirror is a general Lean add-on for writing precise mathematical statements
in familiar language and notation, interpreting them as Lean propositions, and
checking their correspondence with established Lean theorems. It supplies the
language, its interpretation, presentation tools, and certificate machinery.
Subject-specific definitions and applications belong in downstream projects.

## Read the analysis companion

The first proof-document example follows selected passages of **Jiří Lebl’s
[Basic Analysis I, §2.1](https://github.com/jirilebl/ra/blob/e21ec524ca7d54f800c693b948020c188d21d01f/ch-seq-ser.tex)**:
sequence and convergence definitions, uniqueness of limits, and boundedness of
convergent sequences. It keeps the positive integer indices, epsilon/2 proof,
calculation chains, and finite-maximum argument. It does **not** certify the rest
of the textbook. The original source is pinned, licensed, and included for comparison.

```sh
lake exe cache get
npm ci
python scripts/mirror.py serve examples/analysis
```

Open `http://127.0.0.1:8766`. The reader compares the original and precise companion,
links notation to definitions, and lets you inspect proof obligations and mathlib
counterparts. All assets are local; after building, `build/analysis/index.html`
also works offline. `python scripts/mirror.py build` generates it without a server.

The editable, executable source is [Analysis.lean](LeanMirror/Examples/Analysis.lean).
The generated [LaTeX edition](examples/analysis/companion.tex) and
[document data](examples/analysis/document.mirror.json) come from its checked tree.
Change the Lean source and rebuild; do not edit generated formulas separately.

This is a working first version of the document engine, not an automatic translator
for arbitrary articles. The authoring interface is currently Lean plus a controlled
mathematical language. The browser is a reader, not yet a live proof editor.
See [authoring and extending documents](docs/documents.md).

## Classical examples

The [classical examples](LeanMirror/Examples/Classical.lean) connect these precise
statements, for arbitrary real numbers $x,y$, to actual mathlib proofs:

| Readable statement | Mathlib counterpart |
| --- | --- |
| $\lvert x+y\rvert\leq \lvert x\rvert+\lvert y\rvert$ | `abs_add_le` |
| $\lvert xy\rvert=\lvert x\rvert\lvert y\rvert$ | `abs_mul` |
| $2xy\leq x^2+y^2$ | `two_mul_le_add_sq` |

The last is the quadratic form of the arithmetic–geometric mean inequality.
It holds for every pair of real numbers, without nonnegativity assumptions.
The meaning of the square notation is explicitly related to mathlib's power
operation by a checked definition correspondence.

For example, the triangle inequality is written:

```lean
def triangleStatement : Expr Symbol [] .prop :=
  [math| |- Let x be realNumber. Let y be realNumber.
    \abs{x + y} \le \abs{x} + \abs{y}]
```

The target is obtained from the type of the actual mathlib proof, specialized to
real numbers:

```lean
def TriangleTarget : Prop :=
  statement_of% (fun x y : ℝ => abs_add_le x y)
```

Lean compiles a proof of `triangleStatement.eval model () ↔ TriangleTarget`.
A `Certificate` combines that correspondence with mathlib's proof. Its `proved`
theorem then establishes the interpreted companion statement. Each example's
correspondence unfolds definitions without invoking the result being transferred.
All definition bridges, correspondences, certificates, and resulting theorems are
audited for transitive axioms.

The [generated LaTeX companion](examples/classical.tex) presents the same
statements as ordinary mathematical theorems. Repeated binders render as familiar
sentences. Its formulas come from the typed expressions used in the proofs.

## Build and reproduce

With the toolchain in `lean-toolchain` installed:

```sh
lake exe cache get
lake build
python scripts/classical.py
python scripts/classical.py --check
npm ci
npm test
python -m unittest discover -s tests
python scripts/mirror.py check examples/analysis
```

The exporter first builds the checked examples. `--check` rejects stale or
manually altered output. CI builds the library, generic tests, and examples,
then checks that the generated companion and dependency pins are unchanged.
`LAKE` may specify an explicit `lake` executable.

## Use in another Lean project

Add a pinned dependency to `lakefile.toml`:

```toml
[[require]]
name = "lean-mirror"
git = "https://github.com/Corrram/lean-mirror.git"
rev = "<full reviewed commit SHA>"
```

Then `import LeanMirror`. The package uses Lean 4.34.0 and the exact mathlib
revision recorded in its dependency manifest.

## Architecture

| Module | Responsibility |
| --- | --- |
| `Core` | Typed expressions, scoped variables, mathematical interpretation, certificates |
| `Notation` | Controlled language elaborating into typed expressions |
| `Latex` | Mathematical rendering and minimal definition closure |
| `Presentation` | Structured presentation data and definition links |
| `Document` | Scoped proof trees, node obligations, generic soundness theorem, audited export |
| `DocumentNotation` | Readable `Fix`, `Assume`, `Choose`, `Have`, `Suffices`, `Conclude` syntax |
| `Audit` | Extract theorem types and reject nonstandard transitive axioms |
| `Tests` | Scope, interpretation, certificate, and definition-closure checks |
| `Examples.Classical` | Independent classical examples connected to mathlib |

An application supplies named base types, a typed vocabulary, an interpretation,
and notation. Definitions and statements share the same expression language.
Definition bridges relate the chosen meanings to a target library. A statement
correspondence is an ordinary Lean proof, checked by Lean's kernel.

`statement_of% theoremName` extracts the type of an existing theorem declaration.
`statement_of% (proofTerm)` extracts the proposition proved by a specialized
proof, allowing direct use of polymorphic mathlib theorems. The latter rejects
non-proofs and unresolved expression metavariables.

## Current language

- Named typed symbols such as `\square(x)`.
- Scoped variables, natural-number literals, and parentheses.
- Real addition, subtraction, multiplication, fractions, and absolute values.
- Lebesgue integration over `[0,1]`: `\int_{0}^{1}{u}{body}`.
- Explicit interval-to-real inclusion: `\real{u}`.
- Universal/existential quantifiers, strict order `<`, equality, `\le`, `\land`, `\implies`, and `\iff`.
- `Let x be predicate. statement`, interpreted as universal quantification with
  that predicate as a hypothesis; binders may be nested.

In `[math| x, y |- expression]`, external names are listed oldest first; the
internal typed context is newest first. Unknown symbols, unbound variables,
shadowing, mismatched context lengths, and ill-typed applications are errors.
The input is a controlled mathematical language, not unrestricted LaTeX.
Division and integration inherit mathlib's totalized semantics. Applications
must account for the conditions needed by their usual mathematical meanings.

## Extending the language

The goal is to support a broad range of precise mathematical language while
keeping the companion close to how mathematicians normally state results.
A new construction needs its typed syntax, mathematical interpretation, parsing,
rendering, and scope/precedence checks. New mathematical vocabulary needs explicit
meanings and definition correspondences. The companion's required definitions
form a dependency graph; missing definitions, duplicate identifiers, and cycles
are rejected.

Contributions to the core should apply across mathematical subjects. General
examples may use classical results from mathlib. Specialized theories and
individual research developments should remain in their own repositories.

## Trust boundary

Lean checks the interpreted propositions and proof terms. The allowed axioms
are `propext`, `Classical.choice`, and `Quot.sound`; unfinished proofs (`sorryAx`)
and additional axioms are rejected by `#assert_lean_mirror_axioms`.

The parser, notation metadata, primitive glossary, dependency metadata, and
renderers remain inspectable software and author-supplied data. They are not
proved correct in Lean. Sharing the syntax tree ties the interpretation and
presentation together, but a misleading notation function is still possible.
Recognizing the intended mathematics in the displayed statement and definitions
remains a human judgment.

Automatically interpreting unrestricted prose, proving the parser and renderer
correct, and extracting readable definitions from arbitrary Lean declarations
are future work. The rejection tests cover selected failure cases; they are not
a proof of frontend correctness.

LeanMirror’s generic code is licensed under Apache-2.0. The source-derived analysis
example is CC BY-SA 4.0; see [its attribution and license](examples/analysis/README.md).

The original-article renderer accepts `pageReferences`, a map from source labels
to positive printed PDF page numbers, for `\pageref`. Inspect the pinned PDF
when supplying this map: HTML flow does not determine printed pagination.
Missing or unused page entries fail rendering. Unnumbered proof labels retain
clickable anchors, and small-cap and underlined prose retain their styling.
