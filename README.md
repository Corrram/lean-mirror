# LeanMirror

Readable mathematics with Lean-checked correspondence.

Write a mathematical statement in a small controlled language, interpret it as
a Lean proposition, render that same syntax tree as LaTeX, and prove its
correspondence with an existing Lean theorem. LeanMirror applies to mathematical
definitions and theorems in general. The library contains no copula definitions
or imports from this repository's papers.

The first application is the universal Blest--Spearman inequality from
[Rockel, arXiv:2609.27634v1, Corollary 3.2](https://arxiv.org/abs/2609.27634v1):

```lean
def articleStatement : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. \abs{\nu(C) - \rho(C)} \le \frac{1}{4}]
```

The resulting page says “Let C be a bivariate copula. Then ...” and displays
the familiar inequality. Its definition section contains just the statement's
definition closure, ending at an explicit probability-theory foundation.
Sharpness and the equality classification are **not** part of this prototype.

## Try the copula companion in lean-verifications

In a checkout of [lean-verifications](https://github.com/Corrram/lean-verifications), with the pinned Lean toolchain installed:

```sh
python scripts/lean_mirror.py
python scripts/lean_mirror.py --check
python scripts/test_lean_mirror.py
```

The first command builds the certificate and exports
[`blest-bound.tex`](https://github.com/Corrram/lean-verifications/blob/main/examples/paper-bridge/blest-bound.tex) and
[`blest-bound.json`](https://github.com/Corrram/lean-verifications/blob/main/examples/paper-bridge/blest-bound.json), the presentation
data used by the website's clickable mathematical companion.
The second rejects a stale or manually changed presentation. The third checks
that malformed input, statement/definition changes, and untrusted proofs fail.
`LAKE` may specify an explicit `lake` executable if needed.

Open the `.tex` file in a LaTeX editor, or compile it with a normal LaTeX engine.
It is self-contained and uses only common packages. The generated file is an
artifact, not an independently maintained mathematical source.

## What the example proves

The application is in
[`ArticleBridge.lean`](https://github.com/Corrram/lean-verifications/blob/main/Papers/Rockel2026ExactBlest/ArticleBridge.lean).
The article quantifies over probability laws on the unit square satisfying the
two displayed uniform-marginal conditions. The existing theorem quantifies over
the library's bundled `Copula 2` type.

1. `copula_definition_equiv` proves that the article predicate describes exactly
   laws represented by library copulas. The two conversion round trips are proved.
2. `cdf_definition_eq` identifies the displayed lower-rectangle probability with
   the library CDF; `cdf_rectangle_formula` checks its two coordinate inequalities.
3. `rho_definition_eq` and `nu_definition_eq` identify the displayed iterated
   integral definitions with the library coefficients. In particular, rho's
   library definition is a moment under the copula law; its article definition
   is an integral of the CDF with respect to Lebesgue measure.
4. `bound_correspondence` proves a pointwise equivalence for **every real bound**,
   using only those definition equalities.
5. `statement_equivalence` proves the universally quantified equivalence,
   without using the established bound. `statement_of%` obtains the target
   directly from the existing theorem's type.
6. `certificate` supplies the existing proof, and `article_verified` transfers it
   to the interpreted article statement.

All bridges, round trips, the certificate, and the final theorem are audited for
transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
There are no absolute-continuity restrictions: singular copulas are included.

## Reusable architecture

| Module | Responsibility |
| --- | --- |
| `Core` | Typed terms, scoped variables, mathematical interpretation, certificate |
| `Notation` | Controlled input grammar, elaborating into typed terms |
| `Latex` | LaTeX rendering and dependency closure, with cycle/missing-node rejection |
| `Audit` | Extract actual theorem types and reject nonstandard transitive axioms |
| `Presentation` | Derive structured theorem data and definition links from the same expressions |
| `Tests` | A separate real-arithmetic example, scope and dependency-closure checks |

`Expr Symbol context type` separates reusable operations from a subject's
vocabulary. A `Model` interprets named base types and typed symbols. A
`Vocabulary` assigns mathematical notation to those symbols. Applications define
their own indexed `Symbol` types, models, definitions, and bridges.

The example uses three symbol stages: probability primitives, CDF expressions,
and theorem expressions. Coefficient definitions cannot refer to themselves or
to the theorem because their symbol type does not permit it. This avoids
recursive or circular “definitions.” The document's dependency edges are derived
from the expression trees; proof dependencies are not included.

### Supported input

- Named typed symbols: `\rho(C)`, `\cdf(C,u,v)`.
- Explicitly scoped variables, natural-number literals, parentheses.
- Real addition, subtraction, multiplication, fractions, absolute values.
- Lebesgue integration on `[0,1]`:
  `\int_{0}^{1}{u}{body}`. The second brace delimits the entire integrand.
- Explicit interval-to-real inclusion: `\real{u}`.
- Equality, `\le`, `\land`, `\implies`, `\iff`.
- `Let x be predicate. statement`, interpreted as universal quantification
  with the predicate as a hypothesis, including nested binders.

Division and integration inherit mathlib's totalized semantics. Applications
must establish the conditions needed for their usual mathematical use; here the
copula CDFs are continuous and their displayed integrands are integrable.

In `[math| C, u, v |- expression]`, the external context names are listed oldest
first. Internally, the type-level context is newest first. Unknown symbols,
unbound names, shadowing, duplicate context names, and ill-typed applications
are errors. The brackets are Lean quotation delimiters; the contents are a
restricted mathematical language, not arbitrary LaTeX.

## Use as a separate Lean add-on

This directory is also a Lake package. In another compatible project's
`lakefile.toml`, add:

```toml
[[require]]
name = "lean-mirror"
git = "https://github.com/Corrram/lean-mirror.git"
rev = "<full commit SHA>"
```

Then `import LeanMirror`. The package requires only mathlib, pinned to the same
revision used by lean-verifications, and Lean 4.34.0. Pin a reviewed commit
when consuming the library. This repository contains the reusable language,
interpretation, presentation helpers, and certificate machinery; subject-specific
definitions and correspondence proofs belong in downstream projects.

To add another subject, define its base types, typed symbols, interpretation,
and notation; write its definitions and statement with `[math| ...]`; prove the
definition correspondences and theorem equivalence; then construct and audit a
`Certificate`. To extend the language, add a typed constructor, its semantics,
input syntax, rendering, and scope/precedence/rejection tests together.

## Precise trust boundary and limitations

Lean checks the interpreted propositions and the proofs. It does **not** certify
that an arbitrary human sentence, TeX macro, PDF, or rendered glyph has a given
meaning. The parser, symbol presentation, primitive glossary, dependency metadata,
and LaTeX renderer remain inspectable software and author-supplied data. They are
not themselves proved correct in Lean. Rendering never changes the expression
that is interpreted, but a misleading symbol-notation function is still possible.

The probability primitives are explicitly documented in the example. They are a
foundation boundary, not an attempt to recursively explain all of measure theory.
The paper's copula predicate, CDF, and two coefficients have checked bridges.
The CDF primitive uses `Fin 2 → I` for the unit square, with indices 0 and 1
printed as coordinates 1 and 2.

The current LaTeX is generated from controlled input embedded in Lean. Importing
an existing unrestricted `.tex` paper, formally verifying parsing/rendering,
certifying that prose agrees with its intended meaning, and extracting definitions
automatically from arbitrary Lean declarations remain future work.

The ten adversarial tests demonstrate rejection of selected failure cases;
they are not a proof that every frontend or rendering defect is impossible.
The repository's Apache-2.0 license applies to this add-on.

## Build this library

```sh
lake exe cache get
lake build
```

The build includes a real-arithmetic example, a checked equivalence certificate,
binder-scope checks, and definition-dependency checks. CI compiles the same
sources with the pinned toolchain and rejects changed dependency pins.

## Language growth

The goal is to support increasingly rich, precise mathematical prose and LaTeX
while keeping familiar mathematical statements readable. Add constructions with
an explicit interpretation and extend parsing and rendering together. Every
application supplies Lean proofs of its definition correspondences and theorem
equivalence. Lean checks these proofs; LeanMirror does not introduce a second
proof checker. Automatically inferring author intent and proving the rendering
software correct are separate research tasks.
