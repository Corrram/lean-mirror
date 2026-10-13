# Compiling the mathematical source

The source engine in `LeanMirror/Source` adds a second authoring route. The
editable mathematical statements, definitions and proof sentences live in `.tex`
files. The same source strings occur in their Lean certificates and in the reader.
No separately written `Expr` or presentation callback supplies their mathematics.

```sh
npm ci
python scripts/source.py build examples/source
python scripts/source.py check examples/source
python scripts/source.py serve examples/source
```

The build produces `build/source-source/index.html`, local fonts and styles,
the checked document data, the editable source files and an executable source
bundle. The sample includes two precise definitions, a triangle-inequality proof,
and an assertion of equality at every prescribed value of an interval, with
positive and negative witnesses. It is a generic real-analysis example, not a
verification of a particular copula theorem.

## The gap this closes

The original article reader attaches native theorem evidence to source passages.
That attachment alone proves no correspondence with the passage. The older
document engine checks a typed tree and generates a readable rendering; its
author-supplied presentation functions can differ from the mathematical meaning.

The new path consumes the actual companion text. `Source.parse` and
`Source.elaborate` are total Lean definitions. A certificate contains

```lean
compiled : Source.compile language source = .ok statement
correspondence : statement.eval model () ↔ target
established : target
```

`compiled` is a Lean proof about the complete source string. The generic theorem
`Certificate.source_equivalence` proves that the meaning of that source, as
defined by the language, is equivalent to the target. `Certificate.proved`
establishes that meaning. An alternative parser or an LLM may propose a term,
but cannot bypass these obligations. No native-decide axiom is needed.

This defines and checks a precise source language. It is not a theorem that all
of TeX, English, the browser or the conventions of an original author implement
that language. In particular, ordinary LaTeX is a typesetting language rather
than a pre-existing mathematical semantics against which this parser is proved
correct. Extending the grammar means extending its explicit language definition.

## Authoring

A downstream application supplies a typed `Language` and mathematical `Model`.
A symbol's spelling and definition key are registered once. A domain phrase can
refer to a registered predicate, such as “stochastically increasing bivariate
copula”. Its predicate must have the domain's argument type and definition key.
Primitive base types come from the model; new subject-specific foundations must
be documented and reviewed alongside their model interpretations.

```lean
def source := include_str "claim.tex"
def statement := source% (language) source
def Target : Prop := statement_of% existingTheorem

theorem checked : Source.Certificate model language source statement Target :=
  ⟨by source_check, correspondenceProof, existingTheorem⟩

def entry : Lean.Json := checked_source% checked
```

There is no hand-maintained copy of the formula in `statement`. `source%`
compiles the file's contents and reports unsupported text, scope and type errors.
Its native parsing driver proposes a syntax tree; the certificate independently
checks that tree against the original source. `source_check` discharges the
compilation equation by definitional equality in Lean's kernel.
The separate Lean proof establishes the correspondence with the target.

`DefinitionCertificate` additionally requires that the source is a defining
equality or equivalence for its designated symbol, universally quantified over
all arguments in order. Restricted-domain definitions, unused parameters and
direct recursive definitions are rejected. The reader requires the transitive
closure of checked definitions and rejects missing or cyclic dependencies.

`ProofCertificate` additionally compiles a proof source to `Argument`, checks
`Argument.Valid`, and connects its conclusion to both the source statement and
the target. Every `Have` and every existence claim has an obligation. A true
conclusion cannot justify a false intermediate step.

The exporter accepts only actual theorem declarations of these certificate
types, with the standard transitive axiom audit. The model and target remain in
the proof. Downloaded JSON is a view of a completed check, not a standalone proof.

## Supported source constructions

- Inline `\(...\)` and `$...$`, and displayed `\[...\]` mathematics, with checked
  delimiter matching. Comments and mathematical spacing commands are ignored.
- `Let \(x\) be a real number.` scopes over the following sentences.
- `If \(C\) is a domain phrase, then ...` quantifies over that domain; its scope
  ends at the end of that sentence. Separate sentences are conjoined.
- `If \(P\), then ...` is an implication in the existing context.
- `For every \(x\in\mathbb{R}\), ...` and
  `For every \(x\in[0,1]\), ...` introduce universal variables.
- `There exists a domain phrase \(x\) such that ...` introduces an existential
  variable with the domain predicate as a required condition.
- `\forall` and `\exists`, registered symbols, ordinary curried application
  such as `C(u,v)`, parentheses, natural-number literals, unary minus, addition,
  subtraction, explicit multiplication, division, `\frac` and `\abs`.
- Equality, `<`, `\le`/`\leq`, `\land`, `\lor`, `\implies`, `\iff` and comparison
  chains. `f(x)=g(x)=x` requires both equalities.
- The existing explicit-binder integral spelling `\int_{0}^{1}{u}{body}`;
  interval elements are coerced to reals for arithmetic. Integration and division
  retain the semantics of the existing core, including totalized division.
- Proof sentences: `Let`, `Assume`/`Suppose`, `Have`/`Then`, `Hence`/`Conclude`,
  `Choose a ... such that ... to prove ...`, and
  `It suffices to show ... to prove ...`.

This is an extensible first source-language implementation, not coverage of
arbitrary mathematical prose or LaTeX. In particular, theorem environments,
arbitrary macros, set builders, powers, general measures, proof cases and induction
are not silently accepted. The initial `.tex` files contain the mathematical
bodies; headings and identifiers live in `source.json`. Titles are marked as
editorial in the reader.

The word “sharp” has no built-in meaning. Write the intended quantifiers and
equalities explicitly. Unsupported clauses cause compilation to fail.

## Freshness and verification

`source.py` directly recompiles the authoring module on each run so that
`include_str` is reread even if a cached `.olean` exists. It compares each exported
source and proof string with the corresponding editable file before rendering.
Rendering and dependency validation happen in a staging directory first.

The Lean regression suite checks quantifier scope, arithmetic precedence,
comparison chains, prescribed-value witnesses, source substitution, false proof
steps, partial definitions and additional axioms. Reader tests cover definition
closure and proof status; file-integrity tests cover stale source and proof files.

The browser displays the original certified strings through a fixed renderer,
with clickable domain phrases and mathematical symbols. KaTeX, HTML rendering,
the small publishing script and comparison with an original article remain
inspectable software or human-review boundaries. The parser no longer sits
outside the source certificate: its execution is part of the checked proposition.
