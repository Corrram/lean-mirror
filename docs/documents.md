# Executable mathematical documents

LeanMirror’s document engine pairs a typed mathematical vocabulary with a scoped
proof tree. A tree is accepted only when Lean checks a proof of `Argument.Valid`
for every node. `Argument.sound` then proves the conclusion computed from the tree.
A true final theorem does not excuse a false intermediate step.

## Authoring

1. Define the objects and vocabulary: named types, typed symbols, and their Lean
   meanings. Use mathlib types and operations where appropriate. Specify the
   mathematical conventions explicitly, including index sets and domains.
2. Express definitions with `Expr` and prove their correspondence to the Lean
   meanings and, where needed, mathlib definitions.
3. Encode the original argument, preserving its order, witnesses and estimates.
   The controlled grammar automatically manages variable scope:

   ```lean
   def boundedProof : Argument Symbol [] := [proof|
     Fix s : seq named "x";
     Fix x : real named "x";
     Assume \limit(s,x);
     Choose M : idx named "M" satisfying
       Forall n : idx. \indexLe(M,n) \implies \abs{\value(s,n)-x} < 1
       to prove \bounded(s);
     -- Continue with the original estimates and finite maximum.
     Conclude \bounded(s)]
   ```

   This is a shortened illustration, not a complete certificate. The complete
   example is in `LeanMirror/Examples/Analysis.lean`.
4. Prove `boundedProof.Valid model (fun _ => True)`. Each `Have` must be justified
   from earlier assumptions, each `Choose` needs an existence proof, and a
   `Suffices` node needs both a reduction and its subproof. A local Lean tactic
   proof can supply a justification; it cannot erase the displayed obligations.
5. Extract the target from the actual library theorem using `statement_of%`, and
   prove the statement correspondence. The sample bridges use the definition
   correspondences, independently of the two source proofs.
6. Export with `checked_document% (vocabulary) bounded_valid`. The elaborator
   extracts the document from the certificate’s type, checks that it is closed
   with assumption context `True`, and rejects nonstandard transitive axioms.
7. Supply titles, source attribution, notation and a `mirror.json` configuration.
   The sample configuration selects its exporter, module, output and executable
   source. Run `build` to generate HTML, LaTeX, JSON and a build manifest.

The binder display can differ from a symbol’s application notation. For example,
a sequence is bound as `{x_n}_{n=1}^∞`, its nth term is `x_n`, and its scalar limit
is `x`. These choices live in the reviewable `Vocabulary`, not in proof tactics.

## Keeping the source close

The sample preserves exact source excerpts and checks their bytes and line ranges
against a pinned original file before compiling. Its comparison column reproduces
the selected passages, including explanatory prose and footnotes. The controlled
companion makes implicit quantifiers, witness existence and a sufficient condition
explicit. Calculation chains are assembled from consecutive checked relations;
none of their steps is replaced by a summary.

The sample covers only the listed passages. Bounded-above/below terminology,
other examples, exercises, figures and later propositions are outside its formal
scope. The general index convention and finite maximum are stated explicitly.

The small source-comparison TeX parser supports these excerpts and fails on
unsupported commands. It is separate from the proof language and is not a
universal LaTeX importer. More source formats can be added without changing the
proof semantics.

## What is checked

| Layer | Guarantee |
| --- | --- |
| Typed expressions | Variables and operations have the declared types and scopes |
| Definition bridges | Explicit formulas agree with the chosen Lean definitions |
| `Argument.Valid` | Every displayed proof node has its required justification |
| `Argument.sound` | A valid document proves its computed conclusion |
| Statement bridge | That conclusion corresponds to the selected mathlib theorem type |
| Audited export | The actual closed validity theorem has only the standard allowed axioms |
| Build command | Pinned source excerpts match, Lean compiles, and rendering succeeds |
| Check command | In addition, committed JSON and LaTeX match freshly checked output |

The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The negative
fixtures in `DocumentTests.lean` deliberately introduce `sorry` and an extra axiom
and assert that the exporter rejects them; they are not dependencies of the
companion’s certificates.

The parser, vocabulary, renderer and editorial fidelity are **not** proved
correct. Titles and explanatory prose are metadata. The computed statement is
therefore also displayed. The source comparison helps review the relation to the
original. This is a clearly identified trust boundary, not a claim that arbitrary
natural language has acquired formal semantics.

A downloaded JSON file or green badge is not an independently checkable proof.
Verification means rebuilding the pinned Lean project. `verification.json` records
input hashes for comparison; it is not a cryptographic signature. HTML is served
without external assets or tracking scripts.

## Extending the engine

### Preserving a complete article

`reader/article.mjs` supplies a separate, source-preserving LaTeX reader. Its
blocks retain their exact source text and offsets, with numbered results,
equations, proof environments, figures, references and bibliography. Unsupported
content fails the build. Bind compiled evidence by a label or a unique literal
quotation with `resolveBindings`; missing or ambiguous bindings are errors.
Notation links resolve to definition labels that actually exist in the source.

`checked_native% someTheorem` exports the **actual type** of a theorem, its
originating module, direct dependencies and transitive axiom audit. It rejects
definitions, axioms, `sorry`, and theorems depending on extra axioms. Authors
cannot replace the extracted proposition with another text at this step.

This evidence overlay is distinct from a checked `Argument` document. A native
counterpart link certifies its extracted Lean proposition. It does not certify
the adjacent source prose or prove a statement bridge. Applications must keep
that distinction visible, retain unverified passages, and supply definition and
statement bridges plus checked proof documents to complete their verification.
The reader does not rewrite, shorten, or hide the original article to fit the
current formal coverage. Article-specific maps and mathematical proofs belong
in downstream repositories.

Applications can add vocabulary without modifying the engine. New logical
constructs require interpretation, scope handling, rendering and regression
checks. New proof nodes also require extending `Valid` and proving the new case
of `Argument.sound`. This is the gate for growing the readable language.

Current nodes support universally quantified arguments, assumptions, intermediate
claims, existential choices, sufficient conditions and conclusions. Richer nested
case splits, induction, citations attached to each line, an interactive editor,
and a packaging standard for independent downstream projects remain future work.
The engine deliberately uses Lean/Lake/mathlib and KaTeX; its JSON export is a
small interface that could also feed a Verso frontend.

The original-source article reader also retains nested lists, numerical tables, multiple figure panels, declared theorem counters, appendix headings, and parameterized notation. Equation references count outer numbered rows, including unlabeled rows; nested cases do not create extra equation numbers. Comments retain byte offsets for exact source bindings. This presentation support confers no verification status on a source passage. Unsupported source content still stops the build.

Two-column articles may use a `\twocolumn[{...}]` title and abstract wrapper;
the reader retains its contents and original source offsets in a single reading
column. A source containing `\today` requires an explicit ISO `sourceDate`
when rendered. The reader never substitutes the machine's current date for the
published version's date. Superscript affiliations and natbib year suffixes are
retained as text.

Equation numbering declared with `\numberwithin{equation}{section}` or
`subsection` retains its prefixes and resets, including appendix letters.
Definition links support both macros and ordinary names such as `L_b`, including
their braced spelling `L_{b}`. The reader never wraps a term's arguments inside
its definition link.

The controlled formula language supports `\lor` (inclusive logical “or”).
Conjunction binds more tightly than disjunction, and disjunction more tightly
than implication. Both LaTeX and readable prose preserve that scope.

The original-source reader recognizes braced and unbraced LaTeX macro
declarations and simple undelimited TeX definitions such as `\def\abs#1{...}`
and `\def\1{...}`. Unsupported unused or mismatched parameters stop the
build instead of silently changing how many arguments the source consumes.


Repeated source labels fail by default. A downstream article may pass an
explicit `referenceChoices` object to `parseArticle`: each repeated label maps
to a one-based source occurrence. All occurrences retain separate anchors and
the reader displays the selected cross-reference. A binding for a repeated
label also requires its own `occurrence`; the cross-reference choice does not
silently choose which mathematical passage receives evidence. Unknown, stale
and out-of-range choices stop the build. The source is never rewritten.

Decorated coefficient keys such as `\overline{\rho}` and `\underline{\rho}`
may have their own definition links, taking precedence over `\rho`. Both braced
and single-token TeX spellings resolve to the decorated definition.

The article reader supports explicit shared author affiliation marks. A
`\footnotemark[n]` in the author field must reference an earlier `\thanks`
note; unresolved marks stop the build.

`reader/figures.mjs` resolves source figures without changing their original
graphic arguments. A PDF or macro-containing argument requires an explicit
rendering entry, with safe relative source and rendering paths, both SHA-256
hashes, renderer version, page and DPI. Both files must already occur in the
pinned asset manifest. Direct browser-image originals remain source-pinned.
Unknown entries and colliding output filenames stop the build. This checks
provenance, not the mathematical correctness of plotted data.
