# Articles compiled from LaTeX

LeanMirror can compile an ordinary LaTeX article and verify it in Lean. Readers
and Lean then work from one text. The definitions, statements and proof
sentences that people read are the ones Lean checks. There is no second,
hand-written formal version that could drift away from the paper.

The exemplar is Corollary 3.2 of *Rank weighting and asymmetry in Blest's rank
correlation* (arXiv:2609.27634). It lives in `lean-verifications`, under
`Papers/Rockel2026ExactBlest/Source/`. Its statement and every sentence of its
proof are derived in Lean from exactly the results they cite.

## Pipeline

| Stage | Lean command | What is checked |
| --- | --- | --- |
| Compile the source | `#mirror_article Foo "article.tex"` | The kernel proves `Foo.compiled : compileArticle Foo.source = some Foo.doc`. The proof is staged (lexing in chunks, then sentences, then assembly), uses `Eq.refl` only, and uses no `native_decide`. |
| State the meaning | `#mirror_semantics Foo "article.tex"` | It names every definition (`Foo.nu`, `Foo.D`, …) and states every claim (`Foo.claimK`) and its definedness (`Foo.meaningfulK`) as ordinary Lean. Kernel `rfl` theorems tie each one to the compiled document: `Foo.env`, `Foo.holdsK`, `Foo.welldefI`. It also generates the proof obligations `Foo.obligationK`. |
| Justify | your proofs `J.proofK : Foo.obligationK` and `J.definedI : Foo.wellDefinedI` | These are ordinary Lean proofs. |
| Certify | `#mirror_certify Foo "article.tex" using J` | Premises must be verified and acyclic. Claims derived in the text are audited. The kernel checks `Foo.certificate`. Each verified claim is exported as `Foo.verifiedK : Foo.meaningfulK ∧ Foo.claimK`. The command writes `article.mirror.json`. |

`compileArticle` is an ordinary, total Lean function. The kernel evaluates it on
the file's contents, so the readable statements depend on nothing but the text.

## Writing for LeanMirror

* **Symbols are defined in the article before they are used.** The defining
  formula of a symbol (`\nu(C)\coloneqq…`, `define $\Phi:[-1,1]\to[-1,1]$ by …`,
  `We say that a copula $C$ is \emph{supported on the graph} of … if …`) is its
  only meaning. Using an undefined symbol is a compile error for that sentence.
  So is defining a symbol twice. Preamble macros (`\newcommand`) are expanded
  first.
* **One construction per sentence.** The grammar is a fixed list of
  constructions of mathematical English. Each has one reading, which
  `LeanMirror/Tex/Elab.lean` documents. A sentence matches completely or not at
  all. A sentence that matches nothing is *prose*: it is shown, but it asserts
  nothing checked. The reader and the diagnostics mark prose that occurs inside
  results and proofs, so uncompiled mathematics stays visible.
* **Proofs cite what they use.** Inside `\begin{proof}`, a sentence may use the
  earlier sentences of the same proof and the results cited so far in that
  proof (`by Theorem~\ref{…}`, `by \eqref{…}`). When every sentence of a proof
  compiles, the result it proves gets those sentences and citations as its
  premises. That is the closing step.

## The prelude

Besides the article's own definitions, the only meanings are standard mathlib
notions (`LeanMirror/Tex/Term.lean`, `Prim`): real powers, `min`/`max`,
Lebesgue measure on `[0,1]`, distribution functions of probability measures on
`[0,1]^2`, uniform marginals, probability measures on `[0,1]^2` as set
functions, Borel measurability, measurable sets, integrability on `[0,1]`, and
derivatives within a set. Nouns such as "Borel measurable" and "probability
measure on $[0,1]^2$" denote these.

## Definedness

Partial operations are total in Lean, as in mathlib. Every compiled term
therefore also has a syntactic definedness condition, `Tm.defined`, in the
style of TCCs. A claim means `defined ∧ claim`. The condition includes:

* nonzero denominators and nonnegative bases of real powers;
* points that lie in `[0,1]`, and arguments that lie in the domain stated by a
  definition;
* integrability of integrands, and measurability of measured sets;
* coverage of `cases`, and agreement of `cases` where two conditions overlap.

So `1/0 = 0` cannot become true for a conventional reason.

## Justifications and the citation audit

`obligationK` is `P_{j₁} → … → P_{jₙ} → meaningfulK ∧ claimK`, where the
`jᵢ` are the premises the text gives claim `K`. Two tactics help:

* `intro_premises` introduces each premise `J` as `mJ`/`cJ`;
* `definedness [facts]` proves definedness trees.

A claim is *derived in the text* when it is a proof sentence, or a statement
closed by a compiled proof. For such a claim, `#mirror_certify` audits the
justification. Every constant it uses must come from Lean or mathlib, from
LeanMirror, from the compiled article, or from helper declarations in the
justification modules, and those helpers are audited recursively. A proof
sentence therefore cannot be justified by a result it does not cite. Claims
without a compiled proof (cited theorems, displayed formulas) may use any Lean
proof. For the exemplar, these use the companion development, through proved
bridge theorems in `Source/Bridge.lean`. The certificate permits only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Reading and editing

* `reader/compiled.mjs` renders the article from the compiled source. A marker
  at the start of each sentence shows its status:
  * derived from its citations;
  * checked by the companion development;
  * definition;
  * unverified;
  * not compiled;
  * prose.

  Selecting a marker highlights the sentence and shows its formal reading, its
  Lean statement, its definedness condition, its premises and its justification.
* `scripts/tex_diagnostics.py article.mirror.json [--prose] [--strict]` prints
  findings as `file:line:col: severity: message`. Uncompiled sentences are also
  reported as build warnings by `#mirror_semantics`.
* `editors/vscode/tasks.json` runs `lake build` and the diagnostics, and shows
  the findings as problems in the `.tex` file.
* `tex/leanmirror.sty` marks an article as LeanMirror-checked
  (`\leanmirrorcheck{Module}`). It does not change the PDF, and LeanMirror reads
  no markup from it.

## Trust boundary

The kernel checks:

* the compilation of the file;
* the identity of the readable definitions and claims with the compiled
  semantics;
* every justification;
* the certificate.

Outside the proof are the meaning of the fixed readings and of the prelude (a
short, reviewable list), the native evaluation that proposes stage results (the
kernel re-checks them), and the presentation: KaTeX typesetting of formal
readings and the HTML reader.
