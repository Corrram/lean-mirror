# Analysis I sample: sequences and limits

This is a derivative companion to Jiří Lebl, *Basic Analysis I*, §2.1,
[revision e21ec524ca7d54f800c693b948020c188d21d01f](https://github.com/jirilebl/ra/tree/e21ec524ca7d54f800c693b948020c188d21d01f).
The upstream source is dual licensed; this adaptation uses **CC BY-SA 4.0**.
See [the upstream license](source/LICENSE.md) and
[the license terms](https://creativecommons.org/licenses/by-sa/4.0/).

The CC BY-SA license applies to this directory’s source-derived exposition and
generated companion, and to `LeanMirror/Examples/Analysis.lean` and
`LeanMirror/Examples/AnalysisPresentation.lean`. The generic LeanMirror engine,
reader, scripts and tests use the repository’s Apache-2.0 license. KaTeX retains
its own MIT license, copied into each HTML build.

Included: sequence/boundedness and convergence definitions; the propositions
that a convergent sequence has a unique limit and is bounded; their original
proof arguments. Other passages of the textbook are not certified.

The pinned full chapter source is preserved in `source/ch-seq-ser.tex` to make
line comparisons reproducible. Only the four excerpts listed in `source.json`
appear in the reader. Their exact line ranges and SHA-256 hashes are checked.

Changes from the original are listed in `source.json` and displayed in the
reader. The controlled companion expands implicit quantifiers and witness
choices, explicitly records a sufficient condition in the uniqueness proof,
and states the positive-index and nonempty-maximum conventions. The source
comparison retains the original prose. This companion is not endorsed by the
source author.

To read and check, from the repository root:

```sh
npm ci
python scripts/mirror.py serve examples/analysis
# Alternatively:
python scripts/mirror.py build examples/analysis
python scripts/mirror.py check examples/analysis
```

Edit the executable Lean source rather than `document.mirror.json` or
`companion.tex`, which are generated. The HTML reader is `build/analysis/index.html`.
