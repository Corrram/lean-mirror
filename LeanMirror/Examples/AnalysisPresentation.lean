import LeanMirror.Examples.Analysis

namespace LeanMirror.Examples.Analysis
open Lean

def vocabulary : Vocabulary Symbol where
  key
    | .limit => "convergence"
    | .bounded => "sequence"
    | .value => "sequence"
    | .indexLe => "indices"
    | .prefixMax => "maximum"
  typeLatex
    | .real => "\\mathbb{R}"
    | .base "index" => "\\mathbb{N}"
    | .fn (.base "index") .real => "\\mathbb{R}^{\\mathbb{N}}"
    | _ => "\\mathrm{Object}"
  binderLatex
    | .fn (.base "index") .real, n => "\\{" ++ n ++ "_n\\}_{n=1}^{\\infty}"
    | _, n => n
  application
    | .limit, [s,x] => "\\lim_{n\\to\\infty} " ++ s ++ "_n = " ++ x
    | .bounded, [s] => "\\{" ++ s ++ "_n\\}_{n=1}^{\\infty}\\text{ is bounded}"
    | .value, [s,n] => s ++ "_{" ++ n ++ "}"
    | .indexLe, [m,n] => n ++ "\\ge " ++ m
    | .prefixMax, [s,x,m] => "\\max\\{ |" ++ s ++ "_1|,\\ldots,|" ++ s ++ "_{" ++ m ++ "-1}|,1+|" ++ x ++ "|\\}"
    | _, _ => "\\mathrm{symbol}"
  noun | .bounded => "bounded sequence"

def linkedVocabulary := vocabulary.withDefinitionLinks

def definitionJson : Json := toJson ([
  Json.mkObj [("id", .str "indices"), ("title", .str "Index convention"),
    ("text", .str "Natural numbers start at 1, as in the source. A sequence is a function on these positive integers."),
    ("formula", .str "\\mathbb{N}=\\{1,2,3,\\ldots\\},\\qquad x:\\mathbb{N}\\to\\mathbb{R}"),
    ("status", .str "primitive"), ("bridge", .str "Sequence = PNat → Real")],
  Json.mkObj [("id", .str "sequence"), ("title", .str "Sequence and boundedness"),
    ("text", .str "A sequence is bounded if there exists a real number B such that the absolute value of every term is at most B."),
    ("formula", .str (boundedDefinition.latex linkedVocabulary ["x"])),
    ("structured", boundedDefinition.toDocumentJson linkedVocabulary ["x"]),
    ("status", .str "checked"), ("bridge", .str "bounded_definition; bounded_mathlib"),
    ("target", .str "Bornology.IsBounded (Set.range s)")],
  Json.mkObj [("id", .str "convergence"), ("title", .str "Convergence and limit"),
    ("text", .str "A sequence converges to x if, for every ε > 0, there exists an M such that all terms with n ≥ M are within ε of x. A sequence is convergent when it has a limit."),
    ("formula", .str (limitDefinition.latex linkedVocabulary ["x", "x"])),
    ("structured", limitDefinition.toDocumentJson linkedVocabulary ["x", "x"]),
    ("status", .str "checked"), ("bridge", .str "limit_definition; limit_mathlib"),
    ("target", .str "Filter.Tendsto s Filter.atTop (nhds x)")],
  Json.mkObj [("id", .str "maximum"), ("title", .str "Finite maximum"),
    ("text", .str "Take the maximum over the terms with n < M together with 1 + |x|. The initial set is empty when M = 1; the additional element keeps the maximum defined."),
    ("formula", .str "B=\\max\\left(\\{|x_n|:n\\in\\mathbb{N},\\ n<M\\}\\cup\\{1+|x|\\}\\right)"),
    ("status", .str "primitive"), ("bridge", .str "prefixBound; prefix_initial; prefix_tail")]
  ] : List Json)

/-- Mathematical status is only exported through `checked_document%`, which extracts the document from the actual
    audited validity theorem. Prose and provenance remain metadata. -/
def analysisDocument : Json := Json.mkObj [
  ("schemaVersion", toJson (1 : Nat)),
  ("title", .str "Sequences and limits"),
  ("subtitle", .str "Uniqueness and boundedness · a LeanMirror companion to Basic Analysis I"),
  ("definitions", definitionJson),
  ("results", toJson ([
    Json.mkObj [("id", .str "unique"), ("title", .str "A convergent sequence has a unique limit."),
      ("certificate", .str "LeanMirror.Examples.Analysis.unique_valid"),
      ("correspondence", .str "LeanMirror.Examples.Analysis.unique_correspondence"),
      ("target", .str "tendsto_nhds_unique"),
      ("checked", checked_document% (linkedVocabulary) unique_valid)],
    Json.mkObj [("id", .str "bounded"), ("title", .str "A convergent sequence is bounded."),
      ("certificate", .str "LeanMirror.Examples.Analysis.bounded_valid"),
      ("correspondence", .str "LeanMirror.Examples.Analysis.bounded_correspondence"),
      ("target", .str "Metric.isBounded_range_of_tendsto_cofinite"),
      ("checked", checked_document% (linkedVocabulary) bounded_valid)]
    ] : List Json))]
end LeanMirror.Examples.Analysis
