import LeanMirror.Latex
import Lean.Data.Json

/-! Structured presentation data for a mathematical companion.
Formulas and dependency links are derived from the interpreted expression trees.
The JSON and HTML renderers remain part of the documented presentation boundary.
-/

namespace LeanMirror

/-- Links annotate notation; they never alter the expression being interpreted. -/
def Vocabulary.withDefinitionLinks {Symbol : Ty → Type} (v : Vocabulary Symbol) :
    Vocabulary Symbol :=
  { v with application := fun s args =>
      "\\href{#def-" ++ v.key s ++ "}{" ++ v.application s args ++ "}" }

/-- Preserve the familiar introductory sentence for a restricted universal claim. -/
def Expr.theoremJson {Symbol : Ty → Type} (v : Vocabulary Symbol)
    (statement : Expr Symbol [] .prop) : Lean.Json :=
  match statement with
  | .allIn name domain body => Lean.Json.mkObj [
      ("kind", .str "universal"), ("variable", .str name),
      ("noun", .str (v.noun domain)), ("domain", .str (v.key domain)),
      ("formula", .str (body.latex v.withDefinitionLinks [name]))]
  | _ => Lean.Json.mkObj [
      ("kind", .str "formula"),
      ("formula", .str (statement.latex v.withDefinitionLinks))]

def DefinitionCard.toJson (card : DefinitionCard) : Lean.Json := Lean.Json.mkObj [
  ("key", .str card.key), ("title", .str card.title), ("latex", .str card.latex),
  ("dependencies", Lean.toJson card.dependencies), ("bridge", .str card.bridge)]

end LeanMirror
