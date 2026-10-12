import LeanMirror

namespace LeanMirror.Tests
open MeasureTheory
open scoped unitInterval

inductive TestSymbol : Ty → Type where
  | nonnegative : TestSymbol (.real ⇒ₘ .prop)

noncomputable def testModel : Model TestSymbol where
  base _ := Unit
  symbol | .nonnegative => fun x => 0 ≤ x

open TestSymbol in
def unrelatedStatement : Expr TestSymbol [] .prop :=
  [math| |- Let x be nonnegative. 0 \le x + 1]

theorem unrelatedTarget (x : ℝ) (h : 0 ≤ x) : 0 ≤ x + 1 := add_nonneg h zero_le_one

def unrelatedTargetType : Prop := statement_of% unrelatedTarget

theorem unrelatedEquivalence : unrelatedStatement.eval testModel () ↔ unrelatedTargetType := by
  simp only [unrelatedStatement, Expr.eval, testModel, Var.get, Nat.cast_zero, Nat.cast_one,
    unrelatedTargetType]

theorem unrelatedCertificate : Certificate testModel unrelatedStatement unrelatedTargetType :=
  ⟨unrelatedEquivalence, unrelatedTarget⟩

#assert_lean_mirror_axioms unrelatedCertificate

/-- Integration introduces a new variable without capturing the outer variable. -/
def scopedIntegral : Expr TestSymbol [.real] .real :=
  [math| x |- \int_{0}^{1}{u}{\real{u} - x}]

example (x : ℝ) : scopedIntegral.eval testModel (x, ()) = ∫ u : I, (u : ℝ) - x := rfl

def renamedIntegral : Expr TestSymbol [.real] .real :=
  [math| x |- \int_{0}^{1}{v}{\real{v} - x}]

example (x : ℝ) : scopedIntegral.eval testModel (x, ()) =
    renamedIntegral.eval testModel (x, ()) := rfl

private def card (name : String) (deps : List String) : DefinitionCard :=
  ⟨name, name, "", deps, ""⟩

-- Unused definitions and proof infrastructure must not appear in the closure.
#guard (definitionClosure [card "root" ["leaf", "leaf"], card "leaf" [],
    card "unrelated" []] ["root"]).map (·.map (·.key)) == .ok ["leaf", "root"]
private def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard isError (definitionClosure [card "a" ["missing"]] ["a"])
#guard isError (definitionClosure [card "a" ["b"], card "b" ["a"]] ["a"])
#guard isError (definitionClosure [card "a" [], card "a" []] ["a"])

-- Type extraction must reject mathematical objects that are not proofs.
/-- error: expected a proof of a proposition -/
#guard_msgs in
def invalidProofTarget : Prop := statement_of% (Nat.zero)


private def linkVocabulary : Vocabulary TestSymbol where
  key _ := "term"
  typeLatex _ := "R"
  application _ args := "P(" ++ String.intercalate "," args ++ ")"
  noun _ := "term"

-- HTML forbids nested anchors, including when a coefficient takes a linked object.
#guard linkVocabulary.withDefinitionLinks.application TestSymbol.nonnegative
  ["\\href{#def-term}{x}"] == "P(\\href{#def-term}{x})"
#guard linkVocabulary.withDefinitionLinks.application TestSymbol.nonnegative
  ["x"] == "\\href{#def-term}{P(x)}"
#guard ((Expr.eq (Expr.sub (Expr.nat 0) (Expr.nat 1)) (Expr.nat 0) :
  Expr TestSymbol [] .prop).latex linkVocabulary) == "-1 = 0"

end LeanMirror.Tests
