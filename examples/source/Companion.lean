import LeanMirror.Source.Export
import Mathlib.Algebra.Order.Ring.Abs

/-! This file is recompiled directly on every source-companion build. The TeX
files are the editable statements; no duplicate expression is maintained here. -/
namespace SourceExample
open LeanMirror LeanMirror.Source
open scoped unitInterval

set_option maxRecDepth 2048
set_option maxHeartbeats 400000

inductive Symbol : Ty → Type where
  | nonnegative : Symbol (.real ⇒ₘ .prop)
  | nonpositive : Symbol (.real ⇒ₘ .prop)

def language : Language Symbol where
  domains := [⟨"nonnegative real number", "nonnegative", .real, some "\\nonnegative"⟩,
    ⟨"nonpositive real number", "nonpositive", .real, some "\\nonpositive"⟩]
  constants := [⟨"\\nonnegative", "nonnegative", _, .nonnegative⟩,
    ⟨"\\nonpositive", "nonpositive", _, .nonpositive⟩]

noncomputable def model : Model Symbol where
  base _ := Unit
  symbol | .nonnegative => fun x => 0 ≤ x | .nonpositive => fun x => x ≤ 0

def nonnegativeSource := include_str "nonnegative.tex"
def nonpositiveSource := include_str "nonpositive.tex"
def triangleSource := include_str "triangle.tex"
def triangleProofSource := include_str "triangle-proof.tex"
def sharpnessSource := include_str "sharpness.tex"

def nonnegativeStatement := source% (language) nonnegativeSource
def nonpositiveStatement := source% (language) nonpositiveSource
def triangleStatement := source% (language) triangleSource
def triangleArgument := source_proof% (language) triangleProofSource
def sharpnessStatement := source% (language) sharpnessSource

theorem nonnegative_target (x : ℝ) : model.symbol .nonnegative x ↔ 0 ≤ x := Iff.rfl
theorem nonpositive_target (x : ℝ) : model.symbol .nonpositive x ↔ x ≤ 0 := Iff.rfl
def NonnegativeTarget : Prop := statement_of% nonnegative_target
def NonpositiveTarget : Prop := statement_of% nonpositive_target
def TriangleTarget : Prop := statement_of% (fun x y : ℝ => abs_add_le x y)

theorem nonnegative_checked : DefinitionCertificate model language "nonnegative"
    nonnegativeSource nonnegativeStatement NonnegativeTarget :=
  ⟨⟨by source_check, by
    simp only [nonnegativeStatement, Expr.eval, model, Var.get, NonnegativeTarget, Nat.cast_zero],
    nonnegative_target⟩, by source_check⟩

theorem nonpositive_checked : DefinitionCertificate model language "nonpositive"
    nonpositiveSource nonpositiveStatement NonpositiveTarget :=
  ⟨⟨by source_check, by
    simp only [nonpositiveStatement, Expr.eval, model, Var.get, NonpositiveTarget, Nat.cast_zero],
    nonpositive_target⟩, by source_check⟩

theorem triangle_valid : triangleArgument.Valid model (fun _ => True) := by
  simp only [triangleArgument, Argument.Valid, Expr.eval, Var.get, Nat.cast_zero, zero_sub]
  refine ⟨?_, ?_, ?_⟩
  · intro env _
    exact add_le_add (le_abs_self env.2.1) (le_abs_self env.1)
  · intro env _
    change -(abs env.2.1 + abs env.1) ≤ env.2.1 + env.1
    linarith [neg_abs_le env.2.1, neg_abs_le env.1]
  · intro env _
    exact abs_add_le env.2.1 env.1

theorem triangle_checked : ProofCertificate model language triangleSource triangleProofSource
    triangleStatement triangleArgument TriangleTarget :=
  ⟨by source_check, by source_check, triangle_valid, Iff.rfl, Iff.rfl⟩

theorem sharpness_target :
    (∀ x : ℝ, 0 ≤ x → x ≤ |x|) ∧
    (∀ x : ℝ, x ≤ 0 → -x ≤ |x|) ∧
    (∀ a : I, ∃ x : ℝ, 0 ≤ x ∧ (a : ℝ) = x ∧ x = |x|) ∧
    (∀ a : I, ∃ x : ℝ, x ≤ 0 ∧ (a : ℝ) = -x ∧ -x = |x|) := by
  refine ⟨fun x _ => le_abs_self x, fun x _ => neg_le_abs x, ?_, ?_⟩
  · intro a
    exact ⟨a, a.property.1, rfl, (abs_of_nonneg a.property.1).symm⟩
  · intro a
    refine ⟨-(a : ℝ), neg_nonpos.mpr a.property.1, (neg_neg _).symm, ?_⟩
    rw [abs_neg, abs_of_nonneg a.property.1, neg_neg]

def SharpnessTarget : Prop := statement_of% sharpness_target

theorem sharpness_checked : Source.Certificate model language sharpnessSource
    sharpnessStatement SharpnessTarget :=
  ⟨by source_check, by
    simp only [sharpnessStatement, Expr.eval, model, Var.get, SharpnessTarget,
      Nat.cast_zero, zero_sub], sharpness_target⟩

def document : Lean.Json := Lean.Json.mkObj [
  ("schemaVersion", Lean.toJson (1 : Nat)),
  ("entries", Lean.toJson ([checked_source% nonnegative_checked,
    checked_source% nonpositive_checked, checked_source% triangle_checked,
    checked_source% sharpness_checked] : List Lean.Json))]

end SourceExample

def main (args : List String) : IO Unit := do
  match args with
  | [output] => IO.FS.writeFile output SourceExample.document.pretty
  | _ => throw (IO.userError "expected an output JSON path")
