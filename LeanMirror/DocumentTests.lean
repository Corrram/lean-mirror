import LeanMirror.Tests
import Mathlib.Tactic.NormNum

namespace LeanMirror.DocumentTests
open Tests Ty

def correct : Argument TestSymbol [] := [proof|
  Fix x : real named "x";
  Assume 0 \le x;
  Have 0 \le x + 1;
  Conclude 0 \le x + 1]

theorem correct_valid : correct.Valid testModel (fun _ => True) := by
  simp only [correct, Argument.Valid, Expr.eval, Var.get, Ty.denote, Nat.cast_zero, Nat.cast_one]
  constructor
  · intro env h
    exact add_nonneg h.2 (by norm_num)
  · exact fun _ h => h.2

example : correct.goal.eval testModel () := correct.sound _ _ correct_valid () trivial

def truth {Γ : List Ty} : Expr TestSymbol Γ prop := .eq (.nat 0) (.nat 0)
def falsehood {Γ : List Ty} : Expr TestSymbol Γ prop := .lt (.nat 1) (.nat 0)

-- A correct final claim must not mask an incorrect intermediate assertion.
def badStep : Argument TestSymbol [] := .have falsehood (.finish truth)
example : ¬ badStep.Valid testModel (fun _ => True) := by
  intro h
  have := h.1 () trivial
  norm_num [falsehood, Expr.eval] at this

-- The existence of every chosen witness must be established.
def impossibleChoice : Argument TestSymbol [] :=
  .choose real "x" [math| x |- x < x] truth (.finish truth)
example : ¬ impossibleChoice.Valid testModel (fun _ => True) := by
  intro h
  obtain ⟨x,hx⟩ := h.1 () trivial
  exact lt_irrefl x hx

-- A later assumption cannot justify an earlier claim.
def futureAssumption : Argument TestSymbol [] :=
  .have falsehood (.assume falsehood (.finish truth))
example : ¬ futureAssumption.Valid testModel (fun _ => True) := by
  intro h
  have := h.1 () trivial
  norm_num [falsehood, Expr.eval] at this

-- A witness-dependent conclusion cannot masquerade as the outer goal.
def escapingGoal : Argument TestSymbol [] :=
  .choose real "x" truth truth (.finish [math| x |- x = x])
example : ¬ escapingGoal.Valid testModel (fun _ => True) := by
  intro h
  have heq := h.2.1
  cases heq

-- The sufficient condition must be the actual conclusion of its subproof.
def wrongSuffices : Argument TestSymbol [] := .suffices falsehood truth (.finish truth)
example : ¬ wrongSuffices.Valid testModel (fun _ => True) := by
  intro h
  have heq := h.1
  cases heq

/-- error: shadowed proof variable -/
#guard_msgs in
def shadowed : Argument TestSymbol [] := [proof|
  Fix x : real named "x"; Fix x : real named "y"; Conclude x = x]

/-- error: unbound mathematical variable; use a backslash for a symbol -/
#guard_msgs in
def unbound : Argument TestSymbol [] := [proof| Conclude z = z]

def v : Vocabulary TestSymbol where
  key _ := "nonnegative"
  typeLatex _ := "\\mathbb{R}"
  application _ _ := "unused"
  noun _ := "nonnegative"

def goodExport := checked_document% (v) correct_valid

-- No hidden hypotheses may enter a document presented as closed.
theorem conditional : badStep.Valid testModel (fun _ => False) := by
  simp [badStep, Argument.Valid]
/-- error: document has unacknowledged assumptions -/
#guard_msgs in
def badExport := checked_document% (v) conditional

axiom extraAxiom : badStep.Valid testModel (fun _ => True)
theorem tainted : badStep.Valid testModel (fun _ => True) := extraAxiom
/-- error: document depends on nonstandard axiom LeanMirror.DocumentTests.extraAxiom -/
#guard_msgs in
def taintedExport := checked_document% (v) tainted

/-- error: declaration uses `sorry` -/
#guard_msgs in
theorem unfinished : badStep.Valid testModel (fun _ => True) := by sorry
/-- error: document depends on nonstandard axiom sorryAx -/
#guard_msgs in
def unfinishedExport := checked_document% (v) unfinished

#assert_lean_mirror_axioms correct_valid

-- Disjunction remains sound when a proof introduces a fresh bound variable.
def eitherSign : Argument TestSymbol [] := [proof|
  Fix x : real named "x";
  Have x < 0 \lor 0 \le x;
  Conclude x < 0 \lor 0 \le x]
theorem eitherSign_valid : eitherSign.Valid testModel (fun _ => True) := by
  simp only [eitherSign,Argument.Valid,Expr.eval,Var.get,Ty.denote,Nat.cast_zero]
  exact ⟨fun env _ => lt_or_ge env.1 0, fun _ h => h.2⟩
example : eitherSign.goal.eval testModel () :=
  eitherSign.sound _ _ eitherSign_valid () trivial
#assert_lean_mirror_axioms eitherSign_valid
end LeanMirror.DocumentTests
