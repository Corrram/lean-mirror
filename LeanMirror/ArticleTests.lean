import LeanMirror

namespace LeanMirror.ArticleTests
open Lean

theorem checked (n : Nat) : n = n := rfl
def exported : Json := checked_native% checked
#guard (exported.getObjValAs? String "declaration").toOption ==
  some "LeanMirror.ArticleTests.checked"
#guard (exported.getObjValAs? String "type").toOption == some "∀ (n : ℕ), n = n"

def assertion : Prop := True
/-- error: expected a proved theorem, not a definition or axiom -/
#guard_msgs in
def definitionExport : Json := checked_native% assertion

axiom unproved : True
/-- error: expected a proved theorem, not a definition or axiom -/
#guard_msgs in
def axiomExport : Json := checked_native% unproved

theorem tainted : True := unproved
/-- error: article evidence depends on nonstandard axiom LeanMirror.ArticleTests.unproved -/
#guard_msgs in
def taintedExport : Json := checked_native% tainted

/-- error: declaration uses `sorry` -/
#guard_msgs in
theorem unfinished : True := by sorry
/-- error: article evidence depends on nonstandard axiom sorryAx -/
#guard_msgs in
def unfinishedExport : Json := checked_native% unfinished

end LeanMirror.ArticleTests
