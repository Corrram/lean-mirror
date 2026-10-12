import Lean

namespace LeanMirror
open Lean Elab Meta Command

/-- Read the actual type of a theorem, rather than copying its statement by hand. -/
elab "statement_of% " decl:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo decl
  let info ← getConstInfo name
  unless info matches .thmInfo _ do
    throwErrorAt decl "expected an existing theorem"
  inferType (← mkConstWithFreshMVarLevels name)

/-- Check all transitive axioms, including those of definition bridges and imported proofs. -/
elab "#assert_lean_mirror_axioms " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  unless (← getConstInfo name) matches .thmInfo _ do
    throwErrorAt decl "expected a theorem declaration"
  for axiomName in ← collectAxioms name do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwErrorAt decl "{name} depends on nonstandard axiom {axiomName}"

end LeanMirror
