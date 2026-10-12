import LeanMirror.Document

/-! Evidence for a source-preserving article reader. Original prose is not a proof
term: the reader exposes the actual checked proposition beside each source span.
Only this elaborator may create a checked native theorem entry. -/
namespace LeanMirror
open Lean Elab Meta

private def articleJson (s : String) : Json :=
  (Json.parse s).toOption.getD Json.null

/-- Export the actual type of a compiled theorem and audit its transitive axioms.
The caller cannot supply a replacement statement or a checked-status caption. -/
elab "checked_native% " declaration:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo declaration
  let info ← getConstInfo name
  let .thmInfo proofInfo := info
    | throwErrorAt declaration "expected a proved theorem, not a definition or axiom"
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwErrorAt declaration "article evidence depends on nonstandard axiom {ax}"
  let options := (← getOptions).setBool `pp.fullNames true |>.set `pp.width (100 : Nat)
  let statement ← withOptions (fun _ => options) <| ppExpr proofInfo.type
  let env ← getEnv
  let moduleName := match env.getModuleIdxFor? name with
    | some index => env.header.moduleNames[index.toNat]!
    | none => env.header.mainModule
  let data := Json.mkObj [
    ("declaration", .str name.toString),
    ("module", .str moduleName.toString),
    ("type", .str statement.pretty),
    ("axioms", toJson (axioms.toList.map Name.toString)),
    ("dependencies", toJson (proofInfo.value.getUsedConstants.toList.map Name.toString))]
  mkAppM ``articleJson #[toExpr data.compress]

end LeanMirror
