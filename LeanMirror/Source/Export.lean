import LeanMirror.Source.Proof
import LeanMirror.Source.Definition

namespace LeanMirror.Source

open Lean Elab Meta

private def evaluate (e : Lean.Expr) : MetaM Lean.Expr := do
  withTransparency .default <| whnf e

/-- Definitional evaluation: the resulting equality proof is checked by Lean.
Unlike native_decide, this does not add a trusted computation axiom. -/
elab "source_check" : tactic => do
  Elab.Tactic.liftMetaTactic fun goal => do
    goal.refl
    return []

private def successful (e : Lean.Expr) : TermElabM Lean.Expr := do
  let result ← evaluate (← instantiateMVars e)
  if result.isAppOfArity ``Except.ok 3 then return result.getAppArgs[2]!
  if result.isAppOfArity ``Except.error 3 then throwError "companion source: {result.getAppArgs[2]!}"
  throwError "expected a closed compilation result: {result}"

syntax (name := sourceInput) "source% " "(" term ")" term : term
syntax (name := sourceProofInput) "source_proof% " "(" term ")" term : term

private def emptyScope : Scope := []

/-- Native parsing only proposes a tree. The separately required `compiled`
proof checks the original source with the kernel; this driver is not trusted. -/
@[term_elab sourceInput] unsafe def elabSource : Term.TermElab := fun stx _ => do
  let l ← Term.elabTerm stx[2] none
  let s ← Term.elabTerm stx[4] (some (mkConst ``String))
  Term.synthesizeSyntheticMVarsNoPostponing
  discard <| successful (← mkAppM ``Language.validate #[l])
  let parser ← mkAppM ``parse #[s]
  let tree ← evalExpr (Except String Source.Syntax) (← inferType parser) parser
  let tree ← match tree with
    | .ok tree => pure tree
    | .error message => throwError "companion source: {message}"
  let value ← successful (← mkAppM ``elaborate #[l, mkConst ``emptyScope, toExpr tree])
  unless ← isDefEq (← whnf (mkProj ``Sigma 0 value)) (mkConst ``Ty.prop) do
    throwError "the companion statement must be a proposition"
  reduce (mkProj ``Sigma 1 value) (explicitOnly := false)

@[term_elab sourceProofInput] unsafe def elabSourceProof : Term.TermElab := fun stx _ => do
  let l ← Term.elabTerm stx[2] none
  let s ← Term.elabTerm stx[4] (some (mkConst ``String))
  Term.synthesizeSyntheticMVarsNoPostponing
  discard <| successful (← mkAppM ``Language.validate #[l])
  let parser ← mkAppM ``parseProof #[s]
  let tree ← evalExpr (Except String ProofSyntax) (← inferType parser) parser
  let tree ← match tree with
    | .ok tree => pure tree
    | .error message => throwError "companion proof: {message}"
  reduce (← successful (← mkAppM ``elaborateProof #[l, mkConst ``emptyScope, toExpr tree]))
    (explicitOnly := false)

def Syntax.toJson : Source.Syntax → Json
  | .name n => Json.mkObj [("kind", .str "name"), ("name", .str n)]
  | .number n => Json.mkObj [("kind", .str "number"), ("value", Lean.toJson n)]
  | .app f x => Json.mkObj [("kind", .str "app"), ("function", f.toJson), ("argument", x.toJson)]
  | .unary op x => Json.mkObj [("kind", .str "unary"), ("operator", .str op), ("argument", x.toJson)]
  | .binary op x y => Json.mkObj [("kind", .str "binary"), ("operator", .str op), ("left", x.toJson), ("right", y.toJson)]
  | .bind kind n d b => Json.mkObj [("kind", .str kind), ("name", .str n), ("domain", .str d), ("body", b.toJson)]
  | .integral n b => Json.mkObj [("kind", .str "integral"), ("name", .str n), ("body", b.toJson)]

def dependencies {S : Ty → Type} (language : Language S) : Source.Syntax → List String
  | .name n => (language.constants.find? (·.spelling == n)).toList.map (·.key)
  | .number _ => []
  | .app f x | .binary _ f x => dependencies language f ++ dependencies language x
  | .unary _ x => dependencies language x
  | .integral _ x => "unit-interval" :: dependencies language x
  | .bind _ _ phrase x =>
    (domain language phrase).toOption.toList.map (·.key) ++ dependencies language x

private def proofDependencies {S : Ty → Type} (language : Language S) : ProofSyntax → List String
  | .finish p => dependencies language p
  | .have p n | .assume p n => dependencies language p ++ proofDependencies language n
  | .fix _ d n => (domain language d).toOption.toList.map (·.key) ++ proofDependencies language n
  | .choose _ d p q n => (domain language d).toOption.toList.map (·.key) ++
      dependencies language p ++ dependencies language q ++ proofDependencies language n
  | .suffices p q n => dependencies language p ++ dependencies language q ++ proofDependencies language n

private def sourceJson {S : Ty → Type} (language : Language S)
    (source proofSource kind key certificate target modelIdentity languageIdentity : String)
    (axioms : List String) : Json :=
  let tree := (parse source).toOption
  let deps := tree.toList.flatMap (dependencies language) ++
    ((parseProof proofSource).toOption.toList.flatMap (proofDependencies language))
  Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("kind", .str kind), ("key", .str key),
    ("source", .str source), ("proofSource", .str proofSource),
    ("syntax", tree.map Source.Syntax.toJson |>.getD Json.null),
    ("dependencies", toJson (deps.eraseDups.filter (· != key))),
    ("certificate", .str certificate), ("target", .str target), ("axioms", toJson axioms),
    ("modelIdentity", .str modelIdentity), ("languageIdentity", .str languageIdentity),
    ("terms", toJson (language.constants.map (fun c => Json.mkObj [
      ("spelling", .str c.spelling), ("key", .str c.key)]))),
    ("domains", toJson (language.domains.map (fun d => Json.mkObj [
      ("phrase", .str d.phrase), ("key", .str d.key)])))]

/-- Export is selected only from an audited theorem's actual certificate type.
There is no caller-supplied replacement source, proposition, or status. -/
elab "checked_source% " declaration:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo declaration
  let info ← getConstInfo name
  unless info matches .thmInfo _ do throwError "expected a source certificate theorem"
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "source certificate depends on nonstandard axiom {ax}"
  let t := info.type
  let args := t.getAppArgs
  let (kind, key, source, proofSource, target) ←
    if t.isAppOfArity ``Source.Certificate 6 then
      pure ("theorem", mkStrLit "", args[3]!, mkStrLit "", args[5]!)
    else if t.isAppOfArity ``DefinitionCertificate 7 then
      pure ("definition", args[3]!, args[4]!, mkStrLit "", args[6]!)
    else if t.isAppOfArity ``ProofCertificate 8 then
      pure ("proof", mkStrLit "", args[3]!, args[4]!, args[7]!)
    else throwError "expected a closed Source.Certificate, DefinitionCertificate, or ProofCertificate"
  let targetText ← withOptions (·.setBool `pp.fullNames true) (ppExpr (← whnf target))
  mkAppM ``sourceJson #[args[2]!, source, proofSource, mkStrLit kind, key, mkStrLit name.toString,
    mkStrLit targetText.pretty, mkStrLit (reprStr args[1]!), mkStrLit (reprStr args[2]!),
    toExpr (axioms.toList.map Name.toString)]

end LeanMirror.Source
