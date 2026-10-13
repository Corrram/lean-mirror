import LeanMirror.Source.Compile
import LeanMirror.Document

namespace LeanMirror.Source

inductive ProofSyntax where
  | finish (claim : Syntax)
  | have (claim : Syntax) (next : ProofSyntax)
  | assume (claim : Syntax) (next : ProofSyntax)
  | fix (name domain : String) (next : ProofSyntax)
  | choose (name domain : String) (condition goal : Syntax) (next : ProofSyntax)
  | suffices (claim goal : Syntax) (next : ProofSyntax)
  deriving Repr, Lean.ToExpr

private def formula (ts : List String) : Except String Syntax :=
  parseTokens ts

private def splitAtWord (word : String) (ts : List String) : Except String (List String × List String) := do
  let before := ts.takeWhile (· != word)
  match ts.drop before.length with
  | _ :: after => return (before, after)
  | [] => throw s!"expected '{word}' in proof sentence"

private def parseSteps : List (List String) → Except String ProofSyntax
  | [] => .error "proof must end with 'Hence' or 'Conclude'"
  | step :: steps => do
    let t :: rest := step | throw "empty proof sentence"
    if t == "Let" then
      let n :: be :: article :: ds := rest | throw "incomplete proof binder"
      if be != "be" || article != "a" then throw "expected 'be a' in proof binder"
      return .fix n (String.intercalate " " ds) (← parseSteps steps)
    else if t == "Assume" || t == "Suppose" then
      return .assume (← formula rest) (← parseSteps steps)
    else if t == "Have" || t == "Then" then
      return .have (← formula rest) (← parseSteps steps)
    else if t == "Hence" || t == "Conclude" then
      if !steps.isEmpty then throw "proof text after the conclusion"
      return .finish (← formula rest)
    else if t == "Choose" then
      if rest.head? != some "a" then throw "expected 'a' in choice"
      let (decl, rest) ← splitAtWord "such" rest.tail!
      if rest.head? != some "that" then throw "expected 'such that' in choice"
      let (condition, rest) ← splitAtWord "to" rest.tail!
      if rest.head? != some "prove" then throw "choice must state 'to prove' and its goal"
      if decl.length < 2 then throw "choice requires a domain and witness name"
      return .choose decl.getLast! (String.intercalate " " decl.dropLast)
        (← formula condition) (← formula rest.tail!) (← parseSteps steps)
    else if t == "It" then
      if rest.take 3 != ["suffices", "to", "show"] then throw "expected 'It suffices to show'"
      let (claim, rest) ← splitAtWord "to" (rest.drop 3)
      if rest.head? != some "prove" then throw "sufficiency must state its goal"
      return .suffices (← formula claim) (← formula rest.tail!) (← parseSteps steps)
    else throw s!"unsupported proof sentence: {String.intercalate " " step}"

def parseProof (source : String) : Except String ProofSyntax := do
  let ts ← tokenize source
  let steps := ts.splitOn "."
  let steps := if steps.getLast! == [] then steps.dropLast else steps
  parseSteps steps

def elaborateProof {S : Ty → Type} (language : Language S) (scope : Scope) :
    ProofSyntax → Except String (Argument S (scope.map Prod.snd))
  | .finish p => return .finish (← expect .prop (← elaborate language scope p))
  | .have p next => return .have (← expect .prop (← elaborate language scope p)) (← elaborateProof language scope next)
  | .assume p next => return .assume (← expect .prop (← elaborate language scope p)) (← elaborateProof language scope next)
  | .fix n phrase next => do
    if scope.any (·.1 == n) || language.constants.any (·.spelling == n) then throw "shadowed proof variable"
    let d ← domain language phrase
    let next ← elaborateProof language ((n, d.type) :: scope) next
    let next := match ← domainPredicate language d ((n, d.type) :: scope) with
      | none => next
      | some p => .assume (.app p (.var .here)) next
    return .fix d.type n next
  | .choose n phrase condition goal next => do
    if scope.any (·.1 == n) || language.constants.any (·.spelling == n) then throw "shadowed witness variable"
    let d ← domain language phrase
    let condition ← expect .prop (← elaborate language ((n, d.type) :: scope) condition)
    let condition := match ← domainPredicate language d ((n, d.type) :: scope) with
      | none => condition
      | some p => .and (.app p (.var .here)) condition
    return .choose d.type n condition (← expect .prop (← elaborate language scope goal))
      (← elaborateProof language ((n, d.type) :: scope) next)
  | .suffices claim goal next => do
    return .suffices (← expect .prop (← elaborate language scope claim))
      (← expect .prop (← elaborate language scope goal)) (← elaborateProof language scope next)

def compileProof {S : Ty → Type} (language : Language S) (source : String) :
    Except String (Argument S []) := do
  language.validate
  elaborateProof language [] (← parseProof source)

/-- The theorem source and every proof sentence are checked together. A proof of
the target alone cannot stand in for justification of the intermediate steps. -/
structure ProofCertificate {S : Ty → Type} (M : Model S) (language : Language S)
    (source proofSource : String) (statement : Expr S [] .prop) (argument : Argument S [])
    (target : Prop) : Prop where
  compiled : compile language source = .ok statement
  proofCompiled : compileProof language proofSource = .ok argument
  valid : argument.Valid M (fun _ => True)
  conclusion : argument.goal.eval M () ↔ statement.eval M ()
  correspondence : statement.eval M () ↔ target

theorem ProofCertificate.certificate {S : Ty → Type} {M : Model S} {language : Language S}
    {source proofSource : String} {statement : Expr S [] .prop} {argument : Argument S []}
    {target : Prop} (h : ProofCertificate M language source proofSource statement argument target) :
    Certificate M language source statement target :=
  ⟨h.compiled, h.correspondence,
    h.correspondence.mp (h.conclusion.mp (argument.sound M _ h.valid () trivial))⟩

theorem ProofCertificate.proved {S : Ty → Type} {M : Model S} {language : Language S}
    {source proofSource : String} {statement : Expr S [] .prop} {argument : Argument S []}
    {target : Prop} (h : ProofCertificate M language source proofSource statement argument target) :
    Meaning M language source := h.certificate.proved

#assert_lean_mirror_axioms ProofCertificate.proved
end LeanMirror.Source
