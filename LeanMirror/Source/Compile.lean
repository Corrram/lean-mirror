import LeanMirror.Source.Syntax
import LeanMirror.Core
import LeanMirror.Audit

namespace LeanMirror.Source

/-- A domain phrase is a type together with an optional mathematical predicate.
For example, “stochastically increasing bivariate copula” restricts Copula 2 by
SI; it does not introduce an unrelated type with a similar display name. -/
structure Domain (S : Ty → Type) where
  phrase : String
  key : String
  type : Ty
  predicate : Option String := none

structure Constant (S : Ty → Type) where
  spelling : String
  key : String
  type : Ty
  symbol : S type

structure Language (S : Ty → Type) where
  domains : List (Domain S) := []
  constants : List (Constant S) := []

abbrev Scope := List (String × Ty)
abbrev Typed (S : Ty → Type) (scope : Scope) := (a : Ty) × Expr S (scope.map Prod.snd) a

private def lookupVariable : (scope : Scope) → String → Option ((a : Ty) × Var (scope.map Prod.snd) a)
  | [], _ => none
  | (name, a) :: scope, n =>
    if name == n then some ⟨a, .here⟩
    else (lookupVariable scope n).map (fun ⟨b, v⟩ => ⟨b, .there v⟩)

def expect {S : Ty → Type} {scope : Scope} (a : Ty) (v : Typed S scope) :
    Except String (Expr S (scope.map Prod.snd) a) :=
  if h : v.1 = a then .ok (h ▸ v.2) else .error s!"type mismatch: expected {repr a}, found {repr v.1}"

private def real {S : Ty → Type} {scope : Scope} (v : Typed S scope) :
    Except String (Expr S (scope.map Prod.snd) .real) :=
  match v with
  | ⟨.unit, e⟩ => .ok (.coeUnit e)
  | v => expect .real v

def domain {S : Ty → Type} (language : Language S) (phrase : String) : Except String (Domain S) :=
  if ["real number", "\\mathbb { R }"].contains phrase then
    .ok ⟨phrase, "real", .real, none⟩
  else if ["unit interval element", "[ 0 , 1 ]"].contains phrase then
    .ok ⟨phrase, "unit-interval", .unit, none⟩
  else match language.domains.find? (·.phrase == phrase) with
    | some d => .ok d
    | none => .error s!"unknown mathematical domain '{phrase}'"

def Language.validate {S : Ty → Type} (language : Language S) : Except String Unit := do
  let ds := language.domains.map (·.phrase)
  let cs := language.constants.map (·.spelling)
  let keys := language.constants.map (·.key)
  if ds.eraseDups.length != ds.length || cs.eraseDups.length != cs.length then
    throw "duplicate source vocabulary spelling"
  if keys.eraseDups.length != keys.length then
    throw "each mathematical symbol requires its own definition key"
  if ds.any (fun s => ["real number", "\\mathbb { R }", "unit interval element", "[ 0 , 1 ]"].contains s) then
    throw "a built-in mathematical domain cannot be redefined"
  if language.domains.any (·.key.isEmpty) || language.constants.any (·.key.isEmpty) then
    throw "mathematical vocabulary requires definition keys"
  if keys.any (fun k => ["real", "unit-interval"].contains k) then
    throw "built-in foundations cannot be used as custom symbol keys"
  for d in language.domains do
    if ["real", "unit-interval"].contains d.key then
      throw "built-in foundations cannot be used as custom domain keys"
    if let some spelling := d.predicate then
      let some c := language.constants.find? (·.spelling == spelling)
        | throw "domain predicate must refer to a registered symbol"
      if c.key != d.key || c.type != (d.type ⇒ₘ .prop) then
        throw "domain predicate has a different definition key or argument type"
    else if language.constants.any (·.key == d.key) then
      throw "a primitive domain cannot claim a predicate's definition key"

def domainPredicate {S : Ty → Type} (language : Language S) (d : Domain S) (scope : Scope) :
    Except String (Option (Expr S (scope.map Prod.snd) (d.type ⇒ₘ .prop))) := do
  match d.predicate with
  | none => return none
  | some spelling =>
    let some c := language.constants.find? (·.spelling == spelling)
      | throw "undefined domain predicate"
    return some (← expect (d.type ⇒ₘ .prop) ⟨c.type, .symbol c.symbol⟩)

/-- Elaboration is a total, kernel-reducible function, including type checking,
name resolution, coercions, and quantifier scope. There is no unchecked escape
from a source sentence to an arbitrary Lean proposition. -/
def elaborate {S : Ty → Type} (language : Language S) (scope : Scope) :
    Syntax → Except String (Typed S scope)
  | .name n =>
    match lookupVariable scope n with
    | some ⟨a, v⟩ => .ok ⟨a, .var v⟩
    | none => match language.constants.find? (·.spelling == n) with
      | some c => .ok ⟨c.type, .symbol c.symbol⟩
      | none => .error s!"unbound variable or undefined symbol '{n}'"
  | .number n => .ok ⟨.real, .nat n⟩
  | .app fn arg => do
    let f ← elaborate language scope fn
    let x ← elaborate language scope arg
    match f with
    | ⟨.fn a b, e⟩ => return ⟨b, .app e (← expect a x)⟩
    | _ => throw "function application requires a function"
  | .unary op arg => do
    let x ← real (← elaborate language scope arg)
    if op == "-" then return ⟨.real, .sub (.nat 0) x⟩
    else if op == "\\abs" then return ⟨.real, .abs x⟩
    else if op == "\\real" then return ⟨.real, x⟩
    else throw "unknown unary operation"
  | .binary op left right => do
    let x ← elaborate language scope left
    let y ← elaborate language scope right
    if ["and", "or", "imp", "iff"].contains op then
      let p ← expect .prop x
      let q ← expect .prop y
      return ⟨.prop, if op == "and" then .and p q else if op == "or" then .or p q
        else if op == "imp" then .imp p q else .iff p q⟩
    if op == "eq" then
      if h : x.1 = y.1 then return ⟨.prop, .eq (h ▸ x.2) y.2⟩
      else return ⟨.prop, .eq (← real x) (← real y)⟩
    let x ← real x
    let y ← real y
    if op == "le" then return ⟨.prop, .le x y⟩
    else if op == "lt" then return ⟨.prop, .lt x y⟩
    else if op == "add" then return ⟨.real, .add x y⟩
    else if op == "sub" then return ⟨.real, .sub x y⟩
    else if op == "mul" then return ⟨.real, .mul x y⟩
    else if op == "div" then return ⟨.real, .div x y⟩
    else throw "unknown binary operation"
  | .bind kind n phrase body => do
    if scope.any (·.1 == n) || language.constants.any (·.spelling == n) then
      throw s!"shadowed mathematical name '{n}'"
    let d ← domain language phrase
    let p ← expect .prop (← elaborate language ((n, d.type) :: scope) body)
    let p := match ← domainPredicate language d ((n, d.type) :: scope) with
      | none => p
      | some pred => if kind == "all" then .imp (.app pred (.var .here)) p
        else .and (.app pred (.var .here)) p
    if kind == "all" then return ⟨.prop, .all n p⟩
    else if kind == "ex" then return ⟨.prop, .ex n p⟩
    else throw "unknown quantifier"
  | .integral n body => do
    if scope.any (·.1 == n) || language.constants.any (·.spelling == n) then
      throw s!"shadowed integral variable '{n}'"
    let p ← real (← elaborate language ((n, .unit) :: scope) body)
    return ⟨.real, .integral n p⟩

def compile {S : Ty → Type} (language : Language S) (source : String) :
    Except String (Expr S [] .prop) := do
  language.validate
  expect .prop (← elaborate language [] (← parse source))

/-- Meaning of the actual source string, including parsing and elaboration. -/
def Meaning {S : Ty → Type} (M : Model S) (language : Language S) (source : String) : Prop :=
  ∃ p, compile language source = .ok p ∧ p.eval M ()

/-- A certificate is indexed by the source itself, not a separately supplied
rendering. The `compiled` field is checked by kernel reduction. -/
structure Certificate {S : Ty → Type} (M : Model S) (language : Language S)
    (source : String) (statement : Expr S [] .prop) (target : Prop) : Prop where
  compiled : compile language source = .ok statement
  correspondence : statement.eval M () ↔ target
  established : target

theorem meaning_iff {S : Ty → Type} (M : Model S) (language : Language S)
    (source : String) (p : Expr S [] .prop) (h : compile language source = .ok p) :
    Meaning M language source ↔ p.eval M () := by
  constructor
  · rintro ⟨q, hq, hp⟩
    have : p = q := Except.ok.inj (h.symm.trans hq)
    cases this
    exact hp
  · intro hp
    exact ⟨p, h, hp⟩

theorem Certificate.source_equivalence {S : Ty → Type} {M : Model S} {language : Language S}
    {source : String} {statement : Expr S [] .prop} {target : Prop}
    (h : Certificate M language source statement target) :
    Meaning M language source ↔ target :=
  (meaning_iff M language source statement h.compiled).trans h.correspondence

theorem Certificate.proved {S : Ty → Type} {M : Model S} {language : Language S}
    {source : String} {statement : Expr S [] .prop} {target : Prop}
    (h : Certificate M language source statement target) :
    Meaning M language source := h.source_equivalence.mpr h.established

#assert_lean_mirror_axioms meaning_iff
#assert_lean_mirror_axioms Certificate.source_equivalence
#assert_lean_mirror_axioms Certificate.proved

end LeanMirror.Source
