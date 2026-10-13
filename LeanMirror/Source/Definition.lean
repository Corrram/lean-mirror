import LeanMirror.Source.Compile

namespace LeanMirror.Source

private def headAndArgs : Syntax → String × List Syntax
  | .app f x => let (n, xs) := headAndArgs f; (n, xs ++ [x])
  | .name n => (n, [])
  | _ => ("", [])

private def uses (name : String) : Syntax → Bool
  | .name n => n == name
  | .number _ => false
  | .app f x | .binary _ f x => uses name f || uses name x
  | .unary _ x | .integral _ x | .bind _ _ _ x => uses name x

private def definitionHead {S : Ty → Type} (language : Language S) (names : List String) :
    Syntax → Except String String
  | .bind kind n phrase body => do
    if kind != "all" then throw "a definition must be universally quantified"
    let d ← domain language phrase
    if d.predicate.isSome then throw "a definition must cover its entire argument domain"
    definitionHead language (names ++ [n]) body
  | .binary op lhs rhs => do
    if !(["eq", "iff"].contains op) then throw "a definition must be an equality or equivalence"
    let (name, args) := headAndArgs lhs
    if args != names.map Syntax.name then throw "definition arguments must be exactly its universally bound variables, in order"
    let some c := language.constants.find? (·.spelling == name)
      | throw "the left side must define a registered mathematical symbol"
    if uses name rhs then throw "recursive definitions require separate foundational support"
    return c.key
  | _ => .error "expected a universally quantified defining equality or equivalence"

def definitionKey {S : Ty → Type} (language : Language S) (source : String) : Except String String := do
  language.validate
  definitionHead language [] (← parse source)

/-- A checked definition must actually define the named symbol, over its whole
domain; an unrelated true theorem cannot be presented as its definition. -/
structure DefinitionCertificate {S : Ty → Type} (M : Model S) (language : Language S)
    (key source : String) (statement : Expr S [] .prop) (target : Prop) : Prop where
  certificate : Certificate M language source statement target
  defines : definitionKey language source = .ok key

theorem DefinitionCertificate.proved {S : Ty → Type} {M : Model S} {language : Language S}
    {key source : String} {statement : Expr S [] .prop} {target : Prop}
    (h : DefinitionCertificate M language key source statement target) : Meaning M language source :=
  h.certificate.proved

#assert_lean_mirror_axioms DefinitionCertificate.proved
end LeanMirror.Source
