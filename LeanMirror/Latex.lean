import LeanMirror.Core

/-! # LaTeX presentation and definition closure

This renderer is a presentation component, not a kernel-verified TeX engine.
All mathematical operators are rendered from the interpreted syntax tree.
Application-specific symbol notations form an explicit, reviewable vocabulary.
-/

namespace LeanMirror

structure Vocabulary (Symbol : Ty → Type) where
  key : {a : Ty} → Symbol a → String
  typeLatex : Ty → String
  binderLatex : Ty → String → String := fun _ name => name
  application : {a : Ty} → Symbol a → List String → String
  noun : {a : Ty} → Symbol (a ⇒ₘ .prop) → String

private def index {Γ : List Ty} {a : Ty} : Var Γ a → Nat
  | .here => 0
  | .there v => index v + 1

private def paren (s : String) : String := "\\left(" ++ s ++ "\\right)"

mutual
  private def render {Symbol : Ty → Type} (V : Vocabulary Symbol)
      {Γ : List Ty} {a : Ty} (vars : List String) : Expr Symbol Γ a → String
    | .var v => vars[index v]!
    | .symbol s => V.application s []
    | .app f x => renderApp V vars f [render V vars x]
    | .nat n => toString n
    | .coeUnit x => render V vars x
    | .add x y => paren (render V vars x ++ " + " ++ render V vars y)
    | .sub (.nat 0) y => "-" ++ render V vars y
    | .sub x y => paren (render V vars x ++ " - " ++ render V vars y)
    | .mul x y => render V vars x ++ "\\," ++ render V vars y
    | .div x y => "\\frac{" ++ render V vars x ++ "}{" ++ render V vars y ++ "}"
    | .abs (.sub x y) => "\\left|" ++ render V vars x ++ " - " ++ render V vars y ++ "\\right|"
    | .abs x => "\\left|" ++ render V vars x ++ "\\right|"
    | .integral name body =>
        "\\int_0^1 " ++ render V (name :: vars) body ++ "\\,\\mathrm{d}" ++ name
    | .eq x y => render V vars x ++ " = " ++ render V vars y
    | .lt x y => render V vars x ++ " < " ++ render V vars y
    | .ex (a := a) name body => "\\exists " ++ V.binderLatex a name ++ "\\in " ++ V.typeLatex a ++
        ",\\quad " ++ render V (name :: vars) body
    | .le x y => render V vars x ++ " \\le " ++ render V vars y
    | .and p q => paren (render V vars p ++ " \\;\\land\\; " ++ render V vars q)
    | .or p q => paren (render V vars p ++ " \\;\\lor\\; " ++ render V vars q)
    | .imp p q => paren (render V vars p ++ " \\;\\Longrightarrow\\; " ++ render V vars q)
    | .iff p q => paren (render V vars p ++ " \\;\\Longleftrightarrow\\; " ++ render V vars q)
    | .all (a := a) name body => "\\forall " ++ V.binderLatex a name ++ "\\in " ++ V.typeLatex a ++
        ",\\quad " ++ render V (name :: vars) body
    | .allIn name domain body =>
        "\\forall " ++ name ++ ",\\quad " ++ V.application domain [name] ++
        " \\Longrightarrow " ++ render V (name :: vars) body
  private def renderApp {Symbol : Ty → Type} (V : Vocabulary Symbol)
      {Γ : List Ty} {a : Ty} (vars : List String) : Expr Symbol Γ a → List String → String
    | .symbol s, args => V.application s args
    | .app f x, args => renderApp V vars f (render V vars x :: args)
    | e, args => render V vars e ++ paren (String.intercalate "," args)
end

def Expr.latex {Symbol : Ty → Type} (V : Vocabulary Symbol)
    {Γ : List Ty} {a : Ty} (expr : Expr Symbol Γ a) (vars : List String := []) : String :=
  match expr with
  | .add x y => render V vars x ++ " + " ++ render V vars y
  | .sub x y => render V vars x ++ " - " ++ render V vars y
  | _ => render V vars expr

/-- Consecutive binders stay readable as ordinary mathematical sentences. -/
private def theoremTail {Symbol : Ty → Type} (v : Vocabulary Symbol)
    {Γ : List Ty} (vars : List String) : Expr Symbol Γ .prop → String
  | .allIn name domain body =>
      "Let $" ++ name ++ "$ be a " ++ v.noun domain ++ ". " ++
      theoremTail v (name :: vars) body
  | body => "Then\n\\[\n" ++ body.latex v vars ++ ".\n\\]\n"

/-- The controlled phrases have exactly the implication semantics of `allIn`. -/
def Expr.theoremLatex {Symbol : Ty → Type} (v : Vocabulary Symbol)
    (expr : Expr Symbol [] .prop) : String :=
  match expr with
  | .allIn .. => theoremTail v [] expr
  | _ => "\\[\n" ++ expr.latex v ++ ".\n\\]\n"

structure DefinitionCard where
  key : String
  title : String
  latex : String
  dependencies : List String
  bridge : String

/-- Dependency order; reject missing definitions and cycles instead of silently omitting them. -/
def definitionClosure (cards : List DefinitionCard) (roots : List String) :
    Except String (List DefinitionCard) := do
  let rec visit (fuel : Nat) (active done : List String) (output : List DefinitionCard)
      (key : String) : Except String (List String × List DefinitionCard) := do
    if done.contains key then return (done, output)
    if active.contains key then throw ("cyclic mathematical definition: " ++ key)
    match fuel with
    | 0 => throw "definition traversal exhausted"
    | n + 1 =>
      let some card := cards.find? (fun card => card.key == key)
        | throw ("missing mathematical definition: " ++ key)
      let mut state := (done, output)
      for dependency in card.dependencies do
        state ← visit n (key :: active) state.1 state.2 dependency
      return (key :: state.1, state.2 ++ [card])
  if (cards.map (·.key)).eraseDups.length != cards.length then
    throw "duplicate mathematical definition key"
  let mut state := ([], [])
  for root in roots do
    state ← visit (cards.length + 1) [] state.1 state.2 root
  return state.2

end LeanMirror
