import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # A small, typed language for mathematical statements

The syntax tree, rather than a separately written LaTeX string, is the source of
both the proposition and its presentation. Subject-specific vocabulary is supplied by applications.
Named base types and typed symbols are supplied by an application.
-/

namespace LeanMirror

open MeasureTheory
open scoped unitInterval

inductive Ty where
  | real | unit | prop
  | base (name : String)
  | fn (domain codomain : Ty)
  deriving DecidableEq, Repr

infixr:60 " ⇒ₘ " => Ty.fn

abbrev Ty.denote (base : String → Type) : Ty → Type
  | .real => ℝ
  | .unit => I
  | .prop => Prop
  | .base name => base name
  | .fn a b => a.denote base → b.denote base

inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {a : Ty} : Var (a :: Γ) a
  | there {Γ : List Ty} {a b : Ty} : Var Γ a → Var (b :: Γ) a

abbrev Context (base : String → Type) : List Ty → Type
  | [] => Unit
  | a :: Γ => a.denote base × Context base Γ

def Var.get {base : String → Type} {Γ : List Ty} {a : Ty} :
    Var Γ a → Context base Γ → a.denote base
  | .here, (x, _) => x
  | .there v, (_, xs) => v.get xs

/-- Bound variables are typed de Bruijn indices. Binder names affect printing only. -/
inductive Expr (Symbol : Ty → Type) : List Ty → Ty → Type where
  | var {Γ a} : Var Γ a → Expr Symbol Γ a
  | symbol {Γ a} : Symbol a → Expr Symbol Γ a
  | app {Γ a b} : Expr Symbol Γ (a ⇒ₘ b) → Expr Symbol Γ a → Expr Symbol Γ b
  | nat {Γ} : Nat → Expr Symbol Γ .real
  | coeUnit {Γ} : Expr Symbol Γ .unit → Expr Symbol Γ .real
  | add {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real → Expr Symbol Γ .real
  | sub {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real → Expr Symbol Γ .real
  | mul {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real → Expr Symbol Γ .real
  | div {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real → Expr Symbol Γ .real
  | abs {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real
  | integral {Γ} : String → Expr Symbol (.unit :: Γ) .real → Expr Symbol Γ .real
  | eq {Γ a} : Expr Symbol Γ a → Expr Symbol Γ a → Expr Symbol Γ .prop
  | lt {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real → Expr Symbol Γ .prop
  | ex {Γ a} : String → Expr Symbol (a :: Γ) .prop → Expr Symbol Γ .prop
  | le {Γ} : Expr Symbol Γ .real → Expr Symbol Γ .real → Expr Symbol Γ .prop
  | and {Γ} : Expr Symbol Γ .prop → Expr Symbol Γ .prop → Expr Symbol Γ .prop
  | or {Γ} : Expr Symbol Γ .prop → Expr Symbol Γ .prop → Expr Symbol Γ .prop
  | imp {Γ} : Expr Symbol Γ .prop → Expr Symbol Γ .prop → Expr Symbol Γ .prop
  | iff {Γ} : Expr Symbol Γ .prop → Expr Symbol Γ .prop → Expr Symbol Γ .prop
  | all {Γ a} : String → Expr Symbol (a :: Γ) .prop → Expr Symbol Γ .prop
  | allIn {Γ a} : String → Symbol (a ⇒ₘ .prop) →
      Expr Symbol (a :: Γ) .prop → Expr Symbol Γ .prop

/-- Prevent the quotation's external names from silently disagreeing with its typed context. -/
abbrev Expr.withContextSize {Symbol : Ty → Type} {Γ : List Ty} {a : Ty}
    (size : Nat) (_ : Γ.length = size) (expr : Expr Symbol Γ a) : Expr Symbol Γ a := expr

structure Model (Symbol : Ty → Type) where
  base : String → Type
  symbol : {a : Ty} → Symbol a → a.denote base

noncomputable def Expr.eval {Symbol : Ty → Type} (M : Model Symbol)
    {Γ : List Ty} {a : Ty} : Expr Symbol Γ a → Context M.base Γ → a.denote M.base
  | .var v, env => v.get env
  | .symbol s, _ => M.symbol s
  | .app f x, env => f.eval M env (x.eval M env)
  | .nat n, _ => (n : ℝ)
  | .coeUnit x, env => (x.eval M env : ℝ)
  | .add x y, env => x.eval M env + y.eval M env
  | .sub x y, env => x.eval M env - y.eval M env
  | .mul x y, env => x.eval M env * y.eval M env
  | .div x y, env => x.eval M env / y.eval M env
  | .abs x, env => |x.eval M env|
  | .integral _ body, env => ∫ u : I, body.eval M (u, env)
  | .eq x y, env => x.eval M env = y.eval M env
  | .lt x y, env => x.eval M env < y.eval M env
  | .ex _ body, env => ∃ x, body.eval M (x, env)
  | .le x y, env => x.eval M env ≤ y.eval M env
  | .and p q, env => p.eval M env ∧ q.eval M env
  | .or p q, env => p.eval M env ∨ q.eval M env
  | .imp p q, env => p.eval M env → q.eval M env
  | .iff p q, env => p.eval M env ↔ q.eval M env
  | .all _ body, env => ∀ x, body.eval M (x, env)
  | .allIn _ domain body, env => ∀ x, M.symbol domain x → body.eval M (x, env)

/-- A correspondence and a proof of the target imply the companion's proposition. -/
structure Certificate {Symbol : Ty → Type} (M : Model Symbol)
    (statement : Expr Symbol [] .prop) (target : Prop) : Prop where
  correspondence : statement.eval M () ↔ target
  established : target

theorem Certificate.proved {Symbol : Ty → Type} {M : Model Symbol}
    {statement : Expr Symbol [] .prop} {target : Prop}
    (certificate : Certificate M statement target) : statement.eval M () :=
  certificate.correspondence.mpr certificate.established

/-- Bindings used by an expression, excluding proof dependencies. -/
def Expr.symbols {Symbol : Ty → Type} (key : {a : Ty} → Symbol a → String)
    {Γ : List Ty} {a : Ty} : Expr Symbol Γ a → List String
  | .var _ | .nat _ => []
  | .symbol s => [key s]
  | .app x y | .add x y | .sub x y | .mul x y | .div x y |
      .eq x y | .lt x y | .le x y | .and x y | .or x y | .imp x y | .iff x y => x.symbols key ++ y.symbols key
  | .coeUnit x | .abs x => x.symbols key
  | .integral _ x | .ex _ x | .all _ x => x.symbols key
  | .allIn _ s x => key s :: x.symbols key

end LeanMirror
