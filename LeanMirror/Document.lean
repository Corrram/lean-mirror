import LeanMirror.Presentation
import LeanMirror.Audit

/-! A proof document is a scoped syntax tree. `Valid` checks every node; `sound`
    derives its conclusion. Presentation never supplies a mathematical premise. -/
namespace LeanMirror

namespace Expr

def liftRen {Γ Δ : List Ty} {a b : Ty}
    (ρ : {t : Ty} → Var Γ t → Var Δ t) : Var (a :: Γ) b → Var (a :: Δ) b
  | .here => .here
  | .there v => .there (ρ v)

def rename {S : Ty → Type} {Γ Δ : List Ty} {a : Ty}
    (ρ : {t : Ty} → Var Γ t → Var Δ t) : Expr S Γ a → Expr S Δ a
  | .var v => .var (ρ v)
  | .symbol s => .symbol s
  | .app f x => .app (rename ρ f) (rename ρ x)
  | .nat n => .nat n
  | .coeUnit x => .coeUnit (rename ρ x)
  | .add x y => .add (rename ρ x) (rename ρ y)
  | .sub x y => .sub (rename ρ x) (rename ρ y)
  | .mul x y => .mul (rename ρ x) (rename ρ y)
  | .div x y => .div (rename ρ x) (rename ρ y)
  | .abs x => .abs (rename ρ x)
  | .eq x y => .eq (rename ρ x) (rename ρ y)
  | .lt x y => .lt (rename ρ x) (rename ρ y)
  | .le x y => .le (rename ρ x) (rename ρ y)
  | .and p q => .and (rename ρ p) (rename ρ q)
  | .or p q => .or (rename ρ p) (rename ρ q)
  | .imp p q => .imp (rename ρ p) (rename ρ q)
  | .iff p q => .iff (rename ρ p) (rename ρ q)
  | .all n p => .all n (rename (liftRen ρ) p)
  | .ex n p => .ex n (rename (liftRen ρ) p)
  | .integral n p => .integral n (rename (liftRen ρ) p)
  | .allIn n d p => .allIn n d (rename (liftRen ρ) p)

def weaken {S : Ty → Type} {Γ : List Ty} {a b : Ty} (e : Expr S Γ a) :
    Expr S (b :: Γ) a := e.rename Var.there

theorem eval_rename {S : Ty → Type} (M : Model S) {Γ Δ : List Ty} {a : Ty}
    (e : Expr S Γ a) (ρ : {t : Ty} → Var Γ t → Var Δ t)
    (env : Context M.base Γ) (env' : Context M.base Δ)
    (h : ∀ {t} (v : Var Γ t), (ρ v).get env' = v.get env) :
    (e.rename ρ).eval M env' = e.eval M env := by
  induction e generalizing Δ with
  | var v => exact h v
  | symbol s => rfl
  | nat n => rfl
  | «app» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «add» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «sub» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «mul» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «div» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «eq» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «lt» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «le» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «and» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «or» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «imp» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | «iff» x y ihx ihy => simp only [rename, eval, ihx ρ env env' h, ihy ρ env env' h]
  | coeUnit x ih => simp only [rename, eval, ih ρ env env' h]
  | abs x ih => simp only [rename, eval, ih ρ env env' h]
  | all n p ih =>
    simp only [rename, eval]
    have hi : ∀ x, (p.rename (liftRen ρ)).eval M (x, env') = p.eval M (x, env) := by
      intro x
      apply ih
      intro t v
      cases v with
      | here => rfl
      | there v => exact h v
    simp only [hi]
  | ex n p ih =>
    simp only [rename, eval]
    have hi : ∀ x, (p.rename (liftRen ρ)).eval M (x, env') = p.eval M (x, env) := by
      intro x
      apply ih
      intro t v
      cases v with
      | here => rfl
      | there v => exact h v
    simp only [hi]
  | integral n p ih =>
    simp only [rename, eval]
    have hi : ∀ x, (p.rename (liftRen ρ)).eval M (x, env') = p.eval M (x, env) := by
      intro x
      apply ih
      intro t v
      cases v with
      | here => rfl
      | there v => exact h v
    simp only [hi]
  | allIn n d p ih =>
    simp only [rename, eval]
    have hi : ∀ x, (p.rename (liftRen ρ)).eval M (x, env') = p.eval M (x, env) := by
      intro x
      apply ih
      intro t v
      cases v with
      | here => rfl
      | there v => exact h v
    simp only [hi]

@[simp] theorem eval_weaken {S : Ty → Type} (M : Model S) {Γ : List Ty} {a b : Ty}
    (e : Expr S Γ a) (env : Context M.base Γ) (x : b.denote M.base) :
    e.weaken.eval M (x, env) = e.eval M env :=
  eval_rename M e Var.there env (x, env) (fun _ => rfl)
end Expr

/-- Each constructor has fixed logical meaning and fixed controlled prose.
    Arbitrary source prose is kept separately and cannot certify a node. -/
inductive Argument (S : Ty → Type) : List Ty → Type where
  | finish {Γ} (claim : Expr S Γ .prop) : Argument S Γ
  | have {Γ} (claim : Expr S Γ .prop) (next : Argument S Γ) : Argument S Γ
  | fix {Γ} (a : Ty) (name : String) (next : Argument S (a :: Γ)) : Argument S Γ
  | assume {Γ} (claim : Expr S Γ .prop) (next : Argument S Γ) : Argument S Γ
  | choose {Γ} (a : Ty) (name : String) (condition : Expr S (a :: Γ) .prop)
      (goal : Expr S Γ .prop) (next : Argument S (a :: Γ)) : Argument S Γ
  | suffices {Γ} (claim goal : Expr S Γ .prop) (next : Argument S Γ) : Argument S Γ

/-- The conclusion is computed from the proof structure, never a separate caption. -/
def Argument.goal {S : Ty → Type} {Γ : List Ty} : Argument S Γ → Expr S Γ .prop
  | .finish p => p
  | .have _ next => next.goal
  | .fix _ n next => .all n next.goal
  | .assume p next => .imp p next.goal
  | .choose _ _ _ goal _ | .suffices _ goal _ => goal

/-- Verification checks each assertion under exactly the assumptions available at
    that point. Choices require existence. Fresh variables cannot escape scope. -/
noncomputable def Argument.Valid {S : Ty → Type} (M : Model S) {Γ : List Ty}
    (H : Context M.base Γ → Prop) : Argument S Γ → Prop
  | .finish p => ∀ env, H env → p.eval M env
  | .have p next => (∀ env, H env → p.eval M env) ∧ next.Valid M (fun env => H env ∧ p.eval M env)
  | .fix a _ next => next.Valid M (fun env : Context M.base (a :: Γ) => H env.2)
  | .assume p next => next.Valid M (fun env => H env ∧ p.eval M env)
  | .choose a _ condition goal next =>
      (∀ env, H env → ∃ x, condition.eval M (x, env)) ∧
      next.goal = goal.weaken ∧ next.Valid M (fun env : Context M.base (a :: Γ) => H env.2 ∧ condition.eval M env)
  | .suffices p goal next => next.goal = p ∧
      (∀ env, H env → p.eval M env → goal.eval M env) ∧ next.Valid M H

/-- The generic proof-document soundness theorem, checked by Lean's kernel. -/
theorem Argument.sound {S : Ty → Type} (M : Model S) {Γ : List Ty}
    (doc : Argument S Γ) (H : Context M.base Γ → Prop) (valid : doc.Valid M H) :
    ∀ env, H env → doc.goal.eval M env := by
  induction doc with
  | finish p => exact valid
  | «have» p next ih => exact fun env h => ih _ valid.2 env ⟨h, valid.1 env h⟩
  | fix a n next ih => exact fun env h x => ih _ valid (x, env) h
  | assume p next ih => exact fun env h hp => ih _ valid env ⟨h, hp⟩
  | choose a n condition goal next ih =>
    intro env h
    obtain ⟨x, hx⟩ := valid.1 env h
    have result := ih _ valid.2.2 (x, env) ⟨h, hx⟩
    rw [valid.2.1, Expr.eval_weaken] at result
    exact result
  | «suffices» p goal next ih =>
    intro env h
    apply valid.2.1 env h
    have result := ih _ valid.2.2 env h
    rw [valid.1] at result
    exact result

#assert_lean_mirror_axioms Argument.sound


/-- Structured formulas support prose and calculation layout without reparsing TeX. -/
def Expr.toDocumentJson {S : Ty → Type} (v : Vocabulary S) {Γ : List Ty}
    (vars : List String) (e : Expr S Γ .prop) : Lean.Json :=
  let atom := Lean.Json.mkObj [("kind", .str "formula"), ("latex", .str (e.latex v vars))]
  match e with
  | .all (a := a) n body => Lean.Json.mkObj [("kind", .str "forall"), ("name", .str n),
      ("binding", .str (v.binderLatex a n)), ("type", .str (v.typeLatex a)), ("body", body.toDocumentJson v (n :: vars)),
      ("latex", .str (e.latex v vars))]
  | .ex (a := a) n body => Lean.Json.mkObj [("kind", .str "exists"), ("name", .str n),
      ("binding", .str (v.binderLatex a n)), ("type", .str (v.typeLatex a)), ("body", body.toDocumentJson v (n :: vars)),
      ("latex", .str (e.latex v vars))]
  | .imp p q => Lean.Json.mkObj [("kind", .str "imp"), ("premise", p.toDocumentJson v vars),
      ("body", q.toDocumentJson v vars), ("latex", .str (e.latex v vars))]
  | .iff p q => Lean.Json.mkObj [("kind", .str "iff"),
      ("left", p.toDocumentJson v vars), ("right", q.toDocumentJson v vars),
      ("latex", .str (e.latex v vars))]
  | .and p q => Lean.Json.mkObj [("kind", .str "and"),
      ("left", p.toDocumentJson v vars), ("right", q.toDocumentJson v vars),
      ("latex", .str (e.latex v vars))]
  | .or p q => Lean.Json.mkObj [("kind", .str "or"),
      ("left", p.toDocumentJson v vars), ("right", q.toDocumentJson v vars),
      ("latex", .str (e.latex v vars))]
  | .eq x y => Lean.Json.mkObj [("kind", .str "relation"), ("operator", .str "="),
      ("left", .str (x.latex v vars)), ("right", .str (y.latex v vars)), ("latex", .str (e.latex v vars))]
  | .le x y => Lean.Json.mkObj [("kind", .str "relation"), ("operator", .str "\\le"),
      ("left", .str (x.latex v vars)), ("right", .str (y.latex v vars)), ("latex", .str (e.latex v vars))]
  | .lt x y => Lean.Json.mkObj [("kind", .str "relation"), ("operator", .str "<"),
      ("left", .str (x.latex v vars)), ("right", .str (y.latex v vars)), ("latex", .str (e.latex v vars))]
  | _ => atom

/-- Deterministic view of the checked tree; scope nesting is retained. -/
def Argument.toJson {S : Ty → Type} (v : Vocabulary S) {Γ : List Ty}
    (vars : List String) : Argument S Γ → Lean.Json
  | .finish p => Lean.Json.mkObj [("kind", .str "finish"), ("claim", .str (p.latex v vars)), ("formula", p.toDocumentJson v vars)]
  | .have p next => Lean.Json.mkObj [("kind", .str "have"), ("claim", .str (p.latex v vars)), ("formula", p.toDocumentJson v vars),
      ("next", next.toJson v vars)]
  | .fix a n next => Lean.Json.mkObj [("kind", .str "fix"), ("name", .str n),
      ("binding", .str (v.binderLatex a n)), ("type", .str (v.typeLatex a)), ("next", next.toJson v (n :: vars))]
  | .assume p next => Lean.Json.mkObj [("kind", .str "assume"), ("claim", .str (p.latex v vars)), ("formula", p.toDocumentJson v vars),
      ("next", next.toJson v vars)]
  | .choose a n p goal next => Lean.Json.mkObj [("kind", .str "choose"), ("name", .str n),
      ("binding", .str (v.binderLatex a n)), ("type", .str (v.typeLatex a)), ("claim", .str (p.latex v (n :: vars))), ("formula", p.toDocumentJson v (n :: vars)),
      ("goal", .str (goal.latex v vars)), ("next", next.toJson v (n :: vars))]
  | .suffices p goal next => Lean.Json.mkObj [("kind", .str "suffices"),
      ("claim", .str (p.latex v vars)), ("formula", p.toDocumentJson v vars), ("goal", .str (goal.latex v vars)), ("next", next.toJson v vars)]


/-- Data view. Use `checked_document%` to obtain this from an audited certificate. -/
def Argument.documentJson {S : Ty → Type} (v : Vocabulary S) (doc : Argument S []) : Lean.Json :=
  Lean.Json.mkObj [("statement", doc.goal.toDocumentJson v []), ("proof", doc.toJson v [])]

open Lean Elab Meta in
/-- Select the document directly from the type of an audited, closed validity theorem.
    Its noncomputable mathematical model stays in the proof, not in runtime output. -/
elab "checked_document% " "(" vocabulary:term ")" certificate:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo certificate
  let info ← getConstInfo name
  unless info matches .thmInfo _ do throwErrorAt certificate "expected a validity theorem"
  let type := info.type
  unless type.isAppOfArity ``Argument.Valid 5 do
    throwErrorAt certificate "expected a closed Argument.Valid certificate"
  let args := type.getAppArgs
  unless ← isDefEq args[2]! (← mkListLit (mkConst ``Ty) []) do
    throwErrorAt certificate "document has free variables"
  let .forallE _ domain _ _ ← whnf (← inferType args[3]!)
    | throwErrorAt certificate "invalid assumption context"
  unless ← isDefEq args[3]! (mkLambda `_ .default domain (mkConst ``True)) do
    throwErrorAt certificate "document has unacknowledged assumptions"
  for ax in ← collectAxioms name do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwErrorAt certificate "document depends on nonstandard axiom {ax}"
  let v ← Term.elabTerm vocabulary none
  mkAppM ``Argument.documentJson #[v, args[4]!]

end LeanMirror
