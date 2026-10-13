import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Terms compiled from TeX

Every symbol that an article introduces is a *global definition*: its value is
the denotation of the article's own defining formula. There is no model to
choose. The only fixed interpretation is the paper-independent prelude below
(`Prim`), which gives standard mathematical notation its usual mathlib meaning.

Partial operations are total here (as in mathlib), but every compiled term also
has a syntactic *definedness condition* (`Tm.defined`). A compiled claim means
`defined ∧ claim`, so a formula such as `1/0 = 0` or a real power of a negative
number cannot become true for a conventional reason.
-/

namespace LeanMirror.Tex
open MeasureTheory
open scoped unitInterval

inductive Ty where
  | real | unit | prop
  | fn (a b : Ty)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

infixr:60 " ⟶ " => Ty.fn

@[reducible] def Ty.denote : Ty → Type
  | .real => ℝ
  | .unit => I
  | .prop => Prop
  | .fn a b => a.denote → b.denote

def Ty.default : (t : Ty) → t.denote
  | .real => (0 : ℝ)
  | .unit => (0 : I)
  | .prop => False
  | .fn _ b => fun _ => b.default

/-- Subsets of the unit square, read as two-place predicates. -/
abbrev Ty.set2 : Ty := .unit ⟶ .unit ⟶ .prop
abbrev Ty.set1 : Ty := .unit ⟶ .prop
/-- Set functions on the unit square (laws of random pairs). -/
abbrev Ty.meas2 : Ty := Ty.set2 ⟶ .real
/-- Functions on the unit square, such as distribution functions. -/
abbrev Ty.sq : Ty := .unit ⟶ .unit ⟶ .real
abbrev Ty.self : Ty := .unit ⟶ .unit
abbrev Ty.rfun : Ty := .real ⟶ .real

/-- The prelude: standard notions with their usual mathlib meaning. These are
the only symbols whose meaning is not given by the article itself. -/
inductive Prim where
  | rpow | min | max
  /-- Lebesgue measure of a subset of `[0,1]`. -/
  | leb
  /-- Distribution function of a probability measure on `[0,1]^2`. -/
  | distFn2
  /-- Marginal distribution functions `F(·,1)` and `F(1,·)` are uniform. -/
  | dfUniformMarginals
  /-- A probability measure on `[0,1]^2`, as a set function on measurable sets. -/
  | probMeasure2
  /-- Both coordinate laws of a probability measure on `[0,1]^2` are uniform. -/
  | measUniformMarginals
  /-- Borel measurability of a map `[0,1] → [0,1]`. -/
  | borel
  | measurableSet1 | measurableSet2
  /-- Lebesgue integrability on `[0,1]`. -/
  | integrable
  /-- `hasDerivWithin f S x d`: `f` has derivative `d` at `x` within `S`. -/
  | hasDerivWithin
  deriving DecidableEq, Repr, Lean.ToExpr

def Prim.ty : Prim → Ty
  | .rpow | .min | .max => .real ⟶ .real ⟶ .real
  | .leb => Ty.set1 ⟶ .real
  | .distFn2 | .dfUniformMarginals => Ty.sq ⟶ .prop
  | .probMeasure2 | .measUniformMarginals => Ty.meas2 ⟶ .prop
  | .borel => Ty.self ⟶ .prop
  | .measurableSet1 => Ty.set1 ⟶ .prop
  | .measurableSet2 => Ty.set2 ⟶ .prop
  | .integrable => (.unit ⟶ .real) ⟶ .prop
  | .hasDerivWithin => Ty.rfun ⟶ (.real ⟶ .prop) ⟶ .real ⟶ .real ⟶ .prop

namespace Prelude
noncomputable def leb (A : I → Prop) : ℝ := (volume {x : I | A x}).toReal
def distFn2 (F : I → I → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ u v : I, F u v = (μ (Set.Iic u ×ˢ Set.Iic v)).toReal
def dfUniformMarginals (F : I → I → ℝ) : Prop :=
  (∀ u : I, F u 1 = u) ∧ ∀ v : I, F 1 v = v
def probMeasure2 (γ : (I → I → Prop) → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ A : I → I → Prop, MeasurableSet {p : I × I | A p.1 p.2} →
      γ A = (μ {p : I × I | A p.1 p.2}).toReal
def measUniformMarginals (γ : (I → I → Prop) → ℝ) : Prop :=
  (∀ u : I, γ (fun x _ => x ≤ u) = u) ∧ ∀ v : I, γ (fun _ z => z ≤ v) = v
def measurableSet1 (A : I → Prop) : Prop := MeasurableSet {x : I | A x}
def measurableSet2 (A : I → I → Prop) : Prop := MeasurableSet {p : I × I | A p.1 p.2}
def integrable (f : I → ℝ) : Prop := Integrable f
def hasDerivWithin (f : ℝ → ℝ) (S : ℝ → Prop) (x d : ℝ) : Prop :=
  HasDerivWithinAt f d {y | S y} x
end Prelude

noncomputable def Prim.denote : (p : Prim) → p.ty.denote
  | .rpow => fun x y => x ^ y
  | .min => fun x y => Min.min x y
  | .max => fun x y => Max.max x y
  | .leb => Prelude.leb
  | .distFn2 => Prelude.distFn2
  | .dfUniformMarginals => Prelude.dfUniformMarginals
  | .probMeasure2 => Prelude.probMeasure2
  | .measUniformMarginals => Prelude.measUniformMarginals
  | .borel => fun T => Measurable T
  | .measurableSet1 => Prelude.measurableSet1
  | .measurableSet2 => Prelude.measurableSet2
  | .integrable => Prelude.integrable
  | .hasDerivWithin => Prelude.hasDerivWithin

/-- Untyped core terms with de Bruijn locals and indexed article definitions.
Types are checked by `typeOf`; ill-typed terms have no denotation. -/
inductive Tm where
  | glob (i : Nat)
  | loc (i : Nat)
  | prim (p : Prim)
  | app (f x : Tm)
  /-- `lam t dom body`: a function on `t`; `dom` (a proposition about the bound
  variable) is its declared domain, used only for definedness. -/
  | lam (t : Ty) (dom body : Tm)
  | num (n : Nat)
  | ofUnit (x : Tm)
  /-- A real number used as a point of `[0,1]`; defined only inside `[0,1]`. -/
  | toUnit (x : Tm)
  | add (x y : Tm) | sub (x y : Tm) | mul (x y : Tm) | div (x y : Tm)
  | neg (x : Tm) | abs (x : Tm)
  | powNat (x : Tm) (n : Nat)
  /-- `cases c v rest`: the first branch whose condition holds. -/
  | cases (c v rest : Tm)
  | undef (t : Ty)
  | eq (x y : Tm) | lt (x y : Tm) | le (x y : Tm)
  | tt
  | not (p : Tm) | and (p q : Tm) | or (p q : Tm) | imp (p q : Tm) | iff (p q : Tm)
  | all (t : Ty) (body : Tm) | ex (t : Ty) (body : Tm)
  /-- Integral over `[0,1]` of a body in one new local of type `[0,1]`. -/
  | integral (body : Tm)
  /-- Semantically transparent; contributes the condition to definedness. -/
  | guard (c e : Tm)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

def typeOf (gs : List Ty) (ls : List Ty) : Tm → Option Ty
  | .glob i => gs[i]?
  | .loc i => ls[i]?
  | .prim p => some p.ty
  | .app f x =>
    match typeOf gs ls f, typeOf gs ls x with
    | some (.fn a b), some a' => if a' = a then some b else none
    | _, _ => none
  | .lam t _ body =>
    match typeOf gs (t :: ls) body with
    | some b => some (.fn t b)
    | none => none
  | .num _ => some .real
  | .ofUnit x =>
    match typeOf gs ls x with
    | some .unit => some .real
    | _ => none
  | .toUnit x =>
    match typeOf gs ls x with
    | some .real => some .unit
    | _ => none
  | .add x y | .sub x y | .mul x y | .div x y =>
    match typeOf gs ls x, typeOf gs ls y with
    | some .real, some .real => some .real
    | _, _ => none
  | .neg x | .abs x | .powNat x _ =>
    match typeOf gs ls x with
    | some .real => some .real
    | _ => none
  | .cases _ v _ => typeOf gs ls v
  | .undef t => some t
  | .eq _ _ | .lt _ _ | .le _ _ | .tt | .not _ | .and _ _ | .or _ _ | .imp _ _ | .iff _ _
  | .all _ _ | .ex _ _ => some .prop
  | .integral _ => some .real
  | .guard _ e => typeOf gs ls e

abbrev Val := Σ t : Ty, t.denote

/-- Numerals: `0`, `1` and `(n : ℝ)` for larger `n`. -/
def numVal : Nat → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((n + 2 : ℕ) : ℝ)

def Val.cast (b : Ty) : Option Val → b.denote
  | some ⟨a, v⟩ => if h : a = b then h ▸ v else b.default
  | none => b.default

def Val.prop : Option Val → Prop
  | some ⟨.prop, P⟩ => P
  | _ => False

private def real2 (x y : Option Val) (f : ℝ → ℝ → ℝ) : Option Val :=
  match x, y with
  | some ⟨.real, a⟩, some ⟨.real, b⟩ => some ⟨.real, f a b⟩
  | _, _ => none

private def rel2 (x y : Option Val) (f : ℝ → ℝ → Prop) : Option Val :=
  match x, y with
  | some ⟨.real, a⟩, some ⟨.real, b⟩ => some ⟨.prop, f a b⟩
  | _, _ => none

private def prop2 (x y : Option Val) (f : Prop → Prop → Prop) : Option Val :=
  match x, y with
  | some ⟨.prop, a⟩, some ⟨.prop, b⟩ => some ⟨.prop, f a b⟩
  | _, _ => none

/-- The meaning of a core term, given the values of article definitions and locals. -/
noncomputable def denote (G : List Val) : List Val → Tm → Option Val
  | _, .glob i => G[i]?
  | L, .loc i => L[i]?
  | _, .prim p => some ⟨p.ty, p.denote⟩
  | L, .app f x =>
    match denote G L f, denote G L x with
    | some ⟨.fn a b, F⟩, some ⟨a', X⟩ => if h : a' = a then some ⟨b, F (h ▸ X)⟩ else none
    | _, _ => none
  | L, .lam t _ body =>
    match typeOf (G.map (·.1)) (t :: L.map (·.1)) body with
    | some b => some ⟨.fn t b, fun x => Val.cast b (denote G (⟨t, x⟩ :: L) body)⟩
    | none => none
  | _, .num n => some ⟨.real, numVal n⟩
  | L, .ofUnit x =>
    match denote G L x with
    | some ⟨.unit, u⟩ => some ⟨.real, (u : ℝ)⟩
    | _ => none
  | L, .toUnit x =>
    match denote G L x with
    | some ⟨.real, r⟩ => some ⟨.unit, Set.projIcc 0 1 zero_le_one r⟩
    | _ => none
  | L, .add x y => real2 (denote G L x) (denote G L y) (· + ·)
  | L, .sub x y => real2 (denote G L x) (denote G L y) (· - ·)
  | L, .mul x y => real2 (denote G L x) (denote G L y) (· * ·)
  | L, .div x y => real2 (denote G L x) (denote G L y) (· / ·)
  | L, .neg x =>
    match denote G L x with
    | some ⟨.real, r⟩ => some ⟨.real, -r⟩
    | _ => none
  | L, .abs x =>
    match denote G L x with
    | some ⟨.real, r⟩ => some ⟨.real, |r|⟩
    | _ => none
  | L, .powNat x n =>
    match denote G L x with
    | some ⟨.real, r⟩ => some ⟨.real, r ^ n⟩
    | _ => none
  | L, .cases c v rest =>
    match denote G L c, denote G L v, denote G L rest with
    | some ⟨.prop, P⟩, some ⟨a, x⟩, some ⟨b, y⟩ =>
      if h : b = a then some ⟨a, @ite _ P (Classical.propDecidable P) x (h ▸ y)⟩ else none
    | _, _, _ => none
  | _, .undef t => some ⟨t, t.default⟩
  | L, .eq x y =>
    match denote G L x, denote G L y with
    | some ⟨a, u⟩, some ⟨b, v⟩ => if h : b = a then some ⟨.prop, u = h ▸ v⟩ else none
    | _, _ => none
  | L, .lt x y => rel2 (denote G L x) (denote G L y) (· < ·)
  | L, .le x y => rel2 (denote G L x) (denote G L y) (· ≤ ·)
  | _, .tt => some ⟨.prop, True⟩
  | L, .not p =>
    match denote G L p with
    | some ⟨.prop, P⟩ => some ⟨.prop, ¬P⟩
    | _ => none
  | L, .and p q => prop2 (denote G L p) (denote G L q) (· ∧ ·)
  | L, .or p q => prop2 (denote G L p) (denote G L q) (· ∨ ·)
  | L, .imp p q => prop2 (denote G L p) (denote G L q) (· → ·)
  | L, .iff p q => prop2 (denote G L p) (denote G L q) (· ↔ ·)
  | L, .all t body => some ⟨.prop, ∀ x : t.denote, Val.prop (denote G (⟨t, x⟩ :: L) body)⟩
  | L, .ex t body => some ⟨.prop, ∃ x : t.denote, Val.prop (denote G (⟨t, x⟩ :: L) body)⟩
  | L, .integral body =>
    some ⟨.real, ∫ x : I, Val.cast .real (denote G (⟨.unit, x⟩ :: L) body)⟩
  | L, .guard _ e => denote G L e

namespace Tm

/-- Conjunction, implication and universal closure that omit trivial parts.
(`defined` is a definition; omitting `True` keeps it readable.) -/
def mkAnd : Tm → Tm → Tm
  | .tt, q => q
  | p, .tt => p
  | p, q => .and p q

def mkImp : Tm → Tm → Tm
  | _, .tt => .tt
  | .tt, q => q
  | p, q => .imp p q

def mkAll (t : Ty) : Tm → Tm
  | .tt => .tt
  | b => .all t b

/-- The syntactic definedness condition of a term (left-to-right, as for TCCs). -/
def defined : Tm → Tm
  | .glob _ | .loc _ | .prim _ | .num _ | .tt => .tt
  | .undef _ => .not .tt
  | .app f x => mkAnd (defined f) (defined x)
  | .lam t dom body => mkAll t (mkImp dom (defined body))
  | .ofUnit x | .neg x | .abs x | .powNat x _ | .not x => defined x
  | .toUnit x => mkAnd (defined x) (.and (.le (.num 0) x) (.le x (.num 1)))
  | .add x y | .sub x y | .mul x y | .eq x y | .lt x y | .le x y | .iff x y =>
      mkAnd (defined x) (defined y)
  | .div x y => mkAnd (defined x) (mkAnd (defined y) (.not (.eq y (.num 0))))
  | .cases c v rest =>
      mkAnd (defined c) (mkAnd (mkImp c (mkAnd (defined v) (agreesDefined rest v)))
        (mkImp (.not c) (defined rest)))
  | .and p q | .imp p q => mkAnd (defined p) (mkImp p (defined q))
  | .or p q => mkAnd (defined p) (mkImp (.not p) (defined q))
  | .all t body | .ex t body => mkAll t (defined body)
  | .integral body => mkAnd (mkAll .unit (defined body))
      (.app (.prim .integrable) (.lam .unit .tt body))
  -- a guard's condition must hold (e.g. an argument lies in the function's domain)
  | .guard c e => mkAnd (defined c) (mkAnd c (defined e))
where
  /-- Later branches that also apply must be defined and agree. -/
  agreesDefined : Tm → Tm → Tm
    | .cases c w rest, v => mkAnd (mkImp c (mkAnd (defined w) (.eq w v))) (agreesDefined rest v)
    | _, _ => .tt

/-- What a compiled claim asserts: it is meaningful, and it holds. -/
def sound (p : Tm) : Tm := .and (defined p) p

end Tm

/-- The values of an article's definitions, evaluated in order. Definition `i`
is `Tm.glob i`; it may refer only to earlier definitions. -/
noncomputable def evalDefs : List Val → List Tm → Option (List Val)
  | G, [] => some G
  | G, d :: ds =>
    match denote G [] d with
    | some v => evalDefs (G ++ [v]) ds
    | none => none

end LeanMirror.Tex
