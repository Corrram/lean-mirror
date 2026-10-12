import LeanMirror
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.PNat.Interval
import Mathlib.Data.PNat.Order
import Mathlib.Tactic

/-! Companion to selected passages of Jiří Lebl, Basic Analysis I, §2.1.
    Adapted mathematical exposition: CC BY-SA 4.0. Generic engine: Apache-2.0.
    Positive integer indices preserve the source convention exactly. -/
namespace LeanMirror.Examples.Analysis
open Filter
open scoped Topology
abbrev idx : Ty := .base "index"
abbrev seq : Ty := idx ⇒ₘ .real
open Ty
set_option linter.unusedSimpArgs false
abbrev Sequence := ℕ+ → ℝ

def Converges (s : Sequence) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℕ+, ∀ n ≥ M, |s n - x| < ε

def Bounded (s : Sequence) : Prop := ∃ B : ℝ, ∀ n, |s n| ≤ B

noncomputable def prefixBound (s : Sequence) (x : ℝ) (M : ℕ+) : ℝ :=
  (insert (1 + |x|) ((Finset.Iio M).image fun n => |s n|)).sup'
    (Finset.insert_nonempty _ _) id

inductive Symbol : Ty → Type where
  | limit : Symbol (seq ⇒ₘ real ⇒ₘ prop)
  | bounded : Symbol (seq ⇒ₘ prop)
  | value : Symbol (seq ⇒ₘ idx ⇒ₘ real)
  | indexLe : Symbol (idx ⇒ₘ idx ⇒ₘ prop)
  | prefixMax : Symbol (seq ⇒ₘ real ⇒ₘ idx ⇒ₘ real)

noncomputable def model : Model Symbol where
  base _ := ℕ+
  symbol
    | .limit => Converges
    | .bounded => Bounded
    | .value => fun s n => s n
    | .indexLe => fun (m n : ℕ+) => m ≤ n
    | .prefixMax => prefixBound
open Symbol

def limitDefinition : Expr Symbol [real, seq] prop :=
  (.all "\\epsilon" [math| s, x, e |- 0 < e \implies
    Exists M : idx. Forall n : idx. \indexLe(M,n) \implies \abs{\value(s,n)-x} < e])

def boundedDefinition : Expr Symbol [seq] prop :=
  [math| s |- Exists B : real. Forall n : idx. \abs{\value(s,n)} \le B]

theorem limit_definition (s : Sequence) (x : ℝ) :
    limitDefinition.eval model (x, s, ()) ↔ Converges s x := by
  simp only [limitDefinition, Expr.eval, model, Var.get, Converges, Nat.cast_zero]

theorem limit_mathlib (s : Sequence) (x : ℝ) :
    Converges s x ↔ Tendsto s atTop (𝓝 x) := by
  simpa only [Converges, Real.dist_eq] using
    (Metric.tendsto_atTop (u := s) (a := x)).symm

theorem bounded_definition (s : Sequence) :
    boundedDefinition.eval model (s, ()) ↔ Bounded s := Iff.rfl

theorem bounded_mathlib (s : Sequence) :
    Bounded s ↔ Bornology.IsBounded (Set.range s) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
  simp only [Bounded, Set.subset_def, Set.mem_range, Metric.mem_closedBall, Real.dist_eq,
    sub_zero, forall_exists_index, forall_apply_eq_imp_iff]

-- The original epsilon / 2 argument, with every choice and estimate retained.
def uniqueProof : Argument Symbol [] :=
  .fix seq "x" <| .fix real "x" <| .fix real "y" <|
  .assume [math| s,x,y |- \limit(s,x) \land \limit(s,y)] <|
  .suffices (.all "\\epsilon" [math| s,x,y,e |- 0 < e \implies \abs{y-x} < e])
    [math| s,x,y |- y = x] <|
  .fix real "\\epsilon" <|
  .assume [math| s,x,y,e |- 0 < e] <|
  .choose idx "M_1"
    [math| s,x,y,e,M |- Forall n : idx. \indexLe(M,n) \implies \abs{\value(s,n)-x} < \frac{e}{2}]
    [math| s,x,y,e |- \abs{y-x} < e] <|
  .choose idx "M_2"
    [math| s,x,y,e,M1,M2 |- Forall n : idx. \indexLe(M2,n) \implies \abs{\value(s,n)-y} < \frac{e}{2}]
    [math| s,x,y,e,M1 |- \abs{y-x} < e] <|
  .choose idx "n"
    [math| s,x,y,e,M1,M2,n |- \indexLe(M1,n) \land \indexLe(M2,n)]
    [math| s,x,y,e,M1,M2 |- \abs{y-x} < e] <|
  .have [math| s,x,y,e,M1,M2,n |- \abs{y-x} = \abs{(\value(s,n)-x)-(\value(s,n)-y)}] <|
  .have [math| s,x,y,e,M1,M2,n |- \abs{(\value(s,n)-x)-(\value(s,n)-y)} \le
    \abs{\value(s,n)-x} + \abs{\value(s,n)-y}] <|
  .have [math| s,x,y,e,M1,M2,n |- \abs{\value(s,n)-x} + \abs{\value(s,n)-y} <
    \frac{e}{2} + \frac{e}{2}] <|
  .have [math| s,x,y,e,M1,M2,n |- \frac{e}{2} + \frac{e}{2} = e] <|
  .finish [math| s,x,y,e,M1,M2,n |- \abs{y-x} < e]

-- Finite maxima include the tail bound, so the set stays nonempty when M = 1.
theorem prefix_tail (s : Sequence) (x : ℝ) (M : ℕ+) : 1 + |x| ≤ prefixBound s x M := by
  classical
  exact Finset.le_sup' id (Finset.mem_insert_self _ _)

theorem prefix_initial (s : Sequence) (x : ℝ) (M n : ℕ+) (h : n < M) :
    |s n| ≤ prefixBound s x M := by
  classical
  apply Finset.le_sup' id (s := insert (1 + |x|) ((Finset.Iio M).image fun n => |s n|))
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, Finset.mem_Iio.mpr h, rfl⟩)

def boundedProof : Argument Symbol [] := [proof|
  Fix s : seq named "x";
  Fix x : real named "x";
  Assume \limit(s,x);
  Choose M : idx named "M" satisfying
    Forall n : idx. \indexLe(M,n) \implies \abs{\value(s,n)-x} < 1
    to prove \bounded(s);
  Have Forall n : idx. \indexLe(M,n) \implies
    \abs{\value(s,n)} = \abs{\value(s,n)-x+x};
  Have Forall n : idx. \indexLe(M,n) \implies
    \abs{\value(s,n)-x+x} \le \abs{\value(s,n)-x} + \abs{x};
  Have Forall n : idx. \indexLe(M,n) \implies
    \abs{\value(s,n)-x} + \abs{x} < 1 + \abs{x};
  Choose B : real named "B" satisfying B = \prefixMax(s,x,M) to prove \bounded(s);
  Have Forall n : idx. \abs{\value(s,n)} \le B;
  Conclude \bounded(s)]

-- These validation proofs must follow the document tree: changing a displayed
-- assertion changes the required proof at that node, even if the theorem is true.
theorem unique_valid : uniqueProof.Valid model (fun _ => True) := by
  simp only [uniqueProof, Argument.Valid, Argument.goal, Expr.weaken, Expr.rename, Expr.liftRen,
    Expr.eval, Var.get, model, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, idx, seq, Ty.denote]
  constructor
  · trivial
  constructor
  · rintro ⟨y,x,s,⟨⟩⟩ _ h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun e he =>
      by simpa using (h e he).le) (abs_nonneg _)))
  · refine ⟨?_, trivial, ?_⟩
    · rintro ⟨e,y,x,s,⟨⟩⟩ ⟨⟨_,hx,hy⟩,he⟩
      exact hx (e/2) (half_pos he)
    · refine ⟨?_, trivial, ?_⟩
      · rintro ⟨M1,e,y,x,s,⟨⟩⟩ ⟨⟨⟨_,hx,hy⟩,he⟩,_⟩
        exact hy (e/2) (half_pos he)
      · refine ⟨?_, trivial, ?_⟩
        · rintro ⟨M2,M1,e,y,x,s,⟨⟩⟩ _
          exact ⟨max M1 M2, le_max_left _ _, le_max_right _ _⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rintro ⟨n,M2,M1,e,y,x,s,⟨⟩⟩ _
            congr 1
            ring
          · rintro ⟨n,M2,M1,e,y,x,s,⟨⟩⟩ _
            exact abs_sub _ _
          · rintro ⟨n,M2,M1,e,y,x,s,⟨⟩⟩ ⟨⟨⟨⟨⟨_,h1⟩,h2⟩,hn⟩,_⟩,_⟩
            exact add_lt_add (h1 n hn.1) (h2 n hn.2)
          · rintro ⟨n,M2,M1,e,y,x,s,⟨⟩⟩ _
            ring
          · rintro ⟨n,M2,M1,e,y,x,s,⟨⟩⟩ ⟨⟨⟨⟨_,h1⟩,h2⟩,h3⟩,h4⟩
            linarith

theorem bounded_valid : boundedProof.Valid model (fun _ => True) := by
  simp only [boundedProof, Argument.Valid, Argument.goal, Expr.weaken, Expr.rename, Expr.liftRen,
    Expr.eval, Var.get, model, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, idx, seq, Ty.denote]
  refine ⟨?_, trivial, ?_⟩
  · rintro ⟨x,s,⟨⟩⟩ ⟨_,hx⟩
    exact hx 1 zero_lt_one
  · refine ⟨?_, ?_, ?_, ?_, trivial, ?_, ?_⟩
    · rintro ⟨M,x,s,⟨⟩⟩ _ n _
      simp
    · rintro ⟨M,x,s,⟨⟩⟩ _ n _
      exact abs_add_le _ _
    · rintro ⟨M,x,s,⟨⟩⟩ ⟨⟨⟨_,h⟩,_⟩,_⟩ n hn
      have := h n hn
      linarith
    · rintro ⟨M,x,s,⟨⟩⟩ _
      exact ⟨prefixBound s x M, rfl⟩
    · rintro ⟨B,M,x,s,⟨⟩⟩ ⟨⟨⟨⟨_,h1⟩,h2⟩,h3⟩,hB⟩ n
      dsimp at *
      subst B
      by_cases hn : M ≤ n
      · have ht : |s n| < 1 + |x| := by
          rw [h1 n hn]
          exact lt_of_le_of_lt (h2 n hn) (h3 n hn)
        exact ht.le.trans (prefix_tail s x M)
      · exact prefix_initial s x M n (lt_of_not_ge hn)
    · rintro ⟨B,M,x,s,⟨⟩⟩ ⟨_,h⟩
      exact ⟨B,h⟩

theorem unique_verified : uniqueProof.goal.eval model () :=
  uniqueProof.sound model _ unique_valid () trivial

theorem bounded_verified : boundedProof.goal.eval model () :=
  boundedProof.sound model _ bounded_valid () trivial


-- Statement bridges use only the definition correspondences above.
theorem index_cofinite : (cofinite : Filter ℕ+) = atTop := by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun M _ => ?_
  simpa only [mem_cofinite, Set.compl_Ici] using (Set.finite_Iio M)

def UniqueTarget : Prop := statement_of% (fun (s : Sequence) (x y : ℝ)
    (hx : Tendsto s atTop (𝓝 x)) (hy : Tendsto s atTop (𝓝 y)) =>
    (tendsto_nhds_unique hx hy).symm)

def BoundedTarget : Prop := statement_of% (fun (s : Sequence) (x : ℝ)
    (hx : Tendsto s atTop (𝓝 x)) =>
    Metric.isBounded_range_of_tendsto_cofinite (f := s) (by rwa [index_cofinite]))

theorem unique_correspondence : uniqueProof.goal.eval model () ↔ UniqueTarget := by
  simp only [uniqueProof, Argument.goal, Expr.eval, model, Var.get, UniqueTarget,
    limit_mathlib, and_imp]

theorem bounded_correspondence : boundedProof.goal.eval model () ↔ BoundedTarget := by
  simp only [boundedProof, Argument.goal, Expr.eval, model, Var.get, BoundedTarget,
    limit_mathlib, bounded_mathlib]

#assert_lean_mirror_axioms unique_correspondence
#assert_lean_mirror_axioms bounded_correspondence
#assert_lean_mirror_axioms limit_definition
#assert_lean_mirror_axioms limit_mathlib
#assert_lean_mirror_axioms bounded_definition
#assert_lean_mirror_axioms bounded_mathlib
#assert_lean_mirror_axioms unique_valid
#assert_lean_mirror_axioms bounded_valid
#assert_lean_mirror_axioms unique_verified
#assert_lean_mirror_axioms bounded_verified

end LeanMirror.Examples.Analysis
