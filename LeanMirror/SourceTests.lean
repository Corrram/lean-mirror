import LeanMirror.Source.Export

namespace LeanMirror.SourceTests
open Source
open scoped unitInterval
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

inductive Symbol : Ty → Type where
  | positive : Symbol (.real ⇒ₘ .prop)
  | coefficient : Symbol (.real ⇒ₘ .real)

def language : Language Symbol where
  domains := [⟨"positive real number", "positive", .real, some "\\positive"⟩]
  constants := [⟨"\\positive", "positive", _, .positive⟩,
    ⟨"\\f", "coefficient", _, .coefficient⟩]

noncomputable def model : Model Symbol where
  base _ := Unit
  symbol | .positive => fun x => 0 < x | .coefficient => fun x => x

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

-- Kernel-checked scope, implication and arithmetic precedence, from source.
def scopedStatement := source% (language) r#"If \(x\) is a positive real number, then \(x < x+1\)."#
example : scopedStatement.eval model () ↔ ∀ x : ℝ, 0 < x → x < x + 1 := by
  simp only [scopedStatement, Expr.eval, model, Var.get, Nat.cast_one]

def precedence := source% (language) r#"Let \(x\) be a real number. \(x+2*3=x+6\)."#
example : precedence.eval model () ↔ ∀ x : ℝ, x + 2 * 3 = x + 6 := Iff.rfl

def chain := source% (language) r#"For every \(x\in\mathbb{R}\), \(x=\f(x)=x\)."#
example : chain.eval model () ↔ ∀ x : ℝ, x = model.symbol .coefficient x ∧ model.symbol .coefficient x = x := Iff.rfl

def witnesses := source% (language) r#"For every \(a\in[0,1]\), there exists a real number \(x\) such that \(a=x\)."#
example : witnesses.eval model () ↔ ∀ a : I, ∃ x : ℝ, (a : ℝ) = x := Iff.rfl

def independent := source% (language) r#"If \(x\) is a positive real number, then \(0<x\). For every \(x\in\mathbb{R}\), \(x=x\)."#
example : independent.eval model () ↔ (∀ x : ℝ, 0 < x → 0 < x) ∧ (∀ x : ℝ, x = x) := by
  simp only [independent, Expr.eval, model, Var.get, Nat.cast_zero]

def implication := source% (language) r#"\(0=0 \implies 0=1 \implies 1=0\)."#
example : implication.eval model () ↔ ((0 : ℝ) = 0 → (0 : ℝ) = 1 → (1 : ℝ) = 0) := by
  simp only [implication, Expr.eval, Nat.cast_zero, Nat.cast_one]

-- Unknown clauses, commands, names, types, delimiters and shadowing fail closed.
#guard rejected (compile language r#"For every \(x\in\mathbb{R}\), \(x=x\), and both inequalities are sharp."#)
#guard rejected (compile language r#"\(y=y\)."#)
#guard rejected (compile language r#"Let \(x\) be a real number. Let \(x\) be a real number. \(x=x\)."#)
#guard rejected (compile language r#"\(\undefined(1)=1\)."#)
#guard rejected (compile language r#"\(\positive(1)+1=2\)."#)
#guard rejected (compile language r#"If \(x\) is a copula, then \(x=x\)."#)
#guard rejected (compile language r#"\(1=1\]."#)
#guard rejected (compile language r#"\(1=1\). This is obvious."#)
#guard rejected (compile language r#"\newcommand{\f}{0} \(1=1\)."#)

-- Definition cards cannot hide partial domains, an unrelated equation or recursion.
#guard definitionKey language r#"For every \(x\in\mathbb{R}\), \(\positive(x)\iff 0<x\)."# == .ok "positive"
#guard rejected (definitionKey language r#"If \(x\) is a positive real number, then \(\f(x)=x\)."#)
#guard rejected (definitionKey language r#"For every \(x\in\mathbb{R}\), \(x=x\)."#)
#guard rejected (definitionKey language r#"For every \(x\in\mathbb{R}\), \(\f(x)=\f(x)\)."#)
#guard rejected (definitionKey language r#"For every \(x\in\mathbb{R}\), \(\f(1)=x\)."#)

def source := r#"\(1=1\)."#
def statement := source% (language) source
theorem checked : Source.Certificate model language source statement ((1 : ℝ) = 1) :=
  ⟨rfl, by simp only [statement, Expr.eval, Nat.cast_one], rfl⟩
example : Meaning model language source := checked.proved
def exported := checked_source% checked

-- A proof of a true target cannot certify a changed, false source statement.
def changedSource := r#"\(1=2\)."#
def changedStatement := source% (language) changedSource
example : ¬ Source.Certificate model language changedSource changedStatement ((1 : ℝ) = 1) := by
  intro h
  have bad := h.correspondence.mpr h.established
  norm_num [changedStatement, Expr.eval] at bad

-- A true final theorem does not certify a false displayed intermediate step.
def badProof := source_proof% (language) r#"Have \(0=1\). Hence \(1=1\)."#
example : ¬ badProof.Valid model (fun _ => True) := by
  intro h
  have bad : (0 : ℝ) = 1 := by
    simpa only [Expr.eval, Nat.cast_zero, Nat.cast_one] using h.1 () trivial
  exact zero_ne_one bad

def choice := source_proof% (language) r#"Let \(x\) be a real number. Choose a real number \(y\) such that \(y=x\) to prove \(x=x\). Hence \(x=x\)."#
example : choice.Valid model (fun _ => True) := by
  constructor
  · intro env _
    exact ⟨env.1, rfl⟩
  · exact ⟨rfl, fun _ _ => rfl⟩

#guard rejected (compileProof language r#"Hence \(1=1\). Have \(0=1\)."#)
#guard rejected (compileProof language r#"By an obvious argument, the result follows."#)

-- The exporter must audit every transitive dependency.
axiom extra : (1 : ℝ) = 1
theorem tainted : Source.Certificate model language source statement ((1 : ℝ) = 1) :=
  ⟨rfl, by simp only [statement, Expr.eval, Nat.cast_one], extra⟩
/-- error: source certificate depends on nonstandard axiom LeanMirror.SourceTests.extra -/
#guard_msgs in
def refused := checked_source% tainted

#assert_lean_mirror_axioms checked
end LeanMirror.SourceTests
