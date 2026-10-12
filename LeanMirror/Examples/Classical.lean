import LeanMirror
import Mathlib.Algebra.Order.Ring.Abs

/-! Classical real inequalities with precise readable statements and actual mathlib targets.
The correspondence proofs below use definitions only. The established proofs are
supplied separately by mathlib when constructing the certificates.
-/

namespace LeanMirror.Examples.Classical

inductive Symbol : Ty → Type where
  | realNumber : Symbol (.real ⇒ₘ .prop)
  | square : Symbol (.real ⇒ₘ .real)

noncomputable def model : Model Symbol where
  base _ := Unit
  symbol
    | .realNumber => fun _ => True
    | .square => fun x => x * x

theorem real_definition_eq (x : ℝ) : model.symbol .realNumber x ↔ True := Iff.rfl

theorem square_definition_eq (x : ℝ) : model.symbol .square x = x ^ 2 := by
  simp only [model, pow_two]

open Symbol

def triangleStatement : Expr Symbol [] .prop :=
  [math| |- Let x be realNumber. Let y be realNumber.
    \abs{x + y} \le \abs{x} + \abs{y}]

def productStatement : Expr Symbol [] .prop :=
  [math| |- Let x be realNumber. Let y be realNumber.
    \abs{x * y} = \abs{x} * \abs{y}]

def amgmStatement : Expr Symbol [] .prop :=
  [math| |- Let x be realNumber. Let y be realNumber.
    2 * x * y \le \square(x) + \square(y)]

-- Target propositions come from the types of actual specialized mathlib proofs.
-- No separately maintained copy of a mathlib theorem statement is needed.
def TriangleTarget : Prop := statement_of% (fun x y : ℝ => abs_add_le x y)
def ProductTarget : Prop := statement_of% (fun x y : ℝ => abs_mul x y)
def AmgmTarget : Prop := statement_of% (fun x y : ℝ => two_mul_le_add_sq x y)

theorem triangle_equivalence : triangleStatement.eval model () ↔ TriangleTarget := by
  simp only [triangleStatement, Expr.eval, model, Var.get, TriangleTarget, true_implies]

theorem product_equivalence : productStatement.eval model () ↔ ProductTarget := by
  simp only [productStatement, Expr.eval, model, Var.get, ProductTarget, true_implies]

theorem amgm_equivalence : amgmStatement.eval model () ↔ AmgmTarget := by
  simp only [amgmStatement, Expr.eval, model, Var.get, AmgmTarget, true_implies,
    Nat.cast_ofNat, pow_two]

theorem triangleCertificate : Certificate model triangleStatement TriangleTarget :=
  ⟨triangle_equivalence, fun x y => abs_add_le x y⟩

theorem productCertificate : Certificate model productStatement ProductTarget :=
  ⟨product_equivalence, fun x y => abs_mul x y⟩

theorem amgmCertificate : Certificate model amgmStatement AmgmTarget :=
  ⟨amgm_equivalence, fun x y => two_mul_le_add_sq x y⟩

theorem triangle_verified : triangleStatement.eval model () := triangleCertificate.proved
theorem product_verified : productStatement.eval model () := productCertificate.proved
theorem amgm_verified : amgmStatement.eval model () := amgmCertificate.proved

#assert_lean_mirror_axioms real_definition_eq
#assert_lean_mirror_axioms square_definition_eq
#assert_lean_mirror_axioms triangle_equivalence
#assert_lean_mirror_axioms product_equivalence
#assert_lean_mirror_axioms amgm_equivalence
#assert_lean_mirror_axioms triangleCertificate
#assert_lean_mirror_axioms productCertificate
#assert_lean_mirror_axioms amgmCertificate
#assert_lean_mirror_axioms triangle_verified
#assert_lean_mirror_axioms product_verified
#assert_lean_mirror_axioms amgm_verified

def vocabulary : Vocabulary Symbol where
  key | .realNumber => "real" | .square => "square"
  typeLatex | .real => "\\mathbb{R}" | _ => "\\mathrm{Object}"
  application
    | .realNumber, [x] => x ++ "\\in\\mathbb{R}"
    | .square, [x] => x ++ "^{2}"
    | .realNumber, _ => "\\mathbb{R}"
    | .square, _ => "\\operatorname{square}"
  noun | .realNumber => "real number"

def examples : List (String × Expr Symbol [] .prop × String) := [
  ("Triangle inequality", triangleStatement, "abs_add_le"),
  ("Absolute value of a product", productStatement, "abs_mul"),
  ("Quadratic arithmetic--geometric mean inequality", amgmStatement, "two_mul_le_add_sq")]

def latexDocument : String :=
  "\\documentclass[11pt]{article}\n" ++
  "\\usepackage[a4paper,margin=25mm]{geometry}\n" ++
  "\\usepackage{amsmath,amssymb,amsthm}\n" ++
  "\\newtheorem*{statement}{Theorem}\n" ++
  "\\begin{document}\n\\section*{LeanMirror: classical mathematics}\n" ++
  "The following statements are interpreted in Lean and proved equivalent to the " ++
  "indicated mathlib theorem specialized to real numbers.\n\n" ++
  String.intercalate "\n" (examples.map fun (title, statement, target) =>
    "\\subsection*{" ++ title ++ "}\n\\begin{statement}\n" ++
    statement.theoremLatex vocabulary ++ "\\end{statement}\n" ++
    "Mathlib counterpart: \\texttt{" ++ target.replace "_" "\\_" ++ "}.\n") ++
  "\\paragraph{Definitions and scope.} All variables are real numbers; $x^2$ denotes " ++
  "$x\\cdot x$. Absolute value, addition, multiplication, and order have their usual " ++
  "real-number interpretations in mathlib. The quadratic AM--GM form applies to all " ++
  "real $x,y$, with no nonnegativity hypothesis.\n" ++
  "\\paragraph{What is checked.} Lean checks each statement equivalence and the resulting " ++
  "proof. The equivalences unfold definitions; they do not invoke the three inequalities " ++
  "or identities being transferred. The display formulas are generated from those same " ++
  "typed statements. The parser, notation, and renderer remain an explicit, unverified " ++
  "presentation boundary.\n\\end{document}\n"

end LeanMirror.Examples.Classical
