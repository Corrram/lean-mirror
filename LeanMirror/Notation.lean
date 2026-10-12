import LeanMirror.Core
import Lean

/-! # Restricted mathematical input

`[math| C |- ...]` elaborates to the typed syntax in `Core`. Names in the
context are listed oldest first. Unknown symbols, unbound variables, and
ill-typed applications are rejected by Lean. `\real{u}` is the explicit
inclusion of an interval element in the reals; the renderer omits this cast.
This is a controlled grammar, not a parser for arbitrary TeX.
-/

namespace LeanMirror
open Lean Macro

declare_syntax_cat mirror_math
syntax ident : mirror_math
syntax num : mirror_math
syntax "\\" ident : mirror_math
syntax "(" mirror_math ")" : mirror_math
syntax:90 mirror_math:90 "(" mirror_math,+ ")" : mirror_math
syntax:65 mirror_math:65 " + " mirror_math:66 : mirror_math
syntax:65 mirror_math:65 " - " mirror_math:66 : mirror_math
syntax:70 mirror_math:70 " * " mirror_math:71 : mirror_math
syntax "\\frac{" mirror_math "}{" mirror_math "}" : mirror_math
syntax "\\abs{" mirror_math "}" : mirror_math
syntax "\\real{" mirror_math "}" : mirror_math
syntax "\\int_{0}^{1}{" ident "}{" mirror_math "}" : mirror_math
syntax:50 mirror_math:51 " = " mirror_math:51 : mirror_math
syntax:50 mirror_math:51 " \\le " mirror_math:51 : mirror_math
syntax:35 mirror_math:36 " \\land " mirror_math:35 : mirror_math
syntax:25 mirror_math:26 " \\implies " mirror_math:25 : mirror_math
syntax:20 mirror_math:21 " \\iff " mirror_math:20 : mirror_math
syntax "Let " ident " be " ident ". " mirror_math : mirror_math
syntax "[math|" ident,* "|-" mirror_math "]" : term

private def variableSyntax (n : Nat) : MacroM (TSyntax `term) := do
  match n with
  | 0 => `(Var.here)
  | n + 1 => `(Var.there $(← variableSyntax n))

private partial def translate (vars : List Name) (stx : TSyntax `mirror_math) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(mirror_math| $x:ident) =>
    match vars.idxOf? x.getId with
    | some n => `(Expr.var $(← variableSyntax n))
    | none => Macro.throwErrorAt x "unbound mathematical variable; use a backslash for a symbol"
  | `(mirror_math| $n:num) => `(Expr.nat $n)
  | `(mirror_math| \ $s:ident) => `(Expr.symbol $s)
  | `(mirror_math| ($x)) => translate vars x
  | `(mirror_math| $f($xs,*)) => do
    let mut result ← translate vars f
    for x in xs.getElems do
      result ← `(Expr.app $result $(← translate vars x))
    pure result
  | `(mirror_math| $x + $y) => `(Expr.add $(← translate vars x) $(← translate vars y))
  | `(mirror_math| $x - $y) => `(Expr.sub $(← translate vars x) $(← translate vars y))
  | `(mirror_math| $x * $y) => `(Expr.mul $(← translate vars x) $(← translate vars y))
  | `(mirror_math| \frac{$x}{$y}) => `(Expr.div $(← translate vars x) $(← translate vars y))
  | `(mirror_math| \abs{$x}) => `(Expr.abs $(← translate vars x))
  | `(mirror_math| \real{$x}) => `(Expr.coeUnit $(← translate vars x))
  | `(mirror_math| \int_{0}^{1}{$v:ident}{$body}) => do
    if vars.contains v.getId then
      Macro.throwErrorAt v "shadowed mathematical binder; choose a fresh name"
    `(Expr.integral $(quote v.getId.toString) $(← translate (v.getId :: vars) body))
  | `(mirror_math| $x = $y) => `(Expr.eq $(← translate vars x) $(← translate vars y))
  | `(mirror_math| $x \le $y) => `(Expr.le $(← translate vars x) $(← translate vars y))
  | `(mirror_math| $x \land $y) => `(Expr.and $(← translate vars x) $(← translate vars y))
  | `(mirror_math| $x \implies $y) => `(Expr.imp $(← translate vars x) $(← translate vars y))
  | `(mirror_math| $x \iff $y) => `(Expr.iff $(← translate vars x) $(← translate vars y))
  | `(mirror_math| Let $v:ident be $s:ident. $body) => do
    if vars.contains v.getId then
      Macro.throwErrorAt v "shadowed mathematical binder; choose a fresh name"
    `(Expr.allIn $(quote v.getId.toString) $s $(← translate (v.getId :: vars) body))
  | _ => Macro.throwErrorAt stx "unsupported mathematical syntax"

macro_rules
  | `([math| $vars:ident,* |- $body:mirror_math]) => do
    let names := vars.getElems.toList.map TSyntax.getId
    if names.eraseDups.length != names.length then
      Macro.throwError "duplicate variables in mathematical context"
    let expr ← translate names.reverse body
    `(Expr.withContextSize $(quote names.length) (by rfl) $expr)

end LeanMirror
