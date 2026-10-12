import LeanMirror.Document
import LeanMirror.Notation

namespace LeanMirror
open Lean Macro

declare_syntax_cat mirror_argument
syntax "Fix " ident " : " ident " named " str "; " mirror_argument : mirror_argument
syntax "Assume " mirror_math "; " mirror_argument : mirror_argument
syntax "Have " mirror_math "; " mirror_argument : mirror_argument
syntax "Choose " ident " : " ident " named " str " satisfying " mirror_math
  " to " "prove " mirror_math "; " mirror_argument : mirror_argument
syntax "Suffices " mirror_math " to " "prove " mirror_math "; " mirror_argument : mirror_argument
syntax "Conclude " mirror_math : mirror_argument
syntax "[proof|" mirror_argument "]" : term

private partial def argumentSyntax (vars : List Name) (s : TSyntax `mirror_argument) :
    MacroM (TSyntax `term) := do
  match s with
  | `(mirror_argument| Fix $n:ident : $a:ident named $display:str; $next) =>
    if vars.contains n.getId then Macro.throwErrorAt n "shadowed proof variable"
    `(Argument.fix $a $display $(← argumentSyntax (n.getId :: vars) next))
  | `(mirror_argument| Assume $p; $next) =>
    `(Argument.assume $(← translateMath vars p) $(← argumentSyntax vars next))
  | `(mirror_argument| Have $p; $next) =>
    `(Argument.have $(← translateMath vars p) $(← argumentSyntax vars next))
  | `(mirror_argument| Choose $n:ident : $a:ident named $display:str satisfying $p to prove $q; $next) =>
    if vars.contains n.getId then Macro.throwErrorAt n "shadowed proof variable"
    `(Argument.choose $a $display $(← translateMath (n.getId :: vars) p)
        $(← translateMath vars q) $(← argumentSyntax (n.getId :: vars) next))
  | `(mirror_argument| Suffices $p to prove $q; $next) =>
    `(Argument.suffices $(← translateMath vars p) $(← translateMath vars q)
        $(← argumentSyntax vars next))
  | `(mirror_argument| Conclude $p) => `(Argument.finish $(← translateMath vars p))
  | _ => Macro.throwErrorAt s "unsupported proof sentence"

macro_rules
  | `([proof| $body:mirror_argument]) => argumentSyntax [] body
end LeanMirror
