import LeanMirror.Tex.Doc

/-! # Formal readings

Renders compiled terms as explicit mathematics: quantifiers, domains and
definedness guards are written out. This rendering is for reading only; it is
not part of any certificate. -/
namespace LeanMirror.Tex

def Ty.tex : Ty → String
  | .real => "\\mathbb{R}"
  | .unit => "[0,1]"
  | .prop => "\\mathrm{Prop}"
  | .fn a b => (match a with | .fn .. => "(" ++ a.tex ++ ")" | _ => a.tex) ++ "\\to " ++ b.tex

def varNames : List String := ["x", "y", "z", "s", "t", "a", "b", "p", "q", "w", "k", "m"]

def Prim.tex : Prim → String
  | .rpow => "\\operatorname{pow}" | .min => "\\min" | .max => "\\max"
  | .leb => "\\lambda" | .distFn2 => "\\operatorname{DistFn}_{[0,1]^2}"
  | .dfUniformMarginals => "\\operatorname{UnifMarg}" | .probMeasure2 => "\\operatorname{Prob}_{[0,1]^2}"
  | .measUniformMarginals => "\\operatorname{UnifMarg}" | .borel => "\\operatorname{Borel}"
  | .measurableSet1 | .measurableSet2 => "\\operatorname{Meas}"
  | .integrable => "\\operatorname{Int}" | .hasDerivWithin => "\\operatorname{HasDeriv}"

/-- Binding strength for parentheses: propositions (1–4), relations (5), sums (6),
products (7), signs (8), atoms (9). -/
def Tm.prec : Tm → Nat
  | .iff .. => 1 | .imp .. => 2 | .or .. => 3 | .and .. => 4
  | .all .. | .ex .. => 0
  | .eq .. | .lt .. | .le .. => 5
  | .add .. | .sub .. => 6
  | .mul .. | .div .. => 7
  | .neg .. => 8
  | _ => 9

/-- A numeral or a quotient of numerals (displayed without its coercion to `[0,1]`). -/
def Tm.isNumeral : Tm → Bool
  | .num _ => true
  | .div x y => x.isNumeral && y.isNumeral
  | _ => false

partial def Tm.tex (gs : List String) (ls : List String) : Tm → String
  | .glob i => gs.getD i s!"g_{i}"
  | .loc i => ls.getD i s!"v_{i}"
  | .prim p => p.tex
  | .app (.app (.prim .rpow) x) y => "{" ++ wrap 9 x ++ "}^{" ++ y.tex gs ls ++ "}"
  | .app (.app (.prim .min) x) y => "\\min\\{" ++ x.tex gs ls ++ "," ++ y.tex gs ls ++ "\\}"
  | .app (.app (.prim .max) x) y => "\\max\\{" ++ x.tex gs ls ++ "," ++ y.tex gs ls ++ "\\}"
  | .app (.app (.app (.app (.prim .hasDerivWithin) f) s) x) d =>
      "(" ++ f.tex gs ls ++ ")'(" ++ x.tex gs ls ++ ")=" ++ d.tex gs ls ++ "\\text{ within }" ++ s.tex gs ls
  | .app (.prim .leb) s => "\\lambda\\bigl(" ++ s.tex gs ls ++ "\\bigr)"
  -- a domain predicate applied to an argument: read it about the argument
  | .app (.lam _ _ b) x => b.tex gs (x.tex gs ls :: ls)
  | .app (.glob i) x =>
    let n := gs.getD i s!"g_{i}"
    if n.startsWith "^" then "{" ++ wrap 9 x ++ "}" ++ n
    else if n == "\\widehat" then "\\widehat{" ++ x.tex gs ls ++ "}"
    else n ++ "(" ++ x.tex gs ls ++ ")"
  | .app f x => (match f with
      | .lam .. => "(" ++ f.tex gs ls ++ ")"
      | _ => f.tex gs ls) ++ "(" ++ x.tex gs ls ++ ")"
  | .lam t d b =>
    let v := varNames.getD ls.length "v"
    let dom := match d with | .tt => "" | d => "\\,[" ++ d.tex gs (v :: ls) ++ "]"
    "(" ++ v ++ "\\in " ++ t.tex ++ dom ++ "\\mapsto " ++ b.tex gs (v :: ls) ++ ")"
  | .num n => toString n
  | .ofUnit x => x.tex gs ls
  | .toUnit x => if x.isNumeral then x.tex gs ls else "\\langle " ++ x.tex gs ls ++ "\\rangle_{[0,1]}"
  | .add x y => wrap 6 x ++ "+" ++ wrap 7 y
  | .sub x y => wrap 6 x ++ "-" ++ wrap 7 y
  | .mul x y => wrap 7 x ++ "\\," ++ wrap 8 y
  | .div x y => "\\frac{" ++ x.tex gs ls ++ "}{" ++ y.tex gs ls ++ "}"
  | .neg x => "-" ++ wrap 8 x
  | .abs x => "\\lvert " ++ x.tex gs ls ++ "\\rvert"
  | .powNat x n => "{" ++ wrap 9 x ++ "}^{" ++ toString n ++ "}"
  | .cases c v r => "\\begin{cases}" ++ v.tex gs ls ++ "&" ++ c.tex gs ls ++ "\\\\" ++
      (cases r) ++ "\\end{cases}"
  | .undef _ => "\\bot"
  | .eq x y => x.tex gs ls ++ "=" ++ y.tex gs ls
  | .lt x y => x.tex gs ls ++ "<" ++ y.tex gs ls
  | .le x y => x.tex gs ls ++ "\\le " ++ y.tex gs ls
  | .tt => "\\top"
  | .not p => "\\neg " ++ wrap 9 p
  | .and p q => wrap 5 p ++ "\\land " ++ wrap 4 q
  | .or p q => wrap 4 p ++ "\\lor " ++ wrap 3 q
  | .imp p q => wrap 3 p ++ "\\Rightarrow " ++ wrap 2 q
  | .iff p q => wrap 2 p ++ "\\Leftrightarrow " ++ wrap 2 q
  | .all t b => let v := varNames.getD ls.length "v"
    "\\forall " ++ v ++ "\\in " ++ t.tex ++ ",\\ " ++ b.tex gs (v :: ls)
  | .ex t b => let v := varNames.getD ls.length "v"
    "\\exists " ++ v ++ "\\in " ++ t.tex ++ ",\\ " ++ b.tex gs (v :: ls)
  | .integral b => let v := varNames.getD ls.length "v"
    "\\int_0^1 " ++ wrap 7 b ++ "\\,d" ++ v
  | .guard _ e => e.tex gs ls
where
  /-- `t`, parenthesized when it binds more loosely than `p`. -/
  wrap (p : Nat) (t : Tm) : String :=
    let s := t.tex gs ls
    if t.prec < p then "(" ++ s ++ ")" else s
  cases : Tm → String
    | .cases c v r => v.tex gs ls ++ "&" ++ c.tex gs ls ++ "\\\\" ++ cases r
    | _ => ""

def Doc.globNames (d : Doc) : List String :=
  (d.globs.zip (List.range d.globs.length)).map fun (g, i) =>
    if g.key.isEmpty then
      match d.names.find? (·.2 == i) with
      | some (ws, _) => "\\operatorname{" ++ String.intercalate "\\," (ws.map Codes.toString) ++ "}"
      | none => s!"\\mathrm\{op}_\{{i}}"
    else Codes.toString g.key

end LeanMirror.Tex
