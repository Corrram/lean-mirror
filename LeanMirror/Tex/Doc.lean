import LeanMirror.Tex.Elab

/-! # Compiling an article

`compileArticle` reads the complete source: preamble macros, the document body,
its sentences and environments. Every sentence is either compiled (definitions
and claims) or kept as prose with the reason it has no reading. A sentence is
compiled entirely or not at all. Citations become premises: a proof sentence may
use earlier sentences of its proof and the results cited so far in that proof.
A result whose proof compiled completely has the proof's sentences (and their
citations) as its premises: this is the closing step of the proof. -/
namespace LeanMirror.Tex
open Grammar Elab

structure ProofInfo where
  env : Nat
  proves : Codes
  steps : List Nat
  cites : List Nat
  complete : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Doc where
  globs : List Glob
  values : List Tm
  claims : List Claim
  sentences : List (Context × Nat × Nat)
  outcomes : List Outcome
  labels : List (Codes × List Nat)
  proofs : List ProofInfo
  /-- Names of definitions introduced by phrases rather than symbols. -/
  names : List (List Codes × Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace Compile

structure BindInfo where
  name : Codes
  ty : Ty
  pred : Option Tm
  deriving Inhabited

def intervalPred (lo hi : Tm) : Tm := .lam .real .tt (Elab.interval lo hi (.loc 0))

/-- A closed constant bound (numerals and their negations). -/
def constTm : MT → Option Tm
  | .num n => some (.num n)
  | .neg (.num n) => some (.neg (.num n))
  | .frac (.num a) (.num b) => some (.div (.num a) (.num b))
  | _ => none

/-- The type and predicate of the elements of a domain formula. -/
def domainOf (calculus : Bool) (d : MT) : M (Ty × Option Tm) := do
  if isZeroOne d && !calculus then pure (.unit, none)
  else match d with
    | .interval lo hi => do
      let l ← liftO (constTm lo) E.unsupported
      let h ← liftO (constTm hi) E.unsupported
      pure (.real, some (intervalPred l h))
    | .id n => do
      let (i, g) ← liftO (← lookupGlob n) E.undefined n
      match g.ty with
      | .fn a .prop => pure (a, some (.glob i))
      | _ => fail E.type n
    | _ => fail E.unsupported

def isUnitSquare : Option MT → Bool
  | some (.sup (.interval (.num 0) (.num 1)) (.num 2)) => true
  | _ => false

def isUnitInterval : Option MT → Bool
  | some (.interval (.num 0) (.num 1)) => true
  | _ => false

def isPair : Option MT → Option (MT × MT)
  | some (.tuple [a, b]) => some (a, b)
  | _ => none

def wordsOf (cs : List Chunk) : List Codes := cs.filterMap fun c => match c with | .w w => some w | _ => none
def mathsOf (cs : List Chunk) : List (List MTok) := cs.filterMap fun c => match c with | .m t => some t | _ => none

def lookupWords (tbl : List (List Codes × Nat)) (ws : List Codes) : Option Nat := tbl.lookup ws

/-- Noun phrases of the prelude and of the article, with a bound variable. -/
def nounBinder (np : List Chunk) : M BindInfo := do
  let ws := wordsOf np
  match np with
  -- Borel measurable $f:[0,1]\to[0,1]$
  | [.w b, .w m, .m ts] =>
    if b == w!"borel" && m == w!"measurable" then do
      let sg ← liftO (Math.parseSig ts) E.unsupported
      match sg with
      | .sig (.id f) d c =>
        if isZeroOne d && isZeroOne c then pure ⟨f, Ty.self, some (.lam Ty.self .tt (.app (.prim .borel) (.loc 0)))⟩
        else fail E.unsupported
      | _ => fail E.unsupported
    else nounVar ws np
  | _ =>
    -- probability measure $γ$ on $[0,1]^2$ [with uniform marginals]
    if ws.take 2 == [w!"probability", w!"measure"] then do
      let v ← match mathsOf np with
        | [ [.id v], sq ] =>
          if isUnitSquare (Math.parseFormula sq) then pure v
          else fail E.unsupported
        | [ [.cmd v], sq ] =>
          if isUnitSquare (Math.parseFormula sq) then pure ([92] ++ v)
          else fail E.unsupported
        | _ => fail E.unsupported
      let uniform := ws.drop 2 == [w!"on", w!"with", w!"uniform", w!"marginals"]
      if !(uniform || ws.drop 2 == [w!"on"]) then fail E.noun
      let p : Tm := .app (.prim .probMeasure2) (.loc 0)
      let p := if uniform then Tm.and p (.app (.prim .measUniformMarginals) (.loc 0)) else p
      pure ⟨v, Ty.meas2, some (.lam Ty.meas2 .tt p)⟩
    else nounVar ws np
where
  nounVar (ws : List Codes) (np : List Chunk) : M BindInfo := do
    let v ← match mathsOf np with
      | [[.id v]] => pure v
      | _ => fail E.unsupported
    let some i := lookupWords (← get).nouns ws | fail E.noun (ws.flatten)
    match (← get).globs[i]? with
    | some g => match g.ty with
      | .fn a .prop => pure ⟨v, a, some (.glob i)⟩
      | _ => fail E.type
    | none => fail E.undefined

def binderInfos (b : Bind) : M (List BindInfo) :=
  match b with
  | .every vs d => do
    let (ty, p) ← domainOf false d
    pure (vs.map fun v => ⟨v, ty, p⟩)
  | .noun np => do pure [← nounBinder np]
  | .on _ => pure []

def scopeOf (bs : List BindInfo) : Scope := (bs.map fun b => (b.name, b.ty)).reverse

def wrap (bs : List BindInfo) (body : Tm) : Tm :=
  forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body

/-- Free identifiers of a formula (for `On I,`). -/
def freeIds : Nat → List Codes → MT → List Codes
  | 0, _, _ => []
  | f + 1, bound, m =>
    match m with
    | .id n => if bound.contains n then [] else [n]
    | .num _ => []
    | .sub b i => freeIds f bound b ++ freeIds f bound i
    | .sup b e => freeIds f bound b ++ freeIds f bound e
    | .hat x | .neg x | .abs x => freeIds f bound x
    | .app h as => freeIds f bound h ++ (as.flatMap (freeIds f bound))
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => freeIds f bound x ++ freeIds f bound y
    | .minm xs | .maxm xs | .tuple xs | .conj xs => xs.flatMap (freeIds f bound)
    | .int _ _ b v => freeIds f (v :: bound) b
    | .interval a b => freeIds f bound a ++ freeIds f bound b
    | .chain x rs => freeIds f bound x ++ rs.flatMap (fun r => freeIds f bound r.2)
    | .mapsto p b => freeIds f (freeIds f [] p ++ bound) b
    | _ => []

def clauseMaths : Clause → List MT
  | .fact f | .holds f => [f]
  | .deriv d _ c => [d, c]
  | .scoped f _ _ e => f :: e.toList
  | _ => []

/-- The single inequality of a chain, for `with equality only at`. -/
def inequality : MT → Option MT
  | .chain x rs =>
    let terms := x :: rs.map (·.2)
    let idx := rs.findIdx? (fun r => r.1 == .le || r.1 == .lt || r.1 == .ge || r.1 == .gt)
    match idx with
    | some k =>
      if (rs.filter (fun r => r.1 == .le || r.1 == .lt || r.1 == .ge || r.1 == .gt)).length == 1 then
        match terms[k]?, terms[k+1]? with
        | some a, some b => some (.chain a [(.eq, b)])
        | _, _ => none
      else none
    | none => none
  | _ => none

def F := 100000

def prop (sc : Scope) (pf : PF) (m : MT) : M Tm := do
  let (t, ty) ← term F sc pf m
  if ty == .prop then pure t else fail E.type

/-- The domain (type, predicate) of a point-free function formula such as `\nu-\rho`. -/
def pfDomain : Nat → MT → M (Option (Ty × Option Tm))
  | 0, _ => pure none
  | f + 1, m =>
    match m with
    | .id n => do
      match ← lookupGlob n with
      | some (_, g) => match g.ty with
        | .fn a _ => pure (some (a, (g.doms.head?).join))
        | _ => pure none
      | none => pure none
    | .minus x y | .add x y | .mul x y | .div x y => do
      match ← pfDomain f x with
      | some r => pure (some r)
      | none => pfDomain f y
    | .neg x => pfDomain f x
    | _ => pure none

def holdsAt (p : Option Tm) (x : Tm) : Tm := match p with | some p => .app p x | none => .tt

/-- Resolve a relation object: a formula, or a named object (possibly introduced here). -/
def object (sc : Scope) (ty : Ty) : Obj → M Tm
  | .math (.mapsto pat body) => do
    match ty with
    | .fn a r => do let (t, _) ← Elab.lam F sc pat [a] (some r) body; pure t
    | _ => fail E.type
  | .math m => do let (t, mty) ← term F sc none m; coerce t mty ty
  | .named name none => do
    let some i := lookupWords (← get).named name | fail E.referent name.flatten
    pure (.glob i)
  | .named name (some (.mapsto pat body)) => do
    match ty with
    | .fn a r => do
      let (t, tty) ← Elab.lam F [] pat [a] (some r) body
      let i ← addGlob ⟨[], tty, [], false⟩ t
      modify fun st => { st with named := st.named ++ [(name, i)] }
      pure (.glob i)
    | _ => fail E.type
  | _ => fail E.unsupported

def predicate (sc : Scope) (s : Tm × Ty) (phrase : List Codes) (o : Obj) : M Tm := do
  let some i := lookupWords (← get).preds phrase | fail E.noun phrase.flatten
  let g := ((← get).globs[i]?).getD default
  match g.ty with
  | .fn _ (.fn b .prop) => do
    let ot ← object sc b o
    let (t, _) ← applyAll (.glob i) g.ty g.doms [s, (ot, b)]
    pure t
  | _ => fail E.type

def subjectTm (sc : Scope) : Subj → M (Tm × Ty)
  | .math m => term F sc none m
  | .its name => do
    let some (s, sty) := (← get).subject | fail E.referent
    let some i := lookupWords (← get).ops name | fail E.noun name.flatten
    let g := ((← get).globs[i]?).getD default
    applyAll (.glob i) g.ty g.doms [(s, sty)]

/-- Extremum statement: bound, attainment, uniqueness. -/
def extremumTm (sc : Scope) (isMax : Bool) (fm value : MT) (s : Tm × Ty) : M (Tm × Ty × Option Tm) := do
  let some (ty, p) ← pfDomain 16 fm | fail E.unsupported
  let s' ← coerce s.1 s.2 ty
  let inner := (w!"", ty) :: sc
  let fx ← asReal (← term F inner (some (.loc 0, ty)) fm)
  let mx ← asReal (← term F inner none value)
  let bound := Tm.all ty (.imp (holdsAt p (.loc 0)) (if isMax then .le fx mx else .le mx fx))
  let fs ← asReal (← term F sc (some (s', ty)) fm)
  let ms ← asReal (← term F sc none value)
  let attained := Tm.and (holdsAt p s') (.eq fs ms)
  let unique := Tm.all ty (.imp (holdsAt p (.loc 0)) (.imp (.eq fx mx) (.eq (.loc 0) (shift 1 0 s'))))
  pure (.and bound (.and attained unique), ty, p)

def attainsOnly (sc : Scope) (ex : Extremum) (s : Tm × Ty) (withAttained : Bool) : M Tm := do
  let some (ty, p) ← pfDomain 16 ex.f | fail E.unsupported
  let s' ← coerce s.1 s.2 ty
  let inner := (w!"", ty) :: sc
  let fx ← asReal (← term F inner (some (.loc 0, ty)) ex.f)
  let mx ← asReal (← term F inner none ex.value)
  let unique := Tm.all ty (.imp (holdsAt p (.loc 0)) (.imp (.eq fx mx) (.eq (.loc 0) (shift 1 0 s'))))
  if withAttained then
    let fs ← asReal (← term F sc (some (s', ty)) ex.f)
    let ms ← asReal (← term F sc none ex.value)
    pure (.and (.and (holdsAt p s') (.eq fs ms)) unique)
  else pure unique

def findExtremum (env : Nat) (isMax : Bool) : M Extremum := do
  let st ← get
  match st.extrema.find? (fun (e, x) => e == env && x.isMax == isMax) with
  | some (_, x) => pure x
  | none => fail E.referent

structure SentCtx where
  ctx : Context
  /-- Environment index of the result a proof proves. -/
  target : Nat
  idx : Nat

def claimRole (c : SentCtx) : Role :=
  match c.ctx.kind with
  | .result _ => .statement c.ctx.env
  | .proof => .step c.ctx.env
  | .text => .text

/-- Premise claim ids for citing a label (definitions contribute none). -/
def citeClaims (l : Codes) : M (List Nat) := do
  let st ← get
  match st.labels.lookup l with
  | some cs => pure cs
  | none => if st.defLabels.contains l then pure [] else fail E.label l

def addLabels (ls : List Codes) (claims : List Nat) (isDef : Bool) : M Unit := do
  for l in ls do
    modify fun st =>
      let st := if isDef then { st with defLabels := st.defLabels ++ [l] } else st
      match st.labels.lookup l with
      | some cs => { st with labels := st.labels.map fun (k, v) => if k == l then (k, cs ++ claims) else (k, v) }
      | none => { st with labels := st.labels ++ [(l, claims)] }

/-- Record a claim of the current sentence (with premises for proof steps). -/
def emit (c : SentCtx) (body : Tm) (cites : List Codes) : M Nat := do
  let st ← get
  match c.ctx.kind with
  | .proof => do
    let cited ← cites.mapM citeClaims
    let allCites := (st.proofCites ++ cited.flatten).eraseDups
    let premises := (allCites ++ st.proofSteps).eraseDups
    let id ← addClaim ⟨c.idx, body, .step c.ctx.env, cites, premises⟩
    modify fun st => { st with proofCites := allCites, proofSteps := st.proofSteps ++ [id] }
    pure id
  | _ => do
    discard <| cites.mapM citeClaims
    addClaim ⟨c.idx, body, claimRole c, cites, []⟩

/-! ## Definition sentences -/

/-- Registered operation names: the name as written, and without a final `of`. -/
def registerOp (name : List Codes) (i : Nat) : M Unit := do
  let base := match name.reverse with
    | w :: r => if w == w!"of" then r.reverse else name
    | [] => name
  let names := [name, base].eraseDups.filter (!·.isEmpty)
  modify fun st => { st with ops := st.ops ++ names.map (·, i) }

/-- The head of a defining left-hand side: the defined key, whether it is a
family, and its explicit arguments. -/
def defHead (binder : Codes) : MT → M (Codes × Bool × List Codes)
  | .app h args => do
    let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
    match h with
    | .id k => if names == [binder] then pure (k, false, []) else fail E.unsupported k
    | .sup (.id x) (.id d) => if x == binder then pure (w!"^" ++ d, false, names) else fail E.unsupported
    | .hat (.id x) => if x == binder then pure (w!"\\widehat", false, names) else fail E.unsupported
    | .sub (.id k) (.id x) => if x == binder then pure (k, true, names) else fail E.unsupported
    | _ => fail E.unsupported
  | .sup (.id x) (.id d) => if x == binder then pure (w!"^" ++ d, false, []) else fail E.unsupported
  | .hat (.id x) => if x == binder then pure (w!"\\widehat", false, []) else fail E.unsupported
  | .sub (.id k) (.id x) => if x == binder then pure (k, true, []) else fail E.unsupported
  | _ => fail E.unsupported

def argTypes : Ty → Nat → List Ty
  | _, 0 => []
  | .fn a b, n + 1 => a :: argTypes b n
  | _, _ => []

def lamWrap : List Ty → Tm → Tm
  | [], b => b
  | t :: ts, b => .lam t .tt (lamWrap ts b)

def tyWrap : List Ty → Ty → Ty
  | [], r => r
  | t :: ts, r => .fn t (tyWrap ts r)

/-- Claims `a₁ R₁ a₂ R₂ …` after a definition `X := a₁`, pairwise, under binders. -/
def chainClaims (sc : Scope) (first : MT) (rest : List (Rel × MT)) : M (List Tm) := do
  let rec go : MT → List (Rel × MT) → M (List Tm)
    | _, [] => pure []
    | a, (r, b) :: more => do
      let ta ← term F sc none a
      let tb ← term F sc none b
      let p ← relTm r ta tb
      pure (p :: (← go b more))
  go first rest

/-- `For a N $x$, the NAME is DEF`. -/
def defItem (c : SentCtx) (b : BindInfo) (it : DefItem) : M (List Nat × List Nat) := do
  let bty := b.ty
  match it.defn with
  | .chain lhs ((.defeq, rhs) :: more) => do
    let (key, family, args) ← defHead b.name lhs
    let ats := match bty with
      | .fn _ _ => argTypes bty args.length
      | _ => []
    if ats.length != args.length then fail E.type
    let sc := ((args.zip ats).reverse) ++ [(b.name, bty)]
    let (body, rty) ← term F sc none rhs
    let value := Tm.lam bty (holdsAt b.pred (.loc 0)) (lamWrap ats body)
    let ty := Ty.fn bty (tyWrap ats rty)
    let i ← addGlob ⟨key, ty, b.pred :: ats.map (fun _ => none), family⟩ value
    registerOp it.name i
    let cs ← chainClaims sc rhs more
    let bs := b :: (args.zip ats).map fun (n, t) => ⟨n, t, none⟩
    let ids ← cs.mapM fun p => emit c (wrap bs p) []
    addLabels it.labels ids true
    pure ([i], ids)
  | .mapsto pat body => do
    -- an operation named by its noun, e.g. `the copula associated with γ`
    let nouns := (← get).nouns
    let some ni := it.name.findSome? (fun w => nouns.lookup [w]) | fail E.noun
    let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
    let elemTy ← match gty with
      | some (.fn a .prop) => pure a
      | _ => fail E.type
    let ats := argTypes elemTy (match pat with | .tuple vs => vs.length | _ => 1)
    let (lt, lty) ← Elab.lam F [(b.name, bty)] pat ats (some .real) body
    let value := Tm.lam bty (holdsAt b.pred (.loc 0)) lt
    let i ← addGlob ⟨[], .fn bty lty, [b.pred], false⟩ value
    registerOp it.name i
    pure ([i], [])
  | _ => fail E.unsupported

/-- `define $f:A\to B$ by DISPLAY [and observe that φ for every x∈A]`. -/
def defBy (c : SentCtx) (sg disp : MT) (labels : List Codes) (observe : Option (MT × List Codes × MT)) :
    M (List Nat × List Nat) := do
  match sg, disp with
  | .sig (.id f) dom cod, .chain (.app (.id f') [.id x]) [(.defeq, rhs)] => do
    if f != f' then fail E.unsupported
    let (aty, apred) ← domainOf true dom
    let (body, bty) ← term F [(x, aty)] none rhs
    let (cty, cpred) ← domainOf true cod
    let body ← coerce body bty cty
    let value := Tm.lam aty (holdsAt apred (.loc 0)) body
    let i ← addGlob ⟨f, .fn aty cty, [apred], false⟩ value
    let applied := Tm.guard (holdsAt apred (.loc 0)) (.app (.glob i) (.loc 0))
    let codomain := match cpred with
      | some p => [Tm.all aty (.imp (holdsAt apred (.loc 0)) (.app p applied))]
      | none => []
    let ids ← codomain.mapM fun p => emit c p []
    let obs ← match observe with
      | some (φ, vs, d) => do
        let bs ← binderInfos (.every vs d)
        let p ← prop (scopeOf bs) none φ
        pure [← emit c (wrap bs p) []]
      | none => pure []
    addLabels labels (ids ++ obs) true
    pure ([i], ids ++ obs)
  | _, _ => fail E.unsupported

/-- `For B, the NAME $f_c:A\to B$ reads DISPLAY`. -/
def defReads (c : SentCtx) (b : BindInfo) (sg disp : MT) (labels : List Codes) : M (List Nat × List Nat) := do
  match sg, disp with
  | .sig (.sub (.id f) (.id p)) dom cod, .chain (.app (.sub (.id f') (.id p')) [.id x]) ((.defeq, rhs) :: more) => do
    if f != f' || p != b.name || p' != b.name then fail E.unsupported
    let (aty, apred) ← domainOf false dom
    let (cty, cpred) ← domainOf false cod
    if cpred.isSome then fail E.unsupported
    let sc : Scope := [(x, aty), (b.name, b.ty)]
    let (body, bty) ← term F sc none rhs
    let body' ← coerce body bty cty
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (.lam aty (holdsAt apred (.loc 0)) body')
    let i ← addGlob ⟨f, .fn b.ty (.fn aty cty), [b.pred, apred], true⟩ value
    let cs ← chainClaims sc rhs more
    let ids ← cs.mapM fun q => emit c (wrap [b, ⟨x, aty, apred⟩] q) []
    addLabels labels ids true
    pure ([i], ids)
  | _, _ => fail E.unsupported

/-- `Lebesgue measure on $[0,1]$ is denoted by $\mathrm{Leb}$` (a prelude notion). -/
def denotedBy (words : List Codes) (on : List MT) (sym : MT) : M (List Nat × List Nat) := do
  match sym, on with
  | .id k, [d] =>
    if words == [w!"lebesgue", w!"measure", w!"on"] && isZeroOne d then do
      let i ← addGlob ⟨k, .fn Ty.set1 .real, [none], false⟩ (.prim .leb)
      pure ([i], [])
    else fail E.noun words.flatten
  | _, _ => fail E.unsupported

/-- `For B, let $X_p$ denote NP`. -/
def letDenote (b : BindInfo) (sym : MT) (np : List Chunk) : M (List Nat × List Nat) := do
  let (key, family) ← match sym with
    | .sub (.id k) (.id p) => if p == b.name then pure (k, true) else fail E.unsupported
    | .id k => pure (k, false)
    | _ => fail E.unsupported
  let sc : Scope := [(b.name, b.ty)]
  let (val, vty) ← match np with
    -- the law of $(X, f(X))$ for $X$ uniformly distributed on $[0,1]$
    | [.w t, .w l, .w o, .m pair, .w fr, .m [.id x], .w u, .w d, .w on, .m zo] =>
      if [t, l, o, fr, u, d, on] == [w!"the", w!"law", w!"of", w!"for", w!"uniformly", w!"distributed", w!"on"]
          && isUnitInterval (Math.parseFormula zo) then do
        match Math.parseFormula pair with
        | some (.tuple [e1, e2]) => do
          -- λ A. Leb {x : A(e1(x), e2(x))}, with A a measurable subset of [0,1]^2
          let sc' := (x, Ty.unit) :: (w!"", Ty.set2) :: sc
          let a ← coerce (← term F sc' none e1).1 .unit .unit
          let t1 ← term F sc' none e1
          let t2 ← term F sc' none e2
          let a1 ← coerce t1.1 t1.2 .unit
          let a2 ← coerce t2.1 t2.2 .unit
          let _ := a
          let set := Tm.lam .unit .tt (.app (.app (.loc 1) a1) a2)
          let body := Tm.guard (.app (.prim .measurableSet1) set) (.app (.prim .leb) set)
          pure (Tm.lam Ty.set2 (.app (.prim .measurableSet2) (.loc 0)) body, Ty.meas2)
        | _ => fail E.unsupported
      else fail E.noun
    | .w t :: rest =>
      if t != w!"the" then fail E.unsupported
      else do
        let ws := wordsOf rest
        match mathsOf rest with
        | [arg] => do
          let some i := lookupWords (← get).ops ws | fail E.noun ws.flatten
          let g := ((← get).globs[i]?).getD default
          let m ← liftO (Math.parseFormula arg) E.unsupported
          let a ← term F sc none m
          applyAll (.glob i) g.ty g.doms [a]
        | _ => fail E.unsupported
    | _ => fail E.unsupported
  let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) val
  let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family⟩ value
  pure ([i], [])

/-- `We say that a N $x$ is PHRASE of a M $y$ if φ for all u,v∈A`. -/
def weSay (subj : List Chunk) (phrase : List Codes) (o : List Chunk) (cond : MT) (vs : List Codes) (d : MT) :
    M (List Nat × List Nat) := do
  let s ← nounBinder subj
  let t ← nounBinder o
  let bs ← binderInfos (.every vs d)
  let sc := scopeOf ([s, t] ++ bs)
  let body ← prop sc none cond
  let inner := forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body
  let value := Tm.lam s.ty (holdsAt s.pred (.loc 0)) (.lam t.ty (holdsAt t.pred (.loc 0)) inner)
  let i ← addGlob ⟨[], .fn s.ty (.fn t.ty .prop), [s.pred, t.pred], false⟩ value
  modify fun st => { st with preds := st.preds ++ [(phrase, i)] }
  pure ([i], [])

/-- `let $S$ denote the class of Ns, that is, NP`. -/
def defClass (sym : MT) (plural : List Codes) (np : List Chunk) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.unsupported
  let ws := wordsOf np
  -- distribution functions on $[0,1]^2$ [with uniform marginals]
  let ok := ws.take 3 == [w!"distribution", w!"functions", w!"on"] &&
    (match mathsOf np with
     | [sq] => isUnitSquare (Math.parseFormula sq)
     | _ => false)
  if !ok then fail E.noun ws.flatten
  let uniform := ws.drop 3 == [w!"with", w!"uniform", w!"marginals"]
  if !(uniform || (ws.drop 3).isEmpty) then fail E.noun ws.flatten
  let p : Tm := .app (.prim .distFn2) (.loc 0)
  let p := if uniform then Tm.and p (.app (.prim .dfUniformMarginals) (.loc 0)) else p
  let i ← addGlob ⟨key, .fn Ty.sq .prop, [none], false⟩ (.lam Ty.sq .tt p)
  let sing := plural.dropLast ++ (plural.getLast?.map singular).toList
  let names := [sing, (sing.getLast?).toList].eraseDups
  modify fun st => { st with nouns := st.nouns ++ names.map (·, i) }
  pure ([i], [])

/-! ## Claim sentences -/

/-- One clause; `rest` are the following clauses of the sentence (for scopes). -/
def clauseTm (c : SentCtx) (sc : Scope) (onVar : Option BindInfo) (lastRhs : Option MT) :
    Clause → M Tm
  | .fact f | .holds f => prop sc none f
  | .every vs d body => do
    let bs ← binderInfos (.every vs d)
    let p ← prop (scopeOf bs ++ sc) none body
    pure (wrap bs p)
  | .scoped f vs d eq => do
    let bs ← match d with
      | some d => binderInfos (.every vs d)
      | none => pure []
    let sc' := scopeOf bs ++ sc
    let p ← prop sc' none f
    let p ← match eq with
      | some at_ => do
        let ineq ← liftO (inequality f) E.unsupported
        let e ← prop sc' none ineq
        let a ← prop sc' none at_
        pure (Tm.and p (.imp e a))
      | none => pure p
    pure (wrap bs p)
  | .extremum isMax fv s rels => do
    match fv with
    | .chain fm [(.eq, value)] => do
      let st ← subjectTm sc s
      let (core, ty, _) ← extremumTm sc isMax fm value st
      let s' ← coerce st.1 st.2 ty
      let extra ← rels.mapM fun r => match r with
        | .has m => prop sc (some (s', ty)) m
        | .pred ph o => predicate sc (s', ty) ph o
      modify fun st' => { st' with
        extrema := st'.extrema ++ [(c.ctx.env, ⟨isMax, fm, value⟩)], subject := some (s', ty) }
      pure (conjAll (core :: extra))
    | _ => fail E.unsupported
  | .increases (.mapsto pat body) a b => do
    let (aty, apred) ← domainOf false a
    let (bty, bpred) ← domainOf false b
    if bty != .real then fail E.unsupported
    let (fn, _) ← Elab.lam F sc pat [aty] (some .real) body
    let fx : Tm := .app (shift 1 0 fn) (.loc 0)
    let into := Tm.all aty (Tm.mkImp (holdsAt apred (.loc 0)) (holdsAt bpred fx))
    let fxx : Tm := .app (shift 2 0 fn) (.loc 1)
    let fyy : Tm := .app (shift 2 0 fn) (.loc 0)
    let ltA : Tm := if aty == .unit then .lt (.ofUnit (.loc 1)) (.ofUnit (.loc 0)) else .lt (.loc 1) (.loc 0)
    let mono := Tm.all aty (.all aty (Tm.mkImp (holdsAt apred (.loc 1)) (Tm.mkImp (holdsAt apred (.loc 0))
      (.imp ltA (.lt fxx fyy)))))
    let onto := Tm.all .real (Tm.mkImp (holdsAt bpred (.loc 0)) (.ex aty (Tm.mkAnd (holdsAt apred (.loc 0))
      (.eq (.app (shift 2 0 fn) (.loc 0)) (.loc 1)))))
    pure (conjAll [into, mono, onto])
  | .deriv d positive cond => do
    let some v := onVar | fail E.referent
    let some rhs := lastRhs | fail E.referent
    let some ip := v.pred | fail E.unsupported
    let (g, _) ← Elab.lam F sc (.id v.name) [.real] (some .real) rhs
    let g := match g with | .lam t _ b => Tm.lam t (.app ip (.loc 0)) b | g => g
    let dt ← asReal (← term F sc none d)
    let ct ← prop sc none cond
    let hd := Tm.app (.app (.app (.app (.prim .hasDerivWithin) g) ip) (.loc 0)) dt
    let sign := if positive then Tm.lt (.num 0) dt else Tm.lt dt (.num 0)
    pure (.and hd (.imp ct sign))
  | .noOther noun x isMax => do
    let ex ← findExtremum c.target isMax
    let some ni := lookupWords (← get).nouns noun | fail E.noun noun.flatten
    let xt ← term F sc none x
    let u ← attainsOnly sc ex xt false
    match u with
    | .all ty (.imp p rest) =>
      if p == .app (.glob ni) (.loc 0) then pure u
      else pure (.all ty (.imp (.and (.app (.glob ni) (.loc 0)) p) rest))
    | u => pure u
  | .onlyAttains x => do
    let isMax ← match (← get).topic with
      | .maximum => pure true | .minimum => pure false | .none => fail E.referent
    let ex ← findExtremum c.target isMax
    let xt ← term F sc none x
    attainsOnly sc ex xt true
  | .sends (.mapsto (.id v) body) fm gm => do
    let some (ty, p) ← pfDomain 16 fm | fail E.unsupported
    let sc' := (v, ty) :: sc
    let (mt, mty) ← term F sc' none body
    let mt ← coerce mt mty ty
    let lhs ← asReal (← term F sc' (some (mt, ty)) fm)
    let rhs ← asReal (← term F sc' (some (.loc 0, ty)) gm)
    pure (.all ty (.imp (holdsAt p (.loc 0)) (.eq lhs rhs)))
  | .pred s ph o => do
    let st ← subjectTm sc s
    predicate sc st ph o
  | .onlyWith s noun conds => do
    let some ni := lookupWords (← get).nouns noun | fail E.noun noun.flatten
    let (st, sty) ← subjectTm sc s
    let atS ← conds.mapM (prop sc (some (st, sty)))
    let sc' := (w!"", sty) :: sc
    let ay ← conds.mapM (prop sc' (some (.loc 0, sty)))
    let uniq := Tm.all sty (.imp (.app (.glob ni) (.loc 0)) (.imp (conjAll ay) (.eq (.loc 0) (shift 1 0 st))))
    pure (conjAll ([Tm.app (.glob ni) st] ++ atS ++ [uniq]))
  | _ => fail E.unsupported

def rhsOf : Clause → Option MT
  | .fact (.chain _ rs) | .scoped (.chain _ rs) _ _ _ => rs.getLast?.map (·.2)
  | _ => none

def citesOf (cl : CClause) : List Codes := cl.cites

/-- The claims of one sentence. `exactly one` takes the following clauses into its scope. -/
def claimSentence (c : SentCtx) (topic : Topic) (binds : List Bind) (cls : List CClause) : M (List Nat) := do
  modify fun st => { st with topic := if topic == .none then st.topic else topic }
  let bss ← binds.mapM binderInfos
  let bs := bss.flatten
  -- `On I,`: the sentence's single free variable ranges over I
  let onVar ← match binds.find? (fun b => match b with | .on _ => true | _ => false) with
    | some (.on d) => do
      let (_, p) ← domainOf true d
      let known := (scopeOf bs).map (·.1)
      let st ← get
      let free := (cls.flatMap (fun cl => (clauseMaths cl.clause).flatMap (freeIds 64 known))).eraseDups
      let free := free.filter fun n => !(st.globs.any (·.key == n))
      match free with
      | [v] => pure (some (⟨v, .real, p⟩ : BindInfo))
      | _ => fail E.free free.flatten
    | _ => pure none
  let allBs := bs ++ onVar.toList
  let sc := scopeOf allBs
  let rec go : Nat → List CClause → Option MT → M (List Nat)
    | 0, _, _ => pure []
    | _ + 1, [], _ => pure []
    | g + 1, cl :: rest, last =>
      match cl.clause with
      | .exactlyOne noun v cond sat => do
        let some ni := lookupWords (← get).nouns noun | fail E.noun noun.flatten
        let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
        let ty ← match gty with
          | some (.fn a .prop) => pure a
          | _ => fail E.type
        let sx := (v, ty) :: sc
        let cx ← prop sx none cond
        let sx' ← prop sx none sat
        let sy := (v, ty) :: sx
        let cy ← prop sy none cond
        let sy' ← prop sy none sat
        let uniq := Tm.all ty (.imp (.app (.glob ni) (.loc 0)) (.imp cy (.imp sy' (.eq (.loc 0) (.loc 1)))))
        modify fun st => { st with subject := some (.loc 0, ty) }
        -- the remaining clauses are in the scope of the unique element
        let inner ← rest.mapM fun cl' => clauseTm c sx none none cl'.clause
        let body := Tm.ex ty (conjAll ([Tm.app (.glob ni) (.loc 0), cx, sx', uniq] ++ inner))
        let id ← emit c (wrap allBs body) (cl.cites ++ rest.flatMap (·.cites))
        pure [id]
      | k => do
        let p ← clauseTm c sc onVar last k
        let id ← emit c (wrap allBs p) cl.cites
        let ids ← go g rest (match rhsOf k with | some r => some r | none => last)
        pure (id :: ids)
  go 16 cls none

/-- Compile one sentence: definitions and claims, or a reason it has none. -/
def sentence (c : SentCtx) (s : Sent) : M (List Nat × List Nat) := do
  match s with
  | .defClass sym plural np => defClass sym plural np
  | .defIs b items => do
    let bs ← binderInfos b
    let [bi] := bs | fail E.unsupported
    let rs ← items.mapM (defItem c bi)
    pure (rs.flatMap (·.1), rs.flatMap (·.2))
  | .defReads b _ sg disp labels => do
    let [bi] ← binderInfos b | fail E.unsupported
    defReads c bi sg disp labels
  | .defBy sg disp labels obs => defBy c sg disp labels obs
  | .denotedBy ws on sym => denotedBy ws on sym
  | .letDenote b sym np => do
    let [bi] ← binderInfos b | fail E.unsupported
    letDenote bi sym np
  | .weSay sb ph o cond vs d => weSay sb ph o cond vs d
  | .claims topic binds cls => do
    let ids ← claimSentence c topic binds cls
    pure ([], ids)

end Compile

open Compile in
/-- Compile all sentences. A failing sentence leaves no trace in the state. -/
def compileSentences (ss : List Sentence) : StateM St (List Outcome × List ProofInfo) := do
  let envOf (label : Codes) : Nat :=
    match ss.find? (fun s => s.ctx.label == label && match s.ctx.kind with | .result _ => true | _ => false) with
    | some s => s.ctx.env
    | none => 0
  let rec go : Nat → List Sentence → Nat → List Outcome → List ProofInfo →
      StateM St (List Outcome × List ProofInfo)
    | 0, _, _, acc, ps => pure (acc.reverse, ps)
    | _ + 1, [], _, acc, ps => pure (acc.reverse, ps)
    | f + 1, s :: rest, idx, acc, ps => do
      -- entering a new environment resets proof-local state
      let st0 ← get
      if st0.proofEnv != s.ctx.env then
        set { st0 with proofEnv := s.ctx.env, proofCites := [], proofSteps := [], topic := .none }
      let ps := match s.ctx.kind with
        | .proof => if ps.any (·.env == s.ctx.env) then ps
          else ps ++ [({ env := s.ctx.env, proves := s.ctx.proves, steps := [], cites := [], complete := true } : ProofInfo)]
        | _ => ps
      let saved ← get
      match Grammar.parseSentence s with
      | none =>
        let ps := ps.map fun p => if p.env == s.ctx.env then { p with complete := false } else p
        go f rest (idx + 1) (.prose :: acc) ps
      | some sent =>
        let c : SentCtx := ⟨s.ctx, envOf s.ctx.proves, idx⟩
        let labelled : M (List Nat × List Nat) := do
          let (ds, cs) ← Compile.sentence c sent
          match sent with
          | .claims _ _ _ =>
            -- labels of displays in the sentence, and of the enclosing result, name its claims
            let ls := s.toks.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
            let ls := match s.ctx.kind with
              | .result _ => if s.ctx.label.isEmpty then ls else s.ctx.label :: ls
              | _ => ls
            Compile.addLabels ls cs false
          | _ => pure ()
          pure (ds, cs)
        let (r, st) := labelled.run.run saved
        match r with
        | .ok (ds, cs) =>
          set st
          let ps := ps.map fun p => if p.env == s.ctx.env then
            { p with steps := st.proofSteps, cites := st.proofCites } else p
          go f rest (idx + 1) (.compiled ds cs :: acc) ps
        | .error e =>
          set saved
          let ps := ps.map fun p => if p.env == s.ctx.env then { p with complete := false } else p
          go f rest (idx + 1) (.failed e :: acc) ps
  go (ss.length + 1) ss 0 [] []

/-- Results whose printed proof compiled completely: the proof is their premise. -/
def closeProofs (ss : List Sentence) (claims : List Claim) (ps : List ProofInfo) : List Claim :=
  claims.map fun cl =>
    match cl.role with
    | .statement env =>
      let label := (ss.find? (fun s => s.ctx.env == env)).map (·.ctx.label) |>.getD []
      match ps.find? (fun p => p.proves == label && p.complete && !p.steps.isEmpty) with
      | some p => { cl with premises := (p.steps ++ p.cites).eraseDups }
      | none => cl
    | _ => cl

def beginDocument (ts : List PTok) : List PTok :=
  match ts.findIdx? (fun t => t.tok == .begin w!"document") with
  | some i => ts.drop (i + 1)
  | none => ts

/-- Compile the sentences of an article into its document. -/
def assemble (ss : List Sentence) : Doc :=
  let ((outcomes, proofs), st) := (compileSentences ss).run {}
  let claims := closeProofs ss st.claims proofs
  ⟨st.globs, st.values, claims, ss.map (fun s => (s.ctx, s.start, s.stop)), outcomes, st.labels, proofs,
    st.preds ++ st.named ++ st.ops⟩

def isBeginDocument (len n : Nat) : Bool :=
  (unpackLine len n).take 16 == w!"\\begin{document}"

/-- The complete compilation of an article from its packed source lines: the
preamble supplies the macros, the paragraphs after `\begin{document}` the sentences. -/
def compileArticle (src : Packed) : Option Doc := do
  let k ← src.findIdx? (fun (len, n) => isBeginDocument len n)
  let ms ← macrosOf (Packed.join (src.take k))
  let bs := blocksOf (src.drop (k + 1)) (Packed.offset (src.take (k + 1))) none []
  let (ts, _) ← lexBlocks ms bs []
  some (assemble (sentences ts))

/-- Staged kernel certificates compose to the compilation of the whole source. -/
theorem compileArticle_eq {src : Packed} {k : Nat} {ms : Macros} {bs : List (Nat × Packed)}
    {ts : List PTok} {st : List Bool} {ss : List Sentence} {d : Doc}
    (h0 : src.findIdx? (fun (len, n) => isBeginDocument len n) = some k)
    (h1 : macrosOf (Packed.join (src.take k)) = some ms)
    (h2 : blocksOf (src.drop (k + 1)) (Packed.offset (src.take (k + 1))) none [] = bs)
    (h3 : lexBlocks ms bs [] = some (ts, st)) (h4 : sentences ts = ss) (h5 : assemble ss = d) :
    compileArticle src = some d := by
  simp [compileArticle, h0, h1, h2, h3, h4, h5]

end LeanMirror.Tex
