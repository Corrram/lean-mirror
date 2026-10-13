import Lean

/-! The source language is defined by executable, total Lean functions. A source
certificate proves an equation about these functions; an external parser or an
LLM cannot substitute a different statement. Unsupported text is an error.
-/
namespace LeanMirror.Source

inductive Syntax where
  | name (value : String)
  | number (value : Nat)
  | app (fn arg : Syntax)
  | unary (op : String) (arg : Syntax)
  | binary (op : String) (left right : Syntax)
  | bind (kind name domain : String) (body : Syntax)
  | integral (name : String) (body : Syntax)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

private def flush (word : List Char) (out : List String) : List String :=
  if word.isEmpty then out else String.ofList word.reverse :: out

private def lexChars : Nat → List Char → List Char → List String → Except String (List String)
  | 0, _, _, _ => .error "source lexer exhausted its structural bound"
  | _ + 1, [], word, out => .ok (flush word out).reverse
  | fuel + 1, '%' :: cs, word, out => lexChars fuel (cs.dropWhile (· != '\n')) [] (flush word out)
  | fuel + 1, '\\' :: cs, word, out =>
    let cmd := cs.takeWhile Char.isAlpha
    if cmd.isEmpty then
      match cs with
      | [] => .ok ("\\" :: flush word out).reverse
      | c :: rest => lexChars fuel rest [] (("\\" ++ String.singleton c) :: flush word out)
    else lexChars fuel (cs.drop cmd.length) [] (("\\" ++ String.ofList cmd) :: flush word out)
  | fuel + 1, c :: cs, word, out =>
    if c.isWhitespace then lexChars fuel cs [] (flush word out)
    else if c.isAlphanum || c == '_' then lexChars fuel cs (c :: word) out
    else lexChars fuel cs [] (String.singleton c :: flush word out)

/-- Mathematical delimiters must balance. Spacing commands have no semantics;
all other commands survive lexing and must be consumed by the grammar. -/
private def delimiters : List String → Option String → Except String (List String)
  | [], none => .ok []
  | [], some _ => .error "unclosed mathematical delimiter"
  | t :: ts, mode => do
    if ["\\(", "\\[", "$"].contains t && mode.isNone then
      delimiters ts (some (if t == "\\(" then "\\)" else if t == "\\[" then "\\]" else "$"))
    else if ["\\)", "\\]", "$"].contains t then
      if mode == some t then delimiters ts none else throw "mismatched mathematical delimiter"
    else if ["\\(", "\\["].contains t then throw "nested mathematical delimiter"
    else if ["\\,", "\\;", "\\!", "\\quad", "\\qquad"].contains t then delimiters ts mode
    else return t :: (← delimiters ts mode)

def tokenize (text : String) : Except String (List String) := do
  delimiters (← lexChars (text.toList.length + 1) text.toList [] []) none

abbrev ParseResult := Except String (Syntax × List String)

private def require (expected : String) (ts : List String) : Except String (List String) :=
  match ts with
  | t :: rest => if t == expected then .ok rest else .error s!"expected '{expected}', found '{t}'"
  | [] => .error s!"expected '{expected}' at end of source"

private def identifier (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_') &&
    !(s.toList.headD '0').isDigit

private def numeral (s : String) : Option Nat :=
  if s.toList.isEmpty then none
  else s.toList.foldlM (fun n c => if c.isDigit then some (10 * n + c.toNat - '0'.toNat) else none) 0

private def commandName (s : String) : Bool :=
  match s.toList with
  | '\\' :: cs => identifier (String.ofList cs)
  | _ => false

private def before (stop : String) : List String → Nat → List String
  | [], _ => []
  | t :: ts, depth =>
    if t == stop && depth == 0 then []
    else t :: before stop ts (if ["[", "{"].contains t then depth + 1
      else if ["]", "}"].contains t then depth - 1 else depth)

private def domainUntil (stop : String) (ts : List String) : Except String (String × List String) := do
  let words := before stop ts 0
  if words.isEmpty then throw "missing mathematical domain"
  let rest ← require stop (ts.drop words.length)
  return (String.intercalate " " words, rest)

private def operator (s : String) : Option (String × Nat) :=
  if ["\\iff", "\\Longleftrightarrow"].contains s then some ("iff", 10)
  else if ["\\implies", "\\Longrightarrow"].contains s then some ("imp", 15)
  else if s == "\\lor" then some ("or", 20)
  else if ["\\land", "and"].contains s then some ("and", 25)
  else if s == "=" then some ("eq", 30)
  else if ["\\le", "\\leq", "≤"].contains s then some ("le", 30)
  else if s == "<" then some ("lt", 30)
  else if s == "+" then some ("add", 40)
  else if s == "-" then some ("sub", 40)
  else if ["*", "\\cdot"].contains s then some ("mul", 50)
  else if s == "/" then some ("div", 50)
  else none

private def isRelation (s : Syntax) : Bool :=
  match s with
  | .binary op _ r => ["eq", "le", "lt"].contains op || (op == "and" && isRelation r)
  | _ => false

private def lastOperand : Syntax → Syntax
  | .binary op _ r => if op == "and" then lastOperand r else r
  | s => s

private inductive Mode where
  | expression (precedence : Nat)
  | tail (precedence : Nat) (lhs : Syntax)
  | arguments (fn : Syntax)
  | atom | sentence | document

/-- One structurally recursive parser avoids expanding a mutually recursive
tuple of parsers during kernel evaluation. Fuel exhaustion always rejects. -/
private def run : Nat → Mode → List String → ParseResult
    | 0, _, _ => .error "source parser exhausted its structural bound"
    | fuel + 1, .expression precedence, ts => do
      let (lhs, rest) ← run fuel .atom ts
      run fuel (.tail precedence lhs) rest
    | fuel + 1, .tail precedence lhs, ts => do
      let t :: rest := ts | return (lhs, [])
      if t == "(" then
        if precedence > 70 then return (lhs, ts)
        let (applied, remaining) ← run fuel (.arguments lhs) rest
        return ← run fuel (.tail precedence applied) remaining
      match operator t with
      | none => return (lhs, ts)
      | some (op, p) =>
        if p < precedence then return (lhs, ts)
        let rightPrecedence := if ["and", "or", "imp", "iff"].contains op then p else p + 1
        let (rhs, remaining) ← run fuel (.expression rightPrecedence) rest
        let result := if p == 30 && isRelation lhs then
            Syntax.binary "and" lhs (.binary op (lastOperand lhs) rhs)
          else .binary op lhs rhs
        run fuel (.tail precedence result) remaining
    | fuel + 1, .arguments fn, ts => do
      let (arg, rest) ← run fuel (.expression 0) ts
      let t :: remaining := rest | throw "unclosed function application"
      if t == "," then run fuel (.arguments (.app fn arg)) remaining
      else if t == ")" then return (.app fn arg, remaining)
      else throw "expected ',' or ')' in function application"
    | fuel + 1, .atom, ts => do
      let t :: rest := ts | throw "expected mathematical expression"
      if t == "(" || t == "{" then
        let (body, remaining) ← run fuel (.expression 0) rest
        return (body, ← require (if t == "(" then ")" else "}") remaining)
      if ["-", "\\abs", "\\real"].contains t then
        let (body, remaining) ← run fuel (.expression 60) rest
        return (.unary t body, remaining)
      if t == "\\frac" then
        let rest ← require "{" rest
        let (x, remaining) ← run fuel (.expression 0) rest
        let remaining ← require "}" remaining >>= require "{"
        let (y, remaining) ← run fuel (.expression 0) remaining
        return (.binary "div" x y, ← require "}" remaining)
      if t == "\\forall" || t == "\\exists" then
        let n :: rest := rest | throw "missing binder"
        if !identifier n then throw "invalid binder name"
        let rest ← require "\\in" rest
        let (domain, remaining) ← domainUntil "," rest
        let (body, remaining) ← run fuel .sentence remaining
        return (.bind (if t == "\\forall" then "all" else "ex") n domain body, remaining)
      if t == "\\int" then
        let mut rest := rest
        for expected in ["_", "{", "0", "}", "^", "{", "1", "}", "{"] do
          rest ← require expected rest
        let n :: afterName := rest | throw "missing integral binder"
        if !identifier n then throw "invalid integral binder"
        let bodyTokens ← require "}" afterName >>= require "{"
        let (body, remaining) ← run fuel (.expression 0) bodyTokens
        return (.integral n body, ← require "}" remaining)
      match numeral t with
      | some n => return (.number n, rest)
      | none =>
        if identifier t || commandName t then return (.name t, rest)
        throw s!"unsupported mathematical token '{t}'"
    | fuel + 1, .sentence, ts => do
      let t :: rest := ts | throw "expected mathematical sentence"
      if t == "Similarly" then run fuel .sentence (← require "," rest)
      else if t == "If" || t == "if" then
        if rest[1]? == some "is" then
          let n := rest.head!
          if !identifier n then throw "invalid binder name"
          let rest ← require "a" (rest.drop 2)
          let (domain, remaining) ← domainUntil "," rest
          let remaining ← require "then" remaining
          let (body, remaining) ← run fuel .sentence remaining
          return (.bind "all" n domain body, remaining)
        else
          let (hyp, remaining) ← run fuel (.expression 0) rest
          let remaining ← require "," remaining >>= require "then"
          let (body, remaining) ← run fuel .sentence remaining
          return (.binary "imp" hyp body, remaining)
      else if t == "For" || t == "for" then
        let rest ← require "every" rest
        let n :: rest := rest | throw "missing universal binder"
        if !identifier n then throw "invalid binder name"
        let rest ← require "\\in" rest
        let (domain, remaining) ← domainUntil "," rest
        let (body, remaining) ← run fuel .sentence remaining
        return (.bind "all" n domain body, remaining)
      else if t == "There" || t == "there" then
        let rest ← require "exists" rest >>= require "a"
        let words := before "such" rest 0
        let remaining ← require "such" (rest.drop words.length) >>= require "that"
        let n := words.getLast!
        if !identifier n then throw "invalid existential binder"
        let domain := String.intercalate " " words.dropLast
        let (body, remaining) ← run fuel .sentence remaining
        return (.bind "ex" n domain body, remaining)
      else if t == "Then" then run fuel .sentence rest
      else run fuel (.expression 0) ts
    | fuel + 1, .document, ts => do
      if ts.head? == some "Let" then
        let n := ts[1]?.getD ""
        if !identifier n then throw "invalid binder name"
        let rest ← require "be" (ts.drop 2) >>= require "a"
        let (domain, remaining) ← domainUntil "." rest
        let (body, remaining) ← run fuel .document remaining
        return (.bind "all" n domain body, remaining)
      else
        let (first, remaining) ← run fuel .sentence ts
        if remaining.isEmpty || remaining == ["."] then return (first, [])
        if remaining.head? == some "." then
          let (next, remaining) ← run fuel .document remaining.tail!
          return (.binary "and" first next, remaining)
        return (first, remaining)

/-- The complete input must be consumed. In particular, trailing claims such as
“both inequalities are sharp” cannot silently disappear. -/
def parseTokens (ts : List String) : Except String Syntax := do
  let (tree, remaining) ← run (ts.length * 8 + 32) .document ts
  if !remaining.isEmpty then throw s!"unconsumed source: {String.intercalate " " remaining}"
  return tree

def parse (text : String) : Except String Syntax := do
  parseTokens (← tokenize text)

end LeanMirror.Source
