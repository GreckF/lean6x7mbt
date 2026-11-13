/-!
# MoonBit AST and pretty printer

A small abstract syntax for the MoonBit code we generate, together with a
printer.  Everything here is pure (no `Lean.Meta`), so the translation in
`Lean6x7mbt.Translate` only has to build values of these types.

Conventions (mirroring `rocq2mbt`):

* functions of Lean type `α → β` are curried single-argument closures
  `(A) -> (B) -> C`;
* top-level functions are *not* curried (`fn f(x : A, y : B) -> C`);
* enum constructors are always printed qualified (`Tree::Node(..)`).
-/

namespace Lean6x7mbt

/-! ## Types -/

inductive MTy where
  /-- a type variable such as `A` -/
  | var (n : String)
  /-- a type constructor application `Name[args]` (just `Name` when no args) -/
  | con (n : String) (args : Array MTy)
  /-- a type given by a user template, already substituted (printed verbatim) -/
  | raw (s : String)
  /-- tuple type; the empty tuple is `Unit` -/
  | tuple (ts : Array MTy)
  /-- closure type `(A, B) -> R` -/
  | fn (args : Array MTy) (ret : MTy)
  deriving Inhabited, BEq

partial def MTy.render : MTy → String
  | .var n => n
  | .con n #[] => n
  | .con n args => n ++ "[" ++ ", ".intercalate (args.toList.map render) ++ "]"
  | .raw s => s
  | .tuple #[] => "Unit"
  | .tuple ts => "(" ++ ", ".intercalate (ts.toList.map render) ++ ")"
  | .fn args ret => "(" ++ ", ".intercalate (args.toList.map render) ++ ") -> " ++ render ret

/-! ## Patterns -/

inductive Pat where
  | wild
  | var (n : String)
  /-- constructor pattern, `name` is already qualified (`Tree::Node`) -/
  | ctor (name : String) (args : Array Pat)
  | tuple (ps : Array Pat)
  | lit (s : String)
  /-- pattern produced by a user template -/
  | raw (s : String)
  deriving Inhabited

partial def Pat.render : Pat → String
  | .wild => "_"
  | .var n => n
  | .ctor n #[] => n
  | .ctor n ps => n ++ "(" ++ ", ".intercalate (ps.toList.map render) ++ ")"
  | .tuple ps => "(" ++ ", ".intercalate (ps.toList.map render) ++ ")"
  | .lit s => s
  | .raw s => s

/-! ## Expressions -/

inductive MExp where
  | var (n : String)
  /-- literal text (`42N`, `"abc"`, `true`) -/
  | lit (s : String)
  | unit
  | app (f : MExp) (args : Array MExp)
  /-- user template instantiated with arguments; printed as an atom -/
  | tpl (t : String) (args : Array MExp)
  | field (e : MExp) (f : String)
  | tuple (es : Array MExp)
  | ctor (name : String) (args : Array MExp)
  | structLit (ty : String) (fields : Array (String × MExp))
  | lam (ps : Array (String × Option MTy)) (body : MExp)
  | let_ (n : String) (v : MExp) (body : MExp)
  | ite (c t e : MExp)
  | match_ (s : MExp) (arms : Array (Pat × MExp))
  | abort (msg : String)
  deriving Inhabited

/-! ### Free-variable mention test (used to turn unused pattern variables into `_`) -/

partial def MExp.mentions (x : String) : MExp → Bool
  | .var n => n == x
  | .lit _ | .unit | .abort _ => false
  | .app f args => f.mentions x || args.any (·.mentions x)
  | .tpl _ args => args.any (·.mentions x)
  | .field e _ => e.mentions x
  | .tuple es => es.any (·.mentions x)
  | .ctor _ args => args.any (·.mentions x)
  | .structLit _ fs => fs.any (·.2.mentions x)
  | .lam ps b => !(ps.any (·.1 == x)) && b.mentions x
  | .let_ n v b => v.mentions x || (n != x && b.mentions x)
  | .ite c t e => c.mentions x || t.mentions x || e.mentions x
  | .match_ s arms => s.mentions x || arms.any (·.2.mentions x)

/-- Number of syntactic occurrences of the variable `x`. -/
partial def MExp.countVar (x : String) : MExp → Nat
  | .var n => if n == x then 1 else 0
  | .lit _ | .unit | .abort _ => 0
  | .app f args => f.countVar x + args.foldl (· + ·.countVar x) 0
  | .tpl _ args => args.foldl (· + ·.countVar x) 0
  | .field e _ => e.countVar x
  | .tuple es => es.foldl (· + ·.countVar x) 0
  | .ctor _ args => args.foldl (· + ·.countVar x) 0
  | .structLit _ fs => fs.foldl (· + ·.2.countVar x) 0
  | .lam ps b => if ps.any (·.1 == x) then 0 else b.countVar x
  | .let_ n v b => v.countVar x + (if n == x then 0 else b.countVar x)
  | .ite c t e => c.countVar x + t.countVar x + e.countVar x
  | .match_ s arms => arms.foldl (· + ·.2.countVar x) (s.countVar x)

/-! ## Templates -/

/-- Replace `$i` in `t` by `args[i]`. -/
def substTpl (t : String) (args : Array String) : String := Id.run do
  let cs := t.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '$' && i + 1 < cs.size && cs[i+1]!.isDigit then
      let mut j := i + 1
      let mut k := 0
      while j < cs.size && cs[j]!.isDigit do
        k := k * 10 + (cs[j]!.toNat - '0'.toNat)
        j := j + 1
      let a := args.getD k s!"${k}"
      -- `1.to_uint()` would lex as the float `1.`: parenthesize bare integer receivers
      let recv := j < cs.size && cs[j]! == '.' && !a.isEmpty && a.all Char.isDigit
      out := out ++ (if recv then "(" ++ a ++ ")" else a)
      i := j
    else
      out := out.push c
      i := i + 1
  return out

/-- Largest placeholder index in `t` plus one (0 if there is none). -/
def tplArity (t : String) : Nat := Id.run do
  let cs := t.toList.toArray
  let mut best := 0
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '$' && i + 1 < cs.size && cs[i+1]!.isDigit then
      let mut j := i + 1
      let mut k := 0
      while j < cs.size && cs[j]!.isDigit do
        k := k * 10 + (cs[j]!.toNat - '0'.toNat)
        j := j + 1
      best := max best (k + 1)
      i := j
    else
      i := i + 1
  return best

/-- How many times `$k` occurs in `t`. -/
def tplCount (t : String) (k : Nat) : Nat := Id.run do
  let cs := t.toList.toArray
  let mut cnt := 0
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '$' && i + 1 < cs.size && cs[i+1]!.isDigit then
      let mut j := i + 1
      let mut m := 0
      while j < cs.size && cs[j]!.isDigit do
        m := m * 10 + (cs[j]!.toNat - '0'.toNat)
        j := j + 1
      if m == k then cnt := cnt + 1
      i := j
    else
      i := i + 1
  return cnt

/-! ## Printer -/

/-- Strip one pair of outer parentheses `(a + b)` when it wraps the whole text
and the contents are not a tuple. -/
def stripParens (s : String) : String := Id.run do
  let cs := s.toList.toArray
  if cs.size < 3 || cs[0]! != '(' || cs[cs.size - 1]! != ')' then return s
  let mut depth := 0
  let mut inStr := false
  let mut esc := false
  for i in [:cs.size] do
    let c := cs[i]!
    if inStr then
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else if c == '"' then inStr := true
    else if c == '(' || c == '[' || c == '{' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' then
      depth := depth - 1
      if depth == 0 && i != cs.size - 1 then return s
    else if c == ',' && depth == 1 then return s
  return String.ofList (cs.extract 1 (cs.size - 1)).toList

def indentStr (n : Nat) : String := "".pushn ' ' n

/-- Is the rendered text a single line? -/
def oneLine (s : String) : Bool := !s.any (· == '\n')

/-- Expressions that can be used as the head of an application or the receiver
of a field access without parentheses. -/
def MExp.isAtom : MExp → Bool
  | .var _ | .lit _ | .unit | .app .. | .tpl .. | .field .. | .tuple .. | .ctor .. | .abort _ => true
  | .structLit .. => true
  | .lam .. | .let_ .. | .ite .. | .match_ .. => false

mutual

/-- Render an expression; continuation lines are indented relative to `ind`,
the indentation of the line the expression starts on. -/
partial def MExp.render (e : MExp) (ind : Nat) : String :=
  match e with
  | .var n => n
  | .lit s => s
  | .unit => "()"
  | .app f args =>
    -- a call of a closure-valued field must be written `(x.f)(a)`
    let h := match f with
      | .field .. => "(" ++ f.render ind ++ ")"
      | _ => renderAtom f ind
    h ++ "(" ++ ", ".intercalate (args.toList.map (·.render ind)) ++ ")"
  | .tpl t args => stripParens (substTpl t (args.map (renderAtom · ind)))
  | .field e f => renderAtom e ind ++ "." ++ f
  | .tuple es => "(" ++ ", ".intercalate (es.toList.map (·.render ind)) ++ ")"
  | .ctor n #[] => n
  | .ctor n args => n ++ "(" ++ ", ".intercalate (args.toList.map (·.render ind)) ++ ")"
  | .structLit ty fs =>
    ty ++ "::{ " ++ ", ".intercalate (fs.toList.map fun (n, v) => n ++ ": " ++ v.render ind) ++ " }"
  | .abort msg => "abort(" ++ msg ++ ")"
  | .lam ps body =>
    let ps := ", ".intercalate (ps.toList.map fun (n, t) =>
      match t with | some t => n ++ " : " ++ t.render | none => n)
    renderBraced s!"fn({ps}) " body ind
  | .let_ .. => renderBraced "" e ind
  | .ite c t f => renderIte c t f ind
  | .match_ s arms =>
    -- `match match .. {} {}` and `match if .. {} {}` are rejected by MoonBit
    let head := "match " ++ renderSubject s ind ++ " {\n"
    let body := arms.toList.map fun (p, b) =>
      indentStr (ind + 2) ++ p.render ++ " => " ++ renderArm b (ind + 2)
    head ++ "\n".intercalate body ++ "\n" ++ indentStr ind ++ "}"

/-- Scrutinee of a `match` or condition of an `if`: block-like expressions
need parentheses there. -/
partial def renderSubject (e : MExp) (ind : Nat) : String :=
  match e with
  | .lam .. | .let_ .. | .ite .. | .match_ .. => "(" ++ e.render ind ++ ")"
  | _ => e.render ind

partial def renderAtom (e : MExp) (ind : Nat) : String :=
  match e with
  | .tpl t args => substTpl t (args.map (renderAtom · ind))
  | _ => if e.isAtom then e.render ind else "(" ++ e.render ind ++ ")"

/-- `if` expression: one line when short, otherwise a block with `else if` chains. -/
partial def renderIte (c t f : MExp) (ind : Nat) : String :=
  let cs := renderSubject c ind
  let fs := match f with
    | .ite c' t' f' => renderIte c' t' f' ind
    | _ => renderBranch f ind
  let short := match t, f with
    | .let_ .., _ | _, .let_ .. => false
    | _, _ => true
  let ts1 := renderBranch t ind
  let oneL := "if " ++ cs ++ " " ++ ts1 ++ " else " ++ fs
  if short && oneLine oneL && oneL.length + ind <= 80 then oneL
  else
    let tb := match t with
      | .let_ .. => "{
" ++ renderStmts t (ind + 2) ++ "
" ++ indentStr ind ++ "}"
      | _ => "{
" ++ indentStr (ind + 2) ++ t.render (ind + 2) ++ "
" ++ indentStr ind ++ "}"
    let fb := match f with
      | .ite c' t' f' => renderIte c' t' f' ind
      | .let_ .. => "{
" ++ renderStmts f (ind + 2) ++ "
" ++ indentStr ind ++ "}"
      | _ => "{
" ++ indentStr (ind + 2) ++ f.render (ind + 2) ++ "
" ++ indentStr ind ++ "}"
    "if " ++ cs ++ " " ++ tb ++ " else " ++ fb

/-- `{ e }` on one line when possible, otherwise a block. -/
partial def renderBraced (prefix_ : String) (body : MExp) (ind : Nat) : String :=
  match body with
  | .let_ .. =>
    prefix_ ++ "{\n" ++ renderStmts body (ind + 2) ++ "\n" ++ indentStr ind ++ "}"
  | _ =>
    let b := body.render ind
    if oneLine b then prefix_ ++ "{ " ++ b ++ " }"
    else prefix_ ++ "{\n" ++ indentStr (ind + 2) ++ body.render (ind + 2) ++ "\n" ++ indentStr ind ++ "}"

/-- Branch of an `if`: `{ e }` or a multi-line block. -/
partial def renderBranch (body : MExp) (ind : Nat) : String :=
  match body with
  | .let_ .. => renderBraced "" body ind
  | _ =>
    let b := body.render ind
    if oneLine b && b.length < 60 then "{ " ++ b ++ " }"
    else "{\n" ++ indentStr (ind + 2) ++ body.render (ind + 2) ++ "\n" ++ indentStr ind ++ "}"

/-- Right-hand side of a match arm. -/
partial def renderArm (body : MExp) (ind : Nat) : String :=
  match body with
  | .let_ .. => renderBraced "" body ind
  | _ => body.render ind

/-- Statements of a `let` chain (no surrounding braces), each line indented
by `ind`. -/
partial def renderStmts (e : MExp) (ind : Nat) : String :=
  match e with
  | .let_ n v b =>
    indentStr ind ++ "let " ++ n ++ " = " ++ v.render ind ++ "\n" ++ renderStmts b ind
  | _ => indentStr ind ++ e.render ind

end

/-! ## Declarations -/

inductive MDecl where
  | enum (name : String) (tparams : Array String) (ctors : Array (String × Array MTy))
  | struct (name : String) (tparams : Array String) (fields : Array (String × MTy))
  /-- top-level function -/
  | fn (name : String) (tparams : Array String) (params : Array (String × MTy))
      (ret : MTy) (body : MExp)
  /-- top-level constant -/
  | const (name : String) (ty : MTy) (body : MExp)
  deriving Inhabited

def renderTParams (ts : Array String) : String :=
  if ts.isEmpty then "" else "[" ++ ", ".intercalate ts.toList ++ "]"

def MDecl.render : MDecl → String
  | .enum n tps ctors =>
    let cs := ctors.toList.map fun (c, args) =>
      if args.isEmpty then s!"  {c}"
      else s!"  {c}(" ++ ", ".intercalate (args.toList.map MTy.render) ++ ")"
    s!"pub(all) enum {n}{renderTParams tps} \{\n" ++ "\n".intercalate cs ++ "\n}"
  | .struct n tps fields =>
    let fs := fields.toList.map fun (f, t) => s!"  {f} : {t.render}"
    s!"pub(all) struct {n}{renderTParams tps} \{\n" ++ "\n".intercalate fs ++ "\n}"
  | .fn n tps ps ret body =>
    let ps := ", ".intercalate (ps.toList.map fun (x, t) => s!"{x} : {t.render}")
    let tp := if tps.isEmpty then "" else "[" ++ ", ".intercalate tps.toList ++ "]"
    s!"pub fn{tp} {n}({ps}) -> {ret.render} \{\n" ++ renderStmts body 2 ++ "\n}"
  | .const n ty body =>
    match body with
    | .let_ .. => s!"pub let {n} : {ty.render} = \{\n" ++ renderStmts body 2 ++ "\n}"
    | _ => s!"pub let {n} : {ty.render} = " ++ body.render 0

end Lean6x7mbt
