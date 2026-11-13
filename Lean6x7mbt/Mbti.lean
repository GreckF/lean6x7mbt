import Lean
import Lean6x7mbt.Table

/-!
# `import_mbti`: use an existing MoonBit package from Lean

```lean
import_mbti "path/to/pkg.generated.mbti" as Foo
```

reads the interface file written by `moon info` and adds, at elaboration time,

* `@[extern] axiom Foo.f : T₁ → T₂ → R` for every `pub fn f(T₁, T₂) -> R`, together with the extraction
  template `@pkg.f($0, $1)` (an `extract_constant`), so that `extract_moonbit` emits a direct call;
* an axiomatized type (`extract_type`) for every opaque `pub type`/`pub struct`, and a Lean `inductive`/`structure`
  (mapped back to the MoonBit type by `extract_inductive`) for every `pub(all) enum`/`struct`;
* methods `fn T::m(self, ..)` as `Foo.T.m` (usable with dot notation).

Items that have no Lean counterpart are skipped with a warning.  See the README (section `import_mbti`).
-/

open Lean Elab Command

namespace Lean6x7mbt.Mbti

/-! ## Lexer -/

inductive Tok where
  | id (s : String)
  | sym (s : String)
  | lit (s : String)
  deriving BEq, Inhabited

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Tokens of one line; a `//` comment ends the line. -/
def tokenize (s : String) : Array Tok := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Tok := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then
      i := i + 1
    else if c == '/' && cs[i+1]? == some '/' then
      break
    else if isIdChar c then
      let mut t := ""
      while i < cs.size && isIdChar cs[i]! do
        t := t.push cs[i]!
        i := i + 1
      out := out.push (.id t)
    else if c == '"' then
      let mut t := "\""
      i := i + 1
      while i < cs.size && cs[i]! != '"' do
        if cs[i]! == '\\' && i + 1 < cs.size then
          t := t.push cs[i]!
          i := i + 1
        t := t.push cs[i]!
        i := i + 1
      i := i + 1
      out := out.push (.lit (t.push '"'))
    else if c == '-' && cs[i+1]? == some '>' then
      out := out.push (.sym "->")
      i := i + 2
    else if c == ':' && cs[i+1]? == some ':' then
      out := out.push (.sym "::")
      i := i + 2
    else
      out := out.push (.sym (String.singleton c))
      i := i + 1
  return out

/-! ## Syntax of types and items -/

inductive Ty where
  /-- `Name[args]`, `@alias.Name[args]` (`Self` included) -/
  | con (name : String) (args : Array Ty)
  | opt (t : Ty)
  | tuple (ts : Array Ty)
  /-- closure type; `raises` for `raise E` / `raise` -/
  | fn (ps : Array Ty) (ret : Ty) (raises : Bool)
  | dyn (name : String)
  deriving Inhabited

partial def Ty.render : Ty → String
  | .con n #[] => n
  | .con n as => n ++ "[" ++ ", ".intercalate (as.toList.map Ty.render) ++ "]"
  | .opt t => t.render ++ "?"
  | .tuple ts => "(" ++ ", ".intercalate (ts.toList.map Ty.render) ++ ")"
  | .fn ps r raises =>
    "(" ++ ", ".intercalate (ps.toList.map Ty.render) ++ ") -> " ++ r.render ++ (if raises then " raise" else "")
  | .dyn n => "&" ++ n

/-- Names of the type constructors occurring in a type. -/
partial def Ty.cons : Ty → Array String
  | .con n as => as.foldl (fun acc a => acc ++ a.cons) #[n]
  | .opt t => t.cons
  | .tuple ts => ts.foldl (fun acc a => acc ++ a.cons) #[]
  | .fn ps r _ => ps.foldl (fun acc a => acc ++ a.cons) r.cons
  | .dyn _ => #[]

structure Param where
  /-- `x~ : T` (labelled) -/
  label : Option String := none
  /-- `x? : T` (optional, has a default) -/
  optional : Bool := false
  ty : Ty
  deriving Inhabited

structure FnSig where
  generics : Array (String × Array String) := #[]
  owner : Option String := none
  name : String
  params : Array Param
  ret : Ty
  raises : Bool := false
  isAsync : Bool := false
  deriving Inhabited

structure Field where
  name : String
  isMut : Bool
  ty : Ty
  deriving Inhabited

structure Variant where
  name : String
  params : Array Param
  deriving Inhabited

inductive TyBody where
  /-- representation not visible (or not translatable, then with the reason) -/
  | opaque (why : Option String)
  | struct (fields : Array Field)
  | enum (vars : Array Variant)
  deriving Inhabited

inductive Item where
  | fn (f : FnSig) (raw : String)
  /-- `pub let`/`pub const` -/
  | val (name : String) (ty : Ty) (raw : String)
  | ty (name : String) (gens : Array String) (body : TyBody) (raw : String)
  | skip (raw : String) (why : String)
  deriving Inhabited

structure Parsed where
  pkg : String := ""
  imports : Array (String × String) := #[]
  items : Array Item := #[]

/-! ## Parser -/

structure PS where
  toks : Array Tok
  pos : Nat := 0

abbrev P := StateT PS (Except String)

def peek : P (Option Tok) := do
  let s ← get
  return s.toks[s.pos]?

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def acceptSym (x : String) : P Bool := do
  if (← peek) == some (.sym x) then advance; return true else return false

def expectSym (x : String) : P Unit := do
  unless ← acceptSym x do throw s!"expected `{x}`"

def acceptId (x : String) : P Bool := do
  if (← peek) == some (.id x) then advance; return true else return false

def expectId : P String := do
  match ← peek with
  | some (.id s) => advance; return s
  | _ => throw "expected an identifier"

def atEnd : P Bool := return (← peek).isNone

mutual

partial def parseTy : P Ty := do
  let mut t ← parseAtom
  while ← acceptSym "?" do
    t := .opt t
  return t

partial def parseAtom : P Ty := do
  match ← peek with
  | some (.sym "(") =>
    advance
    let mut ts : Array Ty := #[]
    unless (← peek) == some (.sym ")") do
      ts := ts.push (← parseTy)
      while ← acceptSym "," do
        ts := ts.push (← parseTy)
    expectSym ")"
    if ← acceptSym "->" then
      let r ← parseTy
      let raises ← parseRaise
      return .fn ts r raises
    else if ts.size == 1 then return ts[0]!
    else return .tuple ts
  | some (.sym "&") =>
    advance
    let n ← parseName
    return .dyn n
  | some (.sym "@") | some (.id _) =>
    let n ← parseName
    let args ← parseArgs
    return .con n args
  | _ => throw "expected a type"

/-- `Name` or `@alias.Name` -/
partial def parseName : P String := do
  if ← acceptSym "@" then
    let a ← expectId
    expectSym "."
    let n ← expectId
    return s!"@{a}.{n}"
  else expectId

partial def parseArgs : P (Array Ty) := do
  let mut out := #[]
  if ← acceptSym "[" then
    out := out.push (← parseTy)
    while ← acceptSym "," do
      out := out.push (← parseTy)
    expectSym "]"
  return out

/-- After a closure/return type: `raise E`, `raise`, `raise?` (≙ not raising), `noraise`. -/
partial def parseRaise : P Bool := do
  if ← acceptId "noraise" then return false
  if ← acceptId "raise" then
    if ← acceptSym "?" then return false
    match ← peek with
    | some (.id _) | some (.sym "@") => let _ ← parseTy; return true
    | _ => return true
  return false

end

def parseParam : P Param := do
  let s ← get
  match s.toks[s.pos]?, s.toks[s.pos+1]?, s.toks[s.pos+2]? with
  | some (.id l), some (.sym "~"), some (.sym ":") =>
    set { s with pos := s.pos + 3 }
    return { label := some l, ty := ← parseTy }
  | some (.id l), some (.sym "?"), some (.sym ":") =>
    set { s with pos := s.pos + 3 }
    return { label := some l, optional := true, ty := ← parseTy }
  | _, _, _ => return { ty := ← parseTy }

def parseParams : P (Array Param) := do
  expectSym "("
  let mut ps := #[]
  unless (← peek) == some (.sym ")") do
    ps := ps.push (← parseParam)
    while ← acceptSym "," do
      ps := ps.push (← parseParam)
  expectSym ")"
  return ps

/-- `pub`, an optional `(all)`/`(open)`/`(readonly)`; returns the visibility word. -/
def parseVis : P String := do
  unless ← acceptId "pub" do throw "expected `pub`"
  if ← acceptSym "(" then
    let v ← expectId
    expectSym ")"
    return v
  return ""

def parseGenerics : P (Array (String × Array String)) := do
  let mut gs := #[]
  if ← acceptSym "[" then
    repeat
      let n ← expectId
      let mut bounds := #[]
      if ← acceptSym ":" then
        bounds := bounds.push (← parseTy).render
        while ← acceptSym "+" do
          bounds := bounds.push (← parseTy).render
      gs := gs.push (n, bounds)
      unless ← acceptSym "," do break
    expectSym "]"
  return gs

def parseFn : P FnSig := do
  let _ ← parseVis
  let isAsync ← acceptId "async"
  unless ← acceptId "fn" do throw "expected `fn`"
  let generics ← parseGenerics
  let mut name ← expectId
  let mut owner := none
  if ← acceptSym "::" then
    owner := some name
    name ← expectId
  let params ← parseParams
  let mut ret := Ty.tuple #[]
  let mut raises := false
  if ← acceptSym "->" then
    ret ← parseTy
    raises ← parseRaise
  else
    raises ← parseRaise
  unless ← atEnd do throw "unexpected tokens after the signature"
  return { generics, owner, name, params, ret, raises, isAsync }

def parseVal : P (String × Ty) := do
  let _ ← parseVis
  unless (← acceptId "let") || (← acceptId "const") do throw "expected `let` or `const`"
  let n ← expectId
  expectSym ":"
  let t ← parseTy
  -- `pub const X : T = v`: the value is not needed
  return (n, t)

def runP (toks : Array Tok) (p : P α) : Except String α :=
  (p.run { toks }).map (·.1)

/-- `{`/`}` balance of a line (string literals ignored). -/
def braceBalance (toks : Array Tok) : Int :=
  toks.foldl (fun n t => match t with | .sym "{" => n + 1 | .sym "}" => n - 1 | _ => n) 0

def parseVariant (line : String) : Except String Variant := do
  runP (tokenize line) do
    let n ← expectId
    let mut ps := #[]
    if (← peek) == some (.sym "(") then ps ← parseParams
    unless ← atEnd do throw "unexpected tokens"
    return { name := n, params := ps }

def parseField (line : String) : Except String Field := do
  runP (tokenize line) do
    let isMut ← acceptId "mut"
    let n ← expectId
    expectSym ":"
    let t ← parseTy
    unless ← atEnd do throw "unexpected tokens"
    return { name := n, isMut, ty := t }

/-- Header of a type declaration: visibility, keyword, name, generics, and the rest of the tokens. -/
def parseTyHead : P (String × String × String × Array (String × Array String)) := do
  let vis ← parseVis
  let kw ← expectId
  let n ← expectId
  let gs ← parseGenerics
  return (vis, kw, n, gs)

def pushSkip (o : Parsed) (raw why : String) : Parsed := { o with items := o.items.push (.skip raw why) }

/-- Parse the text of an `.mbti` file.  Lines that are not understood become `Item.skip`. -/
def parseFile (src : String) : Parsed := Id.run do
  let lines := (src.splitOn "\n").toArray.map fun l => (l.dropEndWhile (· == '\r')).toString
  let mut out : Parsed := {}
  let mut i := 0
  while i < lines.size do
    let line := lines[i]!
    i := i + 1
    let toks := tokenize line
    if toks.isEmpty then continue
    -- indentation: lines of a block are consumed with their header
    if line.front.isWhitespace then
      out := { out with items := out.items.push (.skip line.trimAscii.toString "unexpected indented line") }
      continue
    match toks[0]! with
    | .sym "#" => continue -- attributes of the next item
    | .id "package" =>
      if let some (Tok.lit s) := toks[1]? then out := { out with pkg := (s.drop 1).dropEnd 1 |>.toString }
    | .id "import" =>
      -- `import { "path" @alias, ... }`
      let mut imps := out.imports
      while i < lines.size && lines[i]!.trimAscii.toString != "}" do
        let ts := tokenize lines[i]!
        if let some (Tok.lit s) := ts[0]? then
          let path := (s.drop 1).dropEnd 1 |>.toString
          let alias := match ts[1]?, ts[2]? with
            | some (Tok.sym "@"), some (Tok.id a) => a
            | _, _ => (path.splitOn "/").getLast!
          imps := imps.push (alias, path)
        i := i + 1
      i := i + 1
      out := { out with imports := imps }
    | .id "pub" =>
      -- the whole block of this item
      let mut raw := line
      let mut bal := braceBalance toks
      let mut body : Array String := #[]
      while bal > 0 && i < lines.size do
        let l := lines[i]!
        i := i + 1
        bal := bal + braceBalance (tokenize l)
        if bal > 0 then body := body.push l
        raw := raw ++ "\n" ++ l
      -- keyword after `pub` and an optional visibility
      let kw := match toks[1]?, toks[2]?, toks[3]?, toks[4]? with
        | some (.sym "("), _, some (.sym ")"), some (.id k) => k
        | some (.id k), _, _, _ => k
        | _, _, _, _ => ""
      match kw with
      | "fn" | "async" =>
        match runP toks parseFn with
        | .ok f => out := { out with items := out.items.push (.fn f raw) }
        | .error e => out := pushSkip out raw s!"cannot parse the signature ({e})"
      | "let" | "const" =>
        match runP (toks.takeWhile (· != .sym "=")) parseVal with
        | .ok (n, t) => out := { out with items := out.items.push (.val n t raw) }
        | .error e => out := pushSkip out raw s!"cannot parse the declaration ({e})"
      | "type" =>
        match runP toks parseTyHead with
        | .ok (_, _, n, gs) =>
          -- `pub type T` / `pub type T[A]` is abstract; `pub type T = U` is an alias
          if toks.contains (.sym "=") then
            out := pushSkip out raw "type alias (aliases are already expanded in signatures)"
          else
            out := { out with items := out.items.push (.ty n (gs.map (·.1)) (.opaque Option.none) raw) }
        | .error e => out := pushSkip out raw s!"cannot parse the declaration ({e})"
      | "struct" | "enum" =>
        match runP toks parseTyHead with
        | .error e => out := pushSkip out raw s!"cannot parse the declaration ({e})"
        | .ok (vis, _, n, gs) =>
          let gnames := gs.map (·.1)
          let bounded := gs.any fun (_, b) => !b.isEmpty
          let hasBody := toks.contains (.sym "{")
          if bounded then
            out := { out with items := out.items.push (.ty n gnames (.opaque (some "type parameter with trait bound")) raw) }
          else if !hasBody then
            -- `struct S(A, B)`: tuple struct
            out := { out with items := out.items.push (.ty n gnames (.opaque (some "tuple struct")) raw) }
          else if vis != "all" then
            -- `pub struct`/`pub enum`: constructors/fields are not available to other packages
            out := { out with items := out.items.push (.ty n gnames (.opaque none) raw) }
          else
            let isEnum := kw == "enum"
            let mut err : Option String := none
            let mut fields : Array Field := #[]
            let mut vars : Array Variant := #[]
            for l in body do
              if (tokenize l).isEmpty then continue
              if isEnum then
                match parseVariant l with
                | .ok v => vars := vars.push v
                | .error e => err := err <|> some s!"cannot parse `{l.trimAscii}` ({e})"
              else
                match parseField l with
                | .ok f => fields := fields.push f
                | .error e => err := err <|> some s!"cannot parse `{l.trimAscii}` ({e})"
            if let some e := err then
              out := { out with items := out.items.push (.ty n gnames (.opaque (some e)) raw) }
            else if isEnum then
              if vars.isEmpty then
                out := { out with items := out.items.push (.ty n gnames (.opaque (some "enum without constructors")) raw) }
              else out := { out with items := out.items.push (.ty n gnames (.enum vars) raw) }
            else if fields.any (·.isMut) then
              out := { out with items := out.items.push (.ty n gnames (.opaque (some "mutable fields (MoonBit values are references)")) raw) }
            else out := { out with items := out.items.push (.ty n gnames (.struct fields) raw) }
      | "suberror" => out := pushSkip out raw "error type (`suberror`)"
      | "trait" => out := pushSkip out raw "trait"
      | "impl" => out := pushSkip out raw "trait implementation (`impl`)"
      | k => out := pushSkip out raw s!"unknown declaration `{k}`"
    | _ =>
      -- e.g. `}` that closes nothing, or an unknown top-level construct
      out := { out with items := out.items.push (.skip line "unknown syntax") }
  return out

/-! ## Lean types -/

structure Ctx where
  mode : NatMode
  ns : Name
  /-- alias used for the MoonBit package in templates (`@alias.f`) -/
  alias : String
  /-- unqualified calls (the caller is in the same MoonBit package) -/
  unqualified : Bool
  /-- aliases of the imports of the `.mbti` file: alias ↦ path -/
  imports : Array (String × String)
  /-- types declared by the package: name ↦ number of type parameters -/
  own : Array (String × Nat)
  tvars : Array String := #[]
  /-- the type `Self` stands for (in methods) -/
  owner : Option String := Option.none
  /-- inside the declaration of this type, refer to it by a relative name -/
  selfName : Option String := Option.none

/-- `_root_.«A».«B»` -/
def Ctx.leanName (c : Ctx) (parts : List String) (root := true) : String :=
  let comps := c.ns.components.map (·.toString) ++ parts
  (if root then "_root_." else "") ++ ".".intercalate (comps.map fun s => "«" ++ s ++ "»")

/-- The MoonBit qualifier of names from the package: `@alias.` or nothing. -/
def Ctx.qual (c : Ctx) : String := if c.unqualified then "" else "@" ++ c.alias ++ "."

def Ctx.leanDecl (c : Ctx) (parts : List String) : Name :=
  parts.foldl Name.mkStr c.ns

def paren (s : String) : String := "(" ++ s ++ ")"

def intMsg (mode : NatMode) (ty : String) : String :=
  s!"MoonBit `{ty}` has no Lean counterpart when `lean6x7mbt.nat` is \"{mode.tyName.toLower}\" (Lean `Nat`/`Int` extract to `{mode.tyName}`)"

/-- Lean type (as source text) of a MoonBit type. -/
partial def leanTy (c : Ctx) : Ty → Except String String
  | .con "Self" args => match c.owner with
    | some o => leanTy c (.con o args)
    | none => throw "`Self` outside of a method"
  | .con n args => do
    let argTexts ← args.mapM (leanTy c)
    let app := fun (h : String) => if argTexts.isEmpty then h else paren (h ++ " " ++ " ".intercalate argTexts.toList)
    let arity := fun (k : Nat) (what : String) =>
      if args.size == k then Except.ok () else Except.error s!"`{what}` takes {k} type argument(s)"
    -- the package's own types
    if n.front != '@' then
      if let some (_, k) := c.own.find? (·.1 == n) then
        unless args.size == k do throw s!"type `{n}` takes {k} type argument(s)"
        let h := if c.selfName == some n then c.leanName [n] (root := false) else c.leanName [n]
        return app h
    -- types of other packages
    if n.front == '@' then
      let body := n.drop 1
      let alias := (body.takeWhile (· != '.')).toString
      let base := (body.dropWhile (· != '.')).drop 1 |>.toString
      let path := (c.imports.find? (·.1 == alias)).map (·.2) |>.getD alias
      if path == "moonbitlang/core/bigint" && base == "BigInt" then
        if c.mode == .bigint then return "Int" else throw (intMsg c.mode "BigInt")
      throw s!"type `{n}` of package `{path}`"
    if c.tvars.contains n then
      unless args.isEmpty do throw s!"type parameter `{n}` applied to arguments"
      return n
    match n with
    | "Bool" => arity 0 n; return "Bool"
    | "String" => arity 0 n; return "String"
    | "Char" => arity 0 n; return "Char"
    | "Unit" => arity 0 n; return "Unit"
    | "Double" => arity 0 n; return "Float"
    | "Byte" => arity 0 n; return "UInt8"
    | "UInt" | "UInt32" => arity 0 n; return "UInt32"
    | "UInt16" => arity 0 n; return "UInt16"
    | "UInt64" => arity 0 n; return "UInt64"
    | "BigInt" => arity 0 n; if c.mode == .bigint then return "Int" else throw (intMsg c.mode n)
    | "Int" | "Int32" => arity 0 n; if c.mode == .int then return "Int" else throw (intMsg c.mode n)
    | "Int64" => arity 0 n; if c.mode == .int64 then return "Int" else throw (intMsg c.mode n)
    | "Float" => throw "MoonBit `Float` (32 bit) has no Lean counterpart (Lean `Float` is `Double`)"
    | "Array" => arity 1 n; return app "Array"
    | "Option" => arity 1 n; return app "Option"
    | "Result" => arity 2 n; return paren ("Except " ++ argTexts[1]! ++ " " ++ argTexts[0]!)
    | _ => throw s!"unknown type `{n}`"
  | .opt t => do return paren ("Option " ++ (← leanTy c t))
  | .tuple ts => do
    match ts.size with
    | 0 => return "Unit"
    | 2 => return paren ("Prod " ++ (← leanTy c ts[0]!) ++ " " ++ (← leanTy c ts[1]!))
    | n => throw s!"{n}-tuple (only pairs correspond to Lean's `Prod`)"
  | .fn ps r raises => do
    if raises then throw "closure that may raise"
    unless ps.size == 1 do
      throw s!"closure with {ps.size} parameters (Lean function values are single-argument closures)"
    return paren ((← leanTy c ps[0]!) ++ " → " ++ (← leanTy c r))
  | .dyn n => throw s!"trait object `&{n}`"

/-- Lean type of a function parameter.  A top-level closure with 0 or ≥ 2 parameters is accepted:
it is curried on the Lean side and the template adapts it.  Returns the number of closure
parameters for such an adapter. -/
def leanParamTy (c : Ctx) (t : Ty) : Except String (String × Option Nat) := do
  match t with
  | .fn ps r raises =>
    if raises then throw "closure parameter that may raise"
    if ps.size == 1 then return (← leanTy c t, none)
    let ps' ← ps.mapM (leanTy c)
    let r' ← leanTy c r
    let all := (if ps.isEmpty then #["Unit"] else ps') ++ #[r']
    return (paren (" → ".intercalate all.toList), some ps.size)
  | _ => return (← leanTy c t, none)

/-! ## Declarations -/

/-- Number of single-argument closure layers at the top of a result type (the Lean type
`A → (B → C)` has those as extra arguments of the axiom). -/
partial def closureDepth : Ty → Nat
  | .fn ps r false => if ps.size == 1 then 1 + closureDepth r else 0
  | _ => 0

structure FnOut where
  /-- everything after the name: binders and type -/
  sig : String
  tpl : String

def genFn (c : Ctx) (f : FnSig) : Except String FnOut := do
  if f.isAsync then throw "async function"
  if f.raises then throw "function that may raise (`raise`)"
  for (g, bs) in f.generics do
    unless bs.isEmpty do throw s!"type parameter `{g}` with trait bound `{" + ".intercalate bs.toList}`"
  let mut c := { c with tvars := f.generics.map (·.1) }
  if let some o := f.owner then
    unless c.own.any (·.1 == o) do throw s!"method of type `{o}`, which this package does not declare"
    c := { c with owner := some o }
  -- parameters
  let mut tys : Array String := #[]
  let mut args : Array String := #[]
  for p in f.params do
    if p.optional then continue
    let (t, ad) ← leanParamTy c p.ty
    let i := tys.size
    tys := tys.push t
    let a := match ad with
      | none => s!"${i}"
      | some 0 => s!"fn() \{ (${i})(()) }"
      | some n =>
        let vs := (List.range n).map fun k => s!"lean_p{i}_{k}"
        s!"fn({", ".intercalate vs}) \{ (${i})" ++ "".intercalate (vs.map fun v => s!"({v})") ++ " }"
    args := args.push (match p.label with
      | some l => l ++ "=" ++ a
      | none => a)
  let isFnLike := true
  let _ := isFnLike
  let ret ← leanTy c f.ret
  let tys' := if tys.isEmpty then #["Unit"] else tys
  let binders := if f.generics.isEmpty then "" else
    " {" ++ " ".intercalate (f.generics.map (·.1)).toList ++ " : Type}"
  let sig := binders ++ " : " ++ " → ".intercalate (tys'.toList ++ [ret])
  let head := (c.qual) ++ (match f.owner with | some o => o ++ "::" | none => "") ++ f.name
  let mut tpl := head ++ "(" ++ ", ".intercalate args.toList ++ ")"
  let k := tys'.size
  for j in [:closureDepth f.ret] do
    tpl := tpl ++ s!"(${k + j})"
  return { sig, tpl }

def genVal (c : Ctx) (name : String) (t : Ty) : Except String FnOut := do
  let ty ← leanTy c t
  let mut tpl := c.qual ++ name
  for j in [:closureDepth t] do
    tpl := tpl ++ s!"(${j})"
  return { sig := " : " ++ ty, tpl }

/-- Safe single-line text for a doc comment. -/
def docText (s : String) : String :=
  ((s.replace "-/" "- /").replace "\n" " ").trimAscii.toString

/-- Elaborate Lean source text as a command.  On failure the environment is restored and the
error returned. -/
def elabText (src : String) : CommandElabM (Option String) := do
  let env ← getEnv
  match Parser.runParserCategory env `command src "<import_mbti>" with
  | .error e => return some e
  | .ok stx =>
    let saved ← get
    modify fun s => { s with messages := {} }
    try
      elabCommand stx
    catch ex =>
      let m ← ex.toMessageData.toString
      set saved
      return some m
    let new := (← get).messages
    if new.hasErrors then
      let mut text := ""
      for m in new.toList do
        if m.severity == .error then
          text := text ++ (← m.data.toString)
          break
      set saved
      return some text
    modify fun s => { s with messages := saved.messages ++ new }
    return none

def typeBinderText (arity : Nat) : String :=
  " : " ++ "".intercalate (List.replicate arity "Type → ") ++ "Type"

def tvarNames (gens : Array String) : String :=
  if gens.isEmpty then "" else " (" ++ " ".intercalate gens.toList ++ " : Type)"

/-- Source of the Lean `inductive`/`structure` for a transparent type. -/
def genTypeDecl (c : Ctx) (name : String) (gens : Array String) (body : TyBody) :
    Except String (String × Array String × Array (Name × String)) := do
  let c := { c with tvars := gens, selfName := some name }
  let selfTy := c.leanName [name] (root := false) ++ (if gens.isEmpty then "" else " " ++ " ".intercalate gens.toList)
  match body with
  | .opaque _ => throw "opaque"
  | .enum vars =>
    let mut lines : Array String := #[]
    let mut ctors : Array String := #[]
    for v in vars do
      let mut ts : Array String := #[]
      let mut targs : Array String := #[]
      for p in v.params do
        ts := ts.push (← leanTy c p.ty)
        let i := ts.size - 1
        targs := targs.push (match p.label with | some l => s!"{l}=${i}" | none => s!"${i}")
      lines := lines.push s!"  | «{v.name}» : {" → ".intercalate (ts.toList ++ [selfTy])}"
      ctors := ctors.push (c.qual ++ name ++ "::" ++ v.name ++
        (if targs.isEmpty then "" else "(" ++ ", ".intercalate targs.toList ++ ")"))
    let src := s!"inductive {c.leanName [name]}{tvarNames gens} : Type where\n" ++ "\n".intercalate lines.toList
    return (src, ctors, #[])
  | .struct fields =>
    let mut lines : Array String := #[]
    let mut projs : Array (Name × String) := #[]
    let mut ctorArgs : Array String := #[]
    for fl in fields, i in [:fields.size] do
      lines := lines.push s!"  («{fl.name}» : {← leanTy c fl.ty})"
      ctorArgs := ctorArgs.push s!"{fl.name}: ${i}"
      projs := projs.push (c.leanDecl [name, fl.name], s!"$0.{fl.name}")
    let src := s!"structure {c.leanName [name]}{tvarNames gens} where\n  mk ::\n" ++ "\n".intercalate lines.toList
    let ctor := c.qual ++ name ++ "::{ " ++ ", ".intercalate ctorArgs.toList ++ " }"
    return (src, #[ctor], projs)

structure Stats where
  fns : Nat := 0
  tys : Nat := 0
  skipped : Nat := 0


/-! ## The command -/

declare_syntax_cat mbtiOpt
syntax " (" &"alias" " := " str ")" : mbtiOpt
syntax " (" &"unqualified" ")" : mbtiOpt

syntax (name := importMbti) "import_mbti " str (&" as " ident)? mbtiOpt* : command

def firstLine (s : String) : String := (s.splitOn "\n").head!

@[command_elab importMbti] def elabImportMbti : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwError "expected a file name"
  let src ← try IO.FS.readFile path catch ex => throwError m!"import_mbti: cannot read {path}: {ex.toMessageData}"
  let parsed := parseFile src
  if parsed.pkg.isEmpty then throwError "import_mbti: {path} has no `package \"..\"` line (is it a `moon info` file?)"
  let opts ← getOptions
  let modeStr := opts.get `lean6x7mbt.nat "bigint"
  let some mode := NatMode.ofString? modeStr
    | throwError "invalid value of lean6x7mbt.nat: {modeStr} (expected bigint, int or int64)"
  let last := (parsed.pkg.splitOn "/").getLast!
  let ns : Name := if stx[2].getNumArgs > 0 then stx[2][1].getId else Name.mkSimple last
  let mut alias := last
  let mut unqualified := false
  for o in stx[3].getArgs do
    if o[1].getAtomVal == "alias" then alias := (o[3].isStrLit?).getD last
    else unqualified := true
  let tys := parsed.items.filterMap fun
    | .ty n g b raw => some (n, g, b, raw)
    | _ => none
  let c : Ctx := { mode, ns, alias, unqualified, imports := parsed.imports,
                   own := tys.map fun (n, g, _, _) => (n, g.size) }
  let mut stats : Stats := {}
  let warn := fun (raw : String) (why : String) => do
    logWarning m!"import_mbti: skipped `{firstLine raw}`: {why}"
  unless unqualified do
    modifyEnv (tableExt.addEntry · (.extPkg alias parsed.pkg))
  -- types: references between the transparent ones decide the order; cycles become opaque
  let names := tys.map (·.1)
  let depsOf := fun (n : String) (b : TyBody) =>
    let cs : Array String := match b with
      | .struct fs => fs.foldl (fun a f => a ++ f.ty.cons) #[]
      | .enum vs => vs.foldl (fun a v => v.params.foldl (fun a p => a ++ p.ty.cons) a) #[]
      | .opaque _ => #[]
    (cs.filter fun x => x != n && names.contains x).toList.eraseDups.toArray
  let deps := tys.map fun (n, _, b, _) => (n, depsOf n b)
  let reach := fun (a b : String) => Id.run do
    let mut seen : Array String := #[a]
    let mut todo := #[a]
    while !todo.isEmpty do
      let x := todo.back!
      todo := todo.pop
      for y in (deps.find? (·.1 == x)).map (·.2) |>.getD #[] do
        if !seen.contains y then
          seen := seen.push y
          todo := todo.push y
    return seen.contains b && a != b
  let cyclic := names.filter fun a => names.any fun b => reach a b && reach b a
  let mut pending : Array (String × Array String × TyBody × String) := #[]
  for (n, g, b, raw) in tys do
    if cyclic.contains n then
      warn raw s!"mutually recursive types are declared as opaque types"
      pending := pending.push (n, g, .opaque none, raw)
    else pending := pending.push (n, g, b, raw)
  let mut declared : Array String := #[]
  let mut ordered : Array (String × Array String × TyBody × String) := #[]
  -- opaque ones first, then transparent ones whose dependencies are declared
  for t in pending do
    if let .opaque _ := t.2.2.1 then
      ordered := ordered.push t
      declared := declared.push t.1
  let mut rest := pending.filter fun t => !declared.contains t.1
  while !rest.isEmpty do
    let some t := rest.find? fun t => ((deps.find? (·.1 == t.1)).map (·.2) |>.getD #[]).all declared.contains
      | break
    ordered := ordered.push t
    declared := declared.push t.1
    rest := rest.filter (·.1 != t.1)
  for (n, g, b, raw) in ordered do
    let declName := c.leanDecl [n]
    let tyTpl := c.qual ++ n ++ (if g.isEmpty then "" else
      "[" ++ ", ".intercalate ((List.range g.size).map fun i => s!"${i}") ++ "]")
    let doc := s!"/-- MoonBit: `{docText (firstLine raw)}` -/\n"
    let asOpaque := fun (why : Option String) => do
      if let some w := why then
        logWarning m!"import_mbti: `{firstLine raw}` is imported as an opaque type: {w}"
      match ← elabText (doc ++ s!"axiom {c.leanName [n]}{typeBinderText g.size}") with
      | Option.none =>
        modifyEnv (tableExt.addEntry · (.ind declName { ty := tyTpl, ctors := #[] }))
        return true
      | some e =>
        warn raw s!"cannot declare the Lean type ({e})"
        return false
    let ok ← match b with
    | .opaque why => asOpaque why
    | _ =>
      match genTypeDecl c n g b with
      | .error e => asOpaque (some e)
      | .ok (decl, ctors, projs) =>
        match ← elabText (doc ++ decl) with
        | some e => asOpaque (some s!"cannot declare it as a Lean inductive/structure ({e})")
        | Option.none =>
          modifyEnv (tableExt.addEntry · (.ind declName { ty := tyTpl, ctors }))
          for (pn, tpl) in projs do
            modifyEnv (tableExt.addEntry · (.const pn tpl))
          pure true
    stats := if ok then { stats with tys := stats.tys + 1 } else { stats with skipped := stats.skipped + 1 }
  -- functions and values
  for it in parsed.items do
    let (parts, raw, r) : List String × String × Except String FnOut := match it with
      | .fn f raw => ((f.owner.toList ++ [f.name]), raw, genFn c f)
      | .val n t raw => ([n], raw, genVal c n t)
      | _ => ([], "", .error "")
    match it with
    | .skip raw why => warn raw why; stats := { stats with skipped := stats.skipped + 1 }
    | .ty .. => pure ()
    | _ =>
      match r with
      | .error e => warn raw e; stats := { stats with skipped := stats.skipped + 1 }
      | .ok out =>
        let declName := c.leanDecl parts
        if (← getEnv).contains declName then
          warn raw s!"`{declName}` already exists"
          stats := { stats with skipped := stats.skipped + 1 }
        else
          let sym := "mbti_" ++ "_".intercalate ((c.ns.components.map (·.toString)) ++ parts)
          let text := s!"/-- MoonBit: `{docText (firstLine raw)}` -/\n@[extern \"{sym}\"] axiom {c.leanName parts}{out.sig}"
          match ← elabText text with
          | none =>
            modifyEnv (tableExt.addEntry · (.const declName out.tpl))
            stats := { stats with fns := stats.fns + 1 }
          | some e =>
            warn raw s!"cannot declare the Lean axiom ({e})"
            stats := { stats with skipped := stats.skipped + 1 }
  logInfo m!"import_mbti: package {parsed.pkg} as {ns}: imported {stats.fns} function(s)/value(s) and {stats.tys} type(s), skipped {stats.skipped} item(s)"

end Lean6x7mbt.Mbti
