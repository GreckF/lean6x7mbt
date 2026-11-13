import Lean
import Lean6x7mbt.Runtime
import Lean6x7mbt.Ast
import Lean6x7mbt.Table

/-!
# Kernel `Expr` → MoonBit

The translation works directly on kernel terms (like Rocq's extraction):

* recursive functions are taken from their `_unsafe_rec` versions, which the
  Lean elaborator keeps for the code generator and which still contain the
  `match` expressions and direct recursion of the source;
* `match` (matcher) applications and `casesOn` become MoonBit `match`/`if`;
* instance projections are reduced (`HAdd.hAdd Nat Nat Nat inst a b` becomes
  `Nat.add a b`) so that arithmetic stays readable;
* type arguments and proofs are erased (type parameters become MoonBit
  generics), `Decidable p` is `Bool`.
-/

open Lean Meta

namespace Lean6x7mbt

/-- What a binder is at run time. -/
inductive Kind where
  | ty    -- type (former): becomes a generic parameter, erased in terms
  | prf   -- proof: erased
  | dict  -- type-class dictionary (kept, but skipped by `$i` templates)
  | val   -- ordinary value
  deriving Inhabited, BEq

def Kind.kept : Kind → Bool
  | .dict | .val => true
  | _ => false

structure Sig where
  kinds : Array Kind
  /-- number of Lean arguments a direct call consumes -/
  arity : Nat
  deriving Inhabited

inductive Shape where
  | enum
  /-- Lean field names of the kept fields -/
  | struct (fields : Array Name)
  deriving Inhabited

/-- A constant (or test term) that could not be extracted. -/
structure ExError where
  /-- dependency chain from a root to the failing item (the missing constant, if any, is last) -/
  chain : List String
  msg : String
  /-- the constant lacking a mapping (`no extraction for ..`), for the summary -/
  missing : Option Name := none

structure ExState where
  mode : NatMode := .bigint
  table : Table := {}
  globalNames : Std.HashMap Name String := {}
  usedGlobals : Std.HashSet String := {}
  allLocals : Std.HashSet String := {}
  locals : Std.HashMap FVarId String := {}
  scope : Std.HashSet String := {}
  tyVars : Std.HashMap FVarId String := {}
  queue : Array Name := #[]
  seen : Std.HashSet Name := {}
  /-- extracted declarations, tagged with their package (`""` in single-file mode) -/
  types : Array (String × MDecl) := #[]
  fns : Array (String × MDecl) := #[]
  helpers : Std.HashSet String := {}
  sigs : Std.HashMap Name Sig := {}
  shapes : Std.HashMap Name Shape := {}
  /-- specializations of higher-kinded functions: key ↦ synthetic constant -/
  specs : Std.HashMap (String × Expr) Name := {}
  /-- synthetic constants: value and type (closed terms) -/
  aux : Std.HashMap Name (Expr × Expr) := {}
  /-- who first enqueued each constant (roots have no entry) -/
  origin : Std.HashMap Name Name := {}
  /-- the constant being extracted right now -/
  cur : Option Name := none
  /-- set when the current item fails for lack of a mapping -/
  curMissing : Option Name := none
  errors : Array ExError := #[]
  /-- project mode (`extract_moonbit_project`): several MoonBit packages -/
  project : Bool := false
  /-- package of the declaration being extracted (`""` in single-file mode) -/
  curPkg : String := ""
  /-- package that receives the tests and the constants of the main module -/
  mainPkg : String := ""
  /-- Lean module ↦ package name -/
  pkgNames : Std.HashMap Name String := {}
  pkgUsed : Std.HashSet String := {}
  /-- package of each synthetic (specialized) constant: the one that requested it -/
  auxPkg : Std.HashMap Name String := {}

abbrev M := StateRefT ExState MetaM

/-! ## Names -/

def keywords : Std.HashSet String := Std.HashSet.ofList [
  "as", "else", "extern", "fn", "if", "let", "const", "match", "using", "mut", "type", "struct",
  "enum", "extenum", "trait", "derive", "while", "break", "continue", "import", "return", "throw",
  "raise", "try", "catch", "pub", "priv", "proof_assert", "proof_let", "readonly", "true", "false",
  "_", "test", "loop", "for", "in", "impl", "with", "guard", "async", "is", "suberror", "and",
  "letrec", "enumview", "noraise", "nocancel", "defer", "lexmatch", "lexscan", "where", "declare",
  "nobreak", "extend", "typealias", "traitalias", "fnalias", "init", "main", "self", "Self", "__",
  "module", "move", "ref", "static", "super", "unsafe", "use", "await", "dyn", "abstract", "do",
  "final", "macro", "override", "typeof", "virtual", "yield", "local", "method", "alias", "assert",
  "package", "recur", "isnot", "define", "downcast", "inherit", "member", "namespace", "upcast",
  "void", "lazy", "include", "mixin", "protected", "sealed", "constructor", "atomic", "volatile",
  "anyframe", "anytype", "asm", "comptime", "errdefer", "export", "opaque", "orelse", "resume",
  "threadlocal", "unreachable", "dynclass", "dynobj", "dynrec", "var", "finally", "noasync",
  "assume",
  -- builtin types / functions we must not shadow
  "Int", "Int8", "Int16", "Int32", "Int64", "UInt", "UInt8", "UInt16", "UInt32", "UInt64", "Byte", "Bool", "Char", "String", "Double",
  "Float", "Unit", "Bytes", "Array", "FixedArray", "Option", "Result", "Ref", "Map", "Error", "Json",
  "BigInt", "abort", "panic", "ignore", "not", "println", "print", "physical_equal", "Eq",
  "Compare", "Show", "Hash", "Default", "Debug", "ToJson", "FromJson", "Logger", "Hasher", "Add",
  "Sub", "Mul", "Div", "Neg", "Mod", "BitAnd", "BitOr", "BitXOr", "Shl", "Shr", "Iter", "Iter2",
  "ArrayView", "StringView", "BytesView"]

def fstChar (s : String) : Char := s.toList.headD ' '

def sanitizeChars (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Base identifier for a local variable: ASCII, starts with a lowercase letter. -/
def localBase (n : Name) : String :=
  let n := n.eraseMacroScopes
  let s := (sanitizeChars (n.toString.map fun c => if c == '.' then '_' else c)).toList
    |>.filter (fun c => c.toNat < 128) |> String.ofList
  let s := (s.dropWhile (· == '_')).toString
  if s.isEmpty then "x"
  else
    let s := if (fstChar s).isDigit then "x" ++ s else s
    let s := s.decapitalize
    if keywords.contains s then s ++ "_" else s

def nameComponents (c : Name) : List String :=
  let c := (privateToUserName? c).getD c
  c.eraseMacroScopes.components.map fun p => sanitizeChars p.toString

/-- `A`, `B`, .., `Z`, `A1`, .. -/
def tyVarName (k : Nat) : String :=
  let c := Char.ofNat ('A'.toNat + k % 26)
  if k < 26 then c.toString else s!"{c}{k / 26}"

def isTyVarLike (s : String) : Bool :=
  s.length ≥ 1 && (fstChar s).isUpper && (s.drop 1).toString.all Char.isDigit

inductive GKind | fn | ty

def globalName (c : Name) (k : GKind) : M String := do
  if let some n := (← get).globalNames[c]? then return n
  let comps := nameComponents c
  let base := "_".intercalate comps
  let base := match k with | .fn => base.decapitalize | .ty => base.capitalize
  let base := if base.isEmpty then "x" else base
  let base := if (fstChar base).isDigit then "x" ++ base else base
  let st ← get
  let bad := fun (s : String) =>
    keywords.contains s || st.usedGlobals.contains s || st.allLocals.contains s ||
      (k matches .ty && isTyVarLike s)
  let mut cand := base
  let mut i := 1
  while bad cand do
    cand := if i == 1 then base ++ "_" else s!"{base}_{i}"
    i := i + 1
  modify fun s => { s with globalNames := s.globalNames.insert c cand,
                           usedGlobals := s.usedGlobals.insert cand }
  return cand

/-! ## Packages (project mode) -/

/-- Package holding the core library (modules `Init*`, `Std*`, `Lean*`) and the helpers. -/
def corePkg : String := "lean_core"

def isCoreModule (m : Name) : Bool :=
  ["Init", "Std", "Lean", "Lean6x7mbt"].contains m.getRoot.toString

/-- `FooBar` ↦ `foo_bar` -/
def snakeCase (s : String) : String := Id.run do
  let mut out := ""
  let mut prev : Option Char := none
  for c in s.toList do
    if c.isUpper then
      if let some p := prev then
        if p.isLower || p.isDigit then out := out.push '_'
      out := out.push c.toLower
    else out := out.push c
    prev := some c
  return out

/-- Package directory name wanted for the Lean module `m` (`Foo.Bar` ↦ `foo_bar`). -/
def pkgBase (m : Name) : String :=
  let comps := m.components.map fun p => snakeCase (sanitizeChars p.toString)
  let s := "_".intercalate comps
  let s := (s.toList.dropWhile (· == '_') |> String.ofList)
  let s := if s.isEmpty then "pkg" else s
  if (fstChar s).isDigit then "m" ++ s else s

def reservedPkgs : List String := ["core", "builtin", "lean_core", "main", "test", "std"]

def allocPkg (m : Name) : M String := do
  if let some p := (← get).pkgNames[m]? then return p
  let st ← get
  let base := pkgBase m
  let bad := fun (s : String) =>
    keywords.contains s || reservedPkgs.contains s || st.pkgUsed.contains s
  let mut cand := base
  let mut i := 2
  while bad cand do
    cand := s!"{base}_{i}"
    i := i + 1
  modify fun s => { s with pkgNames := s.pkgNames.insert m cand, pkgUsed := s.pkgUsed.insert cand }
  return cand

/-- Package that `c` is extracted into (`""` in single-file mode). -/
def pkgOf (c : Name) : M String := do
  let st ← get
  if !st.project then return ""
  if let some p := st.auxPkg[c]? then return p
  let env ← getEnv
  let m := match env.getModuleIdxFor? c with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  if isCoreModule m then return corePkg
  allocPkg m

/-- `name`, written for use from the current package: `@pkg.name` if `c` lives elsewhere. -/
def qualify (c : Name) (name : String) : M String := do
  if !(← get).project then return name
  let p ← pkgOf c
  return if p == (← get).curPkg then name else s!"@{p}.{name}"

/-- Prefix the identifiers satisfying `isH` (not already qualified) with `pre`. -/
def qualifyIdents (isH : String → Bool) (pre : String) (s : String) : String := Id.run do
  let mut out := ""
  let mut tok := ""
  let mut before := ' '
  let mut last := ' '
  for c in s.toList do
    if c.isAlphanum || c == '_' then
      if tok.isEmpty then before := last
      tok := tok.push c
    else
      if !tok.isEmpty then
        out := out ++ (if isH tok && before != '.' && before != '@' then pre ++ tok else tok)
        tok := ""
      out := out.push c
    last := c
  if !tok.isEmpty then
    out := out ++ (if isH tok && before != '.' && before != '@' then pre ++ tok else tok)
  return out

/-- Helper functions live in `lean_core`: template text outside it must say `@lean_core.helper`. -/
def qualifyHelpers (s : String) : M String := do
  let st ← get
  if !st.project || st.curPkg == corePkg then return s
  return qualifyIdents (st.table.helpers.contains ·) s!"@{corePkg}." s

/-- Name of the constructor `c` inside its (extracted) type, unqualified. -/
def ctorBase (c : Name) : String :=
  let s := (sanitizeChars c.eraseMacroScopes.getString!).capitalize
  let s := if s.isEmpty then "C" else s
  let s := if (fstChar s).isDigit then "C" ++ s else s
  s

def freshLocal (n : Name) : M String := do
  let st ← get
  let base := localBase n
  let mut cand := base
  let mut i := 1
  while st.scope.contains cand || st.usedGlobals.contains cand do
    cand := s!"{base}_{i}"
    i := i + 1
  modify fun s => { s with scope := s.scope.insert cand, allLocals := s.allLocals.insert cand }
  return cand

def withScope (k : M α) : M α := do
  let saved := (← get).scope
  try k finally modify fun s => { s with scope := saved }

def bindLocal (x : Expr) (name : String) : M Unit :=
  modify fun s => { s with locals := s.locals.insert x.fvarId! name }

def bindTyVar (x : Expr) (name : String) : M Unit :=
  modify fun s => { s with tyVars := s.tyVars.insert x.fvarId! name }

/-! ## Classification of binders -/

/-- Does the type former type `bt` end in `Prop` (so its inhabitants are
propositions/predicates, which are erased)? -/
def endsInProp (bt : Expr) : MetaM Bool :=
  forallTelescopeReducing bt fun _ r => do
    match ← whnf r with
    | .sort l => return l.isZero
    | _ => return false

def classify (bt : Expr) (bi : BinderInfo) : MetaM Kind := do
  if ← isTypeFormerType bt then
    return (if ← endsInProp bt then .prf else .ty)
  if ← isProp bt then return .prf
  if bi.isInstImplicit then
    unless (← whnfR bt).getAppFn.isConstOf ``Decidable do return .dict
  return .val

def kindsOfType (type : Expr) : MetaM (Array Kind) :=
  forallTelescopeReducing type fun xs _ => xs.mapM fun x => do
    classify (← inferType x) (← x.fvarId!.getBinderInfo)

/-- Kinds of the arguments `args` of `f args`, using `declared` where known. -/
def kindsOfApp (f : Expr) (args : Array Expr) (declared : Array Kind)
    (fty? : Option Expr := none) : MetaM (Array Kind) := do
  let mut ty ← (match fty? with | some t => pure t | none => inferType f)
  let mut ks := #[]
  for i in [:args.size] do
    ty ← whnf ty
    match ty with
    | .forallE _ d b bi =>
      let k ← if h : i < declared.size then pure declared[i] else classify d bi
      ks := ks.push k
      ty := b.instantiate1 args[i]!
    | _ => throwError "too many arguments in application of {f}"
  return ks

def isErasedExpr (e : Expr) : MetaM Bool := do
  if (← isProof e) then return true
  isTypeFormer e

def etaN (e : Expr) (n : Nat) : MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ => do
    unless xs.size == n do throwError "cannot eta-expand {e}"
    mkLambdaFVars xs (mkAppN e xs)

partial def countFVar (fv : FVarId) : Expr → Nat
  | e => if !e.hasFVar then 0 else match e with
    | .fvar f => if f == fv then 1 else 0
    | .app f a => countFVar fv f + countFVar fv a
    | .lam _ t b _ => countFVar fv t + countFVar fv b
    | .forallE _ t b _ => countFVar fv t + countFVar fv b
    | .letE _ t v b _ => countFVar fv t + countFVar fv v + countFVar fv b
    | .mdata _ b => countFVar fv b
    | .proj _ _ b => countFVar fv b
    | _ => 0

/-- Number of run-time occurrences of the loose bound variable `i` in `e`
(binder types are not counted: they are erased). -/
partial def countBVar (e : Expr) (i : Nat) : Nat :=
  if e.looseBVarRange ≤ i then 0 else match e with
    | .bvar j => if j == i then 1 else 0
    | .app f a => countBVar f i + countBVar a i
    | .lam _ _ b _ => countBVar b (i + 1)
    | .letE _ _ v b _ => countBVar v i + countBVar b (i + 1)
    | .mdata _ b => countBVar b i
    | .proj _ _ b => countBVar b i
    | _ => 0

/-- Arguments that may be copied freely: variables, constants and literals. -/
def isCheapArg (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .const .. | .lit _ | .sort _ => true
  | e => e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appArg!.isRawNatLit

/-- Must the argument `a` (of type `d`) be bound by a `let` instead of being
substituted, when its binder is used several times?  Only plain first-order
values: types, proofs, dictionaries and functions (which includes monadic
actions such as `StateM σ α`) are always substituted, so that instance
projections and higher-kinded wrappers still reduce. -/
def needsSharing (a d : Expr) (bi : BinderInfo) : MetaM Bool := do
  if isCheapArg a then return false
  unless (← classify d bi) == .val do return false
  if (← isClass? d).isSome then return false
  return !(← whnf d).isForall

/-- One β-step of `(fun x => b) a rest`.  If `x` occurs several times in `b`
and `a` is a non-trivial value, the redex becomes `let x := a; b rest`, so
that inlining never duplicates work. -/
def betaShare (f : Expr) (args : Array Expr) : MetaM Expr := do
  let .lam n d b bi := f | return mkAppN f args
  let a := args[0]!
  let rest := args.extract 1 args.size
  if countBVar b 0 > 1 && !d.hasLooseBVars && (← needsSharing a d bi) then
    return .letE n d a (mkAppN b (rest.map (·.liftLooseBVars 0 1))) false
  return mkAppN (b.instantiate1 a) rest

/-- `Meta.unfoldProjInst?` without the final `headBeta`: the instance method
is returned still applied to its arguments, so that `betaShare` decides how
each of them is passed (`max (f x) (g y)` must not evaluate `f x` twice). -/
def unfoldProjInstApp? (e : Expr) : MetaM (Option Expr) := do
  let .const declName _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? declName | return none
  unless info.fromClass do return none
  let some e ← withDefault <| unfoldDefinition? e | return none
  let some r ← withReducibleAndInstances <| reduceProj? e.getAppFn | return none
  return some (mkAppN r e.getAppArgs)

/-! ## Queue / dependencies -/

def enqueue (c : Name) : M Unit := do
  let st ← get
  unless st.seen.contains c do
    set { st with seen := st.seen.insert c, queue := st.queue.push c,
                  origin := match st.cur with
                    | some p => st.origin.insert c p
                    | none => st.origin }

/-- Fail because `c` has no extraction; remembered for the final summary of
missing mappings. -/
def throwMissing (c : Name) (msg : MessageData) : M α := do
  modify fun s => { s with curMissing := some c }
  throwError msg

def noteHelpers (tpl : String) : M Unit := do
  let st ← get
  for h in st.table.helperOrder do
    if (tpl.splitOn h).length > 1 then
      modify fun s => { s with helpers := s.helpers.insert h }

def getTpl? (c : Name) : M (Option String) := do
  let st ← get
  match st.table.consts.find? c with
  | some t => let t := expandMode st.mode t; noteHelpers t; return some (← qualifyHelpers t)
  | none => return none

def getIndMap? (I : Name) : M (Option IndMap) := do
  let st ← get
  match st.table.inds.find? I with
  | some m =>
    let ctors := m.ctors.map (expandMode st.mode)
    let ty := expandMode st.mode m.ty
    -- helpers of the constructor templates are noted where a template is used
    -- (`Array[..]` alone must not pull in `lean_array_of_list`, which needs `List`)
    noteHelpers ty
    return some { ty := ← qualifyHelpers ty, ctors := ← ctors.mapM qualifyHelpers }
  | none => return none

/-- Template of a constructor of a mapped inductive. -/
def getCtorTpl? (c : Name) : M (Option String) := do
  let some (.ctorInfo cv) := (← getEnv).find? c | return none
  match ← getIndMap? cv.induct with
  | some m =>
    let t := m.ctors[cv.cidx]?
    if let some t := t then noteHelpers t
    match t with
    | some t => return some (← qualifyHelpers t)
    | none => return none
  | none => return none

/-- A constructor template used as a *pattern*: a record literal `@pkg.S::{ x: $0 }` of another package is
only valid as an expression, the pattern is `{ x: $0 }` (the scrutinee gives the type). -/
def patTpl (t : String) : String :=
  match t.splitOn "::{" with
  | [_, rest] => "{" ++ rest
  | _ => t

def natLit (n : Nat) : M String := do
  return toString n ++ (← get).mode.litSuffix

def strLit (s : String) : String :=
  let esc := s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else if c == '\t' then acc ++ "\\t"
    else if c == '\r' then acc ++ "\\r"
    else if c.toNat < 32 || c.toNat == 127 then acc ++ "\\u{" ++ (Nat.toDigits 16 c.toNat |> String.ofList) ++ "}"
    else acc.push c
  "\"" ++ esc ++ "\""

/-! ## Signatures -/

/-- Body used by the code generator: the `_unsafe_rec` version if present. -/
def getBodyInfo? (c : Name) : MetaM (Option (List Name × Expr)) := do
  let env ← getEnv
  match env.find? (Compiler.mkUnsafeRecName c) with
  | some ci => return ci.value?.map (ci.levelParams, ·)
  | none =>
    -- The value of an `opaque` constant is only an inhabitation witness
    -- (`@[extern] opaque String.Internal.append` is "defined" as `default`):
    -- it is never a definition we may extract.
    match env.find? c with
    | some ci => return ci.value?.map (ci.levelParams, ·)
    | none => return none

def getBody? (c : Name) : M (Option Expr) := do
  if let some (v, _) := (← get).aux[c]? then return some v
  return (← getBodyInfo? c).map (·.2)

/-- Does the type of a definition have a higher-kinded type parameter
(`m : Type → Type`)? Such functions cannot be generic in MoonBit and are
inlined at their call sites. -/
def hasHKBinder (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs _ => do
    for x in xs do
      let bt ← inferType x
      if (← isTypeFormerType bt) && (← whnf bt).isForall && !(← endsInProp bt) then return true
    return false

def lamCount : Expr → Nat
  | .lam _ _ b _ => 1 + lamCount b
  | .mdata _ b => lamCount b
  | _ => 0

def sigOf (c : Name) : M Sig := do
  if let some s := (← get).sigs[c]? then return s
  if let some (v, ty) := (← get).aux[c]? then
    let kinds ← kindsOfType ty
    let s := { kinds, arity := min (lamCount v) kinds.size : Sig }
    modify fun st => { st with sigs := st.sigs.insert c s }
    return s
  let some ci := (← getEnv).find? c | throwError "unknown constant {c}"
  let kinds ← kindsOfType ci.type
  let arity ← match ci with
    | .ctorInfo _ => pure kinds.size
    | .recInfo _ => pure kinds.size
    | _ =>
      match ← getBody? c with
      | some v => pure (min (lamCount v) kinds.size)
      | none => pure kinds.size
  let s := { kinds, arity : Sig }
  modify fun st => { st with sigs := st.sigs.insert c s }
  return s

/-- Is the call of `c` with this signature a function call (as opposed to a constant)? -/
def Sig.isFn (s : Sig) : Bool :=
  (s.kinds.extract 0 s.arity).any fun k => k != .prf

/-- Shape of an inductive type as printed in MoonBit. -/
def shapeOf (I : Name) : M Shape := do
  if let some s := (← get).shapes[I]? then return s
  let env ← getEnv
  let ind ← getConstInfoInduct I
  let shape ← match ind.ctors with
    | [c] =>
      if isStructure env I then
        let cv ← getConstInfoCtor c
        let kinds ← kindsOfType cv.type
        let fields := getStructureFields env I
        let kept := Id.run do
          let mut out := #[]
          for i in [:fields.size] do
            if kinds[ind.numParams + i]?.any Kind.kept then out := out.push fields[i]!
          return out
        pure (if kept.isEmpty then Shape.enum else Shape.struct kept)
      else pure Shape.enum
    | _ => pure Shape.enum
  modify fun s => { s with shapes := s.shapes.insert I shape }
  return shape

def fieldName (f : Name) : String :=
  let s := localBase f
  s

/-! ## Types -/

def curryTy (args : Array MTy) (r : MTy) : MTy :=
  args.foldr (fun a r => .fn #[a] r) r

partial def tyOf (t : Expr) : M MTy := do
  let t ← instantiateMVars t
  let t := t.consumeMData
  if ← isProp t then return .tuple #[]
  match t with
  | .fvar id =>
    match (← get).tyVars[id]? with
    | some n => return .var n
    | none =>
      if let some v ← id.getValue? then return ← tyOf v
      throwError "type variable {t} is not in scope"
  | .forallE .. =>
    forallTelescope t fun xs body => do
      let mut args := #[]
      for x in xs do
        let d ← inferType x
        match ← classify d (← x.fvarId!.getBinderInfo) with
        | .ty => throwError "higher-rank polymorphic type {t} cannot be expressed in MoonBit"
        | .prf => pure ()
        | _ => args := args.push (← tyOf d)
      return curryTy args (← tyOf body)
  | .sort .. => throwError "unexpected sort"
  | _ =>
    match t.getAppFn with
    | .const c _ => tyConst c t.getAppArgs t
    | _ =>
      let t' ← whnfCore t
      if t' != t then tyOf t' else throwError "unsupported type {t}"
where
  tyConst (c : Name) (args : Array Expr) (t : Expr) : M MTy := do
    let env ← getEnv
    let tyArgs (type : Expr) : M (Array MTy) := do
      let kinds ← kindsOfType type
      let mut out := #[]
      for i in [:args.size] do
        if kinds[i]? == some .ty then out := out.push (← tyOf args[i]!)
      return out
    if let some m ← getIndMap? c then
      let ci ← getConstInfo c
      let tas ← if tplArity m.ty == 0 then pure #[] else tyArgs ci.type
      return .raw (substTpl m.ty (tas.map MTy.render))
    match env.find? c with
    | some (.inductInfo _) =>
      let ci ← getConstInfo c
      if args.size < (← kindsOfType ci.type).size then
        throwError "partially applied type constructor {t} (higher-kinded types are not supported)"
      enqueue c
      let name ← qualify c (← globalName c .ty)
      return .con name (← tyArgs ci.type)
    | some (.defnInfo _) =>
      match ← unfoldDefinition? t with
      | some t' => tyOf t'
      | none => throwError "cannot unfold type {t}"
    | _ => throwError "unsupported type {t}"

/-! ## Terms -/

def isAtomic : MExp → Bool
  | .var _ | .lit _ | .unit => true
  | _ => false

/-- `if` with the trivial simplification `(b == true)` ↦ `b`. -/
def mkIte (c t f : MExp) : MExp :=
  match c with
  | .tpl "($0 == $1)" #[a, .lit "true"] => .ite a t f
  | .tpl "($0 == $1)" #[a, .lit "false"] => .ite a f t
  | .tpl "($0 == $1)" #[a, .tpl "true" #[]] => .ite a t f
  | .tpl "($0 == $1)" #[a, .tpl "false" #[]] => .ite a f t
  | _ => .ite c t f

/-- Names of cast-like constants and the index of the value they return. -/
def castLike : List (Name × Nat) :=
  [(``Eq.mpr, 3), (``Eq.mp, 3), (``cast, 3), (``Eq.rec, 3), (``Eq.ndrec, 3), (``Eq.recOn, 5),
   (``Eq.casesOn, 5), (``Eq.ndrec_symm, 3), (``HEq.rec, 3), (``HEq.ndrec, 3), (``Quot.mk, 2)]

def abortLike : List Name :=
  [``False.elim, ``absurd, ``False.rec, ``False.casesOn, ``Empty.rec, ``Empty.casesOn,
   ``PEmpty.rec, ``PEmpty.casesOn, ``lcUnreachable]

/-- Apply the template `tpl` to already translated arguments (binding repeated ones). -/
def mkTpl (tpl : String) (args : Array MExp) : M MExp := do
  let mut args := args
  let mut binds : Array (String × MExp) := #[]
  for k in [:args.size] do
    if tplCount tpl k > 1 && !isAtomic args[k]! then
      let n ← freshLocal `t
      binds := binds.push (n, args[k]!)
      args := args.set! k (.var n)
  let mut r := MExp.tpl tpl args
  for (n, v) in binds.reverse do
    r := .let_ n v r
  return r

/-- Build the specialized body: instantiate the binders flagged in `S` with
`specArgs` and keep the others as parameters. -/
partial def buildSpec (e : Expr) (i n : Nat) (S : Array Bool) (specArgs : Array Expr) (j : Nat)
    (fvars : Array Expr) : MetaM Expr := do
  if i == n then
    -- η-expand along the (unfolded) result type: a loop in `StateM σ` gets the
    -- state as a parameter, so that its recursive call is a saturated tail call
    -- instead of the application of a returned closure
    let ty ← inferType e
    return ← forallTelescopeReducing ty fun xs _ =>
      mkLambdaFVars (fvars ++ xs) (mkAppN e xs).headBeta
  match e with
  | .mdata _ b => buildSpec b i n S specArgs j fvars
  | .lam nm d b bi =>
    if S[i]! then buildSpec (b.instantiate1 specArgs[j]!) (i + 1) n S specArgs (j + 1) fvars
    else withLocalDecl nm bi d fun x => buildSpec (b.instantiate1 x) (i + 1) n S specArgs j (fvars.push x)
  | _ => throwError "unexpected body while specializing"

/-- Specialize the recursive higher-kinded function `c` to the concrete
arguments of this call (the higher-kinded type parameters and the
dictionaries that mention them). Returns the synthetic constant and the
arguments for it: the free type variables of the key, then the remaining
arguments. -/
def specialize (c : Name) (us : List Level) (lps : List Name) (body : Expr)
    (args : Array Expr) (n : Nat) : M (Name × Array Expr) := do
  let val := body.instantiateLevelParams lps us
  let S ← lambdaBoundedTelescope val n fun xs _ => do
    unless xs.size == n do throwError "arity mismatch while specializing {c}"
    let mut hk : Array FVarId := #[]
    let mut S : Array Bool := #[]
    for x in xs do
      let bt ← inferType x
      let isHK := (← isTypeFormerType bt) && (← whnf bt).isForall && !(← endsInProp bt)
      let k ← classify bt (← x.fvarId!.getBinderInfo)
      let dep := k == .dict && bt.hasAnyFVar (hk.contains ·)
      if isHK then hk := hk.push x.fvarId!
      S := S.push (isHK || dep)
    return S
  let mut specArgs : Array Expr := #[]
  let mut rest : Array Expr := #[]
  for i in [:n] do
    if S[i]! then specArgs := specArgs.push (← instantiateMVars args[i]!)
    else rest := rest.push args[i]!
  -- free type variables of the specialization arguments become extra parameters
  let st := collectFVars {} (mkAppN (.const c us) specArgs)
  let lctx ← getLCtx
  let ids := st.fvarIds.qsort fun a b =>
    (lctx.find? a |>.map (·.index) |>.getD 0) < (lctx.find? b |>.map (·.index) |>.getD 0)
  let free := ids.map Expr.fvar
  for fv in free do
    unless (← get).tyVars.contains fv.fvarId! do
      throwError "cannot specialize `{c}`: the instance arguments depend on the local value {fv}"
  let key ← mkLambdaFVars free (mkAppN (.const c us) specArgs)
  -- keyed by package too: every package gets its own copy (a core function's copy must not
  -- live in a user package that the core package would then have to import)
  let skey := ((← get).curPkg, key)
  if let some name := (← get).specs[skey]? then
    return (name, free ++ rest)
  let value ← mkLambdaFVars free (← buildSpec val 0 n S specArgs 0 #[])
  let ty ← inferType value
  let k := (← get).specs.size + 1
  let name := Name.str c s!"spec{k}"
  modify fun st => { st with specs := st.specs.insert skey name,
                             aux := st.aux.insert name (value, ty),
                             auxPkg := st.auxPkg.insert name st.curPkg }
  return (name, free ++ rest)

mutual

partial def tr (e : Expr) : M MExp := do
  match e with
  | .mdata _ b => tr b
  | .lit (.natVal n) => return .lit (← natLit n)
  | .lit (.strVal s) => return .lit (strLit s)
  | .sort .. | .forallE .. => return .unit
  | .bvar .. | .mvar .. => throwError "unexpected term {e}"
  | _ =>
    if ← isErasedExpr e then return .unit
    match e with
    | .fvar id =>
      match (← get).locals[id]? with
      | some n => return .var n
      | none => throwError "unbound local variable {e}"
    | .lam .. => trLam e
    | .letE .. => trLet e
    | .proj S i s => trProj S i s #[]
    | .const .. | .app .. => trApp e
    | _ => throwError "unexpected term {e}"

partial def applyClosure (h : MExp) (args : Array Expr) (kinds : Array Kind) : M MExp := do
  let mut h := h
  for i in [:args.size] do
    if kinds[i]!.kept then h := .app h #[← tr args[i]!]
  return h

partial def trApp (e : Expr) : M MExp := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isConst then
    if let some e' ← unfoldProjInstApp? e then return ← tr e'
  match f with
  | .const c us =>
    let c' := (Compiler.isUnsafeRecName? c).getD c
    trConstApp c' us args e
  | .lam .. => tr (← betaShare f args)
  | .mdata _ b => tr (mkAppN b args)
  | .fvar _ =>
    let h ← tr f
    applyClosure h args (← kindsOfApp f args #[])
  | _ =>
    let h ← tr f
    applyClosure h args (← kindsOfApp f args #[])

partial def trConstApp (c : Name) (us : List Level) (args : Array Expr) (e : Expr) : M MExp := do
  let env ← getEnv
  let f := Expr.const c us
  -- user-mapped constants and constructors first
  if let some tpl ← getTpl? c then return ← trMapped c f tpl args e
  if let some tpl ← getCtorTpl? c then return ← trMapped c f tpl args e
  -- special constants
  if c == ``ite || c == ``dite then
    if args.size < 5 then return ← tr (← etaN e (5 - args.size))
    let cond ← tr args[2]!
    let t ← if c == ``ite then tr args[3]! else trApplyProof args[3]!
    let f' ← if c == ``ite then tr args[4]! else trApplyProof args[4]!
    return ← trExtra (mkIte cond t f') f args 5
  if c == ``Lean.Loop.forIn then
    -- `while`/`repeat`: the core loop body is a private `partial` (opaque), so
    -- redirect to the public equivalent `Lean6x7mbt.loopForIn β m inst f init`
    if args.size < 6 then return ← tr (← etaN e (6 - args.size))
    let e' := mkAppN (.const ``Lean6x7mbt.loopForIn us)
      (#[args[0]!, args[1]!, args[2]!, args[5]!, args[4]!] ++ args.extract 6 args.size)
    return ← tr e'
  if c == ``cond then
    if args.size < 4 then return ← tr (← etaN e (4 - args.size))
    return ← trExtra (mkIte (← tr args[1]!) (← tr args[2]!) (← tr args[3]!)) f args 4
  if c == ``Decidable.decide then
    if args.size < 2 then return ← tr (← etaN e (2 - args.size))
    return ← trExtra (← tr args[1]!) f args 2
  if c == ``Quot.lift then
    if args.size < 6 then return ← tr (← etaN e (6 - args.size))
    let h ← tr args[3]!
    return ← trExtra (.app h #[← tr args[5]!]) f args 6
  if let some (_, idx) := castLike.find? (·.1 == c) then
    -- the cast's own binders (indices, proofs) come after the value and are dropped
    let nb := (← kindsOfType (← getConstInfo c).type).size
    let need := max (idx + 1) nb
    if args.size < need then return ← tr (← etaN e (need - args.size))
    return ← trExtra (← tr args[idx]!) f args need
  if abortLike.contains c then return .abort (strLit s!"unreachable ({c})")
  if c == ``lcProof then return .unit
  if isCasesOnRecursor env c then return ← trCases c args e
  if let some info := getSparseCasesOnInfoCore env c then return ← trSparse c info args e
  if let some info ← getMatcherInfo? c then return ← trMatcher c us info args e
  if isRecCore env c then
    throwError "the recursor {c} cannot be extracted; use structural or well-founded recursion with pattern matching"
  if isNoConfusion env c then return .abort (strLit "noConfusion")
  match env.find? c with
  | some (.ctorInfo cv) => trCtor cv f args e
  | some ci =>
    if let some pinfo ← getProjectionFnInfo? c then
      let n := pinfo.numParams + 1
      if args.size < n then return ← tr (← etaN e (n - args.size))
      let some (.ctorInfo pcv) := env.find? pinfo.ctorName | throwError "bad projection {c}"
      return ← trProjCore pcv.induct pinfo.i args[pinfo.numParams]! (args.extract n args.size) (some c) (some (f, args))
    trGlobal c f args e ci
  | none => throwError "unknown constant {c}"

/-- Apply the closure result to remaining arguments (`args[from_:]`). -/
partial def trExtra (h : MExp) (f : Expr) (args : Array Expr) (from_ : Nat)
    (fty? : Option Expr := none) : M MExp := do
  if args.size ≤ from_ then return h
  let ks ← kindsOfApp f args #[] fty?
  let mut h := h
  for i in [from_:args.size] do
    if ks[i]!.kept then h := .app h #[← tr args[i]!]
  return h

partial def trApplyProof (t : Expr) : M MExp := do
  let ty ← whnf (← inferType t)
  match ty with
  | .forallE n d _ _ =>
    withLocalDecl n .default d fun h => tr (mkApp t h).headBeta
  | _ => throwError "expected a function: {t}"

partial def trMapped (c : Name) (f : Expr) (tpl : String) (args : Array Expr) (e : Expr) : M MExp := do
  let ci ← getConstInfo c
  let kinds ← kindsOfType ci.type
  -- A template stands for the constant applied to all its declared arguments,
  -- whether or not it mentions them (`Array.mkEmpty c` ↦ `[]`); only when it
  -- has more placeholders than there are value arguments is it left as is.
  let need := kinds.size
  if args.size < need then return ← tr (← etaN e (need - args.size))
  let ks ← kindsOfApp f (args.extract 0 need) kinds
  let mut kept := #[]
  for i in [:need] do
    if ks[i]! == .val then kept := kept.push (← tr args[i]!)
  let head ← mkTpl tpl kept
  trExtra head f args need

partial def trGlobal (c : Name) (f : Expr) (args : Array Expr) (e : Expr) (ci : ConstantInfo) : M MExp := do
  let some (lps, body) ← getBodyInfo? c
    | throwMissing c m!"no extraction for `{c}`: it has no definition (axiom, `opaque` or `extern` constant)"
  let sig ← sigOf c
  if (← hasHKBinder ci.type) then
    let recursive := (body.find? fun x => x.isConst && (x.constName! == c ||
      x.constName! == Compiler.mkUnsafeRecName c)).isSome
    if !recursive then
      -- small wrappers (`bind`, `throw`, ...) are simply inlined
      let val := body.instantiateLevelParams lps f.constLevels!
      return ← tr (mkAppN val args)
    -- recursive: generate a copy specialized to the concrete monad
    if args.size < sig.arity then return ← tr (← etaN e (sig.arity - args.size))
    let (sc, newArgs) ← specialize c f.constLevels! lps body args sig.arity
    let sigS ← sigOf sc
    let (_, ty) := (← get).aux[sc]!
    let allArgs := newArgs ++ args.extract sig.arity args.size
    if allArgs.size < sigS.arity then
      -- the copy takes more parameters than the call supplies (η-expanded result)
      return ← trSpecEta sc allArgs sigS ty
    return ← trCall sc (.const sc []) allArgs sigS (some ty)
  if args.size < sig.arity then return ← tr (← etaN e (sig.arity - args.size))
  -- Saturated calls of non-recursive `@[inline]` functions are inlined, as the
  -- Lean compiler does.  Besides giving shorter code this is what makes monadic
  -- loops tail recursive: once `Except.bind`/`StateT.bind` is a `match`, the
  -- recursive call of the loop is no longer inside a continuation closure.
  if sig.isFn && (← inlinable c body) then
    let val := body.instantiateLevelParams lps f.constLevels!
    return ← tr (mkAppN val args)
  trCall c f args sig none

/-- May calls of `c` (with definition `body`) be inlined? -/
partial def inlinable (c : Name) (body : Expr) : M Bool := do
  let env ← getEnv
  unless Compiler.hasInlineAttribute env c || Compiler.hasAlwaysInlineAttribute env c ||
      Compiler.hasMacroInlineAttribute env c do return false
  if isInstanceCore env c then return false
  if (env.find? (Compiler.mkUnsafeRecName c)).isSome then return false
  return (body.find? fun x => x.isConstOf c).isNone

/-- Under-applied call of the specialized copy `sc`: `fun xs => sc args xs`. -/
partial def trSpecEta (sc : Name) (args : Array Expr) (sig : Sig) (ty : Expr) : M MExp := do
  let rest ← instantiateForall ty args
  withScope do
    forallBoundedTelescope rest (some (sig.arity - args.size)) fun xs _ => do
      let mut params : Array (String × Option MTy) := #[]
      for x in xs do
        let d ← inferType x
        match ← classify d (← x.fvarId!.getBinderInfo) with
        | .ty | .prf => pure ()
        | _ =>
          let n ← freshLocal (← x.fvarId!.getUserName)
          bindLocal x n
          let t ← try some <$> tyOf d catch _ => pure none
          params := params.push (n, t)
      let b ← trCall sc (.const sc []) (args ++ xs) sig (some ty)
      return params.foldr (fun p b => MExp.lam #[p] b) b

/-- Call of the global function `c` (whose signature is `sig`) with enough arguments. -/
partial def trCall (c : Name) (f : Expr) (args : Array Expr) (sig : Sig) (fty? : Option Expr) : M MExp := do
  enqueue c
  let name ← qualify c (← globalName c .fn)
  let ks ← kindsOfApp f (args.extract 0 sig.arity) sig.kinds fty?
  let mut kept := #[]
  for i in [:sig.arity] do
    if ks[i]!.kept then kept := kept.push (← tr args[i]!)
  let head := if sig.isFn then MExp.app (.var name) kept else MExp.var name
  trExtra head f args sig.arity fty?

partial def trCtor (cv : ConstructorVal) (f : Expr) (args : Array Expr) (e : Expr) : M MExp := do
  let sig ← sigOf cv.name
  if args.size < sig.arity then return ← tr (← etaN e (sig.arity - args.size))
  let ks ← kindsOfApp f (args.extract 0 sig.arity) sig.kinds
  let mut kept : Array MExp := #[]
  for i in [cv.numParams:sig.arity] do
    if ks[i]!.kept then kept := kept.push (← tr args[i]!)
  enqueue cv.induct
  let tyName ← qualify cv.induct (← globalName cv.induct .ty)
  let head ← match ← shapeOf cv.induct with
    | .struct fields =>
      pure (MExp.structLit tyName ((fields.map fieldName).zip kept))
    | .enum => pure (MExp.ctor (tyName ++ "::" ++ ctorBase cv.name) kept)
  trExtra head f args sig.arity

partial def trProj (S : Name) (i : Nat) (s : Expr) (extra : Array Expr) : M MExp := do
  trProjCore S i s extra none none

partial def trProjCore (S : Name) (i : Nat) (s : Expr) (extra : Array Expr)
    (fn? : Option Name) (app? : Option (Expr × Array Expr)) : M MExp := do
  let env ← getEnv
  let fields := getStructureFields env S
  let some fname := fields[i]? | throwError "bad projection {S}.{i}"
  let projFn := S ++ fname
  if let some tpl ← getTpl? projFn then
    let head ← mkTpl tpl #[← tr s]
    return ← extraApply head extra projFn
  if (← getIndMap? S).isSome then
    throwMissing projFn m!"projection `{projFn}` of the mapped type `{S}` has no extraction"
  enqueue S
  match ← shapeOf S with
  | .struct kept =>
    unless kept.contains fname do throwError "projection of erased field {projFn}"
    let h := MExp.field (← tr s) (fieldName fname)
    extraApply h extra projFn
  | .enum => throwError "projection {projFn} of a structure without runtime fields"
where
  extraApply (h : MExp) (extra : Array Expr) (projFn : Name) : M MExp := do
    if extra.isEmpty then return h
    let some (f, args) := app? | throwError "unexpected extra arguments to projection"
    let n := args.size - extra.size
    let ks ← kindsOfApp f args #[]
    let mut h := h
    for j in [n:args.size] do
      if ks[j]!.kept then h := .app h #[← tr args[j]!]
    return h

partial def trLam (e : Expr) : M MExp := do
  withScope do
    lambdaTelescope e fun xs body => do
      let mut params : Array (String × Option MTy) := #[]
      for x in xs do
        let d ← inferType x
        let bi ← x.fvarId!.getBinderInfo
        match ← classify d bi with
        | .ty | .prf => pure ()
        | _ =>
          let n ← freshLocal (← x.fvarId!.getUserName)
          bindLocal x n
          let t ← try some <$> tyOf d catch _ => pure none
          params := params.push (n, t)
      let b ← tr body
      -- one closure per value binder
      return params.foldr (fun p b =>
        MExp.lam #[(if b.mentions p.1 then p.1 else "_", p.2)] b) b

partial def trLet (e : Expr) : M MExp := do
  let .letE n t v b _ := e | unreachable!
  if (← isTypeFormerType t) || (← isProp t) then
    return ← tr (b.instantiate1 v)
  let vm ← tr v
  withLetDecl n t v fun x => withScope do
    let name ← freshLocal n
    bindLocal x name
    let bm ← tr (b.instantiate1 x)
    return .let_ name vm bm

/-- Open `n` field binders of a `casesOn` minor premise. Returns for each
field `some name` if it is a runtime field, and the translated body. -/
partial def trMinor (minor : Expr) (n : Nat) (extra : Array Expr) : M (Array (Option String) × MExp) := do
  let minor ← if lamCount minor ≥ n then pure minor else etaN minor n
  withScope do
    lambdaBoundedTelescope minor n fun xs body => do
      let mut names : Array (Option String) := #[]
      for x in xs do
        let d ← inferType x
        match ← classify d (← x.fvarId!.getBinderInfo) with
        | .ty => throwError "constructor field of type `{d}` (existential type) cannot be extracted"
        | .prf => names := names.push none
        | _ =>
          let nm ← freshLocal (← x.fvarId!.getUserName)
          bindLocal x nm
          names := names.push (some nm)
      let body := (mkAppN body extra).headBeta
      let bm ← tr body
      return (names.map fun o => o.bind fun nm => if bm.mentions nm then some nm else none, bm)

partial def trCases (c : Name) (args : Array Expr) (e : Expr) : M MExp := do
  let I := c.getPrefix
  let ind ← getConstInfoInduct I
  let np := ind.numParams
  let ni := ind.numIndices
  let nc := ind.ctors.length
  let mi := np + 1 + ni
  if args.size < mi + 1 + nc then return ← tr (← etaN e (mi + 1 + nc - args.size))
  let major := args[mi]!
  let minors := (args.extract (mi + 1) (mi + 1 + nc)).map some
  let extra := args.extract (mi + 1 + nc) args.size
  trCasesCore I ind major minors none extra

/-- `casesOn` with only some constructors and a catch-all. -/
partial def trSparse (c : Name) (info : SparseCasesOnInfo) (args : Array Expr) (e : Expr) : M MExp := do
  if args.size < info.arity then return ← tr (← etaN e (info.arity - args.size))
  let ind ← getConstInfoInduct info.indName
  let major := args[info.majorPos]!
  let nint := info.insterestingCtors.size
  let mut minors : Array (Option Expr) := Array.replicate ind.ctors.length none
  for j in [:nint] do
    let cv ← getConstInfoCtor info.insterestingCtors[j]!
    minors := minors.set! cv.cidx (some args[info.majorPos + 1 + j]!)
  let dflt := args[info.majorPos + 1 + nint]!
  let extra := args.extract info.arity args.size
  trCasesCore info.indName ind major minors (some dflt) extra

partial def trCasesCore (I : Name) (ind : InductiveVal) (major : Expr)
    (minors : Array (Option Expr)) (dflt : Option Expr) (extra : Array Expr) : M MExp := do
  let nc := ind.ctors.length
  let np := ind.numParams
  let fieldsOf (k : Nat) : M Nat := do
    let cv ← getConstInfoCtor ind.ctors[k]!
    return cv.numFields
  -- branch k: fields' names and body
  let branch (k : Nat) : M (Array (Option String) × MExp) := do
    match minors[k]! with
    | some m => trMinor m (← fieldsOf k) extra
    | none =>
      let some d := dflt | throwError "missing alternative in casesOn"
      let ty ← whnf (← inferType d)
      let b ← match ty with
        | .forallE n dd _ _ =>
          withLocalDecl n .default dd fun h => tr (mkAppN (mkApp d h) extra).headBeta
        | _ => tr (mkAppN d extra).headBeta
      return (Array.replicate (← fieldsOf k) none, b)
  -- inductive predicates eliminating into Type: Eq, And, False, ...
  if ← isPropFormerType ind.type then
    if nc == 0 then return .abort (strLit s!"unreachable ({I})")
    let (_, b) ← branch 0
    return b
  if I == ``Nat || I == ``Int || I == ``Bool || I == ``Decidable then
    let s ← tr major
    let (v, wrap) ← bindAtom s
    let r ← match I with
      | ``Bool => do
        let (_, f) ← branch 0
        let (_, t) ← branch 1
        pure (mkIte v t f)
      | ``Decidable => do
        let (_, f) ← branch 0
        let (_, t) ← branch 1
        pure (mkIte v t f)
      | ``Nat => do
        let (_, z) ← branch 0
        let (ns, sc) ← branch 1
        let zero ← natLit 0
        let one ← natLit 1
        let sc := match ns[0]! with
          | some n => MExp.let_ n (.tpl s!"$0 - {one}" #[v]) sc
          | none => sc
        pure (mkIte (.tpl s!"$0 == {zero}" #[v]) z sc)
      | _ => do
        let (ns1, p) ← branch 0
        let (ns2, q) ← branch 1
        let zero ← natLit 0
        let one ← natLit 1
        let p := match ns1[0]! with
          | some n => MExp.let_ n v p
          | none => p
        let q := match ns2[0]! with
          | some n => MExp.let_ n (.tpl s!"-$0 - {one}" #[v]) q
          | none => q
        pure (mkIte (.tpl s!"$0 >= {zero}" #[v]) p q)
    return wrap r
  let s ← tr major
  if let some m ← getIndMap? I then
    let mut arms := #[]
    for k in [:nc] do
      let (names, b) ← branch k
      let pats ← keptPats ind.ctors[k]! names
      noteHelpers m.ctors[k]!
      arms := arms.push (Pat.raw (substTpl (patTpl m.ctors[k]!) (pats.map Pat.render)), b)
    return .match_ s arms
  enqueue I
  match ← shapeOf I with
  | .struct _ =>
    let (names, b) ← branch 0
    let cv ← getConstInfoCtor ind.ctors[0]!
    let kinds ← kindsOfType cv.type
    let (v, wrap) ← bindAtom s
    let all := getStructureFields (← getEnv) I
    let mut body := b
    let mut lets : Array (String × String) := #[]
    for i in [:all.size] do
      if kinds[np + i]?.any Kind.kept then
        if let some (some n) := names[i]? then lets := lets.push (n, fieldName all[i]!)
    for (n, fld) in lets.reverse do
      body := .let_ n (.field v fld) body
    return wrap body
  | .enum =>
    let tyName ← qualify I (← globalName I .ty)
    let mut arms := #[]
    let mut needDflt := false
    for k in [:nc] do
      if minors[k]!.isSome then
        let (names, b) ← branch k
        let pats ← keptPats ind.ctors[k]! names
        arms := arms.push (Pat.ctor (tyName ++ "::" ++ ctorBase ind.ctors[k]!) pats, b)
      else needDflt := true
    if needDflt then
      let some k := (List.range nc).find? (minors[·]!.isNone) | unreachable!
      let (_, b) ← branch k
      arms := arms.push (Pat.wild, b)
    return .match_ s arms
where
  /-- bind a non-atomic scrutinee to a variable -/
  bindAtom (s : MExp) : M (MExp × (MExp → MExp)) := do
    if isAtomic s then return (s, id)
    let n ← freshLocal `s
    return (.var n, fun b => .let_ n s b)
  /-- patterns for the kept fields of constructor `ctor`; `names[i] = none`
  means erased or unused -/
  keptPats (ctor : Name) (names : Array (Option String)) : M (Array Pat) := do
    let cv ← getConstInfoCtor ctor
    let kinds ← kindsOfType cv.type
    let mut out := #[]
    for i in [:cv.numFields] do
      if kinds[cv.numParams + i]?.any Kind.kept then
        out := out.push (match names[i]? with
          | some (some n) => Pat.var n
          | _ => Pat.wild)
    return out

partial def trMatcher (c : Name) (us : List Level) (info : Match.MatcherInfo) (args : Array Expr) (e : Expr) : M MExp := do
  if args.size < info.arity then return ← tr (← etaN e (info.arity - args.size))
  let first := info.getFirstAltPos
  let nalts := info.numAlts
  let ci ← getConstInfo c
  let val ← instantiateValueLevelParams ci us
  -- a non-trivial discriminant that the matcher inspects several times is bound first
  let fd := info.getFirstDiscrPos
  let mut b := val.beta (args.extract 0 fd)
  for i in [fd:fd + info.numDiscrs] do
    let .lam _ _ b' bi := b | break
    if countBVar b' 0 > 1 then
      let ty ← inferType args[i]!
      if ← needsSharing args[i]! ty bi then
        return ← tr (.letE `x ty args[i]! (mkAppN (.const c us) (args.set! i (.bvar 0))) false)
    b := b'.instantiate1 args[i]!
  let rest := val.beta (args.extract 0 first)
  let alts := args.extract first (first + nalts)
  let extra := args.extract info.arity args.size
  lambdaBoundedTelescope rest nalts fun altFVars body => do
    unless altFVars.size == nalts do throwError "unexpected matcher {c}"
    -- alternatives used more than once become local closures
    let rec go (i : Nat) (repl : Array Expr) : M MExp := do
      if h : i < nalts then
        let fv := altFVars[i]!
        if countFVar fv.fvarId! body ≤ 1 then
          go (i + 1) (repl.push alts[i]!)
        else
          let vm ← tr alts[i]!
          let ty ← inferType alts[i]!
          withLetDecl (← mkFreshUserName `alt) ty alts[i]! fun x => withScope do
            let name ← freshLocal `alt
            bindLocal x name
            let r ← go (i + 1) (repl.push x)
            return .let_ name vm r
      else
        tr (mkAppN (body.replaceFVars altFVars repl) extra)
    go 0 #[]

end

/-! ## Declarations -/

def resetDecl : M Unit :=
  modify fun s => { s with locals := {}, scope := {}, tyVars := {} }

/-- Open the leading binders of `value` that form the parameters of the
extracted function and run `k`. -/
def emitFn (c : Name) : M Unit := do
  resetDecl
  let some body ← getBody? c | throwError "no definition for {c}"
  let sig ← sigOf c
  let name ← globalName c .fn
  let decl ← lambdaBoundedTelescope body sig.arity fun xs b => do
    unless xs.size == sig.arity do throwError "arity mismatch for {c}"
    let mut tparams : Array String := #[]
    let mut params : Array (String × MTy) := #[]
    let mut k := 0
    for x in xs do
      let d ← inferType x
      match ← classify d (← x.fvarId!.getBinderInfo) with
      | .ty =>
        let n := tyVarName k
        k := k + 1
        bindTyVar x n
        tparams := tparams.push n
      | .prf => pure ()
      | _ =>
        let n ← freshLocal (← x.fvarId!.getUserName)
        bindLocal x n
        params := params.push (n, ← tyOf d)
    let ret ← tyOf (← inferType b)
    let bm ← tr b
    if sig.isFn then
      pure (MDecl.fn name tparams params ret bm)
    else
      pure (MDecl.const name ret bm)
  modify fun s => { s with fns := s.fns.push (s.curPkg, decl) }

def emitInductive (I : Name) : M Unit := do
  resetDecl
  let ind ← getConstInfoInduct I
  let name ← globalName I .ty
  let np := ind.numParams
  -- type parameters
  let tparams ← forallBoundedTelescope ind.type (some np) fun xs _ => do
    let mut out := #[]
    let mut k := 0
    for x in xs do
      match ← classify (← inferType x) (← x.fvarId!.getBinderInfo) with
      | .ty => out := out.push (tyVarName k); k := k + 1
      | _ => pure ()
    return out
  let shape ← shapeOf I
  let mut ctors : Array (String × Array MTy) := #[]
  let mut sfields : Array (String × MTy) := #[]
  for cn in ind.ctors do
    let cv ← getConstInfoCtor cn
    let (fields : Array (Name × MTy)) ← forallBoundedTelescope cv.type (some np) fun ps rest => do
      let mut k := 0
      for p in ps do
        match ← classify (← inferType p) (← p.fvarId!.getBinderInfo) with
        | .ty => bindTyVar p (tyVarName k); k := k + 1
        | _ => pure ()
      forallTelescope rest fun fs _ => do
        let mut out := #[]
        for f in fs do
          let d ← inferType f
          match ← classify d (← f.fvarId!.getBinderInfo) with
          | .ty => throwError "constructor {cn} has a type field (existential type), which MoonBit cannot express"
          | .prf => pure ()
          | _ => out := out.push ((← f.fvarId!.getUserName), ← tyOf d)
        return out
    match shape with
    | .struct _ => sfields := fields.map fun (n, t) => (fieldName n, t)
    | .enum => ctors := ctors.push (ctorBase cn, fields.map (·.2))
  let decl := match shape with
    | .struct _ => MDecl.struct name tparams sfields
    | .enum => MDecl.enum name tparams ctors
  modify fun s => { s with types := s.types.push (s.curPkg, decl) }

/-- Name shown in diagnostics. -/
def showName (c : Name) : String :=
  ((privateToUserName? c).getD c).eraseMacroScopes.toString

/-- Dependency chain from a root down to `c`. -/
def chainOf (c : Name) : M (List Name) := do
  let origin := (← get).origin
  let mut chain := [c]
  let mut cur := c
  for _ in [:origin.size + 1] do
    match origin[cur]? with
    | some p => chain := p :: chain; cur := p
    | none => break
  return chain

def recordError (chain : List String) (ex : Exception) : M Unit := do
  let msg ← (ex.toMessageData.toString : IO String)
  let missing := (← get).curMissing
  let chain := chain ++ (match missing with
    | some m => if chain.getLast? == some (showName m) then [] else [showName m]
    | none => [])
  modify fun s => { s with errors := s.errors.push { chain, msg, missing } }

/-- Process the work queue until all dependencies are extracted.  A failing
constant is recorded (see `reportErrors`) and extraction goes on with the rest
of the queue. -/
partial def drain : M Unit := do
  let st ← get
  if st.queue.isEmpty then return
  let c := st.queue[0]!
  set { st with queue := st.queue.eraseIdx! 0, cur := some c, curMissing := none }
  let pkg ← pkgOf c
  modify fun s => { s with curPkg := pkg }
  let env ← getEnv
  try
    match env.find? c with
    | some (.inductInfo _) => emitInductive c
    | some _ => emitFn c
    | none => if (← get).aux.contains c then emitFn c else throwError "unknown constant {c}"
  catch ex =>
    recordError ((← chainOf c).map showName) ex
  modify fun s => { s with cur := none, curMissing := none }
  drain

/-- One combined error for everything that failed: the reasons (each once,
with the dependency chains that hit it) and a paste-ready list of the missing
mappings. -/
def reportErrors : M Unit := do
  let errs := (← get).errors
  if errs.isEmpty then return
  let mut reasons : Array (String × Array String) := #[]
  for e in errs do
    let via := " → ".intercalate e.chain
    match reasons.findIdx? (·.1 == e.msg) with
    | some i =>
      unless reasons[i]!.2.contains via do
        reasons := reasons.modify i fun (m, vs) => (m, vs.push via)
    | none => reasons := reasons.push (e.msg, #[via])
  let n := errs.size
  let mut out := s!"extraction failed ({n} item{if n == 1 then "" else "s"} could not be extracted):"
  for (msg, vias) in reasons do
    out := out ++ "\n\n" ++ msg
    for v in vias do out := out ++ "\n  via " ++ v
  let miss := (errs.filterMap (·.missing)).toList.eraseDups.map showName |>.toArray.qsort (· < ·)
  unless miss.isEmpty do
    out := out ++ "\n\nmissing mappings (add them, e.g.):"
    for m in miss do
      out := out ++ s!"\n  extract_constant {m} => \"...\""
  throwError "{out}"

/-- A runtime test: `term` is a closed Bool term whose extraction is compared
with the value Lean computed. -/
structure TestSpec where
  /-- pretty-printed Lean term (the test name) -/
  name : String
  /-- pretty-printed Lean value, for the comment -/
  comment : String
  term : Expr
  /-- `some b`: `assert_eq(term, b)`; `none`: `assert_true(term)` -/
  expect : Option Bool

/-- `let got = m; check` with the `let`s of `m` hoisted to statements. -/
def bindResult (m : MExp) (check : MExp) : MExp :=
  match m with
  | .let_ n v b => .let_ n v (bindResult b check)
  | _ => .let_ "got" m check

def renderTest (t : TestSpec) (m : MExp) : String :=
  let cmt := match t.comment.splitOn "\n" with
    | [] => []
    | l :: ls => ("  // Lean: " ++ l) :: ls.map ("  //       " ++ ·)
  let check := match t.expect with
    | some b => MExp.app (.var "assert_eq") #[.var "got", .lit (toString b)]
    | none => MExp.app (.var "assert_true") #[.var "got"]
  "test " ++ strLit t.name ++ " {\n" ++ "\n".intercalate cmt ++ "\n" ++
    renderStmts (bindResult m check) 2 ++ "\n}"

/-- Enqueue the roots, translate the test terms (they share the name assignment and the
dependency queue) and process the queue. -/
def runRoots (roots : Array Name) (tests : Array TestSpec) : M (Array (Option MExp)) := do
  for r in roots do
    let r := (Compiler.isUnsafeRecName? r).getD r
    enqueue r
  -- test terms first (they enqueue their dependencies), then one `drain`
  let mut bodies : Array (Option MExp) := #[]
  for t in tests do
    resetDecl
    modify fun s => { s with curMissing := none }
    try bodies := bodies.push (some (← tr t.term))
    catch ex =>
      recordError [s!"test `{t.name}`"] ex
      bodies := bodies.push none
  drain
  reportErrors
  return bodies

/-- Sources of the helper functions that the extraction uses (transitively), in table order. -/
def helperSources (st : ExState) (mode : NatMode) : Array String := Id.run do
  let mut used := st.helpers
  let mut changed := true
  while changed do
    changed := false
    for h in st.table.helperOrder do
      if used.contains h then
        let src := expandMode mode (st.table.helpers.getD h "")
        for h2 in st.table.helperOrder do
          if !used.contains h2 && (src.splitOn h2).length > 1 then
            used := used.insert h2
            changed := true
  let helpers := st.table.helperOrder.filter used.contains
  return helpers.map fun h => expandMode mode (st.table.helpers.getD h "")

def renderTests (header : String) (tests : Array TestSpec) (bodies : Array (Option MExp)) : String :=
  if tests.isEmpty then ""
  else
    let ts := (tests.zip bodies).toList.filterMap fun (t, b) => b.map (renderTest t)
    header ++
    "// Each test checks the extracted code against the value Lean computed.\n\n" ++
    "\n\n".intercalate ts ++ "\n"

/-- Run the extraction of `roots` (and of the terms of `tests`, which share
the name assignment and the dependency queue) and return the MoonBit source
and the generated test file (empty without tests). -/
def extractRoots (roots : Array Name) (tests : Array TestSpec) (mode : NatMode) (table : Table) :
    MetaM (String × String) := do
  let act : M (String × String) := do
    let bodies ← runRoots roots tests
    let st ← get
    let hsrc := helperSources st mode
    let parts :=
      #["// Extracted from Lean by lean6x7mbt."] ++
      (if hsrc.isEmpty then #[] else #["// Helpers"] ++ hsrc) ++
      st.types.map (·.2.render) ++ st.fns.map (·.2.render)
    let src := "\n\n".intercalate parts.toList ++ "\n"
    let tsrc := renderTests
      "// Generated by lean6x7mbt (`extract_moonbit .. with_tests [..]`); do not edit.\n" tests bodies
    return (src, tsrc)
  let (s, _) ← act.run { mode, table }
  return s

/-! ## Project mode: one MoonBit package per Lean module -/

/-- One generated package. -/
structure PkgOut where
  name : String
  /-- source of `<name>.mbt` -/
  src : String
  /-- packages imported by `src` -/
  deps : Array String
  /-- extra packages imported (`for "wbtest"`) by the generated tests -/
  testDeps : Array String := #[]
  /-- source of `<name>_gen_wbtest.mbt` (only the main package; empty without tests) -/
  tests : String := ""
  /-- external MoonBit packages (alias, import path; see `import_mbti`) used by `src` -/
  extDeps : Array (String × String) := #[]
  /-- external packages used only by the generated tests -/
  extTestDeps : Array (String × String) := #[]

/-- Packages `@pkg.` mentioned in `src`. -/
def scanDeps (src : String) (known : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  for seg in (src.splitOn "@").drop 1 do
    let cs := seg.toList
    let id := String.ofList (cs.takeWhile fun c => c.isAlphanum || c == '_')
    if (cs.drop id.length).head? == some '.' && known.contains id && !out.contains id then
      out := out.push id
  return out

/-- Kahn's algorithm: the packages that are left over lie on, or behind, a cycle. -/
def cyclicPkgs (deps : Array (String × Array String)) : Array String := Id.run do
  let mut left := deps
  let mut changed := true
  while changed do
    changed := false
    let names := left.map (·.1)
    let ready := left.filter fun (_, ds) => ds.all fun d => !names.contains d
    if !ready.isEmpty then
      left := left.filter fun (n, _) => !(ready.any (·.1 == n))
      changed := true
  return left.map (·.1)

/-- Extract `roots` (and the terms of `tests`) into one package per Lean module: the core
library (`Init*`, `Std*`, `Lean*`) and the helper functions go to `lean_core`; the tests go to
the main package (`mainPkg`; default: the package of the current module). -/
def extractProject (roots : Array Name) (tests : Array TestSpec) (mode : NatMode) (table : Table)
    (mainPkg? : Option String) : MetaM (Array PkgOut) := do
  let act : M (Array PkgOut) := do
    let env ← getEnv
    let mainName ← match mainPkg? with
      | some n => pure n
      | none => if env.mainModule == `_stdin then pure "app" else allocPkg env.mainModule
    modify fun s => { s with project := true, mainPkg := mainName, curPkg := mainName,
                             pkgNames := s.pkgNames.insert env.mainModule mainName,
                             pkgUsed := s.pkgUsed.insert mainName }
    let bodies ← runRoots roots tests
    let st ← get
    let hsrc := (helperSources st mode).map fun h =>
      if h.startsWith "fn" then "pub " ++ h else h
    let decls := st.types ++ st.fns
    let mut users : Array String := #[mainName]
    for (p, _) in decls do
      unless p == corePkg || users.contains p do users := users.push p
    let hasCore := !hsrc.isEmpty || decls.any (·.1 == corePkg)
    let names := (if hasCore then #[corePkg] else #[]) ++ users.qsort (· < ·)
    let tsrc := renderTests
      "// Generated by lean6x7mbt (`extract_moonbit_project .. with_tests [..]`); do not edit.\n" tests bodies
    let mut outs : Array PkgOut := #[]
    for n in names do
      let parts :=
        #[s!"// Extracted from Lean by lean6x7mbt (package `{n}`)."] ++
        (if n == corePkg && !hsrc.isEmpty then #["// Helpers"] ++ hsrc else #[]) ++
        (st.types.filter (·.1 == n)).map (·.2.render) ++ (st.fns.filter (·.1 == n)).map (·.2.render)
      let src := "\n\n".intercalate parts.toList ++ "\n"
      let deps := (scanDeps src names).filter (· != n)
      let (tests, testDeps) :=
        if n == mainName then
          (tsrc, (scanDeps tsrc names).filter fun d => d != n && !deps.contains d)
        else ("", #[])
      -- external MoonBit packages declared by `import_mbti`
      let extAliases := table.extPkgs.map (·.1)
      let extUsed := fun (s : String) =>
        let used := scanDeps s extAliases
        table.extPkgs.filter fun (a, _) => used.contains a
      let extDeps := extUsed src
      let extTestDeps := (if n == mainName then extUsed tsrc else #[]).filter fun e =>
        !extDeps.any (·.1 == e.1)
      outs := outs.push { name := n, src, deps, testDeps, tests, extDeps, extTestDeps }
    -- `lean_core` is a leaf; no cycles between packages
    for o in outs do
      if o.name == corePkg && !o.deps.isEmpty then
        throwError "package {corePkg} would depend on {o.deps} (a cyclic dependency)"
    let cyc := cyclicPkgs (outs.map fun o => (o.name, o.deps ++ o.testDeps))
    unless cyc.isEmpty do
      throwError "cyclic dependency between the generated packages: {cyc}"
    return outs
  let (s, _) ← act.run { mode, table }
  return s

end Lean6x7mbt
