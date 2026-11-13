import Lean

/-!
# Extraction tables and user commands

* `extract_constant c => "template"` — implement `c` by a MoonBit expression.
  `$i` is the i-th *kept* argument: type and proof arguments are erased and
  instance arguments (type-class dictionaries other than `Decidable`) are
  skipped.
* `extract_inductive I => "TyTemplate" ["ctor0", "ctor1", ..]` — map the
  inductive type `I` to an existing MoonBit type.  In the type template `$i` is
  the i-th type parameter; constructor templates are used both as expressions
  and as patterns, `$i` being the i-th kept constructor field.
* `extract_helper name => "source"` — a MoonBit declaration that is emitted
  (once) into the output whenever `name` occurs in a template.

Templates may mention `@Nat` and `@Int`, which are replaced by the MoonBit
type chosen with `set_option lean6x7mbt.nat`.
-/

open Lean Elab Command

namespace Lean6x7mbt

register_option lean6x7mbt.nat : String := {
  defValue := "bigint"
  descr := "MoonBit representation of Nat and Int: \"bigint\" (BigInt, default), \"int\" (Int, wraps on overflow) or \"int64\" (Int64, wraps on overflow)"
}

structure IndMap where
  ty : String
  ctors : Array String
  deriving Inhabited

inductive TableEntry where
  | const (n : Name) (tpl : String)
  | ind (n : Name) (m : IndMap)
  | helper (n : String) (src : String)
  /-- an external MoonBit package referenced as `@alias.` by templates (see `import_mbti`) -/
  | extPkg (alias : String) (path : String)
  deriving Inhabited

structure Table where
  consts : NameMap String := {}
  inds : NameMap IndMap := {}
  helpers : Std.HashMap String String := {}
  helperOrder : Array String := #[]
  /-- external MoonBit packages (alias, import path) that generated packages must import -/
  extPkgs : Array (String × String) := #[]
  deriving Inhabited

def Table.add (t : Table) : TableEntry → Table
  | .const n tpl => { t with consts := t.consts.insert n tpl }
  | .ind n m => { t with inds := t.inds.insert n m }
  | .extPkg a p =>
    { t with extPkgs := if t.extPkgs.any (·.1 == a) then t.extPkgs else t.extPkgs.push (a, p) }
  | .helper n src =>
    { t with helpers := t.helpers.insert n src,
             helperOrder := if t.helpers.contains n then t.helperOrder else t.helperOrder.push n }

initialize tableExt : SimplePersistentEnvExtension TableEntry Table ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Table.add
    addImportedFn := fun es => es.foldl (fun t a => a.foldl Table.add t) {}
  }

/-- The three Nat/Int representations. -/
inductive NatMode where
  | bigint | int | int64
  deriving Inhabited, BEq

def NatMode.ofString? : String → Option NatMode
  | "bigint" => some .bigint
  | "int" => some .int
  | "int64" => some .int64
  | _ => none

def NatMode.tyName : NatMode → String
  | .bigint => "BigInt"
  | .int => "Int"
  | .int64 => "Int64"

/-- Literal suffix used when printing a number of this mode. -/
def NatMode.litSuffix : NatMode → String
  | .bigint => "N"
  | .int => ""
  | .int64 => "L"

/-- Function names converting between MoonBit `Int` and the Nat/Int representation. -/
def NatMode.ofInt : NatMode → String
  | .bigint => "BigInt::from_int"
  | .int => "lean_id_int"
  | .int64 => "Int::to_int64"

def NatMode.toInt : NatMode → String
  | .bigint => "BigInt::to_int"
  | .int => "lean_id_int"
  | .int64 => "Int64::to_int"

def NatMode.toInt64 : NatMode → String
  | .bigint => "BigInt::to_int64"
  | .int => "Int::to_int64"
  | .int64 => "lean_id_int64"

def NatMode.ofU64 : NatMode → String
  | .bigint => "BigInt::from_uint64"
  | .int => "UInt64::to_int"
  | .int64 => "UInt64::to_int64"

def NatMode.ofU32 : NatMode → String
  | .bigint => "BigInt::from_uint"
  | .int => "UInt::to_int"
  | .int64 => "UInt::to_int64"

/-- Nat → `UInt` (wrapping). -/
def NatMode.toU32 : NatMode → String
  | .bigint => "BigInt::to_uint"
  | .int => "Int::to_uint"
  | .int64 => "lean_int64_to_uint"

/-- Expand the template macros: `@Nat`, `@Int` (type names), `@zero`, `@one`
(literals) and the conversion functions `@ofInt`, `@toInt`, `@toInt64`,
`@ofU64`, `@ofU32`, `@toU32`. -/
def expandMode (m : NatMode) (s : String) : String :=
  let s := (s.replace "@Nat" m.tyName).replace "@Int" m.tyName
  let s := (s.replace "@zero" ("0" ++ m.litSuffix)).replace "@one" ("1" ++ m.litSuffix)
  let s := s.replace "@toInt64" m.toInt64
  let s := s.replace "@toInt" m.toInt
  let s := s.replace "@ofInt" m.ofInt
  let s := s.replace "@ofU64" m.ofU64
  let s := s.replace "@toU32" m.toU32
  s.replace "@ofU32" m.ofU32

syntax (name := extractConstant) "extract_constant " ident " => " str : command
syntax (name := extractInductive) "extract_inductive " ident " => " str " [" str,* "]" : command
syntax (name := extractHelper) "extract_helper " ident " => " str : command
syntax (name := extractType) "extract_type " ident " => " str : command

@[command_elab extractConstant] def elabExtractConstant : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let tpl := stx[3].isStrLit?.get!
  modifyEnv (tableExt.addEntry · (.const n tpl))

@[command_elab extractInductive] def elabExtractInductive : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ty := stx[3].isStrLit?.get!
  let ctors := stx[5].getSepArgs.map fun s => s.isStrLit?.get!
  let some (.inductInfo ind) := (← getEnv).find? n
    | throwError "{n} is not an inductive type"
  unless ind.ctors.length == ctors.size do
    throwError "{n} has {ind.ctors.length} constructors, but {ctors.size} templates were given"
  modifyEnv (tableExt.addEntry · (.ind n { ty, ctors }))

@[command_elab extractHelper] def elabExtractHelper : CommandElab := fun stx => do
  let n := stx[1].getId.toString
  let src := stx[3].isStrLit?.get!
  modifyEnv (tableExt.addEntry · (.helper n src))

/-- `extract_type T => "tpl"`: map the (axiomatized) type constant `T` to a MoonBit type.  `$i` is the
i-th type parameter, e.g. `extract_type Foo.Box => "@lib.Box[$0]"`.  It is an `extract_inductive` without
constructors, so such a type can only be built and inspected through `extract_constant` functions. -/
@[command_elab extractType] def elabExtractType : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ty := stx[3].isStrLit?.get!
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  if ci.isInductive then
    throwError "{n} is an inductive type: use `extract_inductive`"
  modifyEnv (tableExt.addEntry · (.ind n { ty, ctors := #[] }))

end Lean6x7mbt
