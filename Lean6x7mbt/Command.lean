import Lean
import Lean6x7mbt.Translate

/-!
# The `extract_moonbit` command

```lean
extract_moonbit "out/basic.mbt" f g Tree.size
```

extracts the given definitions (and everything they depend on) to a MoonBit
source file; without a path the code is shown in the infoview.

```lean
extract_moonbit "out/basic.mbt" f g with_tests [f 5, g [1, 2] == 3, Tree.size t0]
```

additionally generates `out/basic_gen_wbtest.mbt`: every test term is a closed
Lean term that Lean itself evaluates (compiled evaluation, `evalExpr`), and the
generated MoonBit test asserts that the extracted code computes the same value.
-/

open Lean Elab Command Meta

namespace Lean6x7mbt

syntax (name := extractMoonbit)
  "extract_moonbit " (str)? ident* (" with_tests " "[" term,* "]")? : command

unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool :=
  evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe] opaque evalBool (e : Expr) : MetaM Bool

unsafe def evalExprValUnsafe (e : Expr) : MetaM Expr :=
  evalExpr Expr (mkConst ``Expr) e

@[implemented_by evalExprValUnsafe] opaque evalExprVal (e : Expr) : MetaM Expr

/-- Run an evaluation of a test term; explain the failure when the term uses a function of an
external MoonBit package (`import_mbti`), which Lean cannot compute. -/
def withEvalHint (stx : Syntax) (t : Expr) (x : MetaM α) : MetaM α := do
  try x catch ex =>
    let m ← ex.toMessageData.toString
    if (m.splitOn "native implementation").length > 1 then
      let parts := (m.splitOn "external declaration '")
      let c := if parts.length > 1 then (parts[1]!.takeWhile (· != '\'')).toString else "a constant"
      throwErrorAt stx "this test term cannot be evaluated by Lean: it uses `{c}`, a function imported from MoonBit (`import_mbti`) that has no Lean implementation; check such code in a hand-written `*_wbtest.mbt` instead"
    else throw ex

/-- Elaborate a test term, let Lean evaluate it and build the Bool term that the
extracted code must satisfy. -/
def mkTest (stx : Syntax) : TermElabM TestSpec := do
  let t ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← instantiateMVars t
  if t.hasMVar || t.hasFVar then
    throwErrorAt stx "test term must be closed and fully elaborated: {t}"
  let ty ← instantiateMVars (← inferType t)
  let name := toString (← ppExpr t)
  if ← isDefEq ty (mkConst ``Bool) then
    let v ← withEvalHint stx t (evalBool t)
    return { name, comment := toString v, term := t, expect := some v }
  let hint := "write the test as a `Bool` value (e.g. `f x == expected`) or add `deriving ToExpr, BEq`"
  let toExprCls ← mkAppM ``ToExpr #[ty]
  let beqCls ← mkAppM ``BEq #[ty]
  unless (← synthInstance? toExprCls).isSome do
    throwErrorAt stx "test term `{t}` : `{ty}` needs a `ToExpr` instance; {hint}"
  unless (← synthInstance? beqCls).isSome do
    throwErrorAt stx "test term `{t}` : `{ty}` needs a `BEq` instance; {hint}"
  let v ← withEvalHint stx t (evalExprVal (← mkAppM ``toExpr #[t]))
  let eq ← mkAppM ``BEq.beq #[t, v]
  return { name, comment := toString (← ppExpr v), term := eq, expect := none }

@[command_elab extractMoonbit] def elabExtractMoonbit : CommandElab := fun stx => do
  let path? := stx[1].getOptional?.bind (·.isStrLit?)
  let ids := stx[2].getArgs
  let testStxs := if stx[3].getNumArgs == 0 then #[] else stx[3][2].getSepArgs
  let mut roots : Array Name := #[]
  for id in ids do
    roots := roots.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id)
  let opts ← getOptions
  let modeStr := opts.get `lean6x7mbt.nat "bigint"
  let some mode := NatMode.ofString? modeStr
    | throwError "invalid value of lean6x7mbt.nat: {modeStr} (expected bigint, int or int64)"
  let table := tableExt.getState (← getEnv)
  let (src, tsrc) ← liftTermElabM do
    let tests ← testStxs.mapM mkTest
    extractRoots roots tests mode table
  match path? with
  | some path =>
    let p : System.FilePath := path
    if let some dir := p.parent then IO.FS.createDirAll dir
    IO.FS.writeFile p src
    if testStxs.isEmpty then
      logInfo m!"extracted {roots.size} root(s) to {path}"
    else
      let stem := p.fileStem.getD "out"
      let tp := p.withFileName (stem ++ "_gen_wbtest.mbt")
      IO.FS.writeFile tp tsrc
      logInfo m!"extracted {roots.size} root(s) to {path}; {testStxs.size} test(s) to {tp.toString.replace "\\" "/"}"
  | none =>
    if testStxs.isEmpty then logInfo m!"{src}"
    else logInfo m!"{src}\n// ---- tests ----\n{tsrc}"

/-! ## `extract_moonbit_project`: one MoonBit package per Lean module -/

register_option lean6x7mbt.module : String := {
  defValue := "lean6x7mbt/extracted"
  descr := "name of the generated MoonBit module (`moon.mod`), used when the output directory has none"
}

register_option lean6x7mbt.main_package : String := {
  defValue := ""
  descr := "package that receives the generated tests and the constants of the current Lean module (default: derived from the module name, `app` for a standalone file)"
}

syntax (name := extractMoonbitProject)
  "extract_moonbit_project " str ident* (" with_tests " "[" term,* "]")? : command

/-- The `name = "..."` of an existing `moon.mod`. -/
def readModName (file : System.FilePath) : IO (Option String) := do
  let txt ← IO.FS.readFile file
  for l in txt.splitOn "\n" do
    let l := l.trimAscii.toString
    if l.startsWith "name" then
      let rest := (l.drop 4).toString.trimAscii.toString
      if rest.startsWith "=" then
        let v := (rest.drop 1).toString.trimAscii.toString
        return some ((v.replace "\"" "").trimAscii.toString)
  return none

def renderPkgFile (modName : String) (o : PkgOut) : String :=
  let imp := fun (ds : Array String) (ext : Array (String × String)) =>
    "import {\n" ++ "".intercalate (ds.toList.map fun d => s!"  \"{modName}/{d}\",\n") ++
      "".intercalate (ext.toList.map fun (a, p) => s!"  \"{p}\" @{a},\n") ++ "}"
  let blocks :=
    (if o.deps.isEmpty && o.extDeps.isEmpty then [] else [imp o.deps o.extDeps]) ++
    (if o.testDeps.isEmpty && o.extTestDeps.isEmpty then [] else [imp o.testDeps o.extTestDeps ++ " for \"wbtest\""])
  if blocks.isEmpty then "" else "\n".intercalate blocks ++ "\n"

@[command_elab extractMoonbitProject] def elabExtractMoonbitProject : CommandElab := fun stx => do
  let some dir := stx[1].isStrLit? | throwError "expected an output directory"
  let ids := stx[2].getArgs
  let testStxs := if stx[3].getNumArgs == 0 then #[] else stx[3][2].getSepArgs
  let mut roots : Array Name := #[]
  for id in ids do
    roots := roots.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id)
  let opts ← getOptions
  let modeStr := opts.get `lean6x7mbt.nat "bigint"
  let some mode := NatMode.ofString? modeStr
    | throwError "invalid value of lean6x7mbt.nat: {modeStr} (expected bigint, int or int64)"
  let mainPkg := opts.get `lean6x7mbt.main_package ""
  if mainPkg != "" then
    unless mainPkg.all (fun c => c.isDigit || (c.isLower && c.isAlpha) || c == '_') &&
        !(fstChar mainPkg).isDigit && mainPkg != corePkg do
      throwError "invalid value of lean6x7mbt.main_package: {mainPkg} (lowercase letters, digits and `_`; not `{corePkg}`)"
  let table := tableExt.getState (← getEnv)
  let outs ← liftTermElabM do
    let tests ← testStxs.mapM mkTest
    extractProject roots tests mode table (if mainPkg == "" then none else some mainPkg)
  let root : System.FilePath := dir
  IO.FS.createDirAll root
  let modFile := root / "moon.mod"
  let modName ← if ← modFile.pathExists then
      pure ((← readModName modFile).getD (opts.get `lean6x7mbt.module "lean6x7mbt/extracted"))
    else do
      let n := opts.get `lean6x7mbt.module "lean6x7mbt/extracted"
      IO.FS.writeFile modFile s!"name = \"{n}\"\n\nversion = \"0.1.0\"\n"
      pure n
  let mut ntests := 0
  for o in outs do
    let pdir := root / o.name
    IO.FS.createDirAll pdir
    IO.FS.writeFile (pdir / (o.name ++ ".mbt")) o.src
    IO.FS.writeFile (pdir / "moon.pkg") (renderPkgFile modName o)
    unless o.tests.isEmpty do
      IO.FS.writeFile (pdir / (o.name ++ "_gen_wbtest.mbt")) o.tests
      ntests := testStxs.size
  logInfo m!"extracted {roots.size} root(s) into {outs.size} package(s) under {dir}: {", ".intercalate (outs.map (·.name)).toList}; {ntests} test(s)"

end Lean6x7mbt
