module

public import Lean
import all Init.System.Promise
import all Lean.Environment

open Lean

-- 1(a).1: `leanprover/lean4#15717` — 100% safe BaseIO cast via public `ST.Ref.mk`
-- Compiles without `unsafe`, `partial`, `implemented_by`, or `import all`
public def safeCoerce [Nonempty β] (a : α) : BaseIO β := do
  let r ← IO.mkRef a
  let r : IO.Ref β := ⟨r.ref, inferInstance⟩
  r.get

-- Even stronger: 100% safe PURE cast `α → β` via `runST` + `ST.Ref.mk`,
-- written WITHOUT `do` notation using only syntax kinds allowed by Anneal's Phase 1!
public def pureCoerceNoDo (defaultB : β) (a : α) : β :=
  runST (fun σ =>
    Bind.bind (ST.Prim.mkRef a) (fun (r : ST.Ref σ α) =>
      ST.Prim.Ref.get ⟨r.ref, Nonempty.intro defaultB⟩))

-- 1(a).2: `IO.Promise` cast via `import all Init.System.Promise`
public def promiseCoerce [Nonempty β] (a : α) : BaseIO β := do
  have : Nonempty α := ⟨a⟩
  let p ← IO.Promise.new
  p.resolve a
  let p' : IO.Promise β := ⟨p.prom, inferInstance⟩
  return p'.result!.get

-- 1(a).3: `EnvExtension` cast via `import all Lean.Environment`
public def envExtCoerce (defaultB : β) (env : Environment) (a : α) : β :=
  have : Inhabited β := ⟨defaultB⟩
  let extA : EnvExtension α := {
    idx := 0
    mkInitial := pure a
    asyncMode := .sync
    replay? := none
  }
  let extB : EnvExtension β := {
    idx := 0
    mkInitial := pure defaultB
    asyncMode := .sync
    replay? := none
  }
  let env' := extA.setState env a (asyncMode := .sync)
  extB.getState env' (asyncMode := .sync)

public def main : IO Unit := do
  IO.println "=== Probe(a) Probe: #15717 ST.Ref.mk, IO.Promise, and EnvExtension Safe Coercions ==="

  -- Runtime evaluation of safeCoerce (Int -> Nat on negative GMP bignum -2^32)
  let negBignum : Int := -4294967296
  let coercedBaseIO : Nat ← safeCoerce negBignum
  IO.println s!"[1] safeCoerce (-4294967296 : Int) : BaseIO Nat => toString = {coercedBaseIO}, startsWith '-' = {(toString coercedBaseIO).startsWith "-"}"

  -- Runtime evaluation of pureCoerceNoDo (Int -> Nat on -2^32)
  let coercedPure : Nat := pureCoerceNoDo 0 negBignum
  IO.println s!"[2] pureCoerceNoDo 0 (-4294967296 : Int) : Nat => toString = {coercedPure}, startsWith '-' = {(toString coercedPure).startsWith "-"}"

  -- Runtime evaluation of promiseCoerce (Int -> Nat)
  let coercedPromise : Nat ← promiseCoerce negBignum
  IO.println s!"[3] promiseCoerce (-4294967296 : Int) : BaseIO Nat => toString = {coercedPromise}, startsWith '-' = {(toString coercedPromise).startsWith "-"}"

  -- Runtime evaluation of envExtCoerce (Int -> Nat)
  let emptyEnv ← mkEmptyEnvironment
  let coercedEnvExt : Nat := envExtCoerce 0 emptyEnv negBignum
  IO.println s!"[4] envExtCoerce 0 emptyEnv (-4294967296 : Int) : Nat => toString = {coercedEnvExt}, startsWith '-' = {(toString coercedEnvExt).startsWith "-"}"

  -- Inspect ConstantInfo of safeCoerce and pureCoerceNoDo in a non-module file
  let snippet :=
"import Init.System.IO

def safeCoerce [Nonempty β] (a : α) : BaseIO β := do
  let r ← IO.mkRef a
  let r : IO.Ref β := ⟨r.ref, inferInstance⟩
  r.get

def pureCoerceNoDo (defaultB : β) (a : α) : β :=
  runST (fun σ =>
    Bind.bind (ST.Prim.mkRef a) (fun (r : ST.Ref σ α) =>
      ST.Prim.Ref.get ⟨r.ref, Nonempty.intro defaultB⟩))

def forgedFalseTerm : False := pureCoerceNoDo sorry True.intro
"
  -- Wait: without `sorry`, can we define `pureCoerceUnitToBool : Bool := pureCoerceNoDo false ()`? Yes!
  let snippetClean :=
"import Init.System.IO

def safeCoerce [Nonempty β] (a : α) : BaseIO β := do
  let r ← IO.mkRef a
  let r : IO.Ref β := ⟨r.ref, inferInstance⟩
  r.get

def pureCoerceNoDo (defaultB : β) (a : α) : β :=
  runST (fun σ =>
    Bind.bind (ST.Prim.mkRef a) (fun (r : ST.Ref σ α) =>
      ST.Prim.Ref.get ⟨r.ref, Nonempty.intro defaultB⟩))

def coercedNatFromNegInt : Nat := pureCoerceNoDo 0 (-4294967296 : Int)
"
  IO.FS.writeFile "TmpSafeCoerceMod.lean" snippetClean
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["-o", "TmpSafeCoerceMod.olean", "TmpSafeCoerceMod.lean"]
  }
  IO.println s!"[5] Compiling TmpSafeCoerceMod.lean (no `import all`, no `unsafe`, no `partial`): exitCode={out.exitCode}"
  if out.exitCode != 0 then
    IO.println s!"    stderr: {out.stderr}"

  -- Load TmpSafeCoerceMod.olean with loadExts := false and test Phase 2 checks + Kernel.whnf + replay
  let env ← importModules #[{ module := `Init.System.IO }, { module := `TmpSafeCoerceMod }] {} (trustLevel := 0) (loadExts := false)
  let baseEnv ← importModules #[{ module := `Init.System.IO }] {} (trustLevel := 0) (loadExts := false)
  for declName in [`safeCoerce, `pureCoerceNoDo, `coercedNatFromNegInt] do
    if let some ci := env.find? declName then
      let kind := match ci with
        | .defnInfo _ => "defnInfo"
        | .thmInfo _ => "thmInfo"
        | .opaqueInfo _ => "opaqueInfo"
        | .axiomInfo _ => "axiomInfo"
        | _ => "other"
      IO.println s!"    Decl `{declName}`: kind={kind}, isUnsafe={ci.isUnsafe}, isPartial={ci.isPartial}"

  -- Replay TmpSafeCoerceMod's constants into baseEnv.toKernelEnv
  let mut toReplay : Std.HashMap Name ConstantInfo := {}
  if let some modIdx := env.getModuleIdx? `TmpSafeCoerceMod then
    let data := env.header.moduleData[modIdx]!
    for ci in data.constants do
      toReplay := toReplay.insert ci.name ci
  let kenv ← baseEnv.toKernelEnv.replay toReplay
  IO.println s!"[6] baseEnv.toKernelEnv.replay on TmpSafeCoerceMod succeeded! (replayed {toReplay.size} constants)"

  -- Test Kernel.whnf on `coercedNatFromNegInt` in the kernel!
  let appExpr := mkConst `coercedNatFromNegInt
  match Kernel.whnf env {} appExpr with
  | .ok whnfExpr =>
    IO.println s!"[7] Kernel.whnf of `coercedNatFromNegInt`:\n    {whnfExpr}"
    IO.println s!"    Is whnfExpr stuck on opaque `ST.Prim.mkRef`? {whnfExpr.getUsedConstants.contains ``ST.Prim.mkRef}"
    IO.println s!"    Is whnfExpr a Nat literal? {whnfExpr matches .lit (.natVal _)}"
  | .error _ =>
    IO.println s!"[7] Kernel.whnf error"

  -- Test what happens if we try to prove `coercedNatFromNegInt = 0` by `rfl` in the kernel:
  let rflAttempt :=
"import TmpSafeCoerceMod
theorem tryReduceInKernel : coercedNatFromNegInt = 0 := rfl
"
  IO.FS.writeFile "TmpKernelReduceAttempt.lean" rflAttempt
  let outRfl ← IO.Process.output {
    cmd := "lean"
    args := #["TmpKernelReduceAttempt.lean"]
  }
  IO.println s!"[8] Kernel reduction test (`coercedNatFromNegInt = 0 := rfl`): exitCode={outRfl.exitCode}"
  IO.println s!"    stdout: {outRfl.stdout.trimAscii}"
