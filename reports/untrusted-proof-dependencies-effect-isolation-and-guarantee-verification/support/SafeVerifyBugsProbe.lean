module

public import Lean
import all Lean.Util.CollectAxioms

open Lean Meta Core Std

/-!
# — Probe Probe: Runnable Reproduction of `SafeVerify` (`b291b58`) Bugs
   vs Anneal's `TrustedBoundary.lean` in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)

This probe embeds the exact checking logic from `GasStationManager/SafeVerify` at commit
`b291b588a53999a7e837dda61c7dbfe8c550c814` (`SafeVerify/Types.lean`, `SafeVerify/Monads.lean`,
`SafeVerify/Printing.lean`, `SafeVerify/Util.lean`, and `Main.lean`) alongside Anneal's
corresponding checks from `trusted/audit/TrustedBoundary.lean`, and empirically demonstrates:

1. **Bug 1 (`partial def` bypasses `disallowPartial := true`)**:
   - In Lean 4 (`v4.34.1`), `partial def bad (n : Nat) : Nat := bad (n + 1)` compiles to:
     * `bad._unsafe_rec` (`.defnInfo` with `safety := .partial`, `ci.isPartial = true`), and
     * `bad` (`.opaqueInfo` with `isUnsafe := false`, `ci.isPartial = false`).
   - `SafeVerify/Main.lean:157, 202` checks:
     `if disallowPartial && ci.isPartial && !isCompilerUnsafeRecName name then throw ...`
     Because `isCompilerUnsafeRecName` (`Main.lean:28-30`) returns `true` for `bad._unsafe_rec`
     and `ci.isPartial` is `false` for `.opaqueInfo bad`, `SafeVerify` with `disallowPartial := true`
     **accepts** `partial def` without error!
   - By contrast, Anneal's `TrustedBoundary.lean` rejects `partial def` via two independent checks:
     (i) `TrustedBoundary.lean:659` rejects all `.opaqueInfo` constants (`bad`), and
     (ii) `TrustedBoundary.lean:666-685` (`isStructuralRecCompilerHelper`) inspects `env.checked.get.find? `bad`,
          sees `.opaqueInfo` instead of `.defnInfo` with `!baseCi.isUnsafe && !baseCi.isPartial`,
          and therefore rejects `bad._unsafe_rec` as a `partial declaration` (`line 657`).

2. **Bug 2 (Un-replayed `map₁` helper module import bypass)**:
   - `EvilHelper.lean` uses `modifyEnv fun env => env.addDeclCore 0 (.thmDecl ...)` to export
     `theorem evil_false : False` with an ill-typed proof (`True.intro`).
   - `Submission.lean` imports `EvilHelper` and proves `theorem target : False := evil_false`.
   - `SafeVerify`'s `checkImportSuperset` + `replayFileWithEnv` + `checkTargets` **accepts**
     `Submission.olean` with 0 errors because `importModules mod.imports {} 0` loads `EvilHelper.olean`
     into `map₁` without kernel replay, and `env.replay` only replays `Submission.olean`'s `map₂`.
   - Anneal's `TrustedBoundary.lean` walks the entire non-foundation import DAG (`EvilHelper` +
     `Submission`) and replays all non-foundation constants into `base.toKernelEnv`, rejecting
     `EvilHelper` with a kernel type mismatch.

3. **Bug 3 (`equivDefn` `sorryAx` value-check bypass & `supplementedDecls` dead-code regression)**:
   - In `SafeVerify/Main.lean:58`, `equivDefn` is called with `checkVal := (`sorryAx ∉ target.axioms)`.
     When a target definition `def specProp : Prop := False ∧ sorry` contains `sorry`, `SafeVerify`
     skips value comparison completely, allowing `Submission.lean` to redefine `def specProp : Prop := True`
     and trivially prove `theorem targetSpecThm : specProp := True.intro`.
   - In `SafeVerify/Main.lean:418-434`, `supplementedDecls` is computed to include target declarations
     fulfilled by helper imports, but line 433 passes `submissionDecls := submissionDecls` instead of
     `supplementedDecls`, discarding the map entirely.
-/

-- ============================================================================
-- Exact Embedded Code from SafeVerify (`b291b588a53999a7e837dda61c7dbfe8c550c814`)
-- ============================================================================

namespace SafeVerifyExact

structure Info where
  constInfo : ConstantInfo
  axioms : Array Name
deriving Inhabited

inductive CheckFailure
  | kind (kind1 kind2 : String)
  | thmType
  | defnCheck
  | opaqueCheck
  | inductCheck
  | ctorCheck
  | axioms
  | notFound
deriving Inhabited, Repr

instance : ToString CheckFailure where
  toString
    | .kind k1 k2 => s!"kind mismatch (expected {k1}, got {k2})"
    | .thmType => "theorem type mismatch"
    | .defnCheck => "definition type or value mismatch"
    | .opaqueCheck => "opaque type or value mismatch"
    | .inductCheck => "inductive type mismatch"
    | .ctorCheck => "constructor mismatch"
    | .axioms => "uses disallowed axioms"
    | .notFound => "declaration not found in submission"

structure SafeVerifyOutcome where
  targetInfo : Info
  solutionInfo : Option Info
  failureMode : Option CheckFailure
deriving Inhabited

structure Settings where
  targetFile : System.FilePath := default
  submissionFile : System.FilePath := default
  disallowPartial : Bool := false
  verbose : Bool := false
  allowedAxioms : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  allowDisproofs : Bool := false
deriving Inhabited

structure Decls where
  targetDecls : Std.HashMap Name Info := {}
  submissionDecls : Std.HashMap Name Info := {}
  env : Environment

structure State where
  checkOutcomes : Std.HashMap Name SafeVerifyOutcome := {}
  axiomViolations : Array (Name × Array Name) := #[]
deriving Inhabited

abbrev SafeVerifyT (m : Type → Type) := ReaderT Settings (ReaderT Decls (StateT State m))
abbrev SafeVerifyM := SafeVerifyT IO

def getSettings : SafeVerifyM Settings := read
def getDecls : SafeVerifyM Decls := fun _ => read

def cinfoKind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

def equivThm (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all

def equivDefn (ctarget cnew : ConstantInfo) (checkVal : Bool := false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value == tval₂.value else true)

def equivOpaq (ctarget cnew : ConstantInfo) : Bool := Id.run do
  let .opaqueInfo tval₁ := ctarget | false
  let .opaqueInfo tval₂ := cnew | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.isUnsafe == tval₂.isUnsafe
    && tval₁.value == tval₂.value

def equivCtor (ctarget cnew : ConstantInfo) : Bool := Id.run do
  let .ctorInfo tval₁ := ctarget | false
  let .ctorInfo tval₂ := cnew | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.induct == tval₂.induct
    && tval₁.cidx == tval₂.cidx
    && tval₁.numParams == tval₂.numParams
    && tval₁.numFields == tval₂.numFields
    && tval₁.isUnsafe == tval₂.isUnsafe

def processFileDeclarations (env : Environment) : HashMap Name Info := Id.run do
  let mut out : HashMap Name Info := {}
  for (_, ci) in env.constants.map₂ do
    if cinfoKind ci ∈ ["theorem", "def", "opaque", "inductive", "constructor"] then
      let (_, s) := (CollectAxioms.collect (fun _ _ => none) ci.name).run env |>.run {}
      out := out.insert ci.name ⟨ci, s.axioms.toArray⟩
  return out

-- Exact SafeVerify Main.lean:28-30
def isCompilerUnsafeRecName : Name → Bool
  | .str _ s => s == "_unsafe_rec"
  | _ => false

def checkAxioms (info : Info) (allowedAxioms : Array Name) : Bool := Id.run do
  for a in info.axioms do
    if a ∉ allowedAxioms then return false
  return true

def Info.toFailureMode (target submission : Info)
    (allowedAxioms : Array Name) : IO (Option SafeVerifyOutcome) := do
  if cinfoKind target.constInfo ≠ cinfoKind submission.constInfo then
    return some ⟨target, submission, some <| .kind (cinfoKind target.constInfo) (cinfoKind submission.constInfo)⟩
  if cinfoKind submission.constInfo == "theorem" then
    if !equivThm target.constInfo submission.constInfo then
      return some ⟨target, submission, some .thmType⟩
  if cinfoKind submission.constInfo == "def"
      && !equivDefn target.constInfo submission.constInfo (`sorryAx ∉ target.axioms) then
    return some ⟨target, submission, some .defnCheck⟩
  if cinfoKind submission.constInfo == "opaque" && !equivOpaq target.constInfo submission.constInfo then
    return some ⟨target, submission, some .opaqueCheck⟩
  if cinfoKind submission.constInfo == "constructor" && !equivCtor target.constInfo submission.constInfo then
    return some ⟨target, submission, some .ctorCheck⟩
  if !checkAxioms submission allowedAxioms then
    return some ⟨target, submission, some .axioms⟩
  return some ⟨target, submission, none⟩

def checkTargets : SafeVerifyM Unit := do
  let settings ← getSettings
  let decls ← getDecls
  let outArray ← decls.targetDecls.toArray.mapM fun (name, targetInfo) ↦ do
    let optionInfo := decls.submissionDecls.get? targetInfo.constInfo.name
    let optionOutcome ← optionInfo.bindM
      (Info.toFailureMode targetInfo · settings.allowedAxioms)
    return (name, optionOutcome.getD (dflt := ⟨targetInfo, none, some .notFound⟩))
  modify fun s => { s with checkOutcomes := HashMap.ofArray outArray }

partial def rebuildLevel : Level → Level
  | .zero => .zero
  | .succ l => .succ (rebuildLevel l)
  | .max l1 l2 => .max (rebuildLevel l1) (rebuildLevel l2)
  | .imax l1 l2 => .imax (rebuildLevel l1) (rebuildLevel l2)
  | .param n => .param n
  | .mvar id => .mvar id

partial def rebuildExpr : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort l => .sort (rebuildLevel l)
  | .const n ls => .const n (ls.map rebuildLevel)
  | .lit (.natVal n) => .lit (.natVal n)
  | .lit (.strVal s) => .lit (.strVal s)
  | .app f a => .app (rebuildExpr f) (rebuildExpr a)
  | .lam n t b bi => .lam n (rebuildExpr t) (rebuildExpr b) bi
  | .forallE n t b bi => .forallE n (rebuildExpr t) (rebuildExpr b) bi
  | .letE n t v b nd => .letE n (rebuildExpr t) (rebuildExpr v) (rebuildExpr b) nd
  | .mdata m e => .mdata m (rebuildExpr e)
  | .proj s i e => .proj s i (rebuildExpr e)

def sanitizeConstant : ConstantInfo → ConstantInfo
  | .defnInfo d => .defnInfo { d with type := rebuildExpr d.type, value := rebuildExpr d.value }
  | .thmInfo t => .thmInfo { t with type := rebuildExpr t.type, value := rebuildExpr t.value }
  | .opaqueInfo o => .opaqueInfo { o with type := rebuildExpr o.type, value := rebuildExpr o.value }
  | ci => ci

-- Exact SafeVerify Main.lean:190-218
def replayFileWithEnv (filePath : System.FilePath) (disallowPartial : Bool)
    : IO (HashMap Name Info × Environment) := do
  let (mod, _) ← readModuleData filePath
  let env ← importModules mod.imports {} 0
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    if ci.isUnsafe then
      throw <| IO.userError s!"unsafe constant {name} detected"
    if disallowPartial && ci.isPartial && !isCompilerUnsafeRecName name then
      throw <| IO.userError s!"partial constant {name} detected"
    newConstants := newConstants.insert name (sanitizeConstant ci)
  let env ← env.replay newConstants
  for name in mod.constNames, ci in mod.constants do
    if let .thmInfo t := ci then
      let freshValue := rebuildExpr t.value
      let freshType := rebuildExpr t.type
      match Kernel.check env {} freshValue with
      | .ok inferredType =>
        match Kernel.isDefEq env {} inferredType freshType with
        | .ok true => pure ()
        | _ => throw <| IO.userError s!"kernel verification failed for '{name}': inferred type mismatch"
      | .error _ =>
        throw <| IO.userError s!"kernel verification failed for '{name}': proof term rejected"
  return (processFileDeclarations env, env)

def readImports (filePath : System.FilePath) : IO (Array Import) := do
  let (mod, _) ← readModuleData filePath
  return mod.imports

-- Exact SafeVerify Main.lean:232-254
def checkImportSuperset (targetFile submissionFile : System.FilePath)
    (targetImports submissionImports : Array Import) : IO Unit := do
  unless targetImports.any (·.module == `Init) do
    throw <| IO.userError s!"Target '{targetFile}' does not import Init."
  if submissionImports.isEmpty then
    throw <| IO.userError s!"'{submissionFile}' has no imports."
  let targetEnv ← importModules targetImports {} 0
  let submissionEnv ← importModules submissionImports {} 0
  let submissionModuleSet : Std.HashSet Name :=
    submissionEnv.header.moduleNames.foldl (init := {}) fun s n => s.insert n
  let mut missing : Array Name := #[]
  for mod in targetEnv.header.moduleNames do
    unless submissionModuleSet.contains mod do
      missing := missing.push mod
  unless missing.isEmpty do
    throw <| IO.userError s!"Submission '{submissionFile}' is missing transitive imports: {missing}"

-- Exact SafeVerify Main.lean:394-455 pipeline
def runSafeVerifyPipeline (settings : Settings) : IO (Bool × Array String) := do
  let mut logs : Array String := #[]
  let targetImports ← readImports settings.targetFile
  let submissionImports ← readImports settings.submissionFile
  checkImportSuperset settings.targetFile settings.submissionFile targetImports submissionImports
  let (targetDecls, env) ← replayFileWithEnv settings.targetFile settings.disallowPartial
  let (submissionDecls, submissionEnv) ← replayFileWithEnv settings.submissionFile settings.disallowPartial
  let mut supplementedDecls := submissionDecls
  for (name, _) in targetDecls do
    if submissionDecls.get? name |>.isNone then
      if let some ci := submissionEnv.find? name then
        if cinfoKind ci ∈ ["theorem", "def", "opaque", "inductive", "constructor"] then
          let (_, s) := (CollectAxioms.collect (fun _ _ => none) name).run submissionEnv |>.run {}
          supplementedDecls := supplementedDecls.insert name ⟨ci, s.axioms.toArray⟩
          logs := logs.push s!"Note: '{name}' found in submission's imported environment (into supplementedDecls)"
  -- Exact SafeVerify Main.lean:431-435 (note line 433 uses `submissionDecls`, discarding `supplementedDecls`)
  let decls : Decls := {
    targetDecls := targetDecls,
    submissionDecls := submissionDecls,
    env := env
  }
  let checkAction : SafeVerifyM Unit := do
    for (n, info) in (← getDecls).submissionDecls do
      if !checkAxioms info settings.allowedAxioms then
        let disallowed := info.axioms.filter (· ∉ settings.allowedAxioms)
        modify fun s => { s with axiomViolations := s.axiomViolations.push (n, disallowed) }
    checkTargets
  let (_, finalState) ← (checkAction.run settings |>.run decls |>.run {})
  for (name, outcome) in finalState.checkOutcomes do
    if let some failure := outcome.failureMode then
      logs := logs.push s!"Failure on {name}: {failure}"
  for (name, disallowed) in finalState.axiomViolations do
    logs := logs.push s!"Axiom violation on {name}: {disallowed}"
  let ok := !(finalState.checkOutcomes.any fun _ o => o.failureMode.isSome) && finalState.axiomViolations.isEmpty
  return (ok, logs)

end SafeVerifyExact

-- ============================================================================
-- Exact Corresponding Checks from Anneal's `TrustedBoundary.lean`
-- ============================================================================

namespace AnnealBoundaryCheck

-- Exact TrustedBoundary.lean:666-685
def isStructuralRecCompilerHelper (env : Environment) (ci : ConstantInfo) : Bool := Id.run do
  let .defnInfo _ := ci | return false
  let some baseName := Compiler.isUnsafeRecName? ci.name | return false
  let some baseCi := env.checked.get.find? baseName | return false
  let .defnInfo _ := baseCi | return false
  if baseCi.isUnsafe || baseCi.isPartial then return false
  return baseCi.name == baseName

-- Exact TrustedBoundary.lean:645-665
def validateLocalConstant (env : Environment) (m : Name) (ci : ConstantInfo) : Except String Unit := do
  if ci.isUnsafe then
    throw s!"unsafe declaration {ci.name} in {m}"
  if ci.isPartial && !isStructuralRecCompilerHelper env ci then
    throw s!"partial declaration {ci.name} in {m}"
  if ci matches .opaqueInfo _ then
    throw s!"opaque declaration {ci.name} in {m}"
  if ci matches .quotInfo _ then
    throw s!"unexpected quotient primitive {ci.name} in {m}"
  if ci matches .axiomInfo _ then
    throw s!"user-defined axiom {ci.name} in {m}"

-- Full-DAG non-foundation audit (TrustedBoundary.lean:675-735)
def auditNonFoundationModules (baseEnv : Environment) (modules : Array (Name × System.FilePath))
    : IO (Except String Unit) := do
  let fullEnv ← importModules (modules.map fun (n, _) => { module := n }) {} 0 (loadExts := false)
  let mut toReplay : Std.HashMap Name ConstantInfo := {}
  for (modName, oleanPath) in modules do
    let (data, _) ← readModuleData oleanPath
    unless data.constNames == data.constants.map ConstantInfo.name do
      return .error s!"invalid inventory {modName}"
    for ci in data.constants do
      if let .error e := validateLocalConstant fullEnv modName ci then
        return .error e
      if toReplay.contains ci.name then
        return .error s!"duplicate constant {ci.name}"
      toReplay := toReplay.insert ci.name ci
  try
    let _ ← baseEnv.toKernelEnv.replay toReplay
    return .ok ()
  catch e =>
    return .error s!"kernel replay failed: {e.toString}"

end AnnealBoundaryCheck

def runLeanFile (dir : System.FilePath) (leanFile : System.FilePath) (oleanFile : System.FilePath)
    : IO IO.Process.Output := do
  IO.Process.output {
    cmd := "lean"
    args := #[leanFile.toString, "-o", oleanFile.toString]
    cwd := some dir
    env := #[("LEAN_PATH", dir.toString)]
  }

public def main : IO Unit := do
  initSearchPath (← findSysroot)
  let dir : System.FilePath :=
    "/tmp/tmp_sv_bugs"
  IO.FS.createDirAll dir
  let currentPath ← searchPathRef.get
  searchPathRef.set (dir :: currentPath)
  let baseEnv ← importModules #[{ module := `Init }] {} 0 (loadExts := false)

  -- ==========================================================================
  -- BUG 1: `partial def` bypasses `SafeVerify` with `disallowPartial := true`
  -- ==========================================================================
  IO.println "=== [Probe Bug 1] `partial def` vs `SafeVerify` (`disallowPartial := true`) and `TrustedBoundary.lean` ==="
  let target1Lean := dir / "TargetBug1.lean"
  let target1Olean := dir / "TargetBug1.olean"
  let sub1Lean := dir / "SubBug1.lean"
  let sub1Olean := dir / "SubBug1.olean"

  IO.FS.writeFile target1Lean
    "def targetCompute (n : Nat) : Nat := sorry\ntheorem targetThm : targetCompute 0 = targetCompute 0 := sorry\n"
  IO.FS.writeFile sub1Lean
    "partial def diverge (n : Nat) : Nat := diverge (n + 1)\ndef targetCompute (n : Nat) : Nat := diverge n\ntheorem targetThm : targetCompute 0 = targetCompute 0 := rfl\n"

  let outT1 ← runLeanFile dir target1Lean target1Olean
  let outS1 ← runLeanFile dir sub1Lean sub1Olean
  IO.println s!"Compile TargetBug1: exit={outT1.exitCode}, SubBug1: exit={outS1.exitCode}"

  -- Inspect the exact constants emitted in `SubBug1.olean`
  let (sub1Mod, _) ← readModuleData sub1Olean
  for name in sub1Mod.constNames, ci in sub1Mod.constants do
    if name.toString.startsWith "diverge" then
      IO.println s!"  SubBug1 constant `{name}`: kind={SafeVerifyExact.cinfoKind ci}, isPartial={ci.isPartial}, isUnsafe={ci.isUnsafe}, SafeVerify.isCompilerUnsafeRecName={SafeVerifyExact.isCompilerUnsafeRecName name}"

  let (svBug1Ok, svBug1Logs) ← SafeVerifyExact.runSafeVerifyPipeline {
    targetFile := target1Olean
    submissionFile := sub1Olean
    disallowPartial := true
  }
  IO.println s!"SafeVerify (`disallowPartial := true`) result on SubBug1: passed={svBug1Ok}, logs={svBug1Logs}"

  -- Now run Anneal's `TrustedBoundary.lean` check on `SubBug1.olean`
  let sub1FullEnv ← importModules #[{ module := `SubBug1 }] {} 0 (loadExts := false)
  let mut annealBug1Errors : Array String := #[]
  for ci in sub1Mod.constants do
    if let .error e := AnnealBoundaryCheck.validateLocalConstant sub1FullEnv `SubBug1 ci then
      annealBug1Errors := annealBug1Errors.push e
  IO.println s!"Anneal TrustedBoundary.lean errors on SubBug1: {annealBug1Errors}"

  -- ==========================================================================
  -- BUG 2: Un-replayed `map₁` helper module import bypasses `SafeVerify`
  -- ==========================================================================
  IO.println "\n=== [Probe Bug 2] Un-replayed `map₁` helper module (`EvilHelper.lean`) bypass ==="
  let target2Lean := dir / "TargetBug2.lean"
  let target2Olean := dir / "TargetBug2.olean"
  let helper2Lean := dir / "EvilHelper.lean"
  let helper2Olean := dir / "EvilHelper.olean"
  let sub2Lean := dir / "SubBug2.lean"
  let sub2Olean := dir / "SubBug2.olean"

  IO.FS.writeFile target2Lean
    "theorem target_false : False := sorry\n"
  IO.FS.writeFile helper2Lean
    "import Lean\nset_option debug.skipKernelTC true\nopen Lean Elab Command in\nrun_elab do\n  let decl : Declaration := .thmDecl {\n    name := `evil_false\n    levelParams := []\n    type := .const ``False []\n    value := .const ``True.intro []\n    all := [`evil_false]\n  }\n  addDecl decl\n"
  IO.FS.writeFile sub2Lean
    "import EvilHelper\ntheorem target_false : False := evil_false\n"

  let outT2 ← runLeanFile dir target2Lean target2Olean
  let outH2 ← runLeanFile dir helper2Lean helper2Olean
  if outH2.exitCode != 0 then
    IO.println s!"EvilHelper output: {outH2.stdout}{outH2.stderr}"
  let outS2 ← runLeanFile dir sub2Lean sub2Olean
  IO.println s!"Compile TargetBug2: exit={outT2.exitCode}, EvilHelper: exit={outH2.exitCode}, SubBug2: exit={outS2.exitCode}"

  let (svBug2Ok, svBug2Logs) ← SafeVerifyExact.runSafeVerifyPipeline {
    targetFile := target2Olean
    submissionFile := sub2Olean
    disallowPartial := true
  }
  IO.println s!"SafeVerify (`disallowPartial := true`) result on SubBug2 (`theorem target_false : False`): passed={svBug2Ok}, logs={svBug2Logs}"

  let annealBug2Res ← AnnealBoundaryCheck.auditNonFoundationModules baseEnv #[
    (`EvilHelper, helper2Olean),
    (`SubBug2, sub2Olean)
  ]
  IO.println s!"Anneal TrustedBoundary.lean full-DAG audit on (EvilHelper + SubBug2): {annealBug2Res}"

  -- ==========================================================================
  -- BUG 3: `equivDefn` skips value check when `sorryAx ∈ target.axioms`
  --        AND `supplementedDecls` is discarded at `Main.lean:433`
  -- ==========================================================================
  IO.println "\n=== [Probe Bug 3] `equivDefn` `sorryAx` value-check bypass & `supplementedDecls` discard ==="
  let target3Lean := dir / "TargetBug3.lean"
  let target3Olean := dir / "TargetBug3.olean"
  let sub3Lean := dir / "SubBug3.lean"
  let sub3Olean := dir / "SubBug3.olean"

  IO.FS.writeFile target3Lean
    "def specProp : Prop := (1 = 2) ∧ (sorry : Prop)\ntheorem specHolds : specProp := sorry\n"
  IO.FS.writeFile sub3Lean
    "def specProp : Prop := True\ntheorem specHolds : specProp := True.intro\n"

  let _ ← runLeanFile dir target3Lean target3Olean
  let _ ← runLeanFile dir sub3Lean sub3Olean

  let (svBug3aOk, svBug3aLogs) ← SafeVerifyExact.runSafeVerifyPipeline {
    targetFile := target3Olean
    submissionFile := sub3Olean
    disallowPartial := true
  }
  IO.println s!"SafeVerify Bug 3a (`specProp` redefined to `True` because target mentions `sorryAx`): passed={svBug3aOk}, logs={svBug3aLogs}"

  -- Bug 3b: `supplementedDecls` computed at Main.lean:418-425 is discarded at Main.lean:433
  let helper3bLean := dir / "GoodHelper3b.lean"
  let helper3bOlean := dir / "GoodHelper3b.olean"
  let target3bLean := dir / "TargetBug3b.lean"
  let target3bOlean := dir / "TargetBug3b.olean"
  let sub3bLean := dir / "SubBug3b.lean"
  let sub3bOlean := dir / "SubBug3b.olean"

  IO.FS.writeFile helper3bLean "def helperDef : Nat := 42\n"
  IO.FS.writeFile target3bLean "def helperDef : Nat := 42\ntheorem helperThm : helperDef = 42 := sorry\n"
  IO.FS.writeFile sub3bLean "import GoodHelper3b\ntheorem helperThm : helperDef = 42 := rfl\n"

  let _ ← runLeanFile dir helper3bLean helper3bOlean
  let _ ← runLeanFile dir target3bLean target3bOlean
  let _ ← runLeanFile dir sub3bLean sub3bOlean

  let (svBug3bOk, svBug3bLogs) ← SafeVerifyExact.runSafeVerifyPipeline {
    targetFile := target3bOlean
    submissionFile := sub3bOlean
    disallowPartial := true
  }
  IO.println s!"SafeVerify Bug 3b (`supplementedDecls` discarded at Main.lean:433): passed={svBug3bOk}, logs={svBug3bLogs}"
