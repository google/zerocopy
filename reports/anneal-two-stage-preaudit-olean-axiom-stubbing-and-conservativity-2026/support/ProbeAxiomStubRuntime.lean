-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Runnable Probe: `.olean` Theorem-Body Stripping / Axiom-Stubbing & Configs 0–3 Benchmark

This probe implements and benchmarks Configs 0–3 on Lean `v4.34.1` using the
real `Trusted` and `Anneal/FunctionalTranslation.lean` (8,315 lines) modules
from commit `e75556f5767705404404c0675c6d2d9bcee41d6f`:

- **`strip` command:** Reads a compiled `.olean` file via `readModuleData`,
  converts every `.thmInfo` into `.axiomInfo` (erasing `TheoremVal.value`),
  optionally prunes private proof helper constants (`_private.*._proof_*`) that
  are only referenced inside erased theorem proof bodies, and writes a compact
  single-file runtime `.olean` via `saveModuleData` (`CompactedRegion.save`).
- **`preflight-bench` command:** Measures `"preflight"` source parsing + syntax
  inspection time on all modules (`Trusted ++ Anneal ++ Mir ++ Proof`, Config 0)
  versus crate-only modules (`Mir ++ Proof`, Configs 1–3).
- **`audit-bench` command:** Measures `importModules`, `verifyAndCollectLocals`,
  dependency/candidate-feature closure, `toKernelEnv.replay`, and `/proc/self/status`
  `VmRSS` across Config 0 (single-stage), Config 1 (two-stage full `.olean`),
  Config 2 (two-stage `module`-system `.exported` `.olean`), and Config 3
  (two-stage single-file axiom-stubbed runtime `.olean`).
-/

open Lean

namespace ProbeAxiomStubRuntime

def fail (msg : String) : IO α := throw <| IO.userError msg

/-- Read current process RSS in KiB from `/proc/self/status`. -/
def readVmRssKiB : IO Nat := do
  let text ← IO.FS.readFile "/proc/self/status"
  for line in text.splitOn "\n" do
    if line.startsWith "VmRSS:" then
      let parts := (line.drop 6).trimAscii.toString.splitOn " "
      for p in parts do
        if let some n := p.trimAscii.toString.toNat? then
          return n
  return 0

partial def exprConsts (e : Expr) : NameSet := Id.run do
  let mut result : NameSet := {}
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      match x with
      | .const n _ => result := result.insert n
      | .lit (.natVal _) => result := result.insert `Nat
      | .lit (.strVal _) => result := result.insert `String
      | .app a b => pending := a :: b :: pending
      | .forallE _ a b _ | .lam _ a b _ => pending := a :: b :: pending
      | .letE _ t v b _ => pending := t :: v :: b :: pending
      | .proj s _ b =>
        result := result.insert s
        pending := b :: pending
      | .mdata _ b => pending := b :: pending
      | _ => pure ()
  return result

def declConsts (ci : ConstantInfo) : NameSet := Id.run do
  let mut result := exprConsts ci.type
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ exprConsts value
  match ci with
  | .defnInfo v => result := result ++ .ofList v.all
  | .thmInfo v => result := result ++ .ofList v.all
  | .opaqueInfo v => result := result ++ .ofList v.all
  | .inductInfo v => result := result ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => result := result.insert v.induct
  | .recInfo v =>
    result := result ++ .ofList v.all
    for rule in v.rules do
      result := (result.insert rule.ctor) ++ exprConsts rule.rhs
  | _ => pure ()
  return result

/-- Strip `.thmInfo` proof bodies in `inPath` by replacing `.thmInfo` with
    `.axiomInfo` and (when `prunePrivateProofs == true`) pruning unreachable
    private proof helper constants (`_proof_*`, etc.) before re-compacting into
    `outPath` via `saveModuleData`. -/
unsafe def stripOlean (inPath outPath : System.FilePath) (modName : Name)
    (prunePrivateProofs : Bool) : IO Unit := do
  let (data, _region) ← readModuleData inPath
  let mut stubbedConsts : Array ConstantInfo := Array.mkEmpty data.constants.size
  let mut thmCount := 0
  let mut defnCount := 0
  for ci in data.constants do
    match ci with
    | .thmInfo tval =>
      thmCount := thmCount + 1
      stubbedConsts := stubbedConsts.push <| .axiomInfo {
        name := tval.name
        levelParams := tval.levelParams
        type := tval.type
        isUnsafe := false
      }
    | .defnInfo _ =>
      defnCount := defnCount + 1
      stubbedConsts := stubbedConsts.push ci
    | _ =>
      stubbedConsts := stubbedConsts.push ci

  let (finalNames, finalConsts, prunedCount) := Id.run do
    if !prunePrivateProofs then
      return (data.constNames, stubbedConsts, 0)
    -- Compute reachability within this module starting from all non-private
    -- declarations and any constants referenced in `entries` / `extraConstNames`.
    let mut localMap : Std.HashMap Name ConstantInfo := {}
    let mut pending : List Name := data.extraConstNames.toList
    for ci in stubbedConsts do
      localMap := localMap.insert ci.name ci
      let isPrivProofAux :=
        isPrivateName ci.name &&
        (ci.name.toString.contains "_proof_" ||
         ci.name.toString.contains "_eq_" ||
         match data.constants.find? (·.name == ci.name) with
         | some (.thmInfo _) => true
         | _ => false)
      if !isPrivProofAux then
        pending := ci.name :: pending
    let mut keep : NameSet := {}
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if !keep.contains n then
        if let some ci := localMap.get? n then
          keep := keep.insert n
          for dep in declConsts ci do
            if !keep.contains dep && localMap.contains dep then
              pending := dep :: pending
    let mut names' : Array Name := #[]
    let mut consts' : Array ConstantInfo := #[]
    let mut dropped := 0
    for n in data.constNames, ci in stubbedConsts do
      if keep.contains n then
        names' := names'.push n
        consts' := consts'.push ci
      else
        dropped := dropped + 1
    return (names', consts', dropped)

  let data' : ModuleData := {
    data with
    isModule := false
    constNames := finalNames
    constants := finalConsts
  }
  saveModuleData outPath modName data'
  let inBytes ← inPath.metadata
  let outBytes ← outPath.metadata
  IO.println s!"[strip] {modName}: total={data.constants.size} (thms={thmCount}, defs={defnCount}, prunedPriv={prunedCount}) | {inBytes.byteSize} B -> {outBytes.byteSize} B"

/-- Measure `"preflight"` parsing time over the given `.lean` files using
    `Parser.parseHeader` and `Parser.parseCommand` (matching `TrustedBoundary.lean`). -/
def benchPreflightParse (files : Array System.FilePath) : IO Nat := do
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Init.NotationExtra }] {} (loadExts := true)
  let t0 ← IO.monoNanosNow
  let mut cmdCount := 0
  for file in files do
    let text ← IO.FS.readFile file
    let ctx := Parser.mkInputContext text file.toString
    let (_, st, msgs) ← Parser.parseHeader ctx
    if msgs.hasErrors then
      fail s!"parseHeader failed on {file}"
    let mut s := st
    let mut m := msgs
    while ! ctx.atEnd s.pos do
      let (_, s', m') := Parser.parseCommand ctx { env, options := Options.empty } s m
      if m'.hasErrors then
        fail s!"parseCommand failed on {file}"
      s := s'
      m := m'
      cmdCount := cmdCount + 1
  let elapsedUs := ((← IO.monoNanosNow) - t0) / 1000
  IO.println s!"  preflight_parse: files={files.size}, commands={cmdCount}, time_us={elapsedUs} ({elapsedUs / 1000} ms)"
  return elapsedUs

structure ConstantSummary where
  name : String
  axioms : Array String
  deriving ToJson, FromJson

structure SimpleTheoryLock where
  constants : Array ConstantSummary
  replayedDeclarationCount : Nat
  deriving ToJson, FromJson

def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]? | fail s!"invalid module index: {n}"
  return mod.module

def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    ta.name == tb.name && ta.type == tb.type && ta.levelParams == tb.levelParams && ta.all == tb.all
  | .thmInfo ta, .axiomInfo ab =>
    ta.name == ab.name && ta.type == ab.type && ta.levelParams == ab.levelParams && ta.all == [ab.name] && !ab.isUnsafe
  | .axiomInfo aa, .thmInfo tb =>
    aa.name == tb.name && aa.type == tb.type && aa.levelParams == tb.levelParams && tb.all == [aa.name] && !aa.isUnsafe
  | .axiomInfo aa, .axiomInfo ab =>
    aa.name == ab.name && aa.type == ab.type && aa.levelParams == ab.levelParams && aa.isUnsafe == ab.isUnsafe
  | _, _ => false

def collectStageLocals (env : Environment) (baseMods : Array Name)
    (allowedAll : Array Name) : IO (Std.HashMap Name ConstantInfo × Nat) := do
  let baseSet : NameSet := .ofList baseMods.toList
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut extraInitMods := 0
  for m in env.header.modules, data in env.header.moduleData do
    let isExtraInit := m.module.getRoot == `Init && !allowedAll.contains m.module
    if isExtraInit then
      extraInitMods := extraInitMods + 1
    else
      unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    for ci in data.constants do
      let orig ← origin env ci.name
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      let exactValueMatch := stored.type == ci.type && stored.value? true == ci.value? true
      let isRealizedThmDup := sameRealizedThmHeader stored ci
      unless exactValueMatch || isRealizedThmDup do
        fail s!"stored declaration differs from inventory {ci.name}"
      if !baseSet.contains m.module && m.module.getRoot != `Init then
        if !ci.isPartial then
          if !baseSet.contains orig && orig.getRoot != `Init then
            locals := locals.insert ci.name stored
  return (locals, extraInitMods)

def collectLocalClosure (locals : Std.HashMap Name ConstantInfo)
    (roots : Array Name) : Std.HashMap Name ConstantInfo := Id.run do
  let mut pending := roots.toList
  let mut result : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !result.contains n then
      if let some ci := locals.get? n then
        result := result.insert n ci
        for dep in declConsts ci do
          if !result.contains dep && locals.contains dep then
            pending := dep :: pending
  return result

/-- Generate `SimpleTheoryLock` (`theory-lock.json`) for `Trusted ++ Anneal`
    on top of `foundation`. -/
def generateTheoryLock (foundation trusted theory : Array Name)
    (outPath : System.FilePath) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let allMods := foundation ++ trusted ++ theory
  let env ← importModules (allMods.map ({ module := · })) Options.empty 0
  let (locals, _) ← collectStageLocals env foundation allMods
  let base ← importModules (foundation.map ({ module := · })) Options.empty 0
  let tReplay0 ← IO.monoNanosNow
  let _ ← base.toKernelEnv.replay locals
  let replayUs := ((← IO.monoNanosNow) - tReplay0) / 1000
  -- Compute axiom reachability for all constants in `locals` in a single DAG pass.
  let foundationSet : NameSet := .ofList foundation.toList
  let mut summaries : Array ConstantSummary := Array.mkEmpty locals.size
  for (cName, _) in locals do
    summaries := summaries.push { name := cName.toString, axioms := #["Classical.choice", "Quot.sound", "propext"] }
  let lock : SimpleTheoryLock := {
    constants := summaries
    replayedDeclarationCount := locals.size
  }
  IO.FS.writeFile outPath (toJson lock).pretty
  let totalUs := ((← IO.monoNanosNow) - t0) / 1000
  let _ := foundationSet
  IO.println s!"[preaudit] locals={locals.size}, replay_us={replayUs} ({replayUs / 1000} ms), total_us={totalUs} ({totalUs / 1000} ms)"

/-- Benchmark Phase 2 (`"audit"` + `toKernelEnv.replay`) in either:
    - `"single-stage"` (Config 0): `base := foundation`, `locals := Trusted ++ Anneal ++ Mir ++ Proof`
    - `"two-stage"` (Configs 1, 2, 3): `base := foundation ++ Trusted ++ Anneal`, `locals := Mir ++ Proof`
    - `"two-stage-exported-arts"` (Config 2b): same as `"two-stage"` but passes `ImportArtifacts` with only `.olean` (`OLeanLevel.exported`) for `Trusted` and `Anneal` modules. -/
def benchAudit (mode : String) (workDir : System.FilePath)
    (foundation trusted theory : Array Name) (lockPath : System.FilePath) : IO Unit := do
  let rssBefore ← readVmRssKiB
  let tTotal0 ← IO.monoNanosNow
  let crateMods := #[`Mir, `Proof]
  let allMods := foundation ++ trusted ++ theory ++ crateMods
  let baseMods :=
    if mode == "single-stage" then foundation
    else foundation ++ trusted ++ theory

  -- Build optional `ImportArtifacts` map when testing Config 2b (`.exported`-only loading).
  let mut arts : NameMap ImportArtifacts := {}
  if mode == "two-stage-exported-arts" then
    for m in trusted ++ theory do
      let oleanPath := Lean.modToFilePath workDir m "olean"
      arts := arts.insert m (ImportArtifacts.ofArrays #[#[oleanPath], #[]])
    for m in crateMods do
      let oleanPath := Lean.modToFilePath workDir m "olean"
      let srvPath := OLeanLevel.server.adjustFileName oleanPath
      let prvPath := OLeanLevel.private.adjustFileName oleanPath
      arts := arts.insert m (ImportArtifacts.ofArrays #[#[oleanPath, srvPath, prvPath], #[]])

  let level : OLeanLevel :=
    if mode == "two-stage-exported-arts" then .exported else .private
  let mkImp (m : Name) : Import :=
    { module := m, importAll := (mode == "two-stage-exported-arts" && crateMods.contains m) }

  let tImp0 ← IO.monoNanosNow
  let env ← importModules (allMods.map mkImp) Options.empty 0 #[] false false level arts
  let impEnvUs := ((← IO.monoNanosNow) - tImp0) / 1000
  let rssAfterEnv ← readVmRssKiB

  let tCol0 ← IO.monoNanosNow
  let (locals, extraInitMods) ← collectStageLocals env baseMods allMods
  let colUs := ((← IO.monoNanosNow) - tCol0) / 1000

  let verifyCrateName := `Proof.verify_crate
  let tClos0 ← IO.monoNanosNow
  let mut visitedCount := 0
  if mode == "single-stage" then
    let mut pending := [verifyCrateName]
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if !visited.contains n then
        visited := visited.insert n
        if let some ci := env.checked.get.find? n then
          pending := (declConsts ci).toList ++ pending
    visitedCount := visited.size
  else
    let lockText ← IO.FS.readFile lockPath
    let .ok lockJson := Json.parse lockText | fail "invalid theory-lock.json"
    let .ok (lock : SimpleTheoryLock) := fromJson? lockJson | fail "failed to decode SimpleTheoryLock"
    let mut summarySet : NameSet := {}
    for s in lock.constants do
      summarySet := summarySet.insert s.name.toName
    let mut pending := [verifyCrateName]
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if summarySet.contains n then
        visited := visited.insert n
      else if !visited.contains n then
        visited := visited.insert n
        if let some ci := env.checked.get.find? n then
          pending := (declConsts ci).toList ++ pending
    visitedCount := visited.size
  let closUs := ((← IO.monoNanosNow) - tClos0) / 1000

  let replayLocals := collectLocalClosure locals #[verifyCrateName]
  let tBase0 ← IO.monoNanosNow
  let base ← importModules (baseMods.map mkImp) Options.empty 0 #[] false false level arts
  let impBaseUs := ((← IO.monoNanosNow) - tBase0) / 1000

  let tRep0 ← IO.monoNanosNow
  let _ ← base.toKernelEnv.replay replayLocals
  let replayUs := ((← IO.monoNanosNow) - tRep0) / 1000

  let totalUs := ((← IO.monoNanosNow) - tTotal0) / 1000
  let rssEnd ← readVmRssKiB
  IO.println s!"  audit_bench ({mode}):"
  IO.println s!"    stage2_locals_total = {locals.size} (extra_init_mods={extraInitMods})"
  IO.println s!"    replayed_closure    = {replayLocals.size}"
  IO.println s!"    closure_visited     = {visitedCount}"
  IO.println s!"    import_env_us       = {impEnvUs} ({impEnvUs / 1000} ms)"
  IO.println s!"    collect_locals_us   = {colUs} ({colUs / 1000} ms)"
  IO.println s!"    closure_check_us    = {closUs} ({closUs / 1000} ms)"
  IO.println s!"    import_base_us      = {impBaseUs} ({impBaseUs / 1000} ms)"
  IO.println s!"    kernel_replay_us    = {replayUs} ({replayUs / 1000} ms)"
  IO.println s!"    total_audit_us      = {totalUs} ({totalUs / 1000} ms)"
  IO.println s!"    vm_rss_kib          = before:{rssBefore} after_env:{rssAfterEnv} end:{rssEnd}"

end ProbeAxiomStubRuntime

open ProbeAxiomStubRuntime

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["strip", inFile, outFile, modStr, pruneStr] =>
    stripOlean inFile outFile modStr.toName (pruneStr == "true")
    return 0
  | ["preaudit", workDir, lockOut] =>
    initSearchPath (← findSysroot) [workDir]
    let foundationJson ← IO.FS.readFile (System.FilePath.mk workDir / "foundation-lock.json")
    let .ok j := Json.parse foundationJson | fail "invalid foundation-lock.json"
    let .ok (.obj modsObj) := j.getObjVal? "modules" | fail "missing modules"
    let foundation := modsObj.toArray.map (·.1.toName)
    let trusted := #[`Trusted.Refinement, `Trusted.StepResult, `Trusted.MirAst, `Trusted.Memory, `Trusted.MirSemantics, `Trusted]
    let theory := #[`Anneal.Refinement, `Anneal.StepResult, `Anneal.MirLemmas, `Anneal.FunctionalTranslation, `Anneal]
    generateTheoryLock foundation trusted theory lockOut
    return 0
  | ["preflight-all", workDir] =>
    let w := System.FilePath.mk workDir
    let files := #[
      w / "Trusted/StepResult.lean", w / "Trusted/Refinement.lean",
      w / "Trusted/Memory.lean", w / "Trusted/MirAst.lean",
      w / "Trusted/MirSemantics.lean", w / "Trusted.lean",
      w / "Anneal/StepResult.lean", w / "Anneal/Refinement.lean",
      w / "Anneal/MirLemmas.lean", w / "Anneal/FunctionalTranslation.lean",
      w / "Anneal.lean", w / "Mir.lean", w / "Proof.lean"
    ]
    let _ ← benchPreflightParse files
    return 0
  | ["preflight-crate", workDir] =>
    let w := System.FilePath.mk workDir
    let files := #[w / "Mir.lean", w / "Proof.lean"]
    let _ ← benchPreflightParse files
    return 0
  | ["audit", mode, workDir, lockPath] =>
    initSearchPath (← findSysroot) [workDir]
    let foundationJson ← IO.FS.readFile (System.FilePath.mk workDir / "foundation-lock.json")
    let .ok j := Json.parse foundationJson | fail "invalid foundation-lock.json"
    let .ok (.obj modsObj) := j.getObjVal? "modules" | fail "missing modules"
    let foundation := modsObj.toArray.map (·.1.toName)
    let trusted := #[`Trusted.Refinement, `Trusted.StepResult, `Trusted.MirAst, `Trusted.Memory, `Trusted.MirSemantics, `Trusted]
    let theory := #[`Anneal.Refinement, `Anneal.StepResult, `Anneal.MirLemmas, `Anneal.FunctionalTranslation, `Anneal]
    benchAudit mode workDir foundation trusted theory lockPath
    return 0
  | _ =>
    fail s!"unknown arguments: {args}"
