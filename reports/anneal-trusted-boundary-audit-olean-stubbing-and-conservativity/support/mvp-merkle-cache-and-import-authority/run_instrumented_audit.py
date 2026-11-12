#!/usr/bin/env python3
import json
import os
import subprocess
import time
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task3")
MVP_ROOT = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp")
TOOLCHAIN_ROOT = Path("<host-home>/.cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a")
LEAN_BIN = TOOLCHAIN_ROOT / "lean/bin/lean"

INSTRUMENTED_SUFFIX = """
def readProcStatus : IO Json := do
  let s ← IO.FS.readFile "/proc/self/status"
  let mut vmRss := ""
  let mut vmHwm := ""
  for line in s.splitOn "\\n" do
    if line.startsWith "VmRSS:" then vmRss := (line.drop 6).trimAscii.toString
    if line.startsWith "VmHWM:" then vmHwm := (line.drop 6).trimAscii.toString
  return Json.mkObj [("vmRss", toJson vmRss), ("vmHwm", toJson vmHwm)]

def targetAuditInstrumented (j : Json) (foundation : Array Name) : IO Json := do
  let t0 ← IO.monoNanosNow
  let rss0 ← readProcStatus
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let mut roles : Std.HashMap Name TargetOrigin := {}
  for m in foundation do roles := roles.insert m .foundation
  for m in libraries do
    if roles.contains m then fail s!"overlapping target module {m}"
    roles := roles.insert m .library
  let mut roots := foundation ++ libraries
  for item in modules do
    let m := (← field (α := String) item "module").toName
    let role ← targetRole (← field item "role")
    if roles.contains m then fail s!"overlapping target module {m}"
    roles := roles.insert m (.source role)
    roots := roots.push m
  let t_before_import1 ← IO.monoNanosNow
  let env ← importEnv j roots
  let t_after_import1 ← IO.monoNanosNow
  let rss_after_import1 ← readProcStatus
  validateGraph j env
  let t_after_validate_graph ← IO.monoNanosNow
  let provenance n := do
    let m ← origin env n
    let some role := roles.get? m | fail s!"foreign target module {m}"
    return (m, role)
  let lookup n := do
    let some ci := env.checked.get.find? n
      | fail s!"missing target dependency {n}"
    return ci
  let mut sourceInventory : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | fail s!"foreign target module {m.module}"
    if let .source _ := role then
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target inventory {m.module}"
      for ci in data.constants do
        if sourceInventory.contains ci.name then
          fail s!"duplicate target declaration {ci.name}"
        unless (← origin env ci.name) == m.module do
          fail s!"target inventory origin mismatch {ci.name}"
        let stored ← lookup ci.name
        unless stored.type == ci.type && stored.value? true == ci.value? true do
          fail s!"stored target declaration differs {ci.name}"
        sourceInventory := sourceInventory.insert ci.name
  let t_after_inventory ← IO.monoNanosNow
  let theoremName := (← field (α := String) target "theoremName").toName
  let theoremModule := (← field (α := String) target "theoremModule").toName
  let expectedName := (← field (α := String) target "expectedDeclaration").toName
  let expectedModule := (← field (α := String) target "expectedModule").toName
  match roles.get? theoremModule, roles.get? expectedModule with
  | some (.source .proof), some (.source .expected) => pure ()
  | _, _ => fail "incorrect target/expected authority roles"
  let theoremInfo ← lookup theoremName
  let expectedInfo ← lookup expectedName
  unless (← origin env theoremName) == theoremModule &&
      (← origin env expectedName) == expectedModule do
    fail "incorrect target/expected declaration origin"
  unless theoremInfo matches .thmInfo _ do fail "target root must be a theorem"
  unless expectedInfo matches .defnInfo _ do fail "Expected must be a definition"
  unless theoremInfo.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
    fail "target and Expected must have no universe parameters"
  unless expectedInfo.type == .sort .zero do fail "Expected must have type Prop"
  let canonicalRoot := (← field (α := String) target "canonicalRoot").toName
  let subjectName := (← field (α := String) target "subjectDeclaration").toName
  let specName := (← field (α := String) target "specificationDeclaration").toName
  for (n, requiredRole) in [(canonicalRoot, TargetRole.model),
      (subjectName, TargetRole.capture), (specName, TargetRole.specification)] do
    let (_, role) ← provenance n
    match role with
    | .source actual =>
      unless actual == requiredRole do fail s!"incorrect canonical input origin {n}"
    | _ => fail s!"incorrect canonical input origin {n}"
    unless (← lookup n).levelParams.isEmpty do
      fail s!"canonical input has universe parameters {n}"
  let canonical := mkApp2 (mkConst canonicalRoot) (mkConst subjectName) (mkConst specName)
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  unless axiomPolicy == #[("Classical.choice", "Init.Prelude"),
      ("Quot.sound", "Init.Prelude"), ("propext", "Init.Core")] do
    fail "target axiom policy differs from the original foundation"
  let t_before_closure1 ← IO.monoNanosNow
  let (axioms, reached) ← closure lookup (origin env) axiomPolicy
    [theoremName, expectedName, canonicalRoot, subjectName, specName]
  let t_after_closure1 ← IO.monoNanosNow
  let (_, expectedReached) ← closure lookup (origin env) axiomPolicy
    [canonicalRoot, subjectName, specName]
  let t_after_closure2 ← IO.monoNanosNow
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut byModule : Std.HashMap Name (Std.HashMap Name ConstantInfo) := {}
  let mut modelRoots : List Name := []
  let mut specRoots : List Name := []
  for n in reached do
    let ci ← lookup n
    let (modName, role) ← provenance n
    match role with
    | .foundation => pure ()
    | .library | .source _ =>
      if ci.isUnsafe || ci.isPartial then
        fail s!"unsafe/partial logical dependency {n}"
      if ci matches .quotInfo _ then fail s!"unexpected quotient primitive {n}"
      if ci.hasValue true && (ci.value? true).isNone then
        fail s!"missing stored body {n}"
      if let .source _ := role then
        unless sourceInventory.contains n do
          fail s!"uninventoried target dependency {n}"
      for dep in ← declarationEdges ci do
        let (_, depRole) ← provenance dep
        match role, depRole with
        | .source r, .source d =>
          unless r.allows d do fail s!"target authority violation {n} references {dep}"
        | .library, .source _ =>
          fail s!"installed library {n} references target source {dep}"
        | _, _ => pure ()
      replayMap := replayMap.insert n ci
      let sub := byModule.getD modName {}
      byModule := byModule.insert modName (sub.insert n ci)
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()
  let t_after_authority ← IO.monoNanosNow
  let rss_after_authority ← readProcStatus
  let base ← importEnv j foundation
  let t_after_import_base ← IO.monoNanosNow
  let rss_after_import_base ← readProcStatus
  let replayed ← try base.toKernelEnv.replay replayMap
    catch error => fail s!"kernel replay rejected target dependency: {error}"
  let t_after_replay_all ← IO.monoNanosNow
  let rss_after_replay_all ← readProcStatus
  let checkedEnv := Environment.ofKernelEnv replayed
  unless (Kernel.check checkedEnv {} canonical).toOption == some (.sort .zero) do
    fail "canonical root application must have type Prop"
  let some expectedBody := expectedInfo.value? true
    | fail "Expected has no stored body"
  unless Kernel.isDefEqGuarded checkedEnv {} expectedBody canonical do
    fail "compiled Expected body differs from the canonical root"
  match Kernel.isDefEq checkedEnv {} theoremInfo.type canonical with
  | .ok true => pure ()
  | .ok false => fail "target theorem type differs from Expected"
  | .error _ => fail "kernel could not compare target theorem type"
  let t_after_final_defeq ← IO.monoNanosNow
  let fixedMetadata ← importEnv j (foundation ++ libraries) true
  let t_after_fixed_meta ← IO.monoNanosNow
  let rss_after_fixed_meta ← readProcStatus
  let targetMetadata ← importEnv j roots true
  let t_after_target_meta ← IO.monoNanosNow
  let rss_after_target_meta ← readProcStatus
  for n in reached do
    unless Compiler.getImplementedBy? fixedMetadata n ==
        Compiler.getImplementedBy? targetMetadata n &&
        getExternAttrData? fixedMetadata n == getExternAttrData? targetMetadata n do
      fail s!"unchecked compiler override on logical dependency {n}"
    let replacement (metadata : Environment) :=
      (Compiler.CSimp.ext.getState metadata).map.find? n |>.map fun e =>
        (e.toDeclName, e.thmName)
    unless replacement fixedMetadata == replacement targetMetadata do
      fail s!"authored compiler replacement on logical dependency {n}"
  let t_after_compiler_check ← IO.monoNanosNow
  let (_, modelClosure) ← closure lookup (origin env) axiomPolicy modelRoots
  let (_, specClosure) ← closure lookup (origin env) axiomPolicy specRoots
  let t_after_closures34 ← IO.monoNanosNow
  let describe (nodes : NameSet) := nodes.toArray.qsort Name.lt |>.mapM fun n => do
    return Json.mkObj [("name", toJson n), ("module", toJson (← origin env n))]
  let modelClosureJson ← describe modelClosure
  let specClosureJson ← describe specClosure
  let t_after_describe ← IO.monoNanosNow
  let rss_after_describe ← readProcStatus

  -- Now measure staged module-by-module replay in topological order on top of base.toKernelEnv
  let mut stagedKenv := base.toKernelEnv
  let mut perModuleReplay : Array Json := #[]
  for m in env.header.modules, data in env.header.moduleData do
    let modName := m.module
    let some sub := byModule.get? modName | continue
    if sub.isEmpty then continue
    let tm0 ← IO.monoNanosNow
    stagedKenv ← stagedKenv.replay sub
    let tm1 ← IO.monoNanosNow
    let roleStr := match roles.get? modName with
      | some .foundation => "foundation"
      | some .library => "library"
      | some (.source r) =>
        match r with
        | .model => "model"
        | .capture => "capture"
        | .specification => "specification"
        | .expected => "expected"
        | .proof => "proof"
      | none => "unknown"
    let mut thmCount := 0
    let mut defnCount := 0
    let mut otherCount := 0
    for (_, ci) in sub do
      match ci with
      | .thmInfo _ => thmCount := thmCount + 1
      | .defnInfo _ => defnCount := defnCount + 1
      | _ => otherCount := otherCount + 1
    perModuleReplay := perModuleReplay.push <| Json.mkObj [
      ("module", toJson modName),
      ("role", toJson roleStr),
      ("totalModuleDecls", toJson data.constants.size),
      ("replayedDecls", toJson sub.size),
      ("replayedTheorems", toJson thmCount),
      ("replayedDefinitions", toJson defnCount),
      ("replayedOther", toJson otherCount),
      ("replayNanos", toJson (tm1 - tm0))
    ]

  -- Also measure category breakdown within ProductionSteps if present
  let mut prodStepsBreakdown : Array Json := #[]
  if let some psMap := byModule.get? `ProductionSteps then
    let mut stateDefs := 0
    let mut suffixThms := 0
    let mut otherDecls := 0
    for (n, _) in psMap do
      let s := n.toString
      if (s.splitOn "_state").length > 1 then stateDefs := stateDefs + 1
      else if (s.splitOn "_suffix").length > 1 then suffixThms := suffixThms + 1
      else otherDecls := otherDecls + 1
    prodStepsBreakdown := #[Json.mkObj [
      ("totalReplayed", toJson psMap.size),
      ("stateDefs", toJson stateDefs),
      ("suffixThms", toJson suffixThms),
      ("otherDecls", toJson otherDecls)
    ]]

  let rssSnapshots := Json.mkObj [
    ("entry", rss0),
    ("afterImportEnvRootsNoExts", rss_after_import1),
    ("afterAuthorityAndReplayMap", rss_after_authority),
    ("afterImportEnvFoundation", rss_after_import_base),
    ("afterKernelReplayAll", rss_after_replay_all),
    ("afterImportEnvFixedMetadataExts", rss_after_fixed_meta),
    ("afterImportEnvTargetMetadataExts", rss_after_target_meta),
    ("afterDescribe", rss_after_describe)
  ]

  let timings := Json.mkObj [
    ("setupRolesNanos", toJson (t_before_import1 - t0)),
    ("importEnvRootsNoExtsNanos", toJson (t_after_import1 - t_before_import1)),
    ("validateGraphNanos", toJson (t_after_validate_graph - t_after_import1)),
    ("sourceInventoryNanos", toJson (t_after_inventory - t_after_validate_graph)),
    ("sourceInventorySize", toJson sourceInventory.toList.length),
    ("rootChecksNanos", toJson (t_before_closure1 - t_after_inventory)),
    ("closureReachedNanos", toJson (t_after_closure1 - t_before_closure1)),
    ("reachedSize", toJson reached.toList.length),
    ("closureExpectedNanos", toJson (t_after_closure2 - t_after_closure1)),
    ("expectedReachedSize", toJson expectedReached.toList.length),
    ("authorityAndReplayMapNanos", toJson (t_after_authority - t_after_closure2)),
    ("replayMapSize", toJson replayMap.size),
    ("importEnvFoundationNanos", toJson (t_after_import_base - t_after_authority)),
    ("kernelReplayAllNanos", toJson (t_after_replay_all - t_after_import_base)),
    ("kernelFinalDefEqNanos", toJson (t_after_final_defeq - t_after_replay_all)),
    ("importEnvFixedMetadataExtsNanos", toJson (t_after_fixed_meta - t_after_final_defeq)),
    ("importEnvTargetMetadataExtsNanos", toJson (t_after_target_meta - t_after_fixed_meta)),
    ("compilerOverrideCheckNanos", toJson (t_after_compiler_check - t_after_target_meta)),
    ("closureModelAndSpecNanos", toJson (t_after_closures34 - t_after_compiler_check)),
    ("describeJsonNanos", toJson (t_after_describe - t_after_closures34)),
    ("totalTargetAuditBodyNanos", toJson (t_after_describe - t0)),
    ("rssSnapshots", rssSnapshots),
    ("perModuleReplay", .arr perModuleReplay),
    ("productionStepsBreakdown", .arr prodStepsBreakdown)
  ]

  return Json.mkObj [("theorem", toJson theoremName),
    ("canonicalRoot", toJson canonicalRoot), ("subject", toJson subjectName),
    ("specification", toJson specName), ("graph", graph env),
    ("expected", toJson expectedName), ("axioms", toJson axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson replayMap.size),
    ("modelClosure", .arr modelClosureJson),
    ("specificationClosure", .arr specClosureJson),
    ("instrumentedTimings", timings)]
"""

def main():
    work = SCRATCH / "profile_stage"
    orig_tb = (MVP_ROOT / "trusted/audit/TrustedBoundary.lean").read_text()
    # Insert targetAuditInstrumented before `def run` and call it in `"target-audit"`
    target_marker = "/-- Dispatch a repository or target inspection request. -/"
    assert target_marker in orig_tb
    patched = orig_tb.replace(
        target_marker,
        INSTRUMENTED_SUFFIX + "\n" + target_marker,
    ).replace(
        '| "target-audit" => targetAudit j foundation',
        '| "target-audit" => targetAuditInstrumented j foundation',
    )
    inst_path = work / "TrustedBoundaryInstrumented.lean"
    inst_path.write_text(patched)

    clean_env = {
        "HOME": os.environ.get("HOME", "/root"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "PATH": f"{os.path.expanduser('~/.local/bin')}:/usr/bin:/bin",
    }
    audit_req_path = work / "request-target-audit.json"
    audit_res_path = work / "request-target-audit-instrumented.result.json"

    t0 = time.perf_counter()
    res = subprocess.run([
        "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
        str(LEAN_BIN), "-j1", "-M2048", "--run",
        str(inst_path), str(audit_req_path), str(audit_res_path)
    ], cwd=work, env=clean_env, capture_output=True, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    if res.returncode != 0:
        raise RuntimeError(f"Instrumented audit failed:\nstdout: {res.stdout}\nstderr: {res.stderr}")

    out_json = json.loads(audit_res_path.read_text())
    timings = out_json["result"]["instrumentedTimings"]
    timings["outerProcessWallMs"] = wall_ms
    (SCRATCH / "instrumented_audit_timings.json").write_text(json.dumps(timings, indent=2))
    print(json.dumps(timings, indent=2))

if __name__ == "__main__":
    main()
