#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Benchmark Q-C2 Part 2: Environment loading & memory optimization in
TrustedBoundary.lean targetAudit:
  1. baseline_4env: Unmodified 4-Env in single scope (env, base, fixedMetadata, targetMetadata all live)
  2. scoped_sequential_4env: Preserves loadExts=false first, drops env before metadata check, drops metadata before replay
  3. reused_target_metadata_3env: Reuses targetMetadata (importEnv j roots true) for graph/closure + override check, drops before replay
Tested under both `lean --run` and native `leanc -O3 -rdynamic`."""

import json
from pathlib import Path
import re
import shutil
import subprocess
import time

HOME = Path.home()
TOOLCHAIN_BIN = (
    HOME
    / ".cache/anneal/toolchain"
    / "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a/lean/bin"
)
LEAN = str(TOOLCHAIN_BIN / "lean")
LEANC = str(TOOLCHAIN_BIN / "leanc")
BRAIN_ROOT = HOME / "<scratch-dir>"
STAGE_SRC = BRAIN_ROOT / "scratch/mvp-investigations/task3/profile_stage"
MVP_BASELINE = BRAIN_ROOT / "scratch/reference-research/mvp-baseline"
TRACK_C_DIR = BRAIN_ROOT / "scratch/reference-research/track_c"
WORK_DIR = TRACK_C_DIR / "env_opt_stage"

OPT_LEAN_DEFS = """
instance : ToString TargetRole where
  toString
    | .model => "model"
    | .specification => "specification"
    | .capture => "capture"
    | .expected => "expected"
    | .proof => "proof"

def readVmStats : IO (Nat × Nat) := do
  let s ← IO.FS.readFile "/proc/self/status"
  let mut rssKb := 0
  let mut hwmKb := 0
  for line in s.splitOn "\\n" do
    if line.startsWith "VmRSS:" then
      let digits := ((line.drop 6).trimAscii.toString.splitOn " ").headD "0"
      rssKb := digits.toNat?.getD 0
    if line.startsWith "VmHWM:" then
      let digits := ((line.drop 6).trimAscii.toString.splitOn " ").headD "0"
      hwmKb := digits.toNat?.getD 0
  return (rssKb, hwmKb)

structure TargetPlan where
  roots : Array Name
  libraries : Array Name
  reached : NameSet
  replayMap : Std.HashMap Name ConstantInfo
  canonical : Expr
  expectedBody : Expr
  theoremType : Expr
  theoremName : Name
  canonicalRoot : Name
  subjectName : Name
  specName : Name
  expectedName : Name
  graphJson : Json
  axioms : Array Name
  modelClosureJson : Array Json
  specClosureJson : Array Json

@[noinline]
def buildTargetPlan (j : Json) (foundation : Array Name) (loadExtsOnFirst : Bool)
    (useImportedEntriesOnly : Bool := false) :
    IO TargetPlan := do
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
  let env ← importEnv j roots loadExtsOnFirst
  validateGraph j env
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
    for imp in data.imports do
      let some impRole := roles.get? imp.module
        | fail s!"foreign target module {imp.module}"
      match role, impRole with
      | .source r, .source d =>
        unless r.allows d do
          fail s!"target import authority violation {m.module} ({r}) imports {imp.module} ({d})"
      | .library, .source _ =>
        fail s!"installed library {m.module} imports target source {imp.module}"
      | .foundation, .library | .foundation, .source _ =>
        fail s!"foundation module {m.module} imports non-foundation {imp.module}"
      | _, _ => pure ()
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
  let some expectedBody := expectedInfo.value? true
    | fail "Expected has no stored body"
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
  let (axioms, reached) ← closure lookup (origin env) axiomPolicy
    [theoremName, expectedName, canonicalRoot, subjectName, specName]
  let (_, expectedReached) ← closure lookup (origin env) axiomPolicy
    [canonicalRoot, subjectName, specName]
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut modelRoots : List Name := []
  let mut specRoots : List Name := []
  for n in reached do
    let ci ← lookup n
    let (_, role) ← provenance n
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
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()
  if loadExtsOnFirst then
    if useImportedEntriesOnly then
      let implEntries := (Compiler.implementedByAttr.ext.toEnvExtension.getState env).importedEntries
      let extEntries := (externAttr.ext.toEnvExtension.getState env).importedEntries
      let csimpEntries := (Compiler.CSimp.ext.ext.toEnvExtension.getState env).importedEntries
      for idx in [:env.header.modules.size] do
        let m := env.header.modules[idx]!
        if let some (.source _) := roles.get? m.module then
          unless (implEntries[idx]?.map Array.isEmpty |>.getD true) &&
              (extEntries[idx]?.map Array.isEmpty |>.getD true) do
            fail s!"unchecked compiler override in target module {m.module}"
          unless (csimpEntries[idx]?.map Array.isEmpty |>.getD true) do
            fail s!"authored compiler replacement in target module {m.module}"
    else
      let fixedMetadata ← importEnv j (foundation ++ libraries) true
      for n in reached do
        unless Compiler.getImplementedBy? fixedMetadata n ==
            Compiler.getImplementedBy? env n &&
            getExternAttrData? fixedMetadata n == getExternAttrData? env n do
          fail s!"unchecked compiler override on logical dependency {n}"
        let replacement (metadata : Environment) :=
          (Compiler.CSimp.ext.getState metadata).map.find? n |>.map fun e =>
            (e.toDeclName, e.thmName)
        unless replacement fixedMetadata == replacement env do
          fail s!"authored compiler replacement on logical dependency {n}"
  let (_, modelClosure) ← closure lookup (origin env) axiomPolicy modelRoots
  let (_, specClosure) ← closure lookup (origin env) axiomPolicy specRoots
  let describe (nodes : NameSet) := nodes.toArray.qsort Name.lt |>.mapM fun n => do
    return Json.mkObj [("name", toJson n), ("module", toJson (← origin env n))]
  let modelClosureJson ← describe modelClosure
  let specClosureJson ← describe specClosure
  let graphJson := graph env
  return {
    roots, libraries, reached, replayMap, canonical, expectedBody,
    theoremType := theoremInfo.type, theoremName, canonicalRoot,
    subjectName, specName, expectedName, graphJson, axioms,
    modelClosureJson, specClosureJson
  }

@[noinline]
def checkCompilerOverridesSeparate (j : Json) (foundation : Array Name)
    (plan : TargetPlan) : IO Unit := do
  let fixedMetadata ← importEnv j (foundation ++ plan.libraries) true
  let targetMetadata ← importEnv j plan.roots true
  for n in plan.reached do
    unless Compiler.getImplementedBy? fixedMetadata n ==
        Compiler.getImplementedBy? targetMetadata n &&
        getExternAttrData? fixedMetadata n == getExternAttrData? targetMetadata n do
      fail s!"unchecked compiler override on logical dependency {n}"
    let replacement (metadata : Environment) :=
      (Compiler.CSimp.ext.getState metadata).map.find? n |>.map fun e =>
        (e.toDeclName, e.thmName)
    unless replacement fixedMetadata == replacement targetMetadata do
      fail s!"authored compiler replacement on logical dependency {n}"

@[noinline]
def replayAndCheckKernel (j : Json) (foundation : Array Name)
    (plan : TargetPlan) : IO Unit := do
  let base ← importEnv j foundation
  let replayed ← try base.toKernelEnv.replay plan.replayMap
    catch error => fail s!"kernel replay rejected target dependency: {error}"
  let checkedEnv := Environment.ofKernelEnv replayed
  unless (Kernel.check checkedEnv {} plan.canonical).toOption == some (.sort .zero) do
    fail "canonical root application must have type Prop"
  unless Kernel.isDefEqGuarded checkedEnv {} plan.expectedBody plan.canonical do
    fail "compiled Expected body differs from the canonical root"
  match Kernel.isDefEq checkedEnv {} plan.theoremType plan.canonical with
  | .ok true => pure ()
  | .ok false => fail "target theorem type differs from Expected"
  | .error _ => fail "kernel could not compare target theorem type"

def targetAuditScoped4Env (j : Json) (foundation : Array Name) : IO Json := do
  let t0 ← IO.monoNanosNow
  let plan ← buildTargetPlan j foundation false
  let t1 ← IO.monoNanosNow
  let (rssAfterPlan, hwmAfterPlan) ← readVmStats
  checkCompilerOverridesSeparate j foundation plan
  let t2 ← IO.monoNanosNow
  let (rssAfterMeta, hwmAfterMeta) ← readVmStats
  replayAndCheckKernel j foundation plan
  let t3 ← IO.monoNanosNow
  let (rssAfterReplay, hwmAfterReplay) ← readVmStats
  let stats := Json.mkObj [
    ("planMs", toJson ((t1 - t0).toFloat / 1000000.0)),
    ("metaOverrideMs", toJson ((t2 - t1).toFloat / 1000000.0)),
    ("replayMs", toJson ((t3 - t2).toFloat / 1000000.0)),
    ("totalBodyMs", toJson ((t3 - t0).toFloat / 1000000.0)),
    ("rssAfterPlanKb", toJson rssAfterPlan),
    ("hwmAfterPlanKb", toJson hwmAfterPlan),
    ("rssAfterMetaKb", toJson rssAfterMeta),
    ("hwmAfterMetaKb", toJson hwmAfterMeta),
    ("rssAfterReplayKb", toJson rssAfterReplay),
    ("hwmAfterReplayKb", toJson hwmAfterReplay)
  ]
  return Json.mkObj [("theorem", toJson plan.theoremName),
    ("canonicalRoot", toJson plan.canonicalRoot), ("subject", toJson plan.subjectName),
    ("specification", toJson plan.specName), ("graph", plan.graphJson),
    ("expected", toJson plan.expectedName), ("axioms", toJson plan.axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson plan.replayMap.size),
    ("modelClosure", .arr plan.modelClosureJson),
    ("specificationClosure", .arr plan.specClosureJson),
    ("optStats", stats)]

def targetAuditReused3Env (j : Json) (foundation : Array Name) : IO Json := do
  let t0 ← IO.monoNanosNow
  let plan ← buildTargetPlan j foundation true
  let t1 ← IO.monoNanosNow
  let (rssAfterPlan, hwmAfterPlan) ← readVmStats
  replayAndCheckKernel j foundation plan
  let t2 ← IO.monoNanosNow
  let (rssAfterReplay, hwmAfterReplay) ← readVmStats
  let stats := Json.mkObj [
    ("planAndMetaMs", toJson ((t1 - t0).toFloat / 1000000.0)),
    ("replayMs", toJson ((t2 - t1).toFloat / 1000000.0)),
    ("totalBodyMs", toJson ((t2 - t0).toFloat / 1000000.0)),
    ("rssAfterPlanKb", toJson rssAfterPlan),
    ("hwmAfterPlanKb", toJson hwmAfterPlan),
    ("rssAfterReplayKb", toJson rssAfterReplay),
    ("hwmAfterReplayKb", toJson hwmAfterReplay)
  ]
  return Json.mkObj [("theorem", toJson plan.theoremName),
    ("canonicalRoot", toJson plan.canonicalRoot), ("subject", toJson plan.subjectName),
    ("specification", toJson plan.specName), ("graph", plan.graphJson),
    ("expected", toJson plan.expectedName), ("axioms", toJson plan.axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson plan.replayMap.size),
    ("modelClosure", .arr plan.modelClosureJson),
    ("specificationClosure", .arr plan.specClosureJson),
    ("optStats", stats)]

def targetAuditSingle2Env (j : Json) (foundation : Array Name) : IO Json := do
  let t0 ← IO.monoNanosNow
  let plan ← buildTargetPlan j foundation true true
  let t1 ← IO.monoNanosNow
  let (rssAfterPlan, hwmAfterPlan) ← readVmStats
  replayAndCheckKernel j foundation plan
  let t2 ← IO.monoNanosNow
  let (rssAfterReplay, hwmAfterReplay) ← readVmStats
  let stats := Json.mkObj [
    ("planAndMetaMs", toJson ((t1 - t0).toFloat / 1000000.0)),
    ("replayMs", toJson ((t2 - t1).toFloat / 1000000.0)),
    ("totalBodyMs", toJson ((t2 - t0).toFloat / 1000000.0)),
    ("rssAfterPlanKb", toJson rssAfterPlan),
    ("hwmAfterPlanKb", toJson hwmAfterPlan),
    ("rssAfterReplayKb", toJson rssAfterReplay),
    ("hwmAfterReplayKb", toJson hwmAfterReplay)
  ]
  return Json.mkObj [("theorem", toJson plan.theoremName),
    ("canonicalRoot", toJson plan.canonicalRoot), ("subject", toJson plan.subjectName),
    ("specification", toJson plan.specName), ("graph", plan.graphJson),
    ("expected", toJson plan.expectedName), ("axioms", toJson plan.axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson plan.replayMap.size),
    ("modelClosure", .arr plan.modelClosureJson),
    ("specificationClosure", .arr plan.specClosureJson),
    ("optStats", stats)]
"""


def run_timed(cmd, cwd):
  wrapped = [
      "/usr/bin/time",
      "-f",
      "TIME_ELAPSED=%e TIME_RSS_KB=%M",
      "anneal-lean-run",
      "--mode",
      "file",
      "--concurrency",
      "4",
      "--",
  ] + cmd
  t0 = time.perf_counter()
  proc = subprocess.run(
      wrapped, cwd=cwd, capture_output=True, text=True, check=False
  )
  wall_s = time.perf_counter() - t0
  m_rss = re.search(r"TIME_RSS_KB=(\d+)", proc.stderr)
  rss_kb = int(m_rss.group(1)) if m_rss else 0
  return proc.returncode, wall_s, rss_kb, proc.stdout, proc.stderr


def main():
  if WORK_DIR.exists():
    shutil.rmtree(WORK_DIR)
  WORK_DIR.mkdir(parents=True)
  shutil.copytree(STAGE_SRC / "target-lib", WORK_DIR / "target-lib")
  shutil.copytree(STAGE_SRC / "target-src", WORK_DIR / "target-src")
  req_text = (STAGE_SRC / "request-target-audit.json").read_text().replace(
      str(STAGE_SRC), str(WORK_DIR)
  )
  req_path = WORK_DIR / "request-target-audit.json"
  req_path.write_text(req_text)

  orig_tb = (MVP_BASELINE / "trusted/audit/TrustedBoundary.lean").read_text()
  marker = "/-- Dispatch a repository or target inspection request. -/"
  assert marker in orig_tb

  out_file = TRACK_C_DIR / "env_memory_opt_bench.json"
  cached = {}
  if out_file.exists():
    for r in json.loads(out_file.read_text()).get("results", []):
      cached[r["variant"]] = r

  variants = [
      ("baseline_4env", '| "target-audit" => targetAudit j foundation'),
      (
          "scoped_sequential_4env",
          '| "target-audit" => targetAuditScoped4Env j foundation',
      ),
      (
          "reused_target_metadata_3env",
          '| "target-audit" => targetAuditReused3Env j foundation',
      ),
      (
          "single_metadata_2env",
          '| "target-audit" => targetAuditSingle2Env j foundation',
      ),
  ]

  results = []
  for var_name, dispatch_line in variants:
    if var_name in cached:
      print(f"=== Skipping already-measured variant: {var_name} ===", flush=True)
      results.append(cached[var_name])
      continue
    print(f"=== Variant: {var_name} ===", flush=True)
    patched = orig_tb.replace(marker, OPT_LEAN_DEFS + "\n" + marker, 1).replace(
        '| "target-audit" => targetAudit j foundation',
        dispatch_line,
        1,
    )
    lean_file = WORK_DIR / f"TB_{var_name}.lean"
    c_file = WORK_DIR / f"TB_{var_name}.c"
    bin_file = WORK_DIR / f"tb_{var_name}_bin"
    lean_file.write_text(patched)

    # 1. Measure under `lean --run`
    res_interp = WORK_DIR / f"res_{var_name}_interp.json"
    rc_i, wall_i, rss_i, out_i, err_i = run_timed(
        [LEAN, "-j1", "-M2048", "--run", str(lean_file), str(req_path), str(res_interp)],
        cwd=WORK_DIR,
    )
    assert rc_i == 0, f"{var_name} interp failed:\n{out_i}\n{err_i}"
    json_i = json.loads(res_interp.read_text())
    assert json_i["ok"] is True

    # 2. Compile to C and native binary via `leanc -O3 -rdynamic`
    rc_c, _, _, out_c, err_c = run_timed(
        [LEAN, "-c", str(c_file), str(lean_file)], cwd=WORK_DIR
    )
    assert rc_c == 0, f"lean -c failed: {out_c} {err_c}"
    rc_b, _, _, out_b, err_b = run_timed(
        [LEANC, "-O3", "-rdynamic", str(c_file), "-o", str(bin_file)], cwd=WORK_DIR
    )
    assert rc_b == 0, f"leanc failed: {out_b} {err_b}"

    # 3. Measure native binary
    res_bin = WORK_DIR / f"res_{var_name}_bin.json"
    rc_n, wall_n, rss_n, out_n, err_n = run_timed(
        [str(bin_file), str(req_path), str(res_bin)], cwd=WORK_DIR
    )
    assert rc_n == 0, f"{var_name} native failed:\n{out_n}\n{err_n}"
    json_n = json.loads(res_bin.read_text())
    assert json_n["ok"] is True

    row = {
        "variant": var_name,
        "replayed_declarations": json_n["result"]["replayedDeclarations"],
        "lean_run_wall_s": round(wall_i, 4),
        "lean_run_peak_rss_kb": rss_i,
        "lean_run_internal_stats": json_i["result"].get("optStats"),
        "native_bin_wall_s": round(wall_n, 4),
        "native_bin_peak_rss_kb": rss_n,
        "native_bin_internal_stats": json_n["result"].get("optStats"),
    }
    print(json.dumps(row, indent=2), flush=True)
    results.append(row)

  out_file = TRACK_C_DIR / "env_memory_opt_bench.json"
  out_file.write_text(
      json.dumps(
          {
              "benchmark": "Q-C2_Part2_TrustedBoundary_Environment_Memory_Optimization",
              "lean_version": "4.34.1",
              "target": "Starnix apply_endianness (1,683 replayed declarations)",
              "results": results,
          },
          indent=2,
      )
      + "\n"
  )
  print(f"Saved results to {out_file}")


if __name__ == "__main__":
  main()
