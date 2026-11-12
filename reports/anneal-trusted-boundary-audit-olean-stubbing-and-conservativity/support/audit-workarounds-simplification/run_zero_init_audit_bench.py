#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Benchmark and security verification of zero-initializer targetAudit
(`zero_init_2env`: `loadExts := false` on both `env` and `base`, zero
`enableInitializersExecution` calls) vs `single_metadata_2env` (`loadExts := true`
on `env`) and `baseline_4env` (`fixedMetadata` + `targetMetadata` with
`loadExts := true`)."""

import json
from pathlib import Path
import re
import shutil
import subprocess
import time

HOME = Path.home()
TOOLCHAIN_DIR = HOME / ".elan/toolchains/leanprover--lean4---v4.34.1"
LEAN = str(TOOLCHAIN_DIR / "bin/lean")
LEANC = str(TOOLCHAIN_DIR / "bin/leanc")
BRAIN_ROOT = HOME / "<scratch-root>"
STAGE_SRC = BRAIN_ROOT / "scratch/mvp-investigations/task3/profile_stage"
SCRATCH_DIR = BRAIN_ROOT / "scratch/ref-pass-9-audit-simplification"
WORK_DIR = SCRATCH_DIR / "zero_init_bench_stage"
PREV_BENCH = (
    HOME
    / "workspace/anneal/.agent-worktrees/zerocopy-reference/reports"
    / "anneal-trusted-boundary-audit-olean-stubbing-and-conservativity"
    / "support/mvp-merkle-cache-and-import-authority/env_memory_opt_bench.json"
)

ZERO_INIT_LEAN_PATCH = """
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

/-- Inspect raw `.olean` persistent extension entries (`importedEntries` and
`ModuleData.entries`) populated unconditionally by `setImportedEntries` in
`Lean.Environment.finalizeImport` (`src/Lean/Environment.lean:2383`) before the
`if loadExts then` gate. Requires `loadExts := false` and zero
`enableInitializersExecution` calls. -/
def checkTargetOverridesLoadExtsFalse (env : Environment)
    (roles : Std.HashMap Name TargetOrigin) : IO Unit := do
  let implEntries :=
    (Compiler.implementedByAttr.ext.toEnvExtension.getState env).importedEntries
  let extEntries :=
    (externAttr.ext.toEnvExtension.getState env).importedEntries
  let csimpEntries :=
    (Compiler.CSimp.ext.ext.toEnvExtension.getState env).importedEntries
  for idx in [:env.header.modules.size] do
    let m := env.header.modules[idx]!
    let data := env.header.moduleData[idx]!
    if let some (.source _) := roles.get? m.module then
      let hasImpl := !(implEntries[idx]?.map Array.isEmpty |>.getD true)
      let hasExt := !(extEntries[idx]?.map Array.isEmpty |>.getD true)
      let hasCsimp := !(csimpEntries[idx]?.map Array.isEmpty |>.getD true)
      -- Cross-check directly against raw `ModuleData.entries` in the `.olean` header
      let rawImpl := data.entries.any fun (k, entries) =>
        k == `Lean.Compiler.implementedByAttr && !entries.isEmpty
      let rawExt := data.entries.any fun (k, entries) =>
        k == `Lean.externAttr && !entries.isEmpty
      let rawCsimp := data.entries.any fun (k, entries) =>
        k == `Lean.Compiler.CSimp.ext && !entries.isEmpty
      if hasImpl || rawImpl || hasExt || rawExt then
        fail s!"unchecked compiler override in target module {m.module}"
      if hasCsimp || rawCsimp then
        fail s!"authored compiler replacement in target module {m.module}"

@[noinline]
def buildTargetPlanZeroInit (j : Json) (foundation : Array Name)
    (loadExtsOnFirst : Bool) : IO TargetPlan := do
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
  -- When `loadExtsOnFirst = false`, `enableInitializersExecution` is NOT called
  -- and `importModules` runs with `loadExts := false`.
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
  -- Check `@[implemented_by]`, `@[extern]`, and `@[csimp]` directly from
  -- `importedEntries` / `ModuleData.entries` without `loadExts := true`!
  checkTargetOverridesLoadExtsFalse env roles
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
def replayAndCheckKernel (j : Json) (foundation : Array Name)
    (plan : TargetPlan) : IO Unit := do
  let base ← importEnv j foundation false
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

def targetAuditZeroInit2Env (j : Json) (foundation : Array Name) : IO Json := do
  let t0 ← IO.monoNanosNow
  let plan ← buildTargetPlanZeroInit j foundation false
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
      "5",
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

  # Replace both the old profile_stage path and toolchain sysroot path if needed
  req_obj = json.loads((STAGE_SRC / "request-target-audit.json").read_text())
  old_sysroot = req_obj["sysroot"]
  req_text = (
      (STAGE_SRC / "request-target-audit.json")
      .read_text()
      .replace(str(STAGE_SRC), str(WORK_DIR))
      .replace(old_sysroot, str(TOOLCHAIN_DIR))
  )
  req_path = WORK_DIR / "request-target-audit.json"
  req_path.write_text(req_text)

  orig_tb = (SCRATCH_DIR / "inspected/mvp_TrustedBoundary.lean").read_text()
  marker = "/-- Dispatch a repository or target inspection request. -/"
  assert marker in orig_tb

  patched = orig_tb.replace(
      marker, ZERO_INIT_LEAN_PATCH + "\n" + marker, 1
  ).replace(
      '| "target-audit" => targetAudit j foundation',
      '| "target-audit" => targetAuditZeroInit2Env j foundation',
      1,
  )
  lean_file = WORK_DIR / "TB_zero_init_2env.lean"
  c_file = WORK_DIR / "TB_zero_init_2env.c"
  bin_file = WORK_DIR / "tb_zero_init_2env_bin"
  lean_file.write_text(patched)

  print("=== Measuring zero_init_2env under lean --run ===", flush=True)
  res_interp = WORK_DIR / "res_zero_init_interp.json"
  rc_i, wall_i, rss_i, out_i, err_i = run_timed(
      [LEAN, "-j1", "-M2048", "--run", str(lean_file), str(req_path), str(res_interp)],
      cwd=WORK_DIR,
  )
  assert rc_i == 0, f"zero_init_2env interp failed:\n{out_i}\n{err_i}"
  json_i = json.loads(res_interp.read_text())
  assert json_i["ok"] is True

  print("=== Compiling zero_init_2env to native binary ===", flush=True)
  rc_c, _, _, out_c, err_c = run_timed(
      [LEAN, "-c", str(c_file), str(lean_file)], cwd=WORK_DIR
  )
  assert rc_c == 0, f"lean -c failed: {out_c} {err_c}"
  rc_b, _, _, out_b, err_b = run_timed(
      [LEANC, "-O3", "-rdynamic", str(c_file), "-o", str(bin_file)], cwd=WORK_DIR
  )
  assert rc_b == 0, f"leanc failed: {out_b} {err_b}"

  res_bin = WORK_DIR / "res_zero_init_bin.json"
  rc_n, wall_n, rss_n, out_n, err_n = run_timed(
      [str(bin_file), str(req_path), str(res_bin)], cwd=WORK_DIR
  )
  assert rc_n == 0, f"zero_init_2env native failed:\n{out_n}\n{err_n}"
  json_n = json.loads(res_bin.read_text())
  assert json_n["ok"] is True

  zero_init_row = {
      "variant": "zero_init_2env",
      "enableInitializers_calls": 0,
      "loadExts_true_calls": 0,
      "replayed_declarations": json_n["result"]["replayedDeclarations"],
      "lean_run_wall_s": round(wall_i, 4),
      "lean_run_peak_rss_kb": rss_i,
      "lean_run_internal_stats": json_i["result"].get("optStats"),
      "native_bin_wall_s": round(wall_n, 4),
      "native_bin_peak_rss_kb": rss_n,
      "native_bin_internal_stats": json_n["result"].get("optStats"),
  }
  print(json.dumps(zero_init_row, indent=2), flush=True)

  # Security tests: verify that `zero_init_2env` (with `loadExts := false` and
  # zero `enableInitializersExecution` calls) deterministically rejects
  # `@[implemented_by]`, `@[extern]`, and `@[csimp]` in a target module!
  proof_lean = WORK_DIR / "target-src/Proof.lean"
  orig_proof_src = proof_lean.read_text()
  proof_olean = WORK_DIR / "target-lib/Proof.olean"
  orig_proof_olean = proof_olean.read_bytes()

  attacks = [
      (
          "attack_implemented_by",
          orig_proof_src
          + "\ndef evilImpl : Bool := false\n@[implemented_by evilImpl] def targetFn : Bool := true\n",
          "policy:unchecked compiler override in target module Proof",
      ),
      (
          "attack_extern",
          orig_proof_src
          + '\n@[extern "c_evil_symbol"] def externTargetFn (x : Nat) : Nat := x\n',
          "policy:unchecked compiler override in target module Proof",
      ),
      (
          "attack_csimp",
          orig_proof_src
          + "\ndef csimpA (x : Nat) : Nat := x\ndef csimpB (x : Nat) : Nat := x + 0\n@[csimp] theorem csimp_override : @csimpA = @csimpB := rfl\n",
          "policy:authored compiler replacement in target module Proof",
      ),
  ]

  attack_results = []
  for attack_name, patched_proof, expected_msg in attacks:
    proof_lean.write_text(patched_proof)
    # Compile Proof.lean with LEAN_PATH pointing to target-lib
    env_vars = {"LEAN_PATH": str(WORK_DIR / "target-lib")}
    cmd = [
        "anneal-lean-run",
        "--mode",
        "file",
        "--concurrency",
        "5",
        "--",
        LEAN,
        "-o",
        str(proof_olean),
        str(proof_lean),
    ]
    p_comp = subprocess.run(
        cmd,
        cwd=WORK_DIR / "target-src",
        env={** subprocess.os.environ, **env_vars},
        capture_output=True,
        text=True,
        check=False,
    )
    assert p_comp.returncode == 0, (
        f"Failed to compile {attack_name}:\n{p_comp.stdout}\n{p_comp.stderr}"
    )
    res_att = WORK_DIR / f"res_{attack_name}.json"
    rc_a, wall_a, _, out_a, err_a = run_timed(
        [str(bin_file), str(req_path), str(res_att)], cwd=WORK_DIR
    )
    res_obj = json.loads(res_att.read_text())
    assert rc_a == 1 and res_obj["ok"] is False, (
        f"Expected policy rejection for {attack_name}, got rc={rc_a}: {res_obj}"
    )
    assert expected_msg in res_obj["message"], (
        f"Expected {expected_msg!r}, got {res_obj['message']!r}"
    )
    attack_results.append({
        "attack": attack_name,
        "return_code": rc_a,
        "rejected": not res_obj["ok"],
        "category": res_obj["category"],
        "message": res_obj["message"],
        "wall_ms": round(wall_a * 1000.0, 2),
    })
    print(f"Verified rejection of {attack_name}: {res_obj['message']}", flush=True)

  # Restore original Proof.lean and Proof.olean
  proof_lean.write_text(orig_proof_src)
  proof_olean.write_bytes(orig_proof_olean)

  prev_data = json.loads(PREV_BENCH.read_text())
  out_summary = {
      "benchmark": "Zero_Initializer_TargetAudit_vs_LoadExts_Variants",
      "lean_version": "4.34.1",
      "target": "Starnix apply_endianness (1,683 replayed declarations, 17 modules)",
      "prior_variants": prev_data["results"],
      "zero_init_2env": zero_init_row,
      "adversarial_override_tests": attack_results,
  }
  out_json_path = SCRATCH_DIR / "zero_init_audit_bench.json"
  out_json_path.write_text(json.dumps(out_summary, indent=2) + "\n")
  print(f"Wrote {out_json_path}", flush=True)


if __name__ == "__main__":
  main()
