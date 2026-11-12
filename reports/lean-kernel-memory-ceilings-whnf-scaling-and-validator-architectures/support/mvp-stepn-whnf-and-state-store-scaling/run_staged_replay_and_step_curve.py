#!/usr/bin/env python3
"""
Measures:
1. The exact step-count scaling curve of monolithic WHNF reduction along `be64`
   for k = 4, 8, 12, 16, 20, 24, 28, 32 steps (`iterateStep k (be64_state0 value) = be64_stateK value` by `rfl`).
2. Staged Kernel Replay (`TrustedBoundaryStaged.lean`):
   Compares full `base.toKernelEnv.replay` (4,847 ms) against staged prefix replay
   where authenticated cached upstream modules (`library`, `model`, `capture`,
   `Endianness`, `Inputs`, `SourceInputs`, `InitialCache`, `ProductionSteps`) are
   loaded into `prefixBase ← importEnv j authenticatedPrefixMods` after verifying
   their Merkle keys, `.olean` digests, and `replayedSet` coverage, and only
   dirty/leaf modules (`ProductionClaims`, `Spec`, `Expected`, `Proof`, plus any
   newly-reached upstream constants) are replayed via `prefixBase.toKernelEnv.replay`.
"""
import json
import os
import re
import subprocess
import time
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task3")
MVP_ROOT = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp")
TOOLCHAIN_ROOT = Path("<host-home>/.cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a")
LEAN_BIN = TOOLCHAIN_ROOT / "lean/bin/lean"

STAGED_AUDIT_LEAN = """
def targetAuditStaged (j : Json) (foundation : Array Name) : IO Json := do
  let t0 ← IO.monoNanosNow
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let cachedReplayMods ← names j "cachedReplayModules"
  let cachedReplayedConsts ← names j "cachedReplayedConstants"
  let mut cachedModSet : NameSet := {}
  for m in cachedReplayMods do cachedModSet := cachedModSet.insert m
  let mut cachedConstSet : NameSet := {}
  for c in cachedReplayedConsts do cachedConstSet := cachedConstSet.insert c

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

  let env ← importEnv j roots
  validateGraph j env
  let provenance n := do
    let m ← origin env n
    let some role := roles.get? m | fail s!"foreign target module {m}"
    return (m, role)
  let lookup n := do
    let some ci := env.checked.get.find? n
      | fail s!"missing target dependency {n}"
    return ci

  -- Full sourceInventory check across ALL target modules (cached or uncached)
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

  -- Full reachability & role authority checks across ALL reachable constants
  let (axioms, reached) ← closure lookup (origin env) axiomPolicy
    [theoremName, expectedName, canonicalRoot, subjectName, specName]
  let (_, expectedReached) ← closure lookup (origin env) axiomPolicy
    [canonicalRoot, subjectName, specName]
  let mut deltaReplayMap : Std.HashMap Name ConstantInfo := {}
  let mut skippedReplayedCount := 0
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
      -- Only skip replay if BOTH the defining module is in cachedModSet AND `n` was already replayed in cachedConstSet!
      if cachedModSet.contains modName && cachedConstSet.contains n then
        skippedReplayedCount := skippedReplayedCount + 1
      else
        deltaReplayMap := deltaReplayMap.insert n ci
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()

  let t_before_replay ← IO.monoNanosNow
  let base ← importEnv j (foundation ++ cachedReplayMods)
  let replayed ← try base.toKernelEnv.replay deltaReplayMap
    catch error => fail s!"kernel replay rejected target dependency: {error}"
  let t_after_replay ← IO.monoNanosNow
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

  let fixedMetadata ← importEnv j (foundation ++ libraries) true
  let targetMetadata ← importEnv j roots true
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

  let (_, modelClosure) ← closure lookup (origin env) axiomPolicy modelRoots
  let (_, specClosure) ← closure lookup (origin env) axiomPolicy specRoots
  let describe (nodes : NameSet) := nodes.toArray.qsort Name.lt |>.mapM fun n => do
    return Json.mkObj [("name", toJson n), ("module", toJson (← origin env n))]
  let t_end ← IO.monoNanosNow
  return Json.mkObj [("theorem", toJson theoremName),
    ("canonicalRoot", toJson canonicalRoot), ("subject", toJson subjectName),
    ("specification", toJson specName), ("graph", graph env),
    ("expected", toJson expectedName), ("axioms", toJson axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson deltaReplayMap.size),
    ("skippedCachedDeclarations", toJson skippedReplayedCount),
    ("stagedReplayNanos", toJson (t_after_replay - t_before_replay)),
    ("totalStagedAuditBodyNanos", toJson (t_end - t0)),
    ("modelClosure", .arr (← describe modelClosure)),
    ("specificationClosure", .arr (← describe specClosure))]
"""

def main():
    work = SCRATCH / "profile_stage"
    ps_text = (MVP_ROOT / "trusted/cargo-anneal/tests/fixtures/starnix/proof/ProductionSteps.lean").read_text()
    ps_setup = json.loads((work / "ProductionSteps.setup.json").read_text())
    clean_env = {
        "HOME": os.environ.get("HOME", "/root"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "PATH": f"{os.path.expanduser('~/.local/bin')}:/usr/bin:/bin",
    }

    # Part 1: Measure multi-step WHNF scaling along `be64` for k = 1, 4, 8, 12, 16, 20, 24, 28, 32 steps
    m0 = re.search(r"(private def be64_state0 \(value : Word\) : State :=\n(?:  .*\n)+)", ps_text)
    state0_def = m0.group(1)
    step_counts = [1, 4, 8, 12, 16, 20, 24, 28, 32]
    curve_rows = []
    for k in step_counts:
        mk = re.search(rf"(private def be64_state{k} \(value : Word\) : State :=\n(?:  .*\n)+)", ps_text)
        statek_def = mk.group(1)
        src = f"""prelude
import InitialCache

namespace BenchCurve

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

def stepN (body : Body) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
    match step body s with
    | .next s' => stepN body n s'
    | _ => none

{state0_def}
{statek_def}

theorem be64_steps_{k} (value : Word) :
    stepN sourceBody {k} (be64_state0 value) = some (be64_state{k} value) := rfl

end BenchCurve
"""
        lean_file = work / f"BenchCurve_{k}.lean"
        olean_file = work / f"BenchCurve_{k}.olean"
        setup_file = work / f"BenchCurve_{k}.setup.json"
        s_obj = dict(ps_setup)
        s_obj["name"] = f"BenchCurve_{k}"
        setup_file.write_text(json.dumps(s_obj))
        lean_file.write_text(src)
        t0 = time.perf_counter()
        proc = subprocess.run([
            "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
            str(LEAN_BIN), "-j1", "-M2048", "-t0",
            "-DElab.async=false", "-Ddebug.skipKernelTC=false",
            "--setup", str(setup_file),
            "-o", str(olean_file),
            str(lean_file),
        ], cwd=work, env=clean_env, capture_output=True, text=True)
        wall_ms = (time.perf_counter() - t0) * 1000.0
        row = {
            "steps_k": k,
            "returncode": proc.returncode,
            "wall_ms": wall_ms,
            "error": proc.stdout.strip().splitlines()[0] if proc.returncode != 0 and proc.stdout.strip() else "",
        }
        curve_rows.append(row)
        print(f"Step curve k={k:2d}: rc={row['returncode']} wall={wall_ms:8.1f} ms {row['error'][:80]}")

    # Part 2: Measure Staged Kernel Replay (`TrustedBoundaryStaged.lean`)
    orig_tb = (MVP_ROOT / "trusted/audit/TrustedBoundary.lean").read_text()
    target_marker = "/-- Dispatch a repository or target inspection request. -/"
    staged_tb = orig_tb.replace(
        target_marker,
        STAGED_AUDIT_LEAN + "\n" + target_marker,
    ).replace(
        '| "target-audit" => targetAudit j foundation',
        '| "target-audit" => targetAuditStaged j foundation',
    )
    staged_path = work / "TrustedBoundaryStaged.lean"
    staged_path.write_text(staged_tb)

    # Extract all reachable non-foundation constants by module from our previous instrumented run
    base_req = json.loads((work / "request-target-audit.json").read_text())
    # Get the list of all constants in modules before Proof (or before ProductionClaims)
    # Using a tiny helper or reading from env in a 2-step test:
    # Let's test caching all upstream modules except `Proof` (and `Expected`, `Spec`) vs caching all including `ProductionSteps`
    # First get the full list of reached constants from TrustedBoundary by adding a small dump or reading module constants
    dump_const_tb = orig_tb.replace(
        '("replayedDeclarations", toJson replayMap.size),',
        '("replayedDeclarations", toJson replayMap.size), ("replayedNames", toJson (replayMap.toArray.map Prod.fst)),',
    )
    dump_tb_path = work / "TrustedBoundaryDumpNames.lean"
    dump_tb_path.write_text(dump_const_tb)
    dump_res_path = work / "request-dump-names.result.json"
    subprocess.run([
        "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
        str(LEAN_BIN), "-j1", "-M2048", "--run",
        str(dump_tb_path), str(work / "request-target-audit.json"), str(dump_res_path)
    ], cwd=work, env=clean_env, check=True)
    replayed_names = json.loads(dump_res_path.read_text())["result"]["replayedNames"]

    # Scenario A: Leaf edit to `Proof.lean` (all libraries + upstream target modules up to ProductionClaims/Expected cached)
    cached_mods_leaf = list(base_req["libraries"]) + [
        "Trusted.Mvp.Syntax", "Trusted.Mvp.Semantics", "Trusted.Mvp",
        "Anneal.Mvp.Execution", "Captured", "Endianness", "Inputs",
        "SourceInputs", "InitialCache", "ProductionSteps", "ProductionClaims",
        "Spec", "Expected",
    ]
    staged_req_leaf = dict(base_req)
    staged_req_leaf["cachedReplayModules"] = cached_mods_leaf
    staged_req_leaf["cachedReplayedConstants"] = [n for n in replayed_names if n != "Proof.verified"]
    staged_req_leaf_path = work / "request-staged-leaf.json"
    staged_res_leaf_path = work / "request-staged-leaf.result.json"
    staged_req_leaf_path.write_text(json.dumps(staged_req_leaf))

    t0 = time.perf_counter()
    proc = subprocess.run([
        "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
        str(LEAN_BIN), "-j1", "-M2048", "--run",
        str(staged_path), str(staged_req_leaf_path), str(staged_res_leaf_path)
    ], cwd=work, env=clean_env, capture_output=True, text=True, check=True)
    leaf_wall_ms = (time.perf_counter() - t0) * 1000.0
    leaf_res = json.loads(staged_res_leaf_path.read_text())["result"]
    leaf_summary = {
        "outer_wall_ms": leaf_wall_ms,
        "stagedReplayMs": leaf_res["stagedReplayNanos"] / 1e6,
        "totalStagedAuditBodyMs": leaf_res["totalStagedAuditBodyNanos"] / 1e6,
        "replayedDeclarations": leaf_res["replayedDeclarations"],
        "skippedCachedDeclarations": leaf_res["skippedCachedDeclarations"],
    }
    print("Staged audit (leaf Proof.lean edit):", json.dumps(leaf_summary, indent=2))

    # Scenario B: Edit to `ProductionClaims.lean` + `Proof.lean` (ProductionSteps & Endianness cached)
    cached_mods_claims = list(base_req["libraries"]) + [
        "Trusted.Mvp.Syntax", "Trusted.Mvp.Semantics", "Trusted.Mvp",
        "Anneal.Mvp.Execution", "Captured", "Endianness", "Inputs",
        "SourceInputs", "InitialCache", "ProductionSteps",
        "Spec", "Expected",
    ]
    staged_req_claims = dict(base_req)
    staged_req_claims["cachedReplayModules"] = cached_mods_claims
    staged_req_claims["cachedReplayedConstants"] = [
        n for n in replayed_names
        if not (n == "Proof.verified" or n.startswith("ProductionClaims."))
    ]
    staged_req_claims_path = work / "request-staged-claims.json"
    staged_res_claims_path = work / "request-staged-claims.result.json"
    staged_req_claims_path.write_text(json.dumps(staged_req_claims))

    t0 = time.perf_counter()
    proc = subprocess.run([
        "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
        str(LEAN_BIN), "-j1", "-M2048", "--run",
        str(staged_path), str(staged_req_claims_path), str(staged_res_claims_path)
    ], cwd=work, env=clean_env, capture_output=True, text=True, check=True)
    claims_wall_ms = (time.perf_counter() - t0) * 1000.0
    claims_res = json.loads(staged_res_claims_path.read_text())["result"]
    claims_summary = {
        "outer_wall_ms": claims_wall_ms,
        "stagedReplayMs": claims_res["stagedReplayNanos"] / 1e6,
        "totalStagedAuditBodyMs": claims_res["totalStagedAuditBodyNanos"] / 1e6,
        "replayedDeclarations": claims_res["replayedDeclarations"],
        "skippedCachedDeclarations": claims_res["skippedCachedDeclarations"],
    }
    print("Staged audit (ProductionClaims + Proof edit):", json.dumps(claims_summary, indent=2))

    out = {
        "be64_step_curve": curve_rows,
        "staged_audit_leaf_proof": leaf_summary,
        "staged_audit_claims_and_proof": claims_summary,
    }
    (SCRATCH / "staged_replay_and_step_curve.json").write_text(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
