#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Benchmark & PoC for Q-C2 Part 1: Module-Level import vs. declarationEdges
Role Authority Violation PoC and Hardened Repair in TrustedBoundary.lean."""

import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HOME = Path.home()
TOOLCHAIN_BIN = (
    HOME
    / ".cache/anneal/toolchain"
    / "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a/lean/bin"
)
LEAN = str(TOOLCHAIN_BIN / "lean")
BRAIN_ROOT = HOME / "<scratch-dir>"
STAGE_SRC = BRAIN_ROOT / "scratch/mvp-investigations/task3/profile_stage"
MVP_BASELINE = BRAIN_ROOT / "scratch/reference-research/mvp-baseline"
TRACK_C_DIR = BRAIN_ROOT / "scratch/reference-research/track_c"
WORK_DIR = TRACK_C_DIR / "import_authority_stage"

TROJAN_PROOF_LEAN = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace TrojanProof

open Trusted.Mvp

/-- Proof-role notation/macro that expands during elaboration of `Spec.lean`
    without leaving any `TrojanProof` constant in `Spec.specs`'s kernel term. -/
notation "trojanSafetyPre" => (fun (_ : Nat) (_ : List Word) => True)

theorem trojanHelper : True := trivial

end TrojanProof
"""

PATCH_TARGET = """  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | fail s!"foreign target module {m.module}"
    if let .source _ := role then"""

PATCH_REPLACEMENT = """  for m in env.header.modules, data in env.header.moduleData do
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
    if let .source _ := role then"""

TOSTRING_TARGET = """inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq"""

TOSTRING_REPLACEMENT = """inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq

instance : ToString TargetRole where
  toString
    | .model => "model"
    | .specification => "specification"
    | .capture => "capture"
    | .expected => "expected"
    | .proof => "proof\""""


def run_lean(args, cwd):
  cmd = [
      "anneal-lean-run",
      "--mode",
      "file",
      "--concurrency",
      "4",
      "--",
      LEAN,
  ] + args
  return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)


def main():
  if WORK_DIR.exists():
    shutil.rmtree(WORK_DIR)
  WORK_DIR.mkdir(parents=True)
  shutil.copytree(STAGE_SRC / "target-lib", WORK_DIR / "target-lib")
  shutil.copytree(STAGE_SRC / "target-src", WORK_DIR / "target-src")
  for p in STAGE_SRC.glob("*.setup.json"):
    txt = p.read_text().replace(str(STAGE_SRC), str(WORK_DIR))
    (WORK_DIR / p.name).write_text(txt)

  orig_tb = (MVP_BASELINE / "trusted/audit/TrustedBoundary.lean").read_text()
  unmodified_tb_path = WORK_DIR / "TrustedBoundaryUnmodified.lean"
  unmodified_tb_path.write_text(orig_tb)

  assert TOSTRING_TARGET in orig_tb
  assert PATCH_TARGET in orig_tb
  hardened_tb = orig_tb.replace(TOSTRING_TARGET, TOSTRING_REPLACEMENT, 1).replace(
      PATCH_TARGET, PATCH_REPLACEMENT, 1
  )
  hardened_tb_path = WORK_DIR / "TrustedBoundaryHardened.lean"
  hardened_tb_path.write_text(hardened_tb)
  (TRACK_C_DIR / "TrustedBoundaryHardened.lean").write_text(hardened_tb)

  # Save a copy of legitimate request before modifying Spec.lean
  legit_req_text = (STAGE_SRC / "request-target-audit.json").read_text().replace(
      str(STAGE_SRC), str(WORK_DIR)
  )
  legit_req_path = WORK_DIR / "request-target-audit-legit.json"
  legit_req_path.write_text(legit_req_text)

  # 1. Verify hardened TrustedBoundary passes legitimate Starnix target
  legit_res_path = WORK_DIR / "result-legit-hardened.json"
  proc_legit = run_lean(
      [
          "-j1",
          "-M2048",
          "--run",
          str(hardened_tb_path),
          str(legit_req_path),
          str(legit_res_path),
      ],
      cwd=WORK_DIR,
  )
  assert proc_legit.returncode == 0, f"Hardened failed legit: {proc_legit.stderr}"
  legit_res = json.loads(legit_res_path.read_text())
  assert legit_res["ok"] is True

  # 2. Construct PoC: TrojanProof.lean (role: "proof") imported by Spec.lean (role: "specification")
  trojan_src = WORK_DIR / "target-src" / "TrojanProof.lean"
  trojan_olean = WORK_DIR / "target-lib" / "TrojanProof.olean"
  trojan_src.write_text(TROJAN_PROOF_LEAN)
  trojan_sha = hashlib.sha256(TROJAN_PROOF_LEAN.encode()).hexdigest()

  # Setup file for TrojanProof (same deps as Captured.setup.json: Trusted.Mvp)
  trojan_setup = json.loads((WORK_DIR / "Captured.setup.json").read_text())
  trojan_setup["name"] = "TrojanProof"
  trojan_setup_path = WORK_DIR / "TrojanProof.setup.json"
  trojan_setup_path.write_text(json.dumps(trojan_setup))

  proc_tp = run_lean(
      ["--setup", str(trojan_setup_path), "-o", str(trojan_olean), str(trojan_src)],
      cwd=WORK_DIR,
  )
  assert proc_tp.returncode == 0, f"TrojanProof compile failed: {proc_tp.stdout} {proc_tp.stderr}"

  # Modify Spec.lean to import TrojanProof and use trojanSafetyPre
  spec_src = WORK_DIR / "target-src" / "Spec.lean"
  orig_spec = spec_src.read_text()
  poc_spec = orig_spec.replace(
      "import Endianness\n",
      "import Endianness\nimport TrojanProof\n",
  ).replace(
      "{ safety := fun _ _ => True",
      "{ safety := trojanSafetyPre",
  )
  assert poc_spec != orig_spec
  spec_src.write_text(poc_spec)
  spec_sha = hashlib.sha256(poc_spec.encode()).hexdigest()

  # Add TrojanProof.olean to Spec, Expected, ProductionClaims, Proof setup.json and recompile
  for mod in ["Spec", "Expected", "ProductionClaims", "Proof"]:
    sp_path = WORK_DIR / f"{mod}.setup.json"
    sp = json.loads(sp_path.read_text())
    sp["importArts"]["TrojanProof"] = [[str(trojan_olean)], []]
    if mod == "Spec":
      sp["imports"].append({
          "module": "TrojanProof",
          "isMeta": False,
          "isExported": True,
          "importAll": False,
      })
    sp_path.write_text(json.dumps(sp))
    proc_m = run_lean(
        [
            "--setup",
            str(sp_path),
            "-o",
            str(WORK_DIR / "target-lib" / f"{mod}.olean"),
            str(WORK_DIR / "target-src" / f"{mod}.lean"),
        ],
        cwd=WORK_DIR,
    )
    assert proc_m.returncode == 0, f"{mod} compile failed: {proc_m.stdout} {proc_m.stderr}"

  # Build PoC target-audit request JSON
  poc_req = json.loads(legit_req_text)
  poc_req["artifacts"].append(["TrojanProof", [[str(trojan_olean)], []]])
  poc_req["artifacts"].sort(key=lambda x: x[0])
  poc_req["graph"]["TrojanProof"] = [
      {"module": "Trusted.Mvp", "isMeta": False, "isExported": True, "importAll": False}
  ]
  poc_req["graph"]["Spec"].append(
      {"module": "TrojanProof", "isMeta": False, "isExported": True, "importAll": False}
  )
  for m_entry in poc_req["target"]["modules"]:
    if m_entry["module"] == "Spec":
      m_entry["expectedSha256"] = spec_sha
  poc_req["target"]["modules"].append({
      "module": "TrojanProof",
      "source": str(trojan_src),
      "expectedSha256": trojan_sha,
      "role": "proof",
  })

  poc_req_path = WORK_DIR / "request-target-audit-poc.json"
  poc_req_path.write_text(json.dumps(poc_req))

  # 3. Run UNMODIFIED TrustedBoundary.lean on PoC
  unmod_res_path = WORK_DIR / "result-poc-unmodified.json"
  proc_unmod = run_lean(
      [
          "-j1",
          "-M2048",
          "--run",
          str(unmodified_tb_path),
          str(poc_req_path),
          str(unmod_res_path),
      ],
      cwd=WORK_DIR,
  )
  unmod_res = json.loads(unmod_res_path.read_text())

  # 4. Run HARDENED TrustedBoundaryHardened.lean on PoC
  hard_res_path = WORK_DIR / "result-poc-hardened.json"
  proc_hard = run_lean(
      [
          "-j1",
          "-M2048",
          "--run",
          str(hardened_tb_path),
          str(poc_req_path),
          str(hard_res_path),
      ],
      cwd=WORK_DIR,
  )
  hard_res = json.loads(hard_res_path.read_text())

  spec_closure_mods = sorted(
      list({d["module"] for d in unmod_res["result"]["specificationClosure"]})
  )
  trojan_in_spec_closure = any(
      d["module"] == "TrojanProof"
      for d in unmod_res["result"]["specificationClosure"]
  )

  summary = {
      "benchmark": "Q-C2_Part1_Module_Import_Role_Authority_PoC",
      "lean_version": "4.34.1",
      "poc_description": (
          "Spec.lean (role: specification) imports TrojanProof.lean (role: proof) "
          "and uses notation `trojanSafetyPre` defined in TrojanProof. Because Lean "
          "expands notation during elaboration, Spec.specs's kernel ConstantInfo "
          "contains zero constant references (`declarationEdges`) to TrojanProof."
      ),
      "unmodified_trusted_boundary_on_poc": {
          "exit_code": proc_unmod.returncode,
          "ok": unmod_res.get("ok"),
          "recorded_spec_imports_in_result_graph": unmod_res["result"]["graph"]["Spec"],
          "specification_closure_modules": spec_closure_mods,
          "trojan_proof_in_specification_closure": trojan_in_spec_closure,
          "replayed_declarations": unmod_res["result"]["replayedDeclarations"],
      },
      "hardened_trusted_boundary_on_poc": {
          "exit_code": proc_hard.returncode,
          "response": hard_res,
      },
      "hardened_trusted_boundary_on_legit_starnix": {
          "exit_code": proc_legit.returncode,
          "ok": legit_res.get("ok"),
          "replayed_declarations": legit_res["result"]["replayedDeclarations"],
      },
  }

  out_file = TRACK_C_DIR / "import_authority_poc.json"
  out_file.write_text(json.dumps(summary, indent=2) + "\n")
  print(json.dumps(summary, indent=2))


if __name__ == "__main__":
  main()
