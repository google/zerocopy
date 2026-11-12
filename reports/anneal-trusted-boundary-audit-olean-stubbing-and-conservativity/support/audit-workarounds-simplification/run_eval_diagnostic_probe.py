#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical probe for Topic 9 Question 4:
Compare embedding `#eval Anneal.checkCrate Mir.crate` inside `Proof.lean`
against keeping `Proof.lean` pure (`theorem verify_crate : ... :=
Anneal.proveCrate Mir.crate rfl`) and running diagnostic extraction only on the
cold failure path."""

import json
from pathlib import Path
import subprocess
import time

HOME = Path.home()
TOOLCHAIN_DIR = HOME / ".elan/toolchains/leanprover--lean4---v4.34.1"
LEAN = str(TOOLCHAIN_DIR / "bin/lean")
SCRATCH_DIR = (
    HOME
    / "<scratch-root>"
    / "scratch/ref-pass-9-audit-simplification"
)
STAGE_DIR = SCRATCH_DIR / "eval_diag_stage"

PROBE_LEAN = r"""
import Lean
import Lean.Elab.Import
import Lean.Parser

open Lean

def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.prelude, ``Parser.Module.import]

def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

/-- Check top-level command syntax kinds against `TrustedBoundary.lean`'s
`allowedCommandKinds` preflight gate. -/
partial def checkPreflightCommands (env : Environment) (moduleName : Name)
    (text : String) : IO (Except String Nat) := do
  let ctx := Parser.mkInputContext text moduleName.toString
  let (_, state, messages) ← Parser.parseHeader ctx
  if messages.hasErrors || state.recovering then
    return .error s!"header parser error in {moduleName}"
  let mut state := state
  let mut messages := messages
  let mut cmdCount := 0
  while ! ctx.atEnd state.pos do
    let (stx, state', messages') :=
      Parser.parseCommand ctx { env, options := {} } state messages
    state := state'
    messages := messages'
    if messages.hasErrors || state.recovering then
      return .error s!"command parser error in {moduleName}"
    if stx.getKind == ``Parser.Command.eoi then
      break
    cmdCount := cmdCount + 1
    unless allowedCommandKinds.contains stx.getKind do
      return .error s!"policy:unsupported command {stx.getKind} in {moduleName}"
  return .ok cmdCount

def main (args : List String) : IO UInt32 := do
  let [sysrootStr, outJsonPath] := args
    | return 1
  Lean.initSearchPath (System.FilePath.mk sysrootStr)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := true)

  let proofWithEval :=
    "import Mir\nimport Trusted.Theory\nimport Anneal.Diagnostic\n\n" ++
    "#eval Anneal.checkCrate Mir.crate\n\n" ++
    "theorem verify_crate : Trusted.CrateTheorem Mir.crate :=\n" ++
    "  Anneal.proveCrate Mir.crate rfl\n"

  let proofPure :=
    "import Mir\nimport Trusted.Theory\nimport Anneal.Diagnostic\n\n" ++
    "theorem verify_crate : Trusted.CrateTheorem Mir.crate :=\n" ++
    "  Anneal.proveCrate Mir.crate rfl\n"

  let resWithEval :=
    match ← checkPreflightCommands env `Proof proofWithEval with
    | .ok n => Json.mkObj [("accepted", toJson true), ("commands", toJson n)]
    | .error msg => Json.mkObj [("accepted", toJson false), ("error", toJson msg)]

  let resPure :=
    match ← checkPreflightCommands env `Proof proofPure with
    | .ok n => Json.mkObj [("accepted", toJson true), ("commands", toJson n)]
    | .error msg => Json.mkObj [("accepted", toJson false), ("error", toJson msg)]

  let out := Json.mkObj [
    ("leanVersion", toJson "4.34.1"),
    ("proofWithEvalPreflight", resWithEval),
    ("proofPurePreflight", resPure)
  ]
  IO.FS.writeFile outJsonPath (out.pretty ++ "\n")
  return 0
"""

MOCK_MIR_AND_DIAG = """
namespace Trusted
structure Crate where
  items : List Nat
def CrateTheorem (c : Crate) : Prop :=
  (c.items.all (fun x => x < 100)) = true
end Trusted

namespace Mir
def crate : Trusted.Crate :=
  { items := List.range 50 }
def failingCrate : Trusted.Crate :=
  { items := [10, 20, 150] }
end Mir

namespace Anneal
def checkCrate (c : Trusted.Crate) : IO Unit := do
  let mut idx := 0
  for x in c.items do
    if !(x < 100) then
      IO.println s!"fn_{idx}|[item < 100]|x={x}"
    idx := idx + 1

theorem proveCrate (c : Trusted.Crate)
    (h : (c.items.all (fun x => x < 100)) = true) :
    Trusted.CrateTheorem c := h
end Anneal
"""


def run_lean(args, cwd, extra_env=None):
  env = dict(subprocess.os.environ)
  if extra_env:
    env.update(extra_env)
  cmd = [
      "anneal-lean-run",
      "--mode",
      "file",
      "--concurrency",
      "5",
      "--",
      LEAN,
  ] + args
  t0 = time.perf_counter()
  p = subprocess.run(
      cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False
  )
  elapsed_ms = (time.perf_counter() - t0) * 1000.0
  return p.returncode, elapsed_ms, p.stdout, p.stderr


def main():
  STAGE_DIR.mkdir(parents=True, exist_ok=True)
  probe_file = STAGE_DIR / "ProbeEvalDiagnosticVsPureProof.lean"
  probe_file.write_text(PROBE_LEAN.strip() + "\n")
  preflight_json = STAGE_DIR / "preflight_res.json"

  rc, _, out, err = run_lean(
      ["--run", str(probe_file), str(TOOLCHAIN_DIR), str(preflight_json)],
      cwd=STAGE_DIR,
  )
  assert rc == 0, f"Preflight probe failed:\n{out}\n{err}"
  preflight_data = json.loads(preflight_json.read_text())

  # Compile MockBase.lean -> MockBase.olean
  (STAGE_DIR / "MockBase.lean").write_text(MOCK_MIR_AND_DIAG.strip() + "\n")
  env_path = {"LEAN_PATH": str(STAGE_DIR)}
  rc, _, out, err = run_lean(
      ["-o", "MockBase.olean", "MockBase.lean"], cwd=STAGE_DIR, extra_env=env_path
  )
  assert rc == 0, f"MockBase failed:\n{out}\n{err}"

  # Compare passing build with `#eval` vs pure `Proof.lean`
  (STAGE_DIR / "ProofWithEval.lean").write_text(
      "import MockBase\n\n#eval Anneal.checkCrate Mir.crate\n\n"
      "theorem verify_crate : Trusted.CrateTheorem Mir.crate :=\n"
      "  Anneal.proveCrate Mir.crate rfl\n"
  )
  (STAGE_DIR / "ProofPure.lean").write_text(
      "import MockBase\n\n"
      "theorem verify_crate : Trusted.CrateTheorem Mir.crate :=\n"
      "  Anneal.proveCrate Mir.crate rfl\n"
  )
  # Failing build + out-of-band cold-path diagnostic runner
  (STAGE_DIR / "ProofFailingPure.lean").write_text(
      "import MockBase\n\n"
      "theorem verify_crate : Trusted.CrateTheorem Mir.failingCrate :=\n"
      "  Anneal.proveCrate Mir.failingCrate rfl\n"
  )
  (STAGE_DIR / "ColdPathDiag.lean").write_text(
      "import MockBase\n\ndef main : IO Unit := Anneal.checkCrate Mir.failingCrate\n"
  )

  rc_eval, ms_eval, _, _ = run_lean(
      ["-o", "ProofWithEval.olean", "ProofWithEval.lean"],
      cwd=STAGE_DIR,
      extra_env=env_path,
  )
  rc_pure, ms_pure, _, _ = run_lean(
      ["-o", "ProofPure.olean", "ProofPure.lean"],
      cwd=STAGE_DIR,
      extra_env=env_path,
  )
  rc_fail, ms_fail, _, _ = run_lean(
      ["-o", "ProofFailingPure.olean", "ProofFailingPure.lean"],
      cwd=STAGE_DIR,
      extra_env=env_path,
  )
  rc_diag, ms_diag, out_diag, _ = run_lean(
      ["--run", "ColdPathDiag.lean"],
      cwd=STAGE_DIR,
      extra_env=env_path,
  )
  assert rc_eval == 0 and rc_pure == 0 and rc_fail != 0 and rc_diag == 0

  summary = {
      **preflight_data,
      "passingBuildWithEvalMs": round(ms_eval, 2),
      "passingBuildPureMs": round(ms_pure, 2),
      "failingPureKernelRejectMs": round(ms_fail, 2),
      "coldPathOutOfBandDiagnosticOutput": out_diag.strip(),
      "coldPathOutOfBandDiagnosticMs": round(ms_diag, 2),
  }
  out_file = SCRATCH_DIR / "eval_diagnostic_probe_results.json"
  out_file.write_text(json.dumps(summary, indent=2) + "\n")
  print(json.dumps(summary, indent=2))


if __name__ == "__main__":
  main()
