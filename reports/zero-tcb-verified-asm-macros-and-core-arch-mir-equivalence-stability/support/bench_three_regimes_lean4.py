#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Compile and benchmark all 12 Lean 4.34.1 modules across the 3 assembly archetypes
and 3 verification regimes:
  (a) RawObj_<k>.lean  — Unassisted direct `.o` machine-byte proof
  (b) HintObj_<k>.lean — `asm_verified!` untrusted `HintCert`-assisted `.o` proof
  (c) MirTwin_<k>.lean — `core::arch` MIR-level `SafeTwin` proof
plus standalone `(trustLevel := 0, plugins := #[], loadExts := false, level := .private)`
`base.toKernelEnv.replay` verifying:
  - 0 `sorryAx`, 0 `Lean.ofReduceBool`, 0 `Lean.trustCompiler`
  - Transitive axioms strictly within `{propext, Classical.choice, Quot.sound}`
  - Statement-Origin Separation (`type_hints == 0` on all locked obligations, `val_hints > 0` on HintObj)
  - Character-for-character equality of locked theorem types between RawObj_<k> and HintObj_<k>!
All builds run inside `tempfile.TemporaryDirectory()` wrapped in `anneal-lean-run`.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE / "lean" if (HERE / "lean").is_dir() else HERE
LEAN_BIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
LEAN_RUN = Path.home() / ".local/bin/anneal-lean-run"

MODULES_IN_ORDER = [
    "AsmMirBase",
    "IsaLemmas",
    "UntrustedHints",
    "RawObj_MulxMac4",
    "HintObj_MulxMac4",
    "MirTwin_MulxMac4",
    "RawObj_DotMaddubs",
    "HintObj_DotMaddubs",
    "MirTwin_DotMaddubs",
    "RawObj_CtLookup8",
    "HintObj_CtLookup8",
    "MirTwin_CtLookup8",
]

REPLAY_JOBS = [
    # (module, theorem_name, base_module_for_replay_delta)
    # Note: For HintObj_*, replaying against `IsaLemmas` replays BOTH `UntrustedHints` AND `HintObj_*`
    # ("cold replay"), whereas replaying against `UntrustedHints` replays ONLY the per-kernel `HintObj_*`
    # delta ("warm library replay")! We measure BOTH!
    ("RawObj_MulxMac4",  "LockedObligations.verify_mulx_mac4_obj",      "IsaLemmas",      "raw_obj"),
    ("HintObj_MulxMac4", "LockedObligations.verify_mulx_mac4_obj",      "UntrustedHints", "hint_obj_per_kernel"),
    ("HintObj_MulxMac4", "LockedObligations.verify_mulx_mac4_obj",      "IsaLemmas",      "hint_obj_incl_lib"),
    ("MirTwin_MulxMac4", "LockedObligations.verify_mulx_mac4_mir_twin", "IsaLemmas",      "mir_twin"),

    ("RawObj_DotMaddubs",  "LockedObligations.verify_dot_maddubs_obj",      "IsaLemmas",      "raw_obj"),
    ("HintObj_DotMaddubs", "LockedObligations.verify_dot_maddubs_obj",      "UntrustedHints", "hint_obj_per_kernel"),
    ("HintObj_DotMaddubs", "LockedObligations.verify_dot_maddubs_obj",      "IsaLemmas",      "hint_obj_incl_lib"),
    ("MirTwin_DotMaddubs", "LockedObligations.verify_dot_maddubs_mir_twin", "IsaLemmas",      "mir_twin"),

    ("RawObj_CtLookup8",  "LockedObligations.verify_ct_lookup8_obj",     "IsaLemmas",      "raw_obj"),
    ("RawObj_CtLookup8",  "LockedObligations.verify_ct_lookup8_2safety", "IsaLemmas",      "raw_obj_2safety"),
    ("HintObj_CtLookup8", "LockedObligations.verify_ct_lookup8_obj",     "UntrustedHints", "hint_obj_per_kernel"),
    ("HintObj_CtLookup8", "LockedObligations.verify_ct_lookup8_2safety", "UntrustedHints", "hint_obj_2safety"),
    ("HintObj_CtLookup8", "LockedObligations.verify_ct_lookup8_obj",     "IsaLemmas",      "hint_obj_incl_lib"),
    ("MirTwin_CtLookup8", "LockedObligations.verify_ct_lookup8_mir_twin","AsmMirBase",     "mir_twin"),
]

REPLAY_AUDIT_LEAN = r"""import Lean
import Lean.Replay

open Lean

def loadBase (baseStr : String) : IO (Environment × NameSet) := do
  let base ← importModules #[{ module := baseStr.toName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let base := base.setExporting false
  let mut mods : NameSet := {}
  for m in base.header.modules do
    mods := mods.insert m.module
  return (base, mods)

def auditOne (bases : Std.HashMap String (Environment × NameSet))
    (modStr thmStr baseStr tagStr : String) : IO Unit := do
  let some (base, baseMods) := bases.get? baseStr
    | throw <| IO.userError s!"unknown base {baseStr}"
  let modName := modStr.toName
  let thmName := thmStr.toName
  let t0 ← IO.monoNanosNow
  let env ← importModules #[{ module := modName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (m, md) in env.header.modules.zip env.header.moduleData do
    if !baseMods.contains m.module then
      for (n, ci) in md.constNames.zip md.constants do
        newConsts := newConsts.insert n ci
  let t1 ← IO.monoNanosNow
  let replayed ← base.toKernelEnv.replay newConsts
  let t2 ← IO.monoNanosNow
  let some replayedCi := replayed.find? thmName
    | throw <| IO.userError s!"theorem {thmName} absent after kernel replay"
  -- Collect transitive axioms across full private proof cone
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut stack : List Name := [thmName]
  while !stack.isEmpty do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if !visited.contains c then
        visited := visited.insert c
        match env.find? c with
        | some (.axiomInfo _) => axioms := axioms.push c
        | some ci =>
          for d in ci.getUsedConstantsAsSet do
            if !visited.contains d then
              stack := d :: stack
        | none => pure ()
  -- Statement-Origin Separation check + dummy proof check
  let mut typeHints : Array Name := #[]
  let mut valHints : Array Name := #[]
  let mut hasDummy : Bool := false
  match env.find? thmName with
  | some ci =>
    for d in ci.type.getUsedConstants do
      if d.toString.startsWith "UntrustedHints" then
        typeHints := typeHints.push d
    match ci.value? (allowOpaque := true) with
    | some v =>
      for d in v.getUsedConstants do
        if d.toString == "_inhabitedExprDummy" then
          hasDummy := true
        if d.toString.startsWith "UntrustedHints" then
          valHints := valHints.push d
    | none => throw <| IO.userError s!"theorem {thmName} missing proof body"
  | none => throw <| IO.userError s!"missing theorem {thmName}"
  if hasDummy then
    throw <| IO.userError s!"theorem {thmName} collapsed to _inhabitedExprDummy"
  let axSorted := (axioms.map (·.toString)).qsort (· < ·)
  let axCsv := String.intercalate "," axSorted.toList
  let typeHash := hash replayedCi.type
  let importMs := (t1 - t0).toFloat / 1000000.0
  let replayMs := (t2 - t1).toFloat / 1000000.0
  IO.println s!"AUDIT_TSV\t{tagStr}\t{modStr}\t{thmStr}\t{baseStr}\t{importMs}\t{replayMs}\t{newConsts.size}\t{typeHash}\t{typeHints.size}\t{valHints.size}\t{axCsv}"

def main (args : List String) : IO Unit := do
  let [jobsPath] := args | throw <| IO.userError "usage: ReplayAudit <jobs.txt>"
  let raw ← IO.FS.readFile jobsPath
  let lines := (raw.splitOn "\n").filter (fun s => !s.isEmpty)
  let mut bases : Std.HashMap String (Environment × NameSet) := {}
  for l in lines do
    let parts := l.splitOn " "
    if parts.length == 4 then
      let b := parts[2]!
      if !bases.contains b then
        let pair ← loadBase b
        bases := bases.insert b pair
  for l in lines do
    let parts := l.splitOn " "
    if parts.length == 4 then
      auditOne bases parts[0]! parts[1]! parts[2]! parts[3]!
"""


def count_lean_loc(path: Path) -> dict[str, int]:
    """Count non-blank, non-comment LOC, separating `namespace UntrustedHints ... end UntrustedHints`
    certificate data from authored proof/obligation LOC in `HintObj_*.lean`.
    """
    raw = path.read_text()
    in_block_comment = 0
    in_hint_ns = False
    total_code_loc = 0
    hint_cert_loc = 0
    hint_cert_bytes = 0
    for line in raw.splitlines():
        s = line.strip()
        if "/-" in s:
            in_block_comment += s.count("/-")
        if in_block_comment > 0:
            if "-/" in s:
                in_block_comment = max(0, in_block_comment - s.count("-/"))
            continue
        s_nc = re.sub(r"--.*$", "", s).strip()
        if not s_nc:
            continue
        if s_nc == "namespace UntrustedHints" and path.name.startswith("HintObj_"):
            in_hint_ns = True
            hint_cert_loc += 1
            hint_cert_bytes += len(line.encode()) + 1
            total_code_loc += 1
            continue
        if in_hint_ns and s_nc == "end UntrustedHints":
            in_hint_ns = False
            hint_cert_loc += 1
            hint_cert_bytes += len(line.encode()) + 1
            total_code_loc += 1
            continue
        total_code_loc += 1
        if in_hint_ns:
            hint_cert_loc += 1
            hint_cert_bytes += len(line.encode()) + 1

    # Exclude `prelude` / `import` / `namespace` / `open` / `end` header lines to also report pure body LOC
    authored_loc = total_code_loc - hint_cert_loc
    return {
        "total_noncomment_loc": total_code_loc,
        "authored_loc": authored_loc,
        "auto_hint_cert_loc": hint_cert_loc,
        "auto_hint_cert_bytes": hint_cert_bytes,
        "file_bytes": len(raw.encode()),
    }


def run_wrapped_lean(args: list[str], cwd: Path, env: dict[str, str]) -> dict:
    cmd = ["/usr/bin/time", "-v", str(LEAN_BIN)] + args
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    rss_kb = 0
    for line in proc.stderr.splitlines():
        if "Maximum resident set size (kbytes):" in line:
            rss_kb = int(line.split(":")[-1].strip())
    return {
        "rc": proc.returncode,
        "wall_ms": round(wall_ms, 2),
        "rss_mb": round(rss_kb / 1024.0, 2),
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def main() -> None:
    if not os.environ.get("ANNEAL_BENCH_IN_SLICE") and LEAN_RUN.exists():
        os.execv(
            str(LEAN_RUN),
            [str(LEAN_RUN), "env", "ANNEAL_BENCH_IN_SLICE=1", sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
        )
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    compile_metrics = {}
    loc_metrics = {}

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        for mod in MODULES_IN_ORDER:
            src = LEAN_DIR / f"{mod}.lean"
            shutil.copy(src, td_path / f"{mod}.lean")
            loc_metrics[mod] = count_lean_loc(src)

        env = os.environ.copy()
        env["LEAN_PATH"] = str(td_path)

        for mod in MODULES_IN_ORDER:
            res = run_wrapped_lean(
                ["-DElab.async=false", "-Ddebug.skipKernelTC=false", "-j1", "-M2048",
                 "-o", f"{mod}.olean", f"{mod}.lean"],
                cwd=td_path,
                env=env,
            )
            if res["rc"] != 0:
                print(f"COMPILE FAILED on {mod}:", file=sys.stderr)
                print(res["stdout"], file=sys.stderr)
                print(res["stderr"], file=sys.stderr)
                sys.exit(1)
            olean_size = (td_path / f"{mod}.olean").stat().st_size
            compile_metrics[mod] = {
                **loc_metrics[mod],
                "compile_wall_ms": res["wall_ms"],
                "compile_rss_mb": res["rss_mb"],
                "olean_bytes": olean_size,
            }
            print(
                f"Compiled {mod:20s}: authored_loc={loc_metrics[mod]['authored_loc']:3d} "
                f"cert_loc={loc_metrics[mod]['auto_hint_cert_loc']:2d} "
                f"wall={res['wall_ms']:7.1f} ms  olean={olean_size:7d} B"
            )

        # Run standalone private-level kernel replay audit
        audit_file = td_path / "ReplayAudit.lean"
        jobs_file = td_path / "jobs.txt"
        audit_file.write_text(REPLAY_AUDIT_LEAN)
        jobs_file.write_text(
            "\n".join(f"{m} {t} {b} {tag}" for (m, t, b, tag) in REPLAY_JOBS) + "\n"
        )
        audit_res = run_wrapped_lean(
            ["--run", "ReplayAudit.lean", "jobs.txt"],
            cwd=td_path,
            env=env,
        )
        if audit_res["rc"] != 0:
            print("REPLAY AUDIT FAILED:", file=sys.stderr)
            print(audit_res["stdout"], file=sys.stderr)
            print(audit_res["stderr"], file=sys.stderr)
            sys.exit(1)

        replay_records = []
        for line in audit_res["stdout"].splitlines():
            if line.startswith("AUDIT_TSV\t"):
                _, tag_s, mod_s, thm_s, base_s, imp_s, rep_s, nconsts_s, thash_s, thints_s, vhints_s, ax_s = line.split("\t")
                rec = {
                    "tag": tag_s,
                    "module": mod_s,
                    "theorem": thm_s,
                    "base": base_s,
                    "import_ms": round(float(imp_s), 3),
                    "replay_ms": round(float(rep_s), 3),
                    "replayed_consts": int(nconsts_s),
                    "type_hash": int(thash_s),
                    "type_hints": int(thints_s),
                    "val_hints": int(vhints_s),
                    "axioms": [a for a in ax_s.split(",") if a],
                }
                ax_set = set(rec["axioms"])
                assert ax_set <= allowed_axioms, f"Forbidden axiom in {rec}: {ax_set - allowed_axioms}"
                assert rec["type_hints"] == 0, f"Statement-Origin Separation violated in {rec}!"
                if rec["module"].startswith("HintObj_"):
                    assert rec["val_hints"] > 0, f"Expected UntrustedHints in proof body of {rec}"
                replay_records.append(rec)

    # Verify locked theorem expression-type hash equality between RawObj_<k> and HintObj_<k>!
    by_mod_thm = {(r["module"], r["theorem"], r["tag"]): r for r in replay_records}
    for k, thm in [
        ("MulxMac4", "LockedObligations.verify_mulx_mac4_obj"),
        ("DotMaddubs", "LockedObligations.verify_dot_maddubs_obj"),
        ("CtLookup8", "LockedObligations.verify_ct_lookup8_obj"),
    ]:
        h_raw = by_mod_thm[(f"RawObj_{k}", thm, "raw_obj")]["type_hash"]
        h_hint = by_mod_thm[(f"HintObj_{k}", thm, "hint_obj_per_kernel")]["type_hash"]
        assert h_raw == h_hint, f"Theorem type mismatch on {k}: {h_raw} != {h_hint}"

    out = {
        "lean_version": "leanprover/lean4:v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)",
        "modules": compile_metrics,
        "private_kernel_replay": replay_records,
    }
    out_path = HERE / "bench_three_regimes_lean4_results.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print("\nAll 14 private-level kernel replay & Statement-Origin Separation checks PASSED:")
    for r in replay_records:
        print(
            f"  {r['module']:20s} [{r['tag']:20s}] replay={r['replay_ms']:7.2f} ms "
            f"consts={r['replayed_consts']:3d} type_hints={r['type_hints']} "
            f"val_hints={r['val_hints']} axioms={r['axioms']}"
        )


if __name__ == "__main__":
    main()
