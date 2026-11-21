#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compile and fresh-kernel replay all Lean 4.34.1 SFI proofs and GCC `.o` certificate.

Executes inside `tempfile.TemporaryDirectory()`:
1. Compiles `PicMultiFnSfi.lean` (`-DElab.async=false -Ddebug.skipKernelTC=false -j1`);
2. Compiles `UnwindJumpOverAndTreeBorrows.lean`;
3. Generates `StockGccWorkloadCert.lean` from the 2,048-byte `.text.sfi` machine code
   in `stock_gcc_sfi_benchmark_results.json` (emitted by `gcc 15.2.0 -O2` +
   `sfi_gcc_rewriter.py`) and proves `checkSfiPicMultiFn 2048 stockGccWorkloadImg = true`
   plus `stockGccWorkload_pic_sfi_sound` in the Lean 4.34.1 kernel;
4. Runs a standalone `(trustLevel := 0) (plugins := #[]) (loadExts := false)
   (level := .private)` `base.toKernelEnv.replay` audit checking all theorems for
   zero `sorryAx`, zero `Lean.ofReduceBool`, zero `_inhabitedExprDummy`, and
   strict adherence to the 3-axiom ceiling `{propext, Classical.choice, Quot.sound}`.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

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

def collectTransitiveAxioms (env : Environment) (root : Name) : IO (Array Name) := do
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if !visited.contains c then
        visited := visited.insert c
        match env.find? c with
        | some (.axiomInfo _) => axioms := axioms.insert c
        | some ci =>
          for d in ci.getUsedConstantsAsSet do
            if !visited.contains d then
              stack := d :: stack
        | none => pure ()
  let arr := axioms.toArray.qsort (fun a b => a.toString < b.toString)
  return arr

def checkNoDummy (env : Environment) (thmName : Name) : IO Unit := do
  match env.find? thmName with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v =>
      for d in v.getUsedConstants do
        if d.toString == "_inhabitedExprDummy" then
          throw <| IO.userError s!"{thmName} collapsed to _inhabitedExprDummy"
    | none => throw <| IO.userError s!"{thmName} missing proof body"
  | none => throw <| IO.userError s!"missing theorem {thmName}"

def auditModule (bases : Std.HashMap String (Environment × NameSet))
    (modStr baseStr thmsCsv : String) : IO Unit := do
  let some (base, baseMods) := bases.get? baseStr
    | throw <| IO.userError s!"unknown base {baseStr}"
  let modName := modStr.toName
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := modName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (m, md) in env.header.modules.zip env.header.moduleData do
    if !baseMods.contains m.module then
      for (n, ci) in md.constNames.zip md.constants do
        newConsts := newConsts.insert n ci
  let t1 ← IO.monoMsNow
  let replayed ← base.toKernelEnv.replay newConsts
  let t2 ← IO.monoMsNow
  let thmStrs := (thmsCsv.splitOn ",").filter (fun s => !s.isEmpty)
  for ts in thmStrs do
    let tn := ts.toName
    if (replayed.find? tn).isNone then
      throw <| IO.userError s!"theorem {tn} absent after fresh kernel replay"
    checkNoDummy env tn
    let axs ← collectTransitiveAxioms env tn
    let axNames := axs.toList.map Name.toString
    IO.println s!"THM_OK|{modStr}|{ts}|{t1 - t0}|{t2 - t1}|{newConsts.size}|{String.intercalate "," axNames}"

def main (args : List String) : IO Unit := do
  let [jobsPath] := args | throw <| IO.userError "usage: ReplayAudit <jobs.txt>"
  let raw ← IO.FS.readFile jobsPath
  let lines := (raw.splitOn "\n").filter (fun (s : String) => !s.isEmpty)
  let mut bases : Std.HashMap String (Environment × NameSet) := {}
  for l in lines do
    let parts := l.splitOn "|"
    if parts.length == 3 then
      let b := parts[1]!
      if !bases.contains b then
        let pair ← loadBase b
        bases := bases.insert b pair
  for l in lines do
    let parts := l.splitOn "|"
    if parts.length == 3 then
      auditModule bases parts[0]! parts[1]! parts[2]!
"""


def find_lean_runner() -> tuple[list[str], str]:
  lean_env = os.environ.get("LEAN_BIN")
  if lean_env:
    lean_bin = Path(lean_env)
  else:
    elan_4341 = (
        Path.home()
        / ".elan"
        / "toolchains"
        / "leanprover--lean4---v4.34.1"
        / "bin"
        / "lean"
    )
    lean_bin = elan_4341 if elan_4341.exists() else Path(shutil.which("lean") or "lean")

  wrapper_cand = Path.home() / ".local" / "bin" / "anneal-lean-run"
  wrapper_which = shutil.which("anneal-lean-run")
  prefix: list[str] = []
  if wrapper_cand.exists():
    prefix = [str(wrapper_cand)]
  elif wrapper_which:
    prefix = [wrapper_which]

  ver_proc = subprocess.run(
      [*prefix, str(lean_bin), "--version"],
      check=True,
      capture_output=True,
      text=True,
  )
  return [*prefix, str(lean_bin)], ver_proc.stdout.strip()


def run_timed(cmd: list[str], env: dict[str, str], cwd: Path) -> dict[str, object]:
  use_time = Path("/usr/bin/time").exists()
  full_cmd = ["/usr/bin/time", "-v", *cmd] if use_time else cmd
  t0 = time.perf_counter()
  proc = subprocess.run(
      full_cmd,
      cwd=str(cwd),
      env=env,
      capture_output=True,
      text=True,
      check=False,
  )
  wall_s = time.perf_counter() - t0
  if proc.returncode != 0:
    raise RuntimeError(
        f"Command failed (rc={proc.returncode}):\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
    )
  user_s = 0.0
  sys_s = 0.0
  rss_kb = 0
  for line in proc.stderr.splitlines():
    m_u = re.search(r"User time \(seconds\):\s*([0-9.]+)", line)
    m_s = re.search(r"System time \(seconds\):\s*([0-9.]+)", line)
    m_r = re.search(r"Maximum resident set size \(kbytes\):\s*([0-9]+)", line)
    if m_u:
      user_s = float(m_u.group(1))
    if m_s:
      sys_s = float(m_s.group(1))
    if m_r:
      rss_kb = int(m_r.group(1))
  return {
      "wall_s": round(wall_s, 4),
      "cpu_s": round(user_s + sys_s, 4),
      "rss_mb": round(rss_kb / 1024.0, 2),
      "stdout": proc.stdout,
  }


def format_u8_leaf(bs: bytes) -> str:
  rows: list[str] = []
  for off in range(0, len(bs), 16):
    chunk = bs[off : off + 16]
    rows.append("  " + ", ".join(f"0x{b:02X}" for b in chunk))
  return "[\n" + ",\n".join(rows) + "\n]"


def build_gcc_cert_lean(code_bytes: bytes) -> str:
  assert len(code_bytes) == 2048, f"expected 2048 bytes, got {len(code_bytes)}"
  leaves = [code_bytes[i * 512 : (i + 1) * 512] for i in range(4)]
  parts = [
      "prelude",
      "import PicMultiFnSfi",
      "",
      "namespace StockGccWorkloadCert",
      "open PicMultiFnSfi",
      "",
  ]
  for idx, chunk in enumerate(leaves):
    parts.append(f"def gccLeaf{idx} : ByteCodeTree := .leaf {format_u8_leaf(chunk)}")
    parts.append("")
    lo = idx * 512
    hi = (idx + 1) * 512
    parts.append(
        f"theorem gccLeaf{idx}_ok : checkSfiPicSubtree 2048 {lo} {hi} gccLeaf{idx} = true := rfl"
    )
    parts.append("")
  parts.extend([
      "def gccNodeLeft : ByteCodeTree := .node 512 gccLeaf0 gccLeaf1",
      "def gccNodeRight : ByteCodeTree := .node 512 gccLeaf2 gccLeaf3",
      "def stockGccWorkloadImg : X64ObjImage := { code := .node 1024 gccNodeLeft gccNodeRight }",
      "",
      "theorem gccNodeLeft_ok : checkSfiPicSubtree 2048 0 1024 gccNodeLeft = true :=",
      "  checkSfiPicSubtree_node rfl rfl gccLeaf0_ok gccLeaf1_ok",
      "",
      "theorem gccNodeRight_ok : checkSfiPicSubtree 2048 1024 2048 gccNodeRight = true :=",
      "  checkSfiPicSubtree_node rfl rfl gccLeaf2_ok gccLeaf3_ok",
      "",
      "theorem stockGccWorkload_verified : checkSfiPicMultiFn 2048 stockGccWorkloadImg = true := by",
      "  have hroot : checkSfiPicSubtree 2048 0 2048 stockGccWorkloadImg.code = true :=",
      "    checkSfiPicSubtree_node rfl rfl gccNodeLeft_ok gccNodeRight_ok",
      "  dsimp [checkSfiPicMultiFn]",
      "  rw [hroot]",
      "  rfl",
      "",
      "theorem stockGccWorkload_pic_sfi_sound",
      "    {codeBase arenaBase : BitVec 64}",
      "    (hfit : codeBase.toNat + 2048 < 2 ^ 64)",
      "    (s0 : RealX64State) (entryOff : Nat)",
      "    (hentry_lt : entryOff < 2048) (hentry_mod : entryOff % 32 = 0)",
      "    (hrip0 : s0.rip = codeBase + BitVec.ofNat 64 entryOff)",
      "    (hr15_0 : s0.regs .r15 = codeBase)",
      "    (hr14_0 : s0.regs .r14 = arenaBase)",
      "    (hr13_0 : (s0.regs .r13).toNat < 4294967296)",
      "    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (s0.regs .rsp + BitVec.ofNat 64 k))",
      "    (hrun0 : s0.exitKind = .running)",
      "    (hnf0 : s0.fault = false) :",
      "    ∀ (steps : Nat) (nd : Nat → UndefFlags),",
      "      let sf := runPicPortalX64 codeBase 2048 stockGccWorkloadImg steps nd s0",
      "      sf.fault = false ∧",
      "      sf.regs .r15 = codeBase ∧",
      "      sf.regs .r14 = arenaBase ∧",
      "      (sf.regs .r13).toNat < 4294967296 ∧",
      "      (∀ a, OutsideSymmetricArena arenaBase a → sf.mem a = s0.mem a) ∧",
      "      (sf.exitKind = .running →",
      "        codeBase.toNat ≤ sf.rip.toNat ∧ sf.rip.toNat < codeBase.toNat + 2048 ∧",
      "        sf.regs .rsp = s0.regs .rsp ∧",
      "        (∀ r, isPicHostProtectedReg r = true → sf.regs r = s0.regs r)) ∧",
      "      (sf.exitKind = .portalReturn →",
      "        sf.rip = readMem64 s0.mem (s0.regs .rsp) ∧",
      "        sf.regs .rsp = s0.regs .rsp + 8#64 ∧",
      "        (∀ r, isPicHostProtectedReg r = true → r ≠ .rsp → sf.regs r = s0.regs r)) ∧",
      "      (sf.exitKind = .portalHostcall →",
      "        sf.regs .rsp = s0.regs .rsp ∧",
      "        (∀ r, isPicHostProtectedReg r = true → sf.regs r = s0.regs r)) :=",
      "  checkSfiPicMultiFn_sound stockGccWorkload_verified hfit s0 entryOff",
      "    hentry_lt hentry_mod hrip0 hr15_0 hr14_0 hr13_0 hhost_rsp hrun0 hnf0",
      "",
      "end StockGccWorkloadCert",
      "",
  ])
  return "\n".join(parts)


def main() -> None:
  here = Path(__file__).resolve().parent
  pic_src = here / "PicMultiFnSfi.lean"
  unwind_src = here / "UnwindJumpOverAndTreeBorrows.lean"
  gcc_json_path = here / "stock_gcc_sfi_benchmark_results.json"

  gcc_meta = json.loads(gcc_json_path.read_text(encoding="utf-8"))
  hex_2048 = gcc_meta["sfi_text_hex_2048b"]
  code_bytes = bytes.fromhex(hex_2048)
  code_sha256 = hashlib.sha256(code_bytes).hexdigest()

  lean_cmd, lean_version = find_lean_runner()
  lean_flags = ["-DElab.async=false", "-Ddebug.skipKernelTC=false", "-j1", "-M2048"]

  with tempfile.TemporaryDirectory() as tmp:
    tmp_dir = Path(tmp)
    shutil.copy2(pic_src, tmp_dir / "PicMultiFnSfi.lean")
    shutil.copy2(unwind_src, tmp_dir / "UnwindJumpOverAndTreeBorrows.lean")
    cert_text = build_gcc_cert_lean(code_bytes)
    (tmp_dir / "StockGccWorkloadCert.lean").write_text(cert_text, encoding="utf-8")

    env = dict(os.environ)
    env["LEAN_PATH"] = str(tmp_dir)

    c_pic = run_timed(
        [*lean_cmd, *lean_flags, "-o", "PicMultiFnSfi.olean", "PicMultiFnSfi.lean"],
        env=env,
        cwd=tmp_dir,
    )
    c_unw = run_timed(
        [
            *lean_cmd,
            *lean_flags,
            "-o",
            "UnwindJumpOverAndTreeBorrows.olean",
            "UnwindJumpOverAndTreeBorrows.lean",
        ],
        env=env,
        cwd=tmp_dir,
    )
    c_cert = run_timed(
        [
            *lean_cmd,
            *lean_flags,
            "-o",
            "StockGccWorkloadCert.olean",
            "StockGccWorkloadCert.lean",
        ],
        env=env,
        cwd=tmp_dir,
    )

    (tmp_dir / "ReplayAudit.lean").write_text(REPLAY_AUDIT_LEAN, encoding="utf-8")
    jobs = [
        (
            "PicMultiFnSfi|Init|"
            + ",".join([
                "PicMultiFnSfi.raw_ret_0xc3_rop_escape",
                "PicMultiFnSfi.legacy_abs32_indirect_jmp_null_page_fault",
                "PicMultiFnSfi.checkSfiPicMultiFn_rejects_untrusted_ret",
                "PicMultiFnSfi.checkSfiPicMultiFn_sound",
            ])
        ),
        (
            "UnwindJumpOverAndTreeBorrows|Init|"
            + ",".join([
                "SfiUnwindAndTreeBorrows.canary_guest_fde_unwind_rop_escape",
                "SfiUnwindAndTreeBorrows.canary_guest_fde_csr_corrupt",
                "SfiUnwindAndTreeBorrows.canary_stateless_reentrant_clobbers_outer_guest_frame",
                "SfiUnwindAndTreeBorrows.reentrant_watermark_disjointness",
                "SfiUnwindAndTreeBorrows.jump_over_fde_zero_guest_reads",
                "SfiUnwindAndTreeBorrows.jump_over_fde_double_nested_reentrant_unwind_sound",
                "SfiUnwindAndTreeBorrows.sfi_arena_loan_preserves_tree_borrows",
                "SfiUnwindAndTreeBorrows.dual_mapped_prot_read_preserves_frozen_and_host_bytes",
            ])
        ),
        (
            "StockGccWorkloadCert|PicMultiFnSfi|"
            + ",".join([
                "StockGccWorkloadCert.stockGccWorkload_verified",
                "StockGccWorkloadCert.stockGccWorkload_pic_sfi_sound",
            ])
        ),
    ]
    (tmp_dir / "jobs.txt").write_text("\n".join(jobs) + "\n", encoding="utf-8")

    c_rep = run_timed(
        [*lean_cmd, "-j1", "-M8192", "--run", "ReplayAudit.lean", "jobs.txt"],
        env=env,
        cwd=tmp_dir,
    )

    audited_theorems: list[dict[str, object]] = []
    for line in str(c_rep["stdout"]).splitlines():
      if not line.startswith("THM_OK|"):
        continue
      _, mod_name, thm_name, import_ms, replay_ms, new_consts, ax_csv = line.split("|")
      axioms = [a for a in ax_csv.split(",") if a]
      disallowed = sorted(set(axioms) - ALLOWED_AXIOMS)
      if disallowed:
        raise RuntimeError(f"Disallowed axioms on {thm_name}: {disallowed}")
      audited_theorems.append({
          "module": mod_name,
          "theorem": thm_name,
          "import_ms": int(import_ms),
          "fresh_kernel_replay_ms": int(replay_ms),
          "replayed_constants": int(new_consts),
          "axioms": axioms,
      })

    if len(audited_theorems) != 14:
      raise RuntimeError(f"Expected 14 audited theorems, got {len(audited_theorems)}")

    results = {
        "lean_version": lean_version,
        "elab_flags": lean_flags,
        "gcc_sfi_text_2048b_sha256": code_sha256,
        "modules": {
            "PicMultiFnSfi.lean": {
                "source_bytes": pic_src.stat().st_size,
                "source_lines": len(pic_src.read_text(encoding="utf-8").splitlines()),
                "wall_s": c_pic["wall_s"],
                "cpu_s": c_pic["cpu_s"],
                "rss_mb": c_pic["rss_mb"],
            },
            "UnwindJumpOverAndTreeBorrows.lean": {
                "source_bytes": unwind_src.stat().st_size,
                "source_lines": len(unwind_src.read_text(encoding="utf-8").splitlines()),
                "wall_s": c_unw["wall_s"],
                "cpu_s": c_unw["cpu_s"],
                "rss_mb": c_unw["rss_mb"],
            },
            "StockGccWorkloadCert.lean (generated in tmpdir)": {
                "source_bytes": len(cert_text.encode("utf-8")),
                "wall_s": c_cert["wall_s"],
                "cpu_s": c_cert["cpu_s"],
                "rss_mb": c_cert["rss_mb"],
            },
        },
        "replay_audit": {
            "trust_level": 0,
            "load_exts": False,
            "visibility_level": "private",
            "wall_s": c_rep["wall_s"],
            "cpu_s": c_rep["cpu_s"],
            "rss_mb": c_rep["rss_mb"],
            "allowed_axioms_ceiling": sorted(ALLOWED_AXIOMS),
            "audited_theorems": audited_theorems,
        },
    }

  out_path = here / "lean_verification_and_replay_results.json"
  out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
  print("ALL_LEAN_PROOFS_GCC_CERT_AND_FRESH_KERNEL_REPLAY_PASSED")
  print(json.dumps(results["modules"], indent=2))


if __name__ == "__main__":
  main()
