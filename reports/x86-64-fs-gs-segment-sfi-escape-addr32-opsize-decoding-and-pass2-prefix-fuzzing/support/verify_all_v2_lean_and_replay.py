#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compile, 352-vector silicon-certify, and fresh-kernel replay all V2 Lean modules.

Executes strictly inside `tempfile.TemporaryDirectory()`:
1. Compiles all 9 staged `.lean` modules under `-DElab.async=false -Ddebug.skipKernelTC=false -j1`,
   asserting each source file is `< 150 KB`, compiles in `< 15.0 s`, and emits zero warnings:
   - `RealX64PrefixSem.lean`
   - `PicMultiFnSfiV2.lean`
   - `StackCanaryLiftV2.lean`
   - `VendorX86RefV2/{Types,Decode,SemanticsScalar,SemanticsSimd,Machine}.lean`
   - `ByteX86Pass2CorrespondenceV2.lean`
2. Generates and kernel-checks `StockGccCanaryWorkloadCertV2.lean` on the 2,048-byte
   `-fstack-protector-strong` `.text.sfi` image (`sfi_gcc_rewriter_v2.py --canary-mode=arena_guarded`),
   proving `checkSfiPicMultiFnV2 2048 stockGccCanaryImg2048 = true` (`rfl`) and instantiating
   `checkSfiPicMultiFnV2_sound` universally over all `(fsBase, gsBase : BitVec 64)`.
3. Generates and kernel-checks `SiliconCartesian352Cert.lean` over all 352 live Intel Xeon
   Ice Lake-SP silicon vectors in `cartesian_prefix_silicon_and_xed_results.json`, proving
   `100.0%` (`352 / 352`) agreement of `VendorX86RefV2` on verdict (`OK_EXEC` / `FAULT_UD` /
   `FAULT_GP0`), byte length, GPRs, `RFLAGS`, `YMM0`, and all 7 `FS`/`GS`/`addr32`/stack
   memory probes (`0` `native_decide`, pure kernel reduction).
4. Runs fresh `(trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)`
   `base.toKernelEnv.replay` across all modules, asserting `0` `sorryAx`, `0` custom
   `axiom`/`opaque`, `0` `isUnsafe`, `0` `isPartial` (`*._unsafe_rec`), `0` `Lean.ofReduceBool`,
   and strictly `Init.*`-only external dependencies.
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

ALLOWED_LOCAL_MODULES = {
    "RealX64PrefixSem",
    "PicMultiFnSfiV2",
    "StackCanaryLiftV2",
    "VendorX86RefV2.Types",
    "VendorX86RefV2.Decode",
    "VendorX86RefV2.SemanticsScalar",
    "VendorX86RefV2.SemanticsSimd",
    "VendorX86RefV2.Machine",
    "ByteX86Pass2CorrespondenceV2",
    "StockGccCanaryShard0",
    "StockGccCanaryShard1",
    "StockGccCanaryWorkloadCertV2",
    "SiliconCartesian352Shard0",
    "SiliconCartesian352Shard1",
    "SiliconCartesian352Shard2",
    "SiliconCartesian352Shard3",
    "SiliconCartesian352Shard4",
    "SiliconCartesian352Cert",
}

REPLAY_AUDIT_LEAN = r"""import Lean
import Lean.Replay

open Lean

def loadInitBase (initModsCsv : String) : IO (Environment × NameSet) := do
  let names := (initModsCsv.splitOn ",").filter (fun s => !s.isEmpty)
  let imps := names.toArray.map (fun s => { module := s.toName : Import })
  let base ← importModules imps {}
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

def checkConstantPurity (n : Name) (ci : ConstantInfo) : IO Unit := do
  let ns := n.toString
  if ci.isUnsafe then
    throw <| IO.userError s!"unsafe constant forbidden: {ns}"
  if ci.isPartial then
    throw <| IO.userError s!"partial constant forbidden: {ns}"
  if (ns.splitOn "_unsafe_rec").length > 1 then
    throw <| IO.userError s!"_unsafe_rec helper forbidden: {ns}"
  match ci with
  | .axiomInfo _ =>
    throw <| IO.userError s!"user axiom forbidden: {ns}"
  | .opaqueInfo _ =>
    throw <| IO.userError s!"opaque constant forbidden: {ns}"
  | _ => pure ()
  match ci.value? (allowOpaque := true) with
  | some v =>
    for d in v.getUsedConstants do
      let ds := d.toString
      if ds == "_inhabitedExprDummy" || ds == "sorryAx" ||
         ds == "Lean.ofReduceBool" || ds == "Lean.trustCompiler" then
        throw <| IO.userError s!"forbidden constant {ds} referenced in {ns}"
  | none => pure ()

def auditRootModule (modStr initModsCsv thmsCsv : String) : IO Unit := do
  let (base, baseMods) ← loadInitBase initModsCsv
  let modName := modStr.toName
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := modName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut extMods : Array String := #[]
  for (m, md) in env.header.modules.zip env.header.moduleData do
    let ms := m.module.toString
    if !baseMods.contains m.module then
      extMods := extMods.push ms
      for (n, ci) in md.constNames.zip md.constants do
        checkConstantPurity n ci
        newConsts := newConsts.insert n ci
  let t1 ← IO.monoMsNow
  let replayed ← base.toKernelEnv.replay newConsts
  let t2 ← IO.monoMsNow
  IO.println s!"MOD_OK|{modStr}|{t1 - t0}|{t2 - t1}|{newConsts.size}|{String.intercalate "," extMods.toList}"
  let thmStrs := (thmsCsv.splitOn ",").filter (fun s => !s.isEmpty)
  for ts in thmStrs do
    let tn := ts.toName
    if (replayed.find? tn).isNone then
      throw <| IO.userError s!"theorem {tn} absent after fresh kernel replay"
    let axs ← collectTransitiveAxioms env tn
    let axNames := axs.toList.map Name.toString
    IO.println s!"THM_OK|{modStr}|{ts}|{String.intercalate "," axNames}"

def main (args : List String) : IO Unit := do
  let [jobsPath] := args | throw <| IO.userError "usage: ReplayAudit <jobs.txt>"
  let raw ← IO.FS.readFile jobsPath
  let lines := (raw.splitOn "\n").filter (fun (s : String) => !s.isEmpty)
  for l in lines do
    let parts := l.splitOn "|"
    if parts.length == 3 then
      auditRootModule parts[0]! parts[1]! parts[2]!
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
    if proc.stdout.strip():
        # Note: ReplayAudit uses stdout intentionally; `.lean` compiles must have empty stdout!
        pass
    user_s = 0.0
    sys_s = 0.0
    rss_kb = 0
    non_time_stderr: list[str] = []
    for line in proc.stderr.splitlines():
        m_u = re.search(r"User time \(seconds\):\s*([0-9.]+)", line)
        m_s = re.search(r"System time \(seconds\):\s*([0-9.]+)", line)
        m_r = re.search(r"Maximum resident set size \(kbytes\):\s*([0-9]+)", line)
        if m_u:
            user_s = float(m_u.group(1))
        elif m_s:
            sys_s = float(m_s.group(1))
        elif m_r:
            rss_kb = int(m_r.group(1))
        elif not line.startswith("\t") and "Command being timed:" not in line:
            non_time_stderr.append(line)
    return {
        "wall_s": round(wall_s, 4),
        "cpu_s": round(user_s + sys_s, 4),
        "rss_mb": round(rss_kb / 1024.0, 2),
        "stdout": proc.stdout,
        "extra_stderr": "\n".join(non_time_stderr).strip(),
    }


def format_u8_leaf(bs: bytes) -> str:
    rows: list[str] = []
    for off in range(0, len(bs), 16):
        chunk = bs[off : off + 16]
        rows.append("  " + ", ".join(f"0x{b:02X}" for b in chunk))
    return "[\n" + ",\n".join(rows) + "\n]"


def build_gcc_canary_shards_lean(code_bytes: bytes) -> tuple[str, str, str]:
    assert len(code_bytes) == 2048, f"expected 2048 bytes, got {len(code_bytes)}"
    leaves = [code_bytes[i * 512 : (i + 1) * 512] for i in range(4)]

    shard0 = "\n".join([
        "prelude",
        "import PicMultiFnSfiV2",
        "namespace StockGccCanaryShard0",
        "open RealX64PrefixSem PicMultiFnSfiV2",
        f"def leaf0 : ByteCodeTree := .leaf {format_u8_leaf(leaves[0])}",
        f"def leaf1 : ByteCodeTree := .leaf {format_u8_leaf(leaves[1])}",
        "def top0 : ByteCodeTree := .node 512 leaf0 leaf1",
        "theorem top0_ok : checkSfiPicSubtreeBoundedV2 2048 63 0 1024 top0 = true := rfl",
        "end StockGccCanaryShard0",
        "",
    ])
    shard1 = "\n".join([
        "prelude",
        "import PicMultiFnSfiV2",
        "namespace StockGccCanaryShard1",
        "open RealX64PrefixSem PicMultiFnSfiV2",
        f"def leaf2 : ByteCodeTree := .leaf {format_u8_leaf(leaves[2])}",
        f"def leaf3 : ByteCodeTree := .leaf {format_u8_leaf(leaves[3])}",
        "def top1 : ByteCodeTree := .node 512 leaf2 leaf3",
        "theorem top1_ok : checkSfiPicSubtreeBoundedV2 2048 63 1024 2048 top1 = true := rfl",
        "end StockGccCanaryShard1",
        "",
    ])
    top = "\n".join([
        "prelude",
        "import StockGccCanaryShard0",
        "import StockGccCanaryShard1",
        "",
        "namespace StockGccCanaryWorkloadCertV2",
        "open RealX64PrefixSem PicMultiFnSfiV2 StockGccCanaryShard0 StockGccCanaryShard1",
        "",
        "def stockGccCanaryImg2048 : X64ObjImage := { code := .node 1024 top0 top1 }",
        "",
        "theorem stockGccCanaryWorkload2048_verified :"
        " checkSfiPicMultiFnV2 2048 stockGccCanaryImg2048 = true := by",
        "  change (natLeB 96 2048 && natEqB (2048 % 32) 0 &&",
        "    (natEqB (1024 % 32) 0 && natLeB 1024 2048 &&",
        "     checkSfiPicSubtreeBoundedV2 2048 63 0 1024 top0 &&",
        "     checkSfiPicSubtreeBoundedV2 2048 63 1024 2048 top1)) = true",
        "  rw [top0_ok, top1_ok]",
        "  rfl",
        "",
        "theorem stockGccCanaryWorkload2048_sfi_sound",
        "    {codeBase arenaBase fsBase gsBase : BitVec 64}",
        "    (hfit : codeBase.toNat + 2048 < 2 ^ 64)",
        "    (s0 : RealX64PrefixState) (entryOff : Nat)",
        "    (hentry_lt : entryOff < 2048) (hentry_mod : entryOff % 32 = 0)",
        "    (hrip0 : s0.rip = codeBase + BitVec.ofNat 64 entryOff)",
        "    (hfs0 : s0.fsBase = fsBase)",
        "    (hgs0 : s0.gsBase = gsBase)",
        "    (hr15_0 : s0.regs .r15 = codeBase)",
        "    (hr14_0 : s0.regs .r14 = arenaBase)",
        "    (hr13_0 : (s0.regs .r13).toNat < 4294967296)",
        "    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (s0.regs .rsp + BitVec.ofNat 64 k))",
        "    (hrun0 : s0.exitKind = .running)",
        "    (hnf0 : s0.fault = false) :",
        "    ∀ (steps : Nat) (nd : Nat → UndefFlags),",
        "      let sf := runPicPortalX64V2 codeBase 2048 stockGccCanaryImg2048 steps nd s0",
        "      sf.fault = false ∧",
        "      sf.fsBase = fsBase ∧",
        "      sf.gsBase = gsBase ∧",
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
        "  checkSfiPicMultiFnV2_sound stockGccCanaryWorkload2048_verified hfit s0 entryOff",
        "    hentry_lt hentry_mod hrip0 hfs0 hgs0 hr15_0 hr14_0 hr13_0 hhost_rsp hrun0 hnf0",
        "",
        "end StockGccCanaryWorkloadCertV2",
        "",
    ])
    return shard0, shard1, top


def build_silicon_cartesian_352_lean(vectors: list[dict[str, object]]) -> tuple[list[str], str]:
    assert len(vectors) == 352, f"expected 352 vectors, got {len(vectors)}"
    parts = [
        "prelude",
        "import VendorX86RefV2.Machine",
        "",
        "namespace SiliconCartesian352Cert",
        "open VendorX86RefV2",
        "",
        "def initQwordAt (qIdx : Nat) : BitVec 64 :=",
        "  if qIdx == 0x0000000140010000 / 8 + 0 then 0xA1A1A1A111112222#64",
        "  else if qIdx == 0x0000000140010000 / 8 + 1 then (0xA1A1A1A111112222#64 ^^^ 0x0101010101010101#64)",
        "  else if qIdx == 0x0000000140010000 / 8 + 2 then (0xA1A1A1A111112222#64 ^^^ 0x0202020202020202#64)",
        "  else if qIdx == 0x0000000140010000 / 8 + 3 then (0xA1A1A1A111112222#64 ^^^ 0x0303030303030303#64)",
        "  else if qIdx == 0x0000000040010000 / 8 + 0 then 0xB2B2B2B233334444#64",
        "  else if qIdx == 0x0000000040010000 / 8 + 1 then (0xB2B2B2B233334444#64 ^^^ 0x0101010101010101#64)",
        "  else if qIdx == 0x0000000040010000 / 8 + 2 then (0xB2B2B2B233334444#64 ^^^ 0x0202020202020202#64)",
        "  else if qIdx == 0x0000000040010000 / 8 + 3 then (0xB2B2B2B233334444#64 ^^^ 0x0303030303030303#64)",
        "  else if qIdx == 0x0000000440010000 / 8 + 0 then 0xF564F56455556666#64",
        "  else if qIdx == 0x0000000440010000 / 8 + 1 then (0xF564F56455556666#64 ^^^ 0x0101010101010101#64)",
        "  else if qIdx == 0x0000000440010000 / 8 + 2 then (0xF564F56455556666#64 ^^^ 0x0202020202020202#64)",
        "  else if qIdx == 0x0000000440010000 / 8 + 3 then (0xF564F56455556666#64 ^^^ 0x0303030303030303#64)",
        "  else if qIdx == 0x0000000340010000 / 8 + 0 then 0xF532F53277778888#64",
        "  else if qIdx == 0x0000000340010000 / 8 + 1 then (0xF532F53277778888#64 ^^^ 0x0101010101010101#64)",
        "  else if qIdx == 0x0000000340010000 / 8 + 2 then (0xF532F53277778888#64 ^^^ 0x0202020202020202#64)",
        "  else if qIdx == 0x0000000340010000 / 8 + 3 then (0xF532F53277778888#64 ^^^ 0x0303030303030303#64)",
        "  else if qIdx == 0x0000000640010000 / 8 + 0 then 0x656465649999AAAA#64",
        "  else if qIdx == 0x0000000640010000 / 8 + 1 then (0x656465649999AAAA#64 ^^^ 0x0101010101010101#64)",
        "  else if qIdx == 0x0000000640010000 / 8 + 2 then (0x656465649999AAAA#64 ^^^ 0x0202020202020202#64)",
        "  else if qIdx == 0x0000000640010000 / 8 + 3 then (0x656465649999AAAA#64 ^^^ 0x0303030303030303#64)",
        "  else if qIdx == 0x0000000540010000 / 8 + 0 then 0x65326532BBBBCCCC#64",
        "  else if qIdx == 0x0000000540010000 / 8 + 1 then (0x65326532BBBBCCCC#64 ^^^ 0x0101010101010101#64)",
        "  else if qIdx == 0x0000000540010000 / 8 + 2 then (0x65326532BBBBCCCC#64 ^^^ 0x0202020202020202#64)",
        "  else if qIdx == 0x0000000540010000 / 8 + 3 then (0x65326532BBBBCCCC#64 ^^^ 0x0303030303030303#64)",
        "  else if qIdx == 0x0000000300000028 / 8 then 0xCA4A2800DEADBEEF#64",
        "  else if qIdx == 0x0000000040000808 / 8 then 0x32E19000CAFE1234#64",
        "  else if qIdx == 0x0000000700010800 / 8 then 0x0000000240000100#64",
        "  else if qIdx == 0x0000000700010900 / 8 then 0x778899AABBCCDDEE#64",
        "  else if qIdx >= 0x0000000700010000 / 8 && qIdx < 0x0000000700012000 / 8 then 0xEEEEEEEEEEEEEEEE#64",
        "  else 0#64",
        "",
        "def initMem : ByteMem := fun a =>",
        "  byteOf64 (initQwordAt (a.toNat / 8)) (a.toNat % 8)",
        "",
        "def initGpr : Gpr → BitVec 64",
        "  | .rax => 0xA1A1A1A111112222#64",
        "  | .rcx => 0x0123456789ABCDEF#64",
        "  | .rdx => 0xCA4A2800DEADBEEF#64",
        "  | .rsi => 0x0000000200000003#64",
        "  | .rdi => 0x0000000140010000#64",
        "  | .r15 => 0x0000000140010000#64",
        "  | .r8  => 0x8888777766665555#64",
        "  | .r9  => 0x1111222233334444#64",
        "  | .rsp => 0x0000000700010800#64",
        "  | .rbp => 0x0000000700010900#64",
        "  | _    => 0#64",
        "",
        "def initYmm : YmmIdx → BitVec 256 := fun idx =>",
        "  if idx.val == 0 then",
        "    0x3132333435363738212223242526272811121314151617180102030405060708#256",
        "  else 0#256",
        "",
        "def initState : MachineState :=",
        "  { rip    := 0x0000000240000800#64",
        "    gpr    := initGpr",
        "    ymm    := initYmm",
        "    flags  := {}",
        "    fsBase := 0x0000000300000000#64",
        "    gsBase := 0x0000000500000000#64",
        "    mem    := initMem }",
        "",
        "def efl6Of (f : RFlags) : BitVec 16 :=",
        "  (if f.cf then 0x001#16 else 0#16) |||",
        "  (if f.pf then 0x004#16 else 0#16) |||",
        "  (if f.af then 0x010#16 else 0#16) |||",
        "  (if f.zf then 0x040#16 else 0#16) |||",
        "  (if f.sf then 0x080#16 else 0#16) |||",
        "  (if f.of then 0x800#16 else 0#16)",
        "",
        "def codeOf16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : CodeMap := fun a =>",
        "  let off := (a - 0x0000000240000800#64).toNat",
        "  match off with",
        "  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6 | 7 => b7",
        "  | 8 => b8 | 9 => b9 | 10 => b10 | 11 => b11 | 12 => b12 | 13 => b13 | 14 => b14 | 15 => b15",
        "  | _ => 0xCC#8",
        "",
        "def checkFaultGp0 (cm : CodeMap) : Bool :=",
        "  (stepWithOracle cm {} initState).fault == some .gp0LengthExceeds15",
        "",
        "def checkFaultUd (cm : CodeMap) : Bool :=",
        "  match (stepWithOracle cm {} initState).fault with",
        "  | some .udExplicit | some .udIllegalLock | some .udVexPrefix",
        "  | some .udVexField | some .udEvexField | some .udUnmapped => true",
        "  | _ => false",
        "",
        "def checkOkExec (cm : CodeMap) (expLen : Nat)",
        "    (expRax expRcx expRdx expRsp expRbp expR8 expR9 : BitVec 64)",
        "    (expEfl6 : BitVec 16) (expYmm0 : BitVec 256)",
        "    (expHi64 expLo32 expFsHi64 expFsLo32 expGsHi64 expGsLo32 expStk : BitVec 64) : Bool :=",
        "  match decodeRef (fetchWindow16 cm initState.rip) with",
        "  | .fault _ => false",
        "  | .ok _ decLen =>",
        "    let sf := stepWithOracle cm {} initState",
        "    (decLen == expLen) &&",
        "    sf.fault.isNone &&",
        "    (sf.gpr .rax == expRax) && (sf.gpr .rcx == expRcx) && (sf.gpr .rdx == expRdx) &&",
        "    (sf.gpr .rsp == expRsp) && (sf.gpr .rbp == expRbp) &&",
        "    (sf.gpr .r8 == expR8) && (sf.gpr .r9 == expR9) &&",
        "    (efl6Of sf.flags == expEfl6) &&",
        "    (sf.ymm ⟨0, by decide⟩ == expYmm0) &&",
        "    (readMem64 sf.mem 0x0000000140010000#64 == expHi64) &&",
        "    (readMem64 sf.mem 0x0000000040010000#64 == expLo32) &&",
        "    (readMem64 sf.mem 0x0000000440010000#64 == expFsHi64) &&",
        "    (readMem64 sf.mem 0x0000000340010000#64 == expFsLo32) &&",
        "    (readMem64 sf.mem 0x0000000640010000#64 == expGsHi64) &&",
        "    (readMem64 sf.mem 0x0000000540010000#64 == expGsLo32) &&",
        "    (readMem64 sf.mem 0x00000007000107F8#64 == expStk)",
        "",
    ]

    shard_bounds = [(0, 71), (71, 142), (142, 213), (213, 284), (284, 352)]
    shard_texts: list[str] = []
    for s_idx, (lo, hi) in enumerate(shard_bounds):
        s_parts = list(parts)
        s_parts[3] = f"namespace SiliconCartesian352Shard{s_idx}"
        sub = vectors[lo:hi]
        exprs: list[str] = []
        for v in sub:
            raw_b = bytes.fromhex(str(v["hex"]))
            if v["silicon_verdict"] == "OK_EXEC":
                obs_len = int(v["silicon_len"])
                win = (raw_b[:obs_len] + b"\xcc" * 16)[:16]
            else:
                win = (raw_b[:16] + b"\xcc" * 16)[:16]
            cm_str = "(codeOf16 " + " ".join(f"0x{x:02X}#8" for x in win) + ")"
            if v["silicon_verdict"] == "FAULT_GP0":
                exprs.append(f"  checkFaultGp0 {cm_str}")
            elif v["silicon_verdict"] == "FAULT_UD":
                exprs.append(f"  checkFaultUd {cm_str}")
            else:
                y0_int = int.from_bytes(bytes.fromhex(str(v["ymm0_hex"])), "little")
                exprs.append(
                    f"  checkOkExec {cm_str} {int(v['silicon_len'])}"
                    f" {v['rax']}#64 {v['rcx']}#64 {v['rdx']}#64 {v['rsp']}#64 {v['rbp']}#64"
                    f" {v['r8']}#64 {v['r9']}#64 {v['efl6']}#16 0x{y0_int:064x}#256"
                    f" {v['mem_hi64']}#64 {v['mem_lo32']}#64"
                    f" {v['mem_fs_hi64']}#64 {v['mem_fs_lo32']}#64"
                    f" {v['mem_gs_hi64']}#64 {v['mem_gs_lo32']}#64"
                    f" {v['mem_stk_push64']}#64"
                )
        s_parts.append(f"def checkShard{s_idx} : Bool :=\n" + " &&\n".join(exprs))
        s_parts.append(f"theorem shard{s_idx}_ok : checkShard{s_idx} = true := rfl")
        s_parts.append(f"end SiliconCartesian352Shard{s_idx}\n")
        shard_texts.append("\n".join(s_parts))

    top_cart = "\n".join([
        "prelude",
        *(f"import SiliconCartesian352Shard{i}" for i in range(5)),
        "namespace SiliconCartesian352Cert",
        "open " + " ".join(f"SiliconCartesian352Shard{i}" for i in range(5)),
        "def checkAll352Vectors : Bool := " + " && ".join(f"checkShard{i}" for i in range(5)),
        "theorem cartesianAll352_silicon_verified : checkAll352Vectors = true := by",
        "  unfold checkAll352Vectors; rw [shard0_ok, shard1_ok, shard2_ok, shard3_ok, shard4_ok]; rfl",
        "end SiliconCartesian352Cert",
        "",
    ])
    return shard_texts, top_cart


def main() -> None:
    here = Path(__file__).resolve().parent
    sfi_json = json.loads((here / "prefix_sfi_escape_and_rewriter_v2_results.json").read_text())
    cart_json = json.loads((here / "cartesian_prefix_silicon_and_xed_results.json").read_text())

    hex_2048 = sfi_json["sfi_gcc_rewriter_v2_benchmark_and_canary"]["sfi_v2_canary_text_hex_2048b"]
    code_bytes = bytes.fromhex(hex_2048)
    code_sha256 = hashlib.sha256(code_bytes).hexdigest()

    lean_cmd, lean_version = find_lean_runner()
    lean_flags = ["-DElab.async=false", "-Ddebug.skipKernelTC=false", "-j1", "-M4096"]

    staged_mods = [
        ("RealX64PrefixSem.lean", "RealX64PrefixSem.olean"),
        ("PicMultiFnSfiV2.lean", "PicMultiFnSfiV2.olean"),
        ("StackCanaryLiftV2.lean", "StackCanaryLiftV2.olean"),
        ("VendorX86RefV2/Types.lean", "VendorX86RefV2/Types.olean"),
        ("VendorX86RefV2/Decode.lean", "VendorX86RefV2/Decode.olean"),
        ("VendorX86RefV2/SemanticsScalar.lean", "VendorX86RefV2/SemanticsScalar.olean"),
        ("VendorX86RefV2/SemanticsSimd.lean", "VendorX86RefV2/SemanticsSimd.olean"),
        ("VendorX86RefV2/Machine.lean", "VendorX86RefV2/Machine.olean"),
        ("ByteX86Pass2CorrespondenceV2.lean", "ByteX86Pass2CorrespondenceV2.olean"),
    ]

    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        (tmp_dir / "VendorX86RefV2").mkdir()
        for src_rel, _ in staged_mods:
            src_path = here / src_rel
            sz = src_path.stat().st_size
            if sz >= 150_000:
                raise RuntimeError(f"{src_rel} exceeds 150 KB budget ({sz} B)")
            shutil.copy2(src_path, tmp_dir / src_rel)

        gcc_s0, gcc_s1, gcc_cert_text = build_gcc_canary_shards_lean(code_bytes)
        (tmp_dir / "StockGccCanaryShard0.lean").write_text(gcc_s0)
        (tmp_dir / "StockGccCanaryShard1.lean").write_text(gcc_s1)
        (tmp_dir / "StockGccCanaryWorkloadCertV2.lean").write_text(gcc_cert_text)

        cart_shards, cart_cert_text = build_silicon_cartesian_352_lean(cart_json["vectors"])
        for i, cs_txt in enumerate(cart_shards):
            (tmp_dir / f"SiliconCartesian352Shard{i}.lean").write_text(cs_txt)
        (tmp_dir / "SiliconCartesian352Cert.lean").write_text(cart_cert_text)

        env = dict(os.environ, LEAN_PATH=str(tmp_dir))
        module_metrics: dict[str, dict[str, object]] = {}

        all_compile_targets = [
            *staged_mods,
            ("StockGccCanaryShard0.lean", "StockGccCanaryShard0.olean"),
            ("StockGccCanaryShard1.lean", "StockGccCanaryShard1.olean"),
            ("StockGccCanaryWorkloadCertV2.lean", "StockGccCanaryWorkloadCertV2.olean"),
            *((f"SiliconCartesian352Shard{i}.lean", f"SiliconCartesian352Shard{i}.olean") for i in range(5)),
            ("SiliconCartesian352Cert.lean", "SiliconCartesian352Cert.olean"),
        ]
        for src_rel, olean_rel in all_compile_targets:
            p = tmp_dir / src_rel
            res = run_timed(
                [*lean_cmd, *lean_flags, "-R", str(tmp_dir), str(p), "-o", str(tmp_dir / olean_rel)],
                env=env,
                cwd=tmp_dir,
            )
            if str(res["stdout"]).strip() or str(res["extra_stderr"]).strip():
                raise RuntimeError(
                    f"Non-empty diagnostic output on {src_rel}:\n{res['stdout']}\n{res['extra_stderr']}"
                )
            if float(res["wall_s"]) >= 15.0:
                raise RuntimeError(f"{src_rel} exceeded 15.0s compile cap: {res['wall_s']}s")
            label = src_rel if (here / src_rel).exists() else f"{src_rel} (generated in tmpdir)"
            module_metrics[label] = {
                "source_bytes": p.stat().st_size,
                "source_lines": len(p.read_text().splitlines()),
                "wall_s": res["wall_s"],
                "cpu_s": res["cpu_s"],
                "rss_mb": res["rss_mb"],
            }

        init_mods_csv = ",".join([
            "Init.Core",
            "Init.Data.BitVec.Basic",
            "Init.Data.BitVec.Lemmas",
            "Init.Data.List.Basic",
            "Init.Data.List.TakeDrop",
            "Init.Data.Nat.Basic",
            "Init.Data.Nat.Bitwise.Lemmas",
        ])

        jobs = [
            "RealX64PrefixSem|" + init_mods_csv + "|" + ",".join([
                "RealX64PrefixSem.decodeX64V2_len_bounds",
                "RealX64PrefixSem.decodeX64V2_prefix_invariant",
                "RealX64PrefixSem.unpatched_decoder_blinds_sfi_to_fs_prefix",
                "RealX64PrefixSem.fs_escape_overwrites_outside_arena_on_realX64",
                "RealX64PrefixSem.gs_escape_overwrites_outside_arena_on_realX64",
                "RealX64PrefixSem.null_cs_2e_preserves_fs_while_lea_ignores_fs",
                "RealX64PrefixSem.addr32_load_and_lock_cmpxchg_truncate_ea",
                "RealX64PrefixSem.op16_push_rex_precedence_and_imm16_len",
            ]),
            "PicMultiFnSfiV2|" + init_mods_csv + "|" + ",".join([
                "PicMultiFnSfiV2.checkSfiPicMultiFnV2_rejects_fs_escape",
                "PicMultiFnSfiV2.checkSfiPicMultiFnV2_rejects_gs_escape",
                "PicMultiFnSfiV2.checkSfiPicMultiFnV2_rejects_addr32_store",
                "PicMultiFnSfiV2.checkSfiPicMultiFnV2_rejects_op16_push",
                "PicMultiFnSfiV2.checkSfiPicMultiFnV2_rejects_op16_jmp",
                "PicMultiFnSfiV2.checkSfiPicMultiFnV2_sound",
            ]),
            "StackCanaryLiftV2|" + init_mods_csv + "|" + ",".join([
                "StackCanaryLiftV2.unpatched_fs28_flat_mismodel_counterexample",
                "StackCanaryLiftV2.gcc_hash2_canary_verified",
                "StackCanaryLiftV2.rust_unexposed_canary_verified",
                "StackCanaryLiftV2.xor_fs28_canary_verified",
                "StackCanaryLiftV2.gcc_hash2_canary_corrupted_traps_to_stack_chk_fail",
            ]),
            "ByteX86Pass2CorrespondenceV2|" + init_mods_csv + "|" + ",".join([
                "VendorX86RefV2.finishLen_le_15",
                "VendorX86RefV2.decodeRef_window16_invariant",
                "VendorX86RefV2.execStepsN_implies_stepsN",
                "ByteX86V2.vendorX86RefV2_step_sub_byteX86V2_step",
                "ByteX86V2.vendorX86RefV2_stepsN_sub_byteX86V2_stepsN",
                "ByteX86V2.blind_pass2_vacuous_simulation",
                "ByteX86V2.pass2_shared_scanPrefixes_blind_spot_counterexample",
                "ByteX86V2.tcb_fs_0x28_canary_load_and_xor",
            ]),
            "StockGccCanaryWorkloadCertV2|" + init_mods_csv + "|" + ",".join([
                "StockGccCanaryWorkloadCertV2.stockGccCanaryWorkload2048_verified",
                "StockGccCanaryWorkloadCertV2.stockGccCanaryWorkload2048_sfi_sound",
            ]),
            "SiliconCartesian352Cert|" + init_mods_csv + "|" + ",".join([
                "SiliconCartesian352Cert.cartesianAll352_silicon_verified",
            ]),
        ]
        (tmp_dir / "ReplayAudit.lean").write_text(REPLAY_AUDIT_LEAN)
        (tmp_dir / "jobs.txt").write_text("\n".join(jobs) + "\n")

        c_rep = run_timed(
            [*lean_cmd, "-j1", "-M8192", "--run", "ReplayAudit.lean", "jobs.txt"],
            env=env,
            cwd=tmp_dir,
        )

        replayed_roots: list[dict[str, object]] = []
        audited_theorems: list[dict[str, object]] = []
        for line in str(c_rep["stdout"]).splitlines():
            if line.startswith("MOD_OK|"):
                _, mod_name, imp_ms, rep_ms, n_consts, ext_csv = line.split("|")
                ext_mods = [m for m in ext_csv.split(",") if m]
                bad_mods = [
                    m for m in ext_mods
                    if not m.startswith("Init.") and m != "Init" and m not in ALLOWED_LOCAL_MODULES
                ]
                if bad_mods:
                    raise RuntimeError(f"Non-Init external imports in {mod_name}: {bad_mods}")
                replayed_roots.append({
                    "root_module": mod_name,
                    "import_ms": int(imp_ms),
                    "fresh_kernel_replay_ms": int(rep_ms),
                    "replayed_constants": int(n_consts),
                    "non_base_modules_replayed": ext_mods,
                })
            elif line.startswith("THM_OK|"):
                _, mod_name, thm_name, ax_csv = line.split("|")
                axioms = [a for a in ax_csv.split(",") if a]
                disallowed = sorted(set(axioms) - ALLOWED_AXIOMS)
                if disallowed:
                    raise RuntimeError(f"Disallowed axioms on {thm_name}: {disallowed}")
                audited_theorems.append({
                    "root_module": mod_name,
                    "theorem": thm_name,
                    "axioms": axioms,
                })

        if len(audited_theorems) != 30:
            raise RuntimeError(f"Expected 30 audited theorems, got {len(audited_theorems)}")

    results = {
        "lean_version": lean_version,
        "elab_flags": lean_flags,
        "max_source_bytes_budget": 150000,
        "max_compile_wall_s_budget": 15.0,
        "gcc_canary_sfi_text_2048b_sha256": code_sha256,
        "silicon_cartesian_vectors_certified_in_lean_kernel": 352,
        "modules": module_metrics,
        "replay_audit": {
            "trust_level": 0,
            "plugins": [],
            "load_exts": False,
            "visibility_level": "private",
            "wall_s": c_rep["wall_s"],
            "cpu_s": c_rep["cpu_s"],
            "rss_mb": c_rep["rss_mb"],
            "allowed_axioms_ceiling": sorted(ALLOWED_AXIOMS),
            "audited_theorem_count": len(audited_theorems),
            "replayed_roots": replayed_roots,
            "audited_theorems": audited_theorems,
        },
    }

    out_path = here / "lean_v2_verification_and_replay_results.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n")
    print("ALL_V2_LEAN_MODULES_352_SILICON_CERT_2048B_SFI_CERT_AND_REPLAY_PASSED")
    print(json.dumps({k: v["wall_s"] for k, v in module_metrics.items()}, indent=2))


if __name__ == "__main__":
    main()
