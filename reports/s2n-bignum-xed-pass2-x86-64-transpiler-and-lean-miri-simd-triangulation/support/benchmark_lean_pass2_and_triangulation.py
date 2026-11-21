#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""End-to-end compilation, peak-RSS, .olean artifact size, 224-vector live
silicon equivalence, and standalone (trustLevel := 0, level := .private) kernel
replay benchmark for VendorX86Ref, ByteX86Pass2Correspondence, and
SimdTriangulation24 under Lean v4.34.1.

All builds and replay harnesses execute inside tempfile.TemporaryDirectory()
and invoke Lean strictly through the configured cgroup/slot wrapper when given.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

MODULES_IN_ORDER = [
    "VendorX86Ref/Types.lean",
    "VendorX86Ref/Decode.lean",
    "VendorX86Ref/SemanticsScalar.lean",
    "VendorX86Ref/SemanticsSimd.lean",
    "VendorX86Ref/Machine.lean",
    "ByteX86Pass2Correspondence.lean",
    "SimdTriangulation24.lean",
]

FORBIDDEN_SOURCE_TOKENS = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\baxiom\b",
    r"\bopaque\b",
    r"\bunsafe\b",
    r"\bpartial\b",
    r"\bnative_decide\b",
    r"\bbv_decide\b",
    r"\bset_option\b",
]

REPLAY_DRIVER_LEAN = r"""import Lean
import Lean.Replay

open Lean

def readVmHwmKb : IO Nat := do
  let txt ← IO.FS.readFile "/proc/self/status"
  for line in txt.splitOn "\n" do
    if line.startsWith "VmHWM:" then
      let digits := (line.drop 6).trimAscii.toString.takeWhile Char.isDigit
      if let some n := digits.toNat? then
        return n
  return 0

def renderArr (xs : Array String) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map fun s => s!"\"{s}\"") ++ "]"

def collectAxioms (env : Environment) (roots : Array Name) : Array String := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut work := roots.toList
  let mut axs : Std.HashSet String := {}
  while !work.isEmpty do
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if !visited.contains c then
        visited := visited.insert c
        if let some ci := env.find? c then
          match ci with
          | .axiomInfo _ => axs := axs.insert c.toString
          | _ =>
            for dep in ci.getUsedConstantsAsSet do
              if !visited.contains dep then
                work := dep :: work
  return axs.toArray.qsort (· < ·)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mode := args.headD "all"

  let forbiddenConsts : Array Name := #[
    `sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler
  ]

  if mode == "vendor" then
    let baseInit ← importModules #[
      { module := `Init.Core, importAll := true },
      { module := `Init.Data.BitVec.Basic, importAll := true },
      { module := `Init.Data.BitVec.Lemmas, importAll := true },
      { module := `Init.Data.List.Basic, importAll := true },
      { module := `Init.Data.List.TakeDrop, importAll := true },
      { module := `Init.Data.Nat.Basic, importAll := true },
      { module := `Init.Data.Nat.Bitwise.Lemmas, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

    let tLoad0 ← IO.monoMsNow
    let envVendor ← importModules #[
      { module := `VendorX86Ref.Machine, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadMs := (← IO.monoMsNow) - tLoad0

    let mut delta : Std.HashMap Name ConstantInfo := {}
    for (cname, cinfo) in envVendor.constants.toList do
      if !baseInit.constants.contains cname then
        delta := delta.insert cname cinfo

    let tRep0 ← IO.monoMsNow
    let _ ← baseInit.toKernelEnv.replay delta
    let replayMs := (← IO.monoMsNow) - tRep0
    let hwmKb ← readVmHwmKb
    let axs := collectAxioms envVendor #[
      `VendorX86Ref.Step,
      `VendorX86Ref.StepsN,
      `VendorX86Ref.execStepsN_implies_stepsN
    ]
    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"delta_consts\": {delta.size},"
    IO.println s!"  \"replay_ms\": {replayMs},"
    IO.println s!"  \"vmhwm_kb\": {hwmKb},"
    IO.println s!"  \"transitive_axioms\": {renderArr axs}"
    IO.println "}"
    return 0

  else if mode == "pass2" then
    let baseVendor ← importModules #[
      { module := `VendorX86Ref.Machine, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

    let tLoad0 ← IO.monoMsNow
    let envPass2 ← importModules #[
      { module := `ByteX86Pass2Correspondence, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadMs := (← IO.monoMsNow) - tLoad0

    let mut delta : Std.HashMap Name ConstantInfo := {}
    for (cname, cinfo) in envPass2.constants.toList do
      if !baseVendor.constants.contains cname then
        delta := delta.insert cname cinfo

    let tRep0 ← IO.monoMsNow
    let _ ← baseVendor.toKernelEnv.replay delta
    let replayMs := (← IO.monoMsNow) - tRep0
    let hwmKb ← readVmHwmKb
    let axs := collectAxioms envPass2 #[
      `ByteX86.bsf_zero_narrow_refinement_counterexample,
      `ByteX86.iceLake_bsf_in_vendorX86Ref,
      `ByteX86.vendorX86Ref_step_sub_byteX86_step,
      `ByteX86.vendorX86Ref_stepsN_sub_byteX86_stepsN
    ]
    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"delta_consts\": {delta.size},"
    IO.println s!"  \"replay_ms\": {replayMs},"
    IO.println s!"  \"vmhwm_kb\": {hwmKb},"
    IO.println s!"  \"transitive_axioms\": {renderArr axs}"
    IO.println "}"
    return 0

  else if mode == "triangulation_only" then
    let basePass2 ← importModules #[
      { module := `ByteX86Pass2Correspondence, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

    let tLoad0 ← IO.monoMsNow
    let envTriOnly ← importModules #[
      { module := `SimdTriangulation24, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadMs := (← IO.monoMsNow) - tLoad0

    let mut delta : Std.HashMap Name ConstantInfo := {}
    for (cname, cinfo) in envTriOnly.constants.toList do
      if !basePass2.constants.contains cname then
        delta := delta.insert cname cinfo

    let tRep0 ← IO.monoMsNow
    let _ ← basePass2.toKernelEnv.replay delta
    let replayMs := (← IO.monoMsNow) - tRep0
    let hwmKb ← readVmHwmKb
    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"delta_consts\": {delta.size},"
    IO.println s!"  \"replay_ms\": {replayMs},"
    IO.println s!"  \"vmhwm_kb\": {hwmKb}"
    IO.println "}"
    return 0

  else
    let basePass2 ← importModules #[
      { module := `ByteX86Pass2Correspondence, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

    let tLoad0 ← IO.monoMsNow
    let envTri ← importModules #[
      { module := `SimdTriangulation24, importAll := true },
      { module := `SiliconCheck224, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadMs := (← IO.monoMsNow) - tLoad0

    let targetMods : Array Name := #[
      `VendorX86Ref.Types,
      `VendorX86Ref.Decode,
      `VendorX86Ref.SemanticsScalar,
      `VendorX86Ref.SemanticsSimd,
      `VendorX86Ref.Machine,
      `ByteX86Pass2Correspondence,
      `SimdTriangulation24,
      `SiliconCheck224
    ]
    let targetSet : Std.HashSet Name := Std.HashSet.ofArray targetMods
    let mut perModCounts : Std.HashMap Name Nat := {}
    let mut unsafeConsts : Array String := #[]
    let mut partialConsts : Array String := #[]
    let mut axiomConsts : Array String := #[]
    let mut opaqueConsts : Array String := #[]
    let mut forbiddenRefs : Array String := #[]

    for (cname, cinfo) in envTri.constants.toList do
      if let some idx := envTri.getModuleIdxFor? cname then
        let mname := envTri.header.moduleNames[idx.toNat]!
        if targetSet.contains mname then
          perModCounts := perModCounts.insert mname ((perModCounts.getD mname 0) + 1)
          if cinfo.isUnsafe then unsafeConsts := unsafeConsts.push cname.toString
          if cinfo.isPartial then partialConsts := partialConsts.push cname.toString
          match cinfo with
          | .axiomInfo _ => axiomConsts := axiomConsts.push cname.toString
          | .opaqueInfo _ => opaqueConsts := opaqueConsts.push cname.toString
          | _ => pure ()
          let used := cinfo.getUsedConstantsAsSet
          for fc in forbiddenConsts do
            if used.contains fc then
              forbiddenRefs := forbiddenRefs.push s!"{mname}:{cname}->{fc}"

    let mut delta : Std.HashMap Name ConstantInfo := {}
    for (cname, cinfo) in envTri.constants.toList do
      if !basePass2.constants.contains cname then
        delta := delta.insert cname cinfo

    let tRep0 ← IO.monoMsNow
    let _ ← basePass2.toKernelEnv.replay delta
    let replayMs := (← IO.monoMsNow) - tRep0
    let hwmKb ← readVmHwmKb

    let triRoots : Array Name := #[
      `SimdTriangulation24.unguarded_simd_shl_ub_vs_vpsllvd_zero,
      `SimdTriangulation24.unguarded_simd_bitmask_ub_vs_vpmovmskb_msb,
      `SimdTriangulation24.unguarded_simd_funnel_shl_ub_vs_vprolvd_mod32,
      `SimdTriangulation24.triangulate_p01_simd_add,
      `SimdTriangulation24.triangulate_p02_simd_sub,
      `SimdTriangulation24.triangulate_p03_simd_and,
      `SimdTriangulation24.triangulate_p04_simd_or,
      `SimdTriangulation24.triangulate_p05_simd_xor,
      `SimdTriangulation24.triangulate_p06_simd_eq,
      `SimdTriangulation24.triangulate_p07_simd_gt,
      `SimdTriangulation24.triangulate_p08_simd_lt,
      `SimdTriangulation24.triangulate_p09_simd_bitmask,
      `SimdTriangulation24.triangulate_p10_simd_extract,
      `SimdTriangulation24.triangulate_p11_simd_funnel_shl,
      `SimdTriangulation24.triangulate_p12_simd_reduce_or,
      `SimdTriangulation24.triangulate_p13_simd_saturating_sub,
      `SimdTriangulation24.triangulate_p14_simd_shl,
      `SimdTriangulation24.triangulate_p14b_simd_shl_var,
      `SimdTriangulation24.triangulate_p14c_simd_shl_oob40,
      `SimdTriangulation24.triangulate_p15_simd_shr,
      `SimdTriangulation24.triangulate_p15b_simd_sar,
      `SimdTriangulation24.triangulate_p15c_simd_sar_oob40,
      `SimdTriangulation24.triangulate_p16_simd_shuffle,
      `SimdTriangulation24.triangulate_p16b_simd_shuffle_zero,
      `SimdTriangulation24.triangulate_p17_pclmulqdq,
      `SimdTriangulation24.triangulate_p18_aesni,
      `SimdTriangulation24.triangulate_p19_pshufb,
      `SimdTriangulation24.triangulate_p20_psadbw,
      `SimdTriangulation24.triangulate_p21_vperm,
      `SimdTriangulation24.triangulate_p22_pternlog,
      `SimdTriangulation24.triangulate_p23_pmaddwd,
      `SimdTriangulation24.triangulate_p24_pmaddubsw,
      `SiliconCheck224.all_224_silicon_vectors_match
    ]
    let axs := collectAxioms envTri triRoots

    let mut modPairs : Array String := #[]
    for m in targetMods do
      modPairs := modPairs.push s!"\"{m}\": {perModCounts.getD m 0}"

    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"delta_consts\": {delta.size},"
    IO.println s!"  \"replay_ms\": {replayMs},"
    IO.println s!"  \"vmhwm_kb\": {hwmKb},"
    IO.println s!"  \"unsafe_consts\": {renderArr unsafeConsts},"
    IO.println s!"  \"partial_consts\": {renderArr partialConsts},"
    IO.println s!"  \"axiom_consts\": {renderArr axiomConsts},"
    IO.println s!"  \"opaque_consts\": {renderArr opaqueConsts},"
    IO.println s!"  \"forbidden_refs\": {renderArr forbiddenRefs},"
    IO.println s!"  \"transitive_axioms\": {renderArr axs},"
    IO.println ("  \"per_module_kernel_consts\": {" ++ String.intercalate ", " modPairs.toList ++ "}")
    IO.println "}"
    return 0
"""


def generate_silicon_check_lean(silicon_json_path: Path) -> str:
    data = json.loads(silicon_json_path.read_text())
    vecs = data["vectors"]
    lines = [
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.List.Basic",
        "import VendorX86Ref.Machine",
        "",
        "namespace SiliconCheck224",
        "open VendorX86Ref",
        "",
        "def flagsToMask (f : RFlags) : Nat :=",
        "  (if f.cf then 1 else 0) |||",
        "  (if f.pf then 4 else 0) |||",
        "  (if f.af then 16 else 0) |||",
        "  (if f.zf then 64 else 0) |||",
        "  (if f.sf then 128 else 0) |||",
        "  (if f.of then 2048 else 0)",
        "",
        "def maskToFlags (m : Nat) : RFlags :=",
        "  { cf := (m &&& 1) != 0",
        "    pf := (m &&& 4) != 0",
        "    af := (m &&& 16) != 0",
        "    zf := (m &&& 64) != 0",
        "    sf := (m &&& 128) != 0",
        "    of := (m &&& 2048) != 0 }",
        "",
        "def arenaAddr : BitVec 64 := 0x400000#64",
        "def stackAddr : BitVec 64 := 0x800000#64",
        "",
        "def mkSiliconState (rax rcx rdx rsi r8 efl mem0 mem1 : BitVec 64)",
        "    (y0 y1 y2 : BitVec 256) : MachineState :=",
        "  let m0 := writeMem64 (fun _ => 0#8) arenaAddr mem0",
        "  let m1 := writeMem64 m0 (arenaAddr + 8#64) mem1",
        "  let m2 := writeMem64 m1 (arenaAddr + 16#64) 0xCAFEBABE11223344#64",
        "  let m3 := writeMem64 m2 (arenaAddr + 24#64) 0x5566778899AABBCC#64",
        "  { rip := 0#64",
        "    gpr := fun r => match r with",
        "      | .rax => rax | .rcx => rcx | .rdx => rdx | .rsi => rsi",
        "      | .rdi => arenaAddr | .r8 => r8 | .rsp => stackAddr | _ => 0#64",
        "    ymm := fun i => match i.val with",
        "      | 0 => y0 | 1 => y1 | 2 => y2 | _ => 0#256",
        "    flags := maskToFlags efl.toNat",
        "    mem := m3",
        "    halted := false",
        "    fault := none }",
        "",
        "def codeFromWindow (bs : List (BitVec 8)) : CodeMap := fun a =>",
        "  match bs[a.toNat]? with | some b => b | none => 0xCC#8",
        "",
        "def isFaultGp0 : Option FaultKind → Bool",
        "  | some .gp0LengthExceeds15 | some .gp0Privilege => true",
        "  | _ => false",
        "",
        "def isFaultUd : Option FaultKind → Bool",
        "  | some .udExplicit | some .udIllegalLock | some .udVexPrefix",
        "  | some .udVexField | some .udEvexField | some .udUnmapped => true",
        "  | _ => false",
        "",
        "def checkOneExec (bs : List (BitVec 8)) (steps : Nat) (rax rcx rdx rsi r8 efl mem0 mem1 : BitVec 64)",
        "    (y0 y1 y2 : BitVec 256)",
        "    (expLen : Nat) (expRax expRcx expRdx expMem0 expMem1 : BitVec 64)",
        "    (expEfl : Nat) (expY0 : BitVec 256) (checkRipp : Bool) : Bool :=",
        "  let code := codeFromWindow bs",
        "  let s0 := mkSiliconState rax rcx rdx rsi r8 efl mem0 mem1 y0 y1 y2",
        "  let oracle : UndefOracle := { flags := maskToFlags expEfl, gpr := expRax }",
        "  let lenOk := if steps == 1 then",
        "    match decodeRef (fetchWindow16 code 0#64) with | .ok _ l => l == expLen | .fault _ => false",
        "  else true",
        "  let s1 := execStepsN code steps oracle s0",
        "  let ripOk := if checkRipp then s1.rip == BitVec.ofNat 64 expLen else true",
        "  lenOk && s1.fault.isNone && ripOk &&",
        "  (s1.gpr .rax == expRax) && (s1.gpr .rcx == expRcx) && (s1.gpr .rdx == expRdx) &&",
        "  (readMem64 s1.mem arenaAddr == expMem0) &&",
        "  (readMem64 s1.mem (arenaAddr + 8#64) == expMem1) &&",
        "  (flagsToMask s1.flags == expEfl) &&",
        "  (s1.ymm ⟨0, by decide⟩ == expY0)",
        "",
        "def checkOneFault (bs : List (BitVec 8)) (expectGp0 : Bool) : Bool :=",
        "  let code := codeFromWindow bs",
        "  let s0 := mkSiliconState 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#256 0#256 0#256",
        "  let s1 := stepWithOracle code {} s0",
        "  if expectGp0 then isFaultGp0 s1.fault else isFaultUd s1.fault",
        "",
    ]
    names = []
    for idx, v in enumerate(vecs):
        raw = bytes.fromhex(v["hex"])
        padded = raw + b"\xcc" * max(0, 16 - len(raw))
        blist = "[" + ", ".join(f"0x{b:02X}#8" for b in padded[:16]) + "]"
        cname = f"vec_{idx:03d}"
        names.append(cname)
        verdict = v["silicon_verdict"]
        if verdict == "FAULT_GP0":
            lines.append(f"def {cname} : Bool := checkOneFault {blist} true")
        elif verdict == "FAULT_UD":
            lines.append(f"def {cname} : Bool := checkOneFault {blist} false")
        elif verdict == "OK_EXEC":
            y0_int = int.from_bytes(bytes.fromhex(v["y0"]), "little")
            y1_int = int.from_bytes(bytes.fromhex(v["y1"]), "little")
            y2_int = int.from_bytes(bytes.fromhex(v["y2"]), "little")
            sy0_int = int.from_bytes(bytes.fromhex(v["silicon_ymm0_hex"]), "little")
            # Control-flow jcc/jmp change rip to target rather than +len
            is_branch = v["id"].startswith(("jmp_", "jcc_"))
            check_rip = "false" if is_branch else "true"
            steps = 2 if v["measure_len"] == 0 else 1
            lines.append(
                f"def {cname} : Bool := checkOneExec {blist} {steps} "
                f"0x{v['rax']:X}#64 0x{v['rcx']:X}#64 0x{v['rdx']:X}#64 "
                f"0x{v['rsi']:X}#64 0x{v['r8']:X}#64 0x{v['efl']:X}#64 "
                f"0x{v['mem0']:X}#64 0x{v['mem1']:X}#64 "
                f"0x{y0_int:064X}#256 0x{y1_int:064X}#256 0x{y2_int:064X}#256 "
                f"{v['silicon_len']} "
                f"0x{v['silicon_rax']:X}#64 0x{v['silicon_rcx']:X}#64 0x{v['silicon_rdx']:X}#64 "
                f"0x{v['silicon_mem0']:X}#64 0x{v['silicon_mem1']:X}#64 "
                f"{v['silicon_efl6']} 0x{sy0_int:064X}#256 {check_rip}"
            )
        else:
            raise ValueError(f"Unexpected silicon verdict: {verdict}")

    lines.append("")
    for cname in names:
        lines.append(f"theorem thm_{cname} : {cname} = true := rfl")
    chunk_exprs = []
    for cidx in range(0, len(names), 16):
        grp = " && ".join(names[cidx : cidx + 16])
        gname = f"chunk_{cidx // 16:02d}"
        lines.append(f"def {gname} : Bool := {grp}")
        chunk_exprs.append(gname)
    lines.append(
        "theorem all_224_silicon_vectors_match : ("
        + " && ".join(chunk_exprs)
        + ") = true := rfl"
    )
    lines.append("end SiliconCheck224")
    return "\n".join(lines) + "\n"


def strip_comments_lean(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def run_cmd_with_rss(cmd: list[str], cwd: Path, env: dict[str, str]) -> tuple[subprocess.CompletedProcess, float, int]:
    time_bin = Path("/usr/bin/time")
    t0 = time.perf_counter()
    if time_bin.exists():
        with tempfile.NamedTemporaryFile(mode="r+", suffix=".rss") as tf:
            full_cmd = [str(time_bin), "-f", "%M", "-o", tf.name, "--"] + cmd
            proc = subprocess.run(full_cmd, cwd=str(cwd), env=env, capture_output=True, text=True)
            dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
            tf.seek(0)
            rss_txt = tf.read().strip()
            maxrss_kb = int(rss_txt.splitlines()[-1]) if rss_txt and rss_txt.splitlines()[-1].isdigit() else 0
            return proc, dt_ms, maxrss_kb
    proc = subprocess.run(cmd, cwd=str(cwd), env=env, capture_output=True, text=True)
    dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    return proc, dt_ms, 0


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--transpiler-script", type=Path, required=True)
    ap.add_argument("--pass2-lean", type=Path, required=True)
    ap.add_argument("--triangulation-lean", type=Path, required=True)
    ap.add_argument("--silicon-json", type=Path, required=True)
    ap.add_argument("--lean-bin", type=str, default="lean")
    ap.add_argument("--lean-wrapper", type=str, default=None)
    ap.add_argument("--out-json", type=Path, required=True)
    args = ap.parse_args()

    wrap = [args.lean_wrapper, "--"] if args.lean_wrapper else []
    lean_ver = subprocess.run(
        wrap + [args.lean_bin, "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        subprocess.run(
            ["python3", "-B", str(args.transpiler_script), "--emit-lean-dir", str(td_path)],
            check=True,
        )
        (td_path / "ByteX86Pass2Correspondence.lean").write_text(args.pass2_lean.read_text())
        (td_path / "SimdTriangulation24.lean").write_text(args.triangulation_lean.read_text())
        (td_path / "SiliconCheck224.lean").write_text(generate_silicon_check_lean(args.silicon_json))
        (td_path / "ReplayDriver.lean").write_text(REPLAY_DRIVER_LEAN)

        env = os.environ.copy()
        lean_resolved = Path(args.lean_bin).resolve()
        env["LEAN_PATH"] = str(td_path)
        env["LEAN_SYSROOT"] = str(lean_resolved.parent.parent)
        env["PATH"] = f"{lean_resolved.parent}:{env.get('PATH', '')}"

        module_metrics: dict[str, dict] = {}
        total_compile_ms = 0.0
        total_olean_bytes = 0

        for rel in MODULES_IN_ORDER + ["SiliconCheck224.lean"]:
            src = td_path / rel
            olean = src.with_suffix(".olean")
            raw = src.read_bytes()
            txt = raw.decode("utf-8")
            uncommented = strip_comments_lean(txt)
            token_hits = [
                pat for pat in FORBIDDEN_SOURCE_TOKENS if re.search(pat, uncommented)
            ]
            if token_hits:
                raise RuntimeError(f"Forbidden token(s) {token_hits} in {rel}")

            cmd = wrap + [
                args.lean_bin,
                "-j1",
                "-M4096",
                "-t0",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-R",
                str(td_path),
                "-o",
                str(olean),
                str(src),
            ]
            proc, dt_ms, maxrss_kb = run_cmd_with_rss(cmd, td_path, env)
            if proc.returncode != 0:
                raise RuntimeError(
                    f"Lean compile failed on {rel} (rc={proc.returncode}):\n"
                    f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
                )
            if proc.stdout.strip() or proc.stderr.strip():
                raise RuntimeError(
                    f"Non-empty compiler diagnostics on {rel}:\n"
                    f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
                )

            priv = src.with_suffix(".olean.private")
            srv = src.with_suffix(".olean.server")
            obytes = olean.stat().st_size
            all_obytes = (
                obytes
                + (priv.stat().st_size if priv.exists() else 0)
                + (srv.stat().st_size if srv.exists() else 0)
            )
            if rel != "SiliconCheck224.lean":
                total_compile_ms += dt_ms
                total_olean_bytes += obytes

            module_metrics[rel] = {
                "source_bytes": len(raw),
                "source_lines": txt.count("\n"),
                "source_sha256": hashlib.sha256(raw).hexdigest(),
                "compile_wall_ms": dt_ms,
                "maxrss_kb": maxrss_kb,
                "olean_bytes": obytes,
                "olean_all_parts_bytes": all_obytes,
                "olean_sha256": hashlib.sha256(olean.read_bytes()).hexdigest(),
                "zero_warnings_and_errors": True,
                "zero_forbidden_tokens": True,
            }
            print(f"[OK] {rel:36s} wall={dt_ms:7.2f}ms rss={maxrss_kb:7d}kB olean={obytes:8d}B")

        replay_results = {}
        for mode in ("vendor", "pass2", "triangulation_only", "triangulation"):
            rcmd = wrap + [
                args.lean_bin,
                "-j1",
                "-M8192",
                "--run",
                str(td_path / "ReplayDriver.lean"),
                mode,
            ]
            rproc = subprocess.run(rcmd, cwd=str(td_path), env=env, capture_output=True, text=True)
            if rproc.returncode != 0:
                raise RuntimeError(
                    f"ReplayDriver {mode} failed (rc={rproc.returncode}):\n"
                    f"STDOUT:\n{rproc.stdout}\nSTDERR:\n{rproc.stderr}"
                )
            replay_results[mode] = json.loads(rproc.stdout)
            print(f"[REPLAY {mode}] {json.dumps(replay_results[mode])}")

        vendor_only_ms = round(
            sum(
                module_metrics[m]["compile_wall_ms"]
                for m in MODULES_IN_ORDER
                if m.startswith("VendorX86Ref/")
            ),
            2,
        )
        vendor_only_olean = sum(
            module_metrics[m]["olean_bytes"]
            for m in MODULES_IN_ORDER
            if m.startswith("VendorX86Ref/")
        )

        out = {
            "lean_version": lean_ver,
            "compile_flags": [
                "-j1",
                "-M4096",
                "-t0",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
            ],
            "summary": {
                "staged_lean_modules_count": len(MODULES_IN_ORDER),
                "vendor_x86_ref_5_modules_compile_wall_ms": vendor_only_ms,
                "vendor_x86_ref_5_modules_olean_bytes": vendor_only_olean,
                "all_7_staged_modules_compile_wall_ms": round(total_compile_ms, 2),
                "all_7_staged_modules_olean_bytes": total_olean_bytes,
                "max_single_module_compile_wall_ms": max(
                    module_metrics[m]["compile_wall_ms"] for m in MODULES_IN_ORDER
                ),
                "max_single_module_source_bytes": max(
                    module_metrics[m]["source_bytes"] for m in MODULES_IN_ORDER
                ),
                "silicon_vectors_kernel_verified": 224,
                "triangulation_theorems_kernel_verified": 29,
                "mir_ub_asymmetry_theorems_kernel_verified": 3,
            },
            "modules": module_metrics,
            "standalone_private_kernel_replay": replay_results,
        }
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
        print(f"Wrote {args.out_json}")


if __name__ == "__main__":
    main()
