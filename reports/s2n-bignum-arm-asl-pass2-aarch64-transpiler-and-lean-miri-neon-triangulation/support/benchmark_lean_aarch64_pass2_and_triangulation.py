#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""End-to-end compilation, peak-RSS, .olean artifact size, 224-vector live QEMU
rfl equivalence, and standalone (trustLevel := 0, level := .private) kernel
replay benchmark for IntrinsicAarch64Ext, VendorArm64Ref,
WordArm64Pass2Correspondence, NeonTriangulation24, and QemuCheck224 under
Lean v4.34.1.

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
    "IntrinsicAarch64Ext.lean",
    "VendorArm64Ref/Types.lean",
    "VendorArm64Ref/Decode.lean",
    "VendorArm64Ref/SemanticsScalar.lean",
    "VendorArm64Ref/SemanticsNeon.lean",
    "VendorArm64Ref/Machine.lean",
    "WordArm64Pass2Correspondence.lean",
    "NeonTriangulationCore.lean",
    "NeonTriangulation24.lean",
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

  let baseInit ← importModules #[
    { module := `Init.Core, importAll := true },
    { module := `Init.Data.BitVec.Basic, importAll := true },
    { module := `Init.Data.BitVec.Lemmas, importAll := true },
    { module := `Init.Data.List.Basic, importAll := true },
    { module := `Init.Data.Nat.Basic, importAll := true }
  ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

  if mode == "vendor" then
    let tLoad0 ← IO.monoMsNow
    let envVendor ← importModules #[
      { module := `VendorArm64Ref.Machine, importAll := true }
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
      `VendorArm64Ref.Step,
      `VendorArm64Ref.StepsN,
      `VendorArm64Ref.execStepsN_implies_stepsN
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
      { module := `VendorArm64Ref.Machine, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

    let tLoad0 ← IO.monoMsNow
    let envPass2 ← importModules #[
      { module := `WordArm64Pass2Correspondence, importAll := true }
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
      `WordArm64.s2n_assigns_entirety_unsound_frame_violation,
      `WordArm64.misaligned_ldar_lse2_narrow_refinement_counterexample,
      `WordArm64.stlxr_spurious_fail_narrow_refinement_counterexample,
      `WordArm64.vendorArm64Ref_step_sub_wordArm64_step,
      `WordArm64.vendorArm64Ref_stepsN_sub_wordArm64_stepsN
    ]
    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"delta_consts\": {delta.size},"
    IO.println s!"  \"replay_ms\": {replayMs},"
    IO.println s!"  \"vmhwm_kb\": {hwmKb},"
    IO.println s!"  \"transitive_axioms\": {renderArr axs}"
    IO.println "}"
    return 0

  else
    let tLoad0 ← IO.monoMsNow
    let envAll ← importModules #[
      { module := `NeonTriangulation24, importAll := true },
      { module := `QemuCheck224, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadMs := (← IO.monoMsNow) - tLoad0

    let targetMods : Array Name := #[
      `IntrinsicAarch64Ext,
      `VendorArm64Ref.Types,
      `VendorArm64Ref.Decode,
      `VendorArm64Ref.SemanticsScalar,
      `VendorArm64Ref.SemanticsNeon,
      `VendorArm64Ref.Machine,
      `WordArm64Pass2Correspondence,
      `NeonTriangulationCore,
      `NeonTriangulation24,
      `QemuCheck224
    ]
    let targetSet : Std.HashSet Name := Std.HashSet.ofArray targetMods
    let mut perModCounts : Std.HashMap Name Nat := {}
    let mut unsafeConsts : Array String := #[]
    let mut partialConsts : Array String := #[]
    let mut axiomConsts : Array String := #[]
    let mut opaqueConsts : Array String := #[]
    let mut forbiddenRefs : Array String := #[]
    let mut delta : Std.HashMap Name ConstantInfo := {}

    for (cname, cinfo) in envAll.constants.toList do
      if !baseInit.constants.contains cname then
        delta := delta.insert cname cinfo
      if let some idx := envAll.getModuleIdxFor? cname then
        let mname := envAll.header.moduleNames[idx.toNat]!
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

    let tRep0 ← IO.monoMsNow
    let _ ← baseInit.toKernelEnv.replay delta
    let replayMs := (← IO.monoMsNow) - tRep0
    let hwmKb ← readVmHwmKb

    let axs := collectAxioms envAll #[
      `IntrinsicAarch64Ext.evalAarch64Ext,
      `WordArm64.vendorArm64Ref_step_sub_wordArm64_step,
      `WordArm64.vendorArm64Ref_stepsN_sub_wordArm64_stepsN,
      `NeonTriangulation24.unguarded_miri_simd_shl_ub_vs_neon_ushl_bidir,
      `NeonTriangulation24.unguarded_miri_simd_shr_32_ub_vs_rustc_cmlt_zero,
      `NeonTriangulation24.arm_aese_aesmc_ne_x86_vaesenc_single_key,
      `NeonTriangulation24.arm_aese_aesmc_eor_eq_x86_vaesenc_universal,
      `NeonTriangulation24.triangulate_p01_vaddq_u8,
      `NeonTriangulation24.triangulate_p16_vaddlvq_u8,
      `NeonTriangulation24.triangulate_p22b_vmull_p64,
      `NeonTriangulation24.triangulate_p23_vaeseq_u8,
      `NeonTriangulation24.triangulate_p24_vsha512hq_u64,
      `NeonTriangulation24.triangulate_p25_crc32cd,
      `QemuCheck224.all_224_qemu_vectors_match
    ]

    let mut modPairs : Array String := #[]
    for m in targetMods do
      modPairs := modPairs.push s!"\"{m}\": {perModCounts.getD m 0}"

    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"delta_consts\": {delta.size},"
    IO.println s!"  \"replay_ms\": {replayMs},"
    IO.println s!"  \"vmhwm_kb\": {hwmKb},"
    IO.println s!"  \"per_module_const_counts\": \{ {String.intercalate ", " modPairs.toList} },"
    IO.println s!"  \"unsafe_consts\": {renderArr unsafeConsts},"
    IO.println s!"  \"partial_consts\": {renderArr partialConsts},"
    IO.println s!"  \"axiom_consts\": {renderArr axiomConsts},"
    IO.println s!"  \"opaque_consts\": {renderArr opaqueConsts},"
    IO.println s!"  \"forbidden_refs\": {renderArr forbiddenRefs},"
    IO.println s!"  \"transitive_axioms\": {renderArr axs}"
    IO.println "}"
    return 0
"""


def generate_qemu_check_lean(qemu_json_path: Path) -> str:
    data = json.loads(qemu_json_path.read_text(encoding="utf-8"))
    vecs = data["vectors"]
    lines = [
        "-- Copyright 2026 The Fuchsia Authors",
        "--",
        "-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0",
        "-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT",
        "-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.",
        "-- This file may not be copied, modified, or distributed except according to",
        "-- those terms.",
        "",
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.BitVec.Lemmas",
        "import Init.Data.List.Basic",
        "import Init.Data.Nat.Basic",
        "import VendorArm64Ref.Machine",
        "",
        "namespace QemuCheck224",
        "open VendorArm64Ref",
        "",
        "def packNzcv (f : PStateFlags) : BitVec 64 :=",
        "  (if f.nf then 8#64 else 0#64) |||",
        "  (if f.zf then 4#64 else 0#64) |||",
        "  (if f.cf then 2#64 else 0#64) |||",
        "  (if f.vf then 1#64 else 0#64)",
        "",
        "def flagsOfNzcv (n : Nat) : PStateFlags :=",
        "  { nf := ((n / 8) % 2) == 1",
        "    zf := ((n / 4) % 2) == 1",
        "    cf := ((n / 2) % 2) == 1",
        "    vf := (n % 2) == 1 }",
        "",
        "def mkVecState (pcVal spVal : BitVec 64) (x0 x1 x2 x3 memOff : BitVec 64)",
        "    (nzcv : Nat) (mem0 mem1 : BitVec 64) (v0 v1 v2 : BitVec 128) : MachineState :=",
        "  let m0 := writeMem64 (fun _ => 0#8) 0x20000#64 mem0",
        "  let m1 := writeMem64 m0 0x20008#64 mem1",
        "  { pc    := pcVal",
        "    sp    := spVal",
        "    xreg  := fun r =>",
        "      if r == 0#5 then x0",
        "      else if r == 1#5 then x1",
        "      else if r == 2#5 then x2",
        "      else if r == 3#5 then x3",
        "      else if r == 4#5 then 0x20000#64 + memOff",
        "      else 0#64",
        "    flags := flagsOfNzcv nzcv",
        "    vreg  := fun v =>",
        "      if v == 0#5 then v0",
        "      else if v == 1#5 then v1",
        "      else if v == 2#5 then v2",
        "      else 0#128",
        "    mem   := m1 }",
        "",
        "def checkFault (words : List (BitVec 32)) (expected : ArmFault) : Bool :=",
        "  let s := execStep (loadWordsAt 0x10000#64 words) false false { pc := 0x10000#64, sp := 0x80000#64 }",
        "  s.fault == some expected",
        "",
        "def checkSpAlignFault (words : List (BitVec 32)) (spSub : BitVec 64) : Bool :=",
        "  let s := execStep (loadWordsAt 0x10000#64 words) false false { pc := 0x10000#64, sp := 0x80000#64 - spSub }",
        "  s.fault == some .spAlignmentFault",
        "",
        "def checkBothAlignFault (words : List (BitVec 32)) (memOff : BitVec 64) : Bool :=",
        "  let s0 := mkVecState 0x10000#64 0x80000#64 0#64 0#64 0#64 0#64 memOff 0 0#64 0#64 0#128 0#128 0#128",
        "  let rA53 := execStep (loadWordsAt 0x10000#64 words) false false s0",
        "  let rMax := execStep (loadWordsAt 0x10000#64 words) false true  s0",
        "  (rA53.fault == some .alignmentFault) && (rMax.fault == some .alignmentFault)",
        "",
        "def checkSplitLse2 (words : List (BitVec 32)) (x0 x1 x2 x3 memOff : BitVec 64)",
        "    (nzcv : Nat) (mem0 mem1 : BitVec 64) (v0 v1 v2 : BitVec 128)",
        "    (ex0 ex1 ex2 em0 em1 : BitVec 64) : Bool :=",
        "  let s0 := mkVecState 0x10000#64 0x80000#64 x0 x1 x2 x3 memOff nzcv mem0 mem1 v0 v1 v2",
        "  let code := loadWordsAt 0x10000#64 words",
        "  let rA53 := execStep code false false s0",
        "  let rMax := execStep code false true  s0",
        "  (rA53.fault == some .alignmentFault) &&",
        "  rMax.fault.isNone &&",
        "  (rMax.xreg 0#5 == ex0) && (rMax.xreg 1#5 == ex1) && (rMax.xreg 2#5 == ex2) &&",
        "  (readMem64 rMax.mem 0x20000#64 == em0) && (readMem64 rMax.mem 0x20008#64 == em1)",
        "",
        "def checkOkExec (pcVal spVal : BitVec 64) (words : List (BitVec 32)) (steps : Nat) (pageAdrp : Bool)",
        "    (x0 x1 x2 x3 memOff : BitVec 64) (nzcv : Nat) (mem0 mem1 : BitVec 64)",
        "    (v0 v1 v2 : BitVec 128)",
        "    (ex0 ex1 ex2 ex3 ex4Off enzcv em0 em1 : BitVec 64) (ev0 : BitVec 128) : Bool :=",
        "  let s0 := mkVecState pcVal spVal x0 x1 x2 x3 memOff nzcv mem0 mem1 v0 v1 v2",
        "  let code := loadWordsAt pcVal words",
        "  let sf := execStepsN code false true steps s0",
        "  let x0Actual := if pageAdrp then sf.xreg 0#5 - 0x10000#64 else sf.xreg 0#5",
        "  sf.fault.isNone &&",
        "  (x0Actual == ex0) && (sf.xreg 1#5 == ex1) && (sf.xreg 2#5 == ex2) && (sf.xreg 3#5 == ex3) &&",
        "  ((sf.xreg 4#5 - 0x20000#64) == ex4Off) &&",
        "  (packNzcv sf.flags == enzcv) &&",
        "  (readMem64 sf.mem 0x20000#64 == em0) && (readMem64 sf.mem 0x20008#64 == em1) &&",
        "  (sf.vreg 0#5 == ev0)",
        "",
    ]

    names = []
    for idx, v in enumerate(vecs):
        cname = f"vec_{idx:03d}"
        names.append(cname)
        wlist = "[" + ", ".join(f"{w}#32" for w in v["words_hex"]) + "]"
        inp = v["input"]
        qm = v["qemu_max"]
        em = v["expected_model"]

        if em == "FAULT_UNDEFINED":
            lines.append(f"def {cname} : Bool := checkFault {wlist} .undefinedEncoding")
        elif em == "FAULT_CONSTRAINED_UNPRED":
            lines.append(f"def {cname} : Bool := checkFault {wlist} .constrainedUnpredictable")
        elif em == "FAULT_SP_ALIGN":
            lines.append(f"def {cname} : Bool := checkSpAlignFault {wlist} {inp['sp_misalign']}#64")
        elif em == "FAULT_ALIGN":
            lines.append(f"def {cname} : Bool := checkBothAlignFault {wlist} {inp['mem_off']}#64")
        elif em == "SPLIT_LSE2_ALIGN":
            lines.append(
                f"def {cname} : Bool := checkSplitLse2 {wlist} "
                f"0x{inp['x0']:x}#64 0x{inp['x1']:x}#64 0x{inp['x2']:x}#64 0x{inp['x3']:x}#64 {inp['mem_off']}#64 "
                f"{inp['nzcv']} 0x{inp['mem0']:x}#64 0x{inp['mem1']:x}#64 "
                f"0x{inp['v0_hex']}#128 0x{inp['v1_hex']}#128 0x{inp['v2_hex']}#128 "
                f"0x{qm['x0']:x}#64 0x{qm['x1']:x}#64 0x{qm['x2']:x}#64 "
                f"0x{qm['mem0']:x}#64 0x{qm['mem1']:x}#64"
            )
        elif em == "OK_EXEC":
            if v["id"] == "c72_adr_rel_sub":
                pc_s = f"0x{qm['x2'] - 4:x}#64"
            elif v["page_end_adrp"]:
                pc_s = "0x10ffc#64"
            else:
                pc_s = "0x10000#64"
            sp_s = f"0x{qm['x2']:x}#64" if v["id"] == "c12_add_sp_read" else "0x80000#64"
            steps = (len(v["words_hex"]) - 1) if v["is_branch_rel"] else len(v["words_hex"])
            pa_s = "true" if v["page_end_adrp"] else "false"
            lines.append(
                f"def {cname} : Bool := checkOkExec {pc_s} {sp_s} {wlist} {steps} {pa_s} "
                f"0x{inp['x0']:x}#64 0x{inp['x1']:x}#64 0x{inp['x2']:x}#64 0x{inp['x3']:x}#64 {inp['mem_off']}#64 "
                f"{inp['nzcv']} 0x{inp['mem0']:x}#64 0x{inp['mem1']:x}#64 "
                f"0x{inp['v0_hex']}#128 0x{inp['v1_hex']}#128 0x{inp['v2_hex']}#128 "
                f"0x{qm['x0']:x}#64 0x{qm['x1']:x}#64 0x{qm['x2']:x}#64 0x{qm['x3']:x}#64 "
                f"0x{qm['x4_off']:x}#64 0x{qm['nzcv']:x}#64 "
                f"0x{qm['mem0']:x}#64 0x{qm['mem1']:x}#64 0x{qm['v0_hex']}#128"
            )
        else:
            raise ValueError(f"Unknown expected_model: {em}")

    lines.append("")
    for cname in names:
        lines.append(f"theorem thm_{cname} : {cname} = true := rfl")
    chunk_props = []
    chunk_thms = []
    for cidx in range(0, len(names), 16):
        slice_names = names[cidx : cidx + 16]
        pname = f"ChunkProp_{cidx // 16:02d}"
        tname = f"thm_chunk_{cidx // 16:02d}"
        prop_body = " ∧ ".join(f"{n} = true" for n in slice_names)
        proof_body = "⟨" + ", ".join(f"thm_{n}" for n in slice_names) + "⟩"
        lines.append(f"def {pname} : Prop := {prop_body}")
        lines.append(f"theorem {tname} : {pname} := {proof_body}")
        chunk_props.append(pname)
        chunk_thms.append(tname)
    lines.append(
        "theorem all_224_qemu_vectors_match : "
        + " ∧ ".join(chunk_props)
        + " := ⟨"
        + ", ".join(chunk_thms)
        + "⟩"
    )
    lines.append("end QemuCheck224")
    return "\n".join(lines) + "\n"


def strip_comments_lean(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def run_cmd_with_rss(
    cmd: list[str], cwd: Path, env: dict[str, str]
) -> tuple[subprocess.CompletedProcess, float, int]:
    time_bin = Path("/usr/bin/time")
    t0 = time.perf_counter()
    if time_bin.exists():
        with tempfile.NamedTemporaryFile(mode="r+", suffix=".rss") as tf:
            full_cmd = [str(time_bin), "-f", "%M", "-o", tf.name, "--"] + cmd
            proc = subprocess.run(full_cmd, cwd=str(cwd), env=env, capture_output=True, text=True)
            dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
            tf.seek(0)
            rss_txt = tf.read().strip()
            maxrss_kb = (
                int(rss_txt.splitlines()[-1])
                if rss_txt and rss_txt.splitlines()[-1].isdigit()
                else 0
            )
            return proc, dt_ms, maxrss_kb
    proc = subprocess.run(cmd, cwd=str(cwd), env=env, capture_output=True, text=True)
    dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    return proc, dt_ms, 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--support-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
    )
    ap.add_argument("--lean-bin", type=str, default="lean")
    ap.add_argument("--lean-wrapper", type=str, default=None)
    ap.add_argument(
        "--out-json",
        type=Path,
        default=Path(__file__)
        .resolve()
        .with_name("lean_aarch64_pass2_and_triangulation_benchmark_results.json"),
    )
    args = ap.parse_args()

    sup = args.support_dir.resolve()
    wrap = [args.lean_wrapper, "--"] if args.lean_wrapper else []
    lean_ver = subprocess.run(
        wrap + [args.lean_bin, "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        subprocess.run(
            ["python3", "-B", str(sup / "transpile_s2n_arm_to_lean.py"), "--emit-lean-dir", str(td_path)],
            check=True,
        )
        for fname in [
            "IntrinsicAarch64Ext.lean",
            "WordArm64Pass2Correspondence.lean",
            "NeonTriangulationCore.lean",
            "NeonTriangulation24.lean",
        ]:
            (td_path / fname).write_text((sup / fname).read_text(encoding="utf-8"), encoding="utf-8")

        (td_path / "QemuCheck224.lean").write_text(
            generate_qemu_check_lean(sup / "probe_qemu_224_aarch64_vectors_results.json"),
            encoding="utf-8",
        )
        (td_path / "ReplayDriver.lean").write_text(REPLAY_DRIVER_LEAN, encoding="utf-8")

        env = os.environ.copy()
        lean_resolved = Path(args.lean_bin).resolve()
        env["LEAN_PATH"] = str(td_path)
        env["LEAN_SYSROOT"] = str(lean_resolved.parent.parent)
        env["PATH"] = f"{lean_resolved.parent}:{env.get('PATH', '')}"

        module_metrics: dict[str, dict] = {}
        total_compile_ms = 0.0
        total_olean_bytes = 0

        for rel in MODULES_IN_ORDER + ["QemuCheck224.lean"]:
            src = td_path / rel
            olean = src.with_suffix(".olean")
            raw = src.read_bytes()
            txt = raw.decode("utf-8")
            uncommented = strip_comments_lean(txt)
            token_hits = [
                pat for pat in FORBIDDEN_SOURCE_TOKENS if re.search(pat, uncommented)
            ]
            if token_hits:
                raise RuntimeError(f"Forbidden tokens in {rel}: {token_hits}")

            cmd = wrap + [
                args.lean_bin,
                "-R",
                str(td_path),
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-o",
                str(olean),
                str(src),
            ]
            proc, dt_ms, maxrss_kb = run_cmd_with_rss(cmd, td_path, env)
            print(f"[compile] {rel:38s}: rc={proc.returncode} {dt_ms:7.2f} ms rss={maxrss_kb} KB")
            if proc.returncode != 0 or proc.stdout.strip() or proc.stderr.strip():
                print("STDOUT:\n" + proc.stdout[:3000])
                print("STDERR:\n" + proc.stderr[:3000])
                raise RuntimeError(f"Clean build failed on {rel}")

            osz = olean.stat().st_size
            total_compile_ms = round(total_compile_ms + dt_ms, 2)
            total_olean_bytes += osz
            module_metrics[rel] = {
                "source_bytes": len(raw),
                "source_lines": len(txt.splitlines()),
                "source_sha256": hashlib.sha256(raw).hexdigest(),
                "compile_ms": dt_ms,
                "maxrss_kb": maxrss_kb,
                "olean_bytes": osz,
                "forbidden_source_tokens": [],
                "zero_warnings_and_errors": True,
            }

        replay_results: dict[str, dict] = {}
        for mode in ["vendor", "pass2", "all"]:
            r_cmd = wrap + [args.lean_bin, "--run", str(td_path / "ReplayDriver.lean"), mode]
            r_proc, r_ms, r_rss = run_cmd_with_rss(r_cmd, td_path, env)
            if r_proc.returncode != 0:
                print("REPLAY STDERR:\n" + r_proc.stderr)
                raise RuntimeError(f"Replay mode={mode} failed")
            rep_data = json.loads(r_proc.stdout)
            rep_data["wall_ms"] = r_ms
            rep_data["maxrss_kb"] = r_rss
            replay_results[mode] = rep_data

    all_rep = replay_results["all"]
    for bad_key in [
        "unsafe_consts",
        "partial_consts",
        "axiom_consts",
        "opaque_consts",
        "forbidden_refs",
    ]:
        if all_rep[bad_key]:
            raise RuntimeError(f"Audit violation in {bad_key}: {all_rep[bad_key]}")

    out = {
        "lean_version": lean_ver,
        "total_compile_ms": total_compile_ms,
        "total_olean_bytes": total_olean_bytes,
        "modules": module_metrics,
        "private_kernel_replay": replay_results,
    }
    args.out_json.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"total_compile_ms": total_compile_ms, "replay_all": all_rep}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
