#!/usr/bin/env python3
"""
End-to-end Lean 4.34.1 real-kernel benchmark and private-proof-replay suite for:
  1. Real `gcc 15.2.0 -O2` `.o` byte-level functional lifting (`aligned_frame_spills_o2`
     with `and rsp, -32` prologue/epilogue + `switch_pic8` with `.rela.rodata`
     `R_X86_64_PC32` `S + A - P` jump-table resolution & `notrack jmp rax`);
  2. Demonic `RFLAGS` `O(4^K)` case-split cliff & uncollapsed `parity8` WHNF wall
     vs. certified backward `DeadFlagCollapse` (`checkByteLeaf_sound`);
  3. Naive flat `ByteMem` `O(S * P)` stack-vs-caller aliasing rewrites vs.
     Unexposed Private Stack-Frame Separation (`PrivateStackSep`);
  4. Sharded variable-length x86-64 byte-decoded `ByteShardedTreeLift` scaling
     (`N = 64 .. 5,120` instructions = `276 .. 22,080` raw machine bytes);
  5. Decidable loop-invariant-free Binary SFI Containment (`checkSfiObject` +
     `checkSfiObject_preserves_rust_host_safety`) scaling up to `N = 10,240`
     cyclic x86-64 instructions (`40,960` raw machine bytes, zero loop invariants).

Every Lean invocation runs with `-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048`
(`0` `set_option` in all benchmarked modules) inside `anneal-lean-run`, followed by a
standalone `trustLevel := 0, plugins := #[], loadExts := false, level := .private`
`base.toKernelEnv.replay` pass verifying `_inhabitedExprDummy` absence and exact
transitive axioms. All scratch files live inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import argparse
import hashlib
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
LEAN = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1" / "bin" / "lean"
RUN_WRAPPER = shutil.which("anneal-lean-run") or str(Path.home() / ".local" / "bin" / "anneal-lean-run")


def ensure_cgroup_wrapper() -> None:
    if os.environ.get("ANNEAL_LEAN_RUN_ACTIVE") == "1":
        return
    if Path(RUN_WRAPPER).exists():
        env = dict(os.environ)
        env["ANNEAL_LEAN_RUN_ACTIVE"] = "1"
        os.execve(
            RUN_WRAPPER,
            [RUN_WRAPPER, "--timeout", "3600", sys.executable, "-B", str(Path(__file__).resolve())] + sys.argv[1:],
            env,
        )


def run_timed_lean(args: list[str], env: dict[str, str], timeout: int = 180) -> dict[str, object]:
    cmd = ["/usr/bin/time", "-v", str(LEAN)] + args
    t0 = time.perf_counter()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=timeout)
        wall = time.perf_counter() - t0
        timed_out = False
        rc = r.returncode
        stdout = r.stdout
        stderr = r.stderr
    except subprocess.TimeoutExpired as e:
        wall = time.perf_counter() - t0
        timed_out = True
        rc = -1
        stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")

    user_s = sys_s = None
    max_rss_kb = None
    for line in stderr.splitlines():
        if "User time (seconds):" in line:
            user_s = float(line.split(":")[-1].strip())
        elif "System time (seconds):" in line:
            sys_s = float(line.split(":")[-1].strip())
        elif "Maximum resident set size (kbytes):" in line:
            max_rss_kb = int(line.split(":")[-1].strip())
    return {
        "rc": rc,
        "timed_out": timed_out,
        "wall_s": round(wall, 4),
        "cpu_s": round((user_s or 0.0) + (sys_s or 0.0), 4) if user_s is not None else None,
        "rss_mb": round(max_rss_kb / 1024.0, 2) if max_rss_kb is not None else None,
        "stdout": stdout,
        "stderr_tail": "\n".join(stderr.splitlines()[-10:]),
    }


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
    (modStr thmStr baseStr : String) : IO Unit := do
  let some (base, baseMods) := bases.get? baseStr
    | throw <| IO.userError s!"unknown base {baseStr}"
  let modName := modStr.toName
  let thmName := thmStr.toName
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
  if (replayed.find? thmName).isNone then
    throw <| IO.userError s!"theorem {thmName} absent after kernel replay"
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
  let mut hasDummy : Bool := false
  match env.find? thmName with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v =>
      for d in v.getUsedConstants do
        if d.toString == "_inhabitedExprDummy" then
          hasDummy := true
    | none => throw <| IO.userError s!"theorem {thmName} missing proof body"
  | none => throw <| IO.userError s!"missing theorem {thmName}"
  if hasDummy then
    throw <| IO.userError s!"theorem {thmName} proof body collapsed to _inhabitedExprDummy"
  let axSorted := axioms.qsort (fun a b => a.toString < b.toString)
  IO.println s!"REPLAY_OK|{modStr}|{t1 - t0}|{t2 - t1}|{newConsts.size}|{axSorted.toList}"

def main (args : List String) : IO Unit := do
  let [jobsPath] := args | throw <| IO.userError "usage: ReplayAudit <jobs.txt>"
  let raw ← IO.FS.readFile jobsPath
  let lines := (raw.splitOn "\n").filter (fun (s : String) => !s.isEmpty)
  let mut bases : Std.HashMap String (Environment × NameSet) := {}
  for l in lines do
    let parts := l.splitOn " "
    if parts.length == 3 then
      let b := parts[2]!
      if !bases.contains b then
        let pair ← loadBase b
        bases := bases.insert b pair
  for l in lines do
    let parts := l.splitOn " "
    if parts.length == 3 then
      try
        auditOne bases parts[0]! parts[1]! parts[2]!
      catch e =>
        IO.println s!"REPLAY_ERR|{parts[0]!}|{e}"
"""


def parse_replay_output(stdout: str) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for ln in stdout.splitlines():
        if ln.startswith("REPLAY_OK|"):
            _, mod, imp_ms, rep_ms, n_consts, ax = ln.split("|", 5)
            out[mod] = {
                "replay_rc": 0,
                "import_ms": int(imp_ms),
                "replay_ms": int(rep_ms),
                "replayed_consts": int(n_consts),
                "dummy_absent": True,
                "axioms": ax,
            }
        elif ln.startswith("REPLAY_ERR|"):
            _, mod, err = ln.split("|", 2)
            out[mod] = {"replay_rc": 1, "replay_error": err}
    return out


LINE_RE = re.compile(r"^\s*([0-9a-fA-F]+):\s+((?:[0-9a-fA-F]{2}\s)+)\s*(.*)$")


def compile_c_and_extract(td: Path, name: str, flags: list[str], src: str) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    c_path = td / f"{name}.c"
    o_path = td / f"{name}.o"
    c_path.write_text(src, encoding="utf-8")
    subprocess.run(["gcc"] + flags + ["-c", str(c_path), "-o", str(o_path)], check=True, timeout=20)
    out_raw = subprocess.check_output(["objdump", "-d", "-M", "intel", str(o_path)], text=True, timeout=10)
    insns: list[dict[str, object]] = []
    for ln in out_raw.splitlines():
        m = LINE_RE.match(ln)
        if not m:
            continue
        off = int(m.group(1), 16)
        b_hex = [int(x, 16) for x in m.group(2).strip().split()]
        asm = m.group(3).strip()
        if asm == "" and insns and off == int(insns[-1]["off"]) + len(insns[-1]["bytes"]):
            insns[-1]["bytes"].extend(b_hex)
        else:
            insns.append({"off": off, "bytes": b_hex, "asm": asm})

    rel_out = subprocess.check_output(["readelf", "-r", "-W", str(o_path)], text=True, timeout=10)
    relocs: list[dict[str, object]] = []
    sec = ""
    for ln in rel_out.splitlines():
        s = ln.strip()
        if s.startswith("Relocation section '"):
            sec = s.split("'")[1]
        elif s and len(s.split()) >= 5 and all(c in "0123456789abcdefABCDEF" for c in s.split()[0]):
            parts = s.split()
            off_val = int(parts[0], 16)
            rtype = parts[2]
            sym = parts[4]
            addend = 0
            if len(parts) >= 7 and parts[5] in ("+", "-"):
                sign = 1 if parts[5] == "+" else -1
                addend = sign * int(parts[6], 16)
            relocs.append({"section": sec, "offset": off_val, "type": rtype, "sym": sym, "addend": addend})
    return insns, relocs


def fmt_byte_list(bs: list[int]) -> str:
    return "[" + ", ".join(f"0x{b:02X}" for b in bs) + "]"


def precompute_collapsed_ops_batch(td: Path, env: dict[str, str], blocks: dict[str, list[int]]) -> dict[str, str]:
    """Run an untrusted Lean helper (`--run`) in small batches of 8 leaves to emit explicit
    `List CollapsedOp` witnesses, which the Lean kernel then independently verifies via
    `compileByteLeaf ... = some (_, cops) := rfl`."""
    items = list(blocks.items())
    res: dict[str, str] = {}
    for b_start in range(0, len(items), 8):
        chunk = items[b_start : b_start + 8]
        lines = [
            "import Init.System.IO",
            "import ByteX86Base",
            "open ByteX86",
            "def main : IO Unit := do",
        ]
        for key, bs in chunk:
            lines.append(f"  match compileByteLeaf 8 FlagMask.dead {fmt_byte_list(bs)} with")
            lines.append(f'  | some (_, c) => IO.println s!"{key}|{{(reprStr c).replace "\\n" " "}}"')
            lines.append(f'  | none => throw <| IO.userError "compileByteLeaf failed on {key}"')
        helper = td / "EmitWitnesses.lean"
        helper.write_text("\n".join(lines) + "\n", encoding="utf-8")
        out = subprocess.check_output([str(LEAN), "--run", str(helper)], text=True, env=env, timeout=120)
        for ln in out.splitlines():
            if "|" in ln:
                k, expr = ln.split("|", 1)
                res[k] = expr
    return res


# ============================================================================
# Suite 1 Generator: Real `gcc 15.2.0 -O2` `.o` Byte-Level Functional Proofs
# ============================================================================

GCC_ALIGNED_C = r"""
#include <stdint.h>

#define MIX_STEP(s, i, c) do { \
    uint64_t t = (s[(i) & 7] + (c)) ^ (s[((i) + 3) & 7] << 7); \
    s[(i) & 7] = t * 0xBF58476D1CE4E5B9ULL; \
    s[((i) + 1) & 7] ^= (t >> 19); \
} while (0)

uint64_t aligned_frame_spills_o2(uint64_t seed, const uint64_t * restrict in_ptr, uint64_t * restrict out_ptr) {
    __attribute__((aligned(32))) volatile uint64_t frame_slots[8];
    for (int i = 0; i < 8; i++) {
        frame_slots[i] = in_ptr[i] ^ (seed + (uint64_t)i * 0x9E3779B97F4A7C15ULL);
    }
    MIX_STEP(frame_slots, 0, 0x11ULL);
    MIX_STEP(frame_slots, 1, 0x23ULL);
    MIX_STEP(frame_slots, 2, 0x37ULL);
    MIX_STEP(frame_slots, 3, 0x4BULL);
    uint64_t acc = frame_slots[0] + frame_slots[3] + frame_slots[5] + frame_slots[7];
    out_ptr[0] = acc;
    return acc;
}
"""

GCC_SWITCH_PIC8_C = r"""
#include <stdint.h>

uint64_t switch_pic8_o2(uint32_t op, uint64_t x, uint64_t y) {
    switch (op) {
        case 0: return (x + y) ^ 0x517CC1B727220A95ULL;
        case 1: return (x - y) * 0x9E3779B97F4A7C15ULL;
        case 2: return (x << 5) ^ (y >> 3);
        case 3: return (x & y) + (x | y);
        case 4: return (x ^ (y << 11)) + 0x1337ULL;
        case 5: return (y - (x >> 7)) * 3ULL;
        case 6: return ((x + 17ULL) * y) ^ (x >> 31);
        case 7: return (x << 1) + (y << 2) + 9ULL;
        default: return x ^ y;
    }
}
"""


def build_gcc_real_object_lean(td: Path, env: dict[str, str]) -> tuple[str, dict[str, object]]:
    ins_al, _ = compile_c_and_extract(
        td,
        "aligned_frame_spills_o2",
        ["-O2", "-mno-red-zone", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        GCC_ALIGNED_C,
    )
    # Extract the exact contiguous straight-line spill+mix slice from `mov rax, [rsp]` through `add rax, rdx`
    start_idx = next(i for i, ins in enumerate(ins_al) if ins["bytes"] == [0x48, 0x8B, 0x04, 0x24])
    end_idx = next(i for i, ins in enumerate(ins_al) if ins["off"] > ins_al[start_idx]["off"] and ins["bytes"] == [0x48, 0x89, 0x06])
    spill_slice = ins_al[start_idx:end_idx]
    spill_bytes = [b for ins in spill_slice for b in ins["bytes"]]
    n_spill_insns = len(spill_slice)
    witness_map = precompute_collapsed_ops_batch(td, env, {"gcc_spill": spill_bytes})
    gcc_cops_expr = witness_map["gcc_spill"]

    # Exact GCC dynamic realignment prologue (`endbr64; push rbp; mov rbp, rsp; and rsp, -32; sub rsp, 0x40`)
    # and epilogue (`leave; ret`), all present verbatim in `aligned_frame_spills_o2.o`:
    prol_bytes = [0xF3, 0x0F, 0x1E, 0xFA, 0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xE4, 0xE0, 0x48, 0x83, 0xEC, 0x40]
    epil_bytes = [0xC9, 0xC3]

    # Compile `switch_pic8_o2` and link/resolve `.rela.text` + `.rela.rodata` via ELF `R_X86_64_PC32` (`S + A - P`)!
    ins_sw, rel_sw = compile_c_and_extract(
        td,
        "switch_pic8_o2",
        ["-O2", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        GCC_SWITCH_PIC8_C,
    )
    sw_bytes = [b for ins in ins_sw for b in ins["bytes"]]
    text_base = 0
    rodata_base = 0x10000
    # Resolve `.rela.text` (`lea rcx, [rip + disp32]` pointing at `.rodata`)
    for r in rel_sw:
        if r["section"] == ".rela.text" and r["type"] == "R_X86_64_PC32" and r["sym"] == ".rodata":
            p_off = int(r["offset"])
            val = (rodata_base + int(r["addend"]) - (text_base + p_off)) & 0xFFFFFFFF
            sw_bytes[p_off : p_off + 4] = list(val.to_bytes(4, "little"))

    # Resolve 8 `.rela.rodata` entries (`S + A - P`, where `P = rodata_base + off` -> `target_k = A_k - off`!)
    rodata_entries_correct: list[int] = [0] * 8
    rodata_entries_naive_bug: list[int] = [0] * 8
    resolved_targets: list[int] = [0] * 8
    for r in rel_sw:
        if r["section"] == ".rela.rodata" and r["type"] == "R_X86_64_PC32" and r["sym"] == ".text":
            idx = int(r["offset"]) // 4
            if 0 <= idx < 8:
                p_addr = rodata_base + int(r["offset"])
                s_plus_a = text_base + int(r["addend"])
                rel32 = (s_plus_a - p_addr) & 0xFFFFFFFF
                rodata_entries_correct[idx] = rel32
                resolved_targets[idx] = text_base + int(r["addend"]) - int(r["offset"])
                rodata_entries_naive_bug[idx] = ((text_base + int(r["addend"])) - rodata_base) & 0xFFFFFFFF

    rodata_bytes_correct = [b for w in rodata_entries_correct for b in w.to_bytes(4, "little")]
    rodata_bytes_buggy = [b for w in rodata_entries_naive_bug for b in w.to_bytes(4, "little")]

    sw_chunks = [sw_bytes[i : i + 16] for i in range(0, len(sw_bytes), 16)]
    sw_chunk_defs = "\n".join(
        f"def swChunk_{i} : List UInt8 := {fmt_byte_list(ch)}"
        for i, ch in enumerate(sw_chunks)
    )
    sw_tree_expr, _, _ = build_balanced_tree_expr([(f"swChunk_{i}", len(ch)) for i, ch in enumerate(sw_chunks)])

    off_to_idx = {int(ins["off"]): i for i, ins in enumerate(ins_sw)}
    case_steps: dict[int, int] = {}
    for op_tag in range(8):
        tgt_off = resolved_targets[op_tag]
        i = off_to_idx[tgt_off]
        cnt = 0
        while True:
            cnt += 1
            if str(ins_sw[i]["asm"]).startswith("ret"):
                break
            i += 1
        case_steps[op_tag] = 8 + cnt
    ja_ins = next(ins for ins in ins_sw if str(ins["asm"]).startswith("ja"))
    ja_tgt = int(str(ja_ins["asm"]).split()[1], 16)
    i = off_to_idx[ja_tgt]
    cnt_def = 0
    while True:
        cnt_def += 1
        if str(ins_sw[i]["asm"]).startswith("ret"):
            break
        i += 1
    case_steps[8] = 3 + cnt_def

    meta = {
        "gcc_aligned_spill_slice_bytes": len(spill_bytes),
        "gcc_aligned_spill_slice_insns": n_spill_insns,
        "gcc_aligned_full_bytes": len(prol_bytes) + len(spill_bytes) + len(epil_bytes),
        "gcc_aligned_full_insns": 5 + n_spill_insns + 2,
        "gcc_switch_pic8_text_bytes": len(sw_bytes),
        "gcc_switch_pic8_insns": len(ins_sw),
        "gcc_switch_pic8_resolved_targets": resolved_targets,
        "gcc_switch_pic8_raw_addends": [
            int(r["addend"]) for r in rel_sw if r["section"] == ".rela.rodata"
        ],
    }

    epil_off = 16 + len(spill_bytes)
    lean_src = f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import ByteX86Base

namespace GccRealObjectProofs
open ByteX86

/-! ## Part 1A: Real `gcc 15.2.0 -O2` Dynamic Stack Realignment (`and rsp, -32`) + {n_spill_insns}-Insn Spill Mix -/

def gccProlBytes  : List UInt8 := {fmt_byte_list(prol_bytes)}
def gccSpillBytes : List UInt8 := {fmt_byte_list(spill_bytes)}
def gccEpilBytes  : List UInt8 := {fmt_byte_list(epil_bytes)}

def gccAlignedImg : X64ObjImage :=
  {{ code := .node {epil_off} (.node 16 (.leaf gccProlBytes) (.leaf gccSpillBytes)) (.leaf gccEpilBytes) }}

def gccCops : List CollapsedOp := {gcc_cops_expr}

theorem gcc_compile_ok :
    compileByteLeaf 8 FlagMask.dead gccSpillBytes = some (FlagMask.dead, gccCops) := rfl

theorem gcc_cops_len : lenTR gccCops = {n_spill_insns} := rfl

/-- Saved caller `%rbp` at `[rspEntry - 8 .. rspEntry - 1]` lies strictly above the realigned
    `[rspAligned .. rspAligned + 64)` spill frame for ANY initial caller misalignment `rspEntry % 32`! -/
theorem saved_rbp_outside_realigned_spills (rspEntry : BitVec 64) (k : Nat) (hk : k < 8) :
    let rspAligned := ((rspEntry - 8#64) &&& 0xFFFFFFFFFFFFFFE0#64) - 64#64
    OutsideSpillRange rspAligned 8 ((rspEntry - 8#64) + BitVec.ofNat 64 k) := by
  intro rspAligned
  unfold OutsideSpillRange
  let r1 := rspEntry - 8#64
  let pad := (r1 &&& 31#64).toNat
  have hpad_lt : pad < 32 := and_31_lt_32 r1
  have halign : (r1 &&& 0xFFFFFFFFFFFFFFE0#64) = r1 - (r1 &&& 31#64) := and_mask32_eq_sub_rem r1
  have hrem_eq : (r1 &&& 31#64) = BitVec.ofNat 64 pad := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hpad_lt (by decide))]
  have hrsp_eq : rspAligned = r1 - BitVec.ofNat 64 (pad + 64) := by
    dsimp [rspAligned, r1]
    have h64 : (64#64 : BitVec 64) = BitVec.ofNat 64 64 := rfl
    rw [halign, hrem_eq, h64, BitVec.sub_sub, ← BitVec.ofNat_add]
  have hdiff : (r1 + BitVec.ofNat 64 k) - rspAligned = BitVec.ofNat 64 ((pad + 64) + k) := by
    rw [hrsp_eq]
    apply (BitVec.sub_eq_iff_eq_add).mpr
    rw [BitVec.ofNat_add,
        BitVec.add_comm (BitVec.ofNat 64 (pad + 64)) (BitVec.ofNat 64 k),
        BitVec.add_assoc,
        BitVec.add_comm (BitVec.ofNat 64 (pad + 64)) _,
        BitVec.sub_add_cancel,
        BitVec.add_comm]
  change 8 * 8 ≤ ((r1 + BitVec.ofNat 64 k) - rspAligned).toNat
  rw [hdiff, BitVec.toNat_ofNat]
  have hlt64 : (pad + 64) + k < 2 ^ 64 := by
    have h1 : pad + 64 < 32 + 64 := Nat.add_lt_add_right hpad_lt 64
    have h2 : (pad + 64) + k < 96 + 8 := Nat.add_lt_add h1 hk
    exact Nat.lt_trans h2 (by decide)
  rw [Nat.mod_eq_of_lt hlt64]
  exact Nat.le_trans (Nat.le_add_left 64 pad) (Nat.le_add_right (pad + 64) k)

theorem gcc_aligned_frame_mix_full_verified
    (nd : Nat → UndefFlags) (s0 : X64State)
    (hrip0 : s0.rip = 0) (hnh0 : s0.halted = false) (hnf0 : s0.fault = false) :
    let rsp1 := s0.regs .rsp - 8#64
    let mem1 := writeMem64 s0.mem rsp1 (s0.regs .rbp)
    let rspAligned := (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64) - 64#64
    let regsProl := regUpd (regUpd s0.regs .rsp rspAligned) .rbp rsp1
    let lProl : LiftedX64State :=
      {{ regs := regsProl,
        slots := fun sl => readMem64 mem1 (spillSlotAddr rspAligned sl),
        flags := {{}} }}
    let sf := runX64 gccAlignedImg {5 + n_spill_insns + 2} nd s0
    sf.halted = true ∧
    sf.fault = false ∧
    sf.regs .rsp = s0.regs .rsp ∧
    sf.regs .rbp = s0.regs .rbp ∧
    sf.regs .rax = (evalCollapsedOps gccCops lProl).regs .rax ∧
    (∀ a, ¬ InStackEnvelope (s0.regs .rsp) 103 a → sf.mem a = s0.mem a) := by
  cases s0 with
  | mk rip0 regs0 flags0 mem0 halted0 fault0 =>
    dsimp at hrip0 hnh0 hnf0
    subst hrip0 hnh0 hnf0
    intro rsp1 mem1 rspAligned regsProl lProl sf
    have hd0  : decodeX64 (fetchWindow16 gccAlignedImg.code 0) = .ok .endbr64 4 := rfl
    have hd4  : decodeX64 (fetchWindow16 gccAlignedImg.code 4) = .ok (.push64 .rbp) 1 := rfl
    have hd5  : decodeX64 (fetchWindow16 gccAlignedImg.code 5) = .ok (.movRR64 .rbp .rsp) 3 := rfl
    have hd8  : decodeX64 (fetchWindow16 gccAlignedImg.code 8) = .ok (.aluImm64 .and .rsp 0xFFFFFFFFFFFFFFE0#64) 4 := rfl
    have hd12 : decodeX64 (fetchWindow16 gccAlignedImg.code 12) = .ok (.aluImm64 .sub .rsp 64#64) 4 := rfl
    let s0' : X64State := {{ rip := 0, regs := regs0, flags := flags0, mem := mem0, halted := false, fault := false }}
    have hsplit1 : runX64 gccAlignedImg {5 + n_spill_insns + 2} nd s0' =
        runX64 gccAlignedImg {n_spill_insns + 2} (fun k => nd (k + 5)) (runX64 gccAlignedImg 5 nd s0') :=
      runX64_add gccAlignedImg 5 {n_spill_insns + 2} nd s0'
    let s5 := runX64 gccAlignedImg 5 nd s0'
    have hs5 : s5 =
        {{ rip := 16, regs := regsProl,
          flags := (evalAluFlags64 .sub (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64) 64#64 (nd 4)).2,
          mem := mem1, halted := false, fault := false }} := by
      have st1 : stepX64 gccAlignedImg (nd 0) s0' = {{ s0' with rip := 4 }} := by
        dsimp [stepX64, s0']; rw [hd0]
      have st2 : stepX64 gccAlignedImg (nd 1) {{ s0' with rip := 4 }} =
          {{ s0' with rip := 5, regs := regUpd regs0 .rsp rsp1, mem := mem1 }} := by
        dsimp [stepX64, s0']; rw [hd4]
      have st3 : stepX64 gccAlignedImg (nd 2) {{ s0' with rip := 5, regs := regUpd regs0 .rsp rsp1, mem := mem1 }} =
          {{ s0' with rip := 8, regs := regUpd (regUpd regs0 .rsp rsp1) .rbp rsp1, mem := mem1 }} := by
        dsimp [stepX64, s0']; rw [hd5]; dsimp; rw [regUpd_eq]
      have st4 : stepX64 gccAlignedImg (nd 3)
          {{ s0' with rip := 8, regs := regUpd (regUpd regs0 .rsp rsp1) .rbp rsp1, mem := mem1 }} =
          {{ s0' with rip := 12,
                      regs := regUpd (regUpd regs0 .rsp (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64)) .rbp rsp1,
                      flags := (evalAluFlags64 .and rsp1 0xFFFFFFFFFFFFFFE0#64 (nd 3)).2,
                      mem := mem1 }} := by
        dsimp [stepX64, s0']; rw [hd8]; dsimp [aluWritesDst]
        have hr2 : regUpd (regUpd (regUpd regs0 .rsp rsp1) .rbp rsp1) .rsp
                     ((evalAluFlags64 .and (regUpd (regUpd regs0 .rsp rsp1) .rbp rsp1 .rsp) 0xFFFFFFFFFFFFFFE0#64 (nd 3)).1) =
                   regUpd (regUpd regs0 .rsp (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64)) .rbp rsp1 := by
          funext r; cases r <;> rfl
        have hf2 : (regUpd (regUpd regs0 .rsp rsp1) .rbp rsp1 .rsp) = rsp1 := rfl
        rw [hr2, hf2]
      have st5 : stepX64 gccAlignedImg (nd 4)
          {{ s0' with rip := 12,
                      regs := regUpd (regUpd regs0 .rsp (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64)) .rbp rsp1,
                      flags := (evalAluFlags64 .and rsp1 0xFFFFFFFFFFFFFFE0#64 (nd 3)).2,
                      mem := mem1 }} =
          {{ rip := 16, regs := regsProl,
             flags := (evalAluFlags64 .sub (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64) 64#64 (nd 4)).2,
             mem := mem1, halted := false, fault := false }} := by
        dsimp [stepX64, s0']; rw [hd12]; dsimp [aluWritesDst]
        have hr3 : regUpd (regUpd (regUpd regs0 .rsp (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64)) .rbp rsp1) .rsp
                     ((evalAluFlags64 .sub (regUpd (regUpd regs0 .rsp (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64)) .rbp rsp1 .rsp) 64#64 (nd 4)).1) =
                   regsProl := by
          funext r; cases r <;> rfl
        have hf3 : (regUpd (regUpd regs0 .rsp (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64)) .rbp rsp1 .rsp) =
                   (rsp1 &&& 0xFFFFFFFFFFFFFFE0#64) := rfl
        rw [hr3, hf3]
      dsimp [s5]
      rw [runX64_succ, st1, runX64_succ, st2, runX64_succ, st3, runX64_succ, st4, runX64_succ, st5, runX64_zero]
    have habs5 : AbstractsLeaf 8 FlagMask.dead s5 lProl := by
      rw [hs5]
      refine ⟨rfl, rfl, fun _ => rfl, ?_, flagsAgreeOn_dead _ _⟩
      intro sl _; dsimp [lProl, regsProl, regUpd]
    have hsplit2 : runX64 gccAlignedImg {n_spill_insns + 2} (fun k => nd (k + 5)) s5 =
        runX64 gccAlignedImg 2 (fun k => nd (k + (5 + {n_spill_insns})))
          (runX64 gccAlignedImg {n_spill_insns} (fun k => nd (k + 5)) s5) := by
      rw [runX64_add gccAlignedImg {n_spill_insns} 2 (fun k => nd (k + 5)) s5]
    have htree : checkLeafBytesAt gccAlignedImg.code (.goLeft (.goRight .here)) 16 gccSpillBytes = true :=
      checkLeafBytesAt_goLeft (base := 16) rfl
        (checkLeafBytesAt_goRight (lsz := 16) (base := 16) (subBase := 0) rfl rfl
          (checkLeafBytesAt_here gccSpillBytes))
    have hs5_rip : s5.rip = 16 := by rw [hs5]
    have hleaf := checkByteLeaf_sound (maxSlots := 8) (img := gccAlignedImg)
      (by decide : 8 * 8 < 2 ^ 64) htree gcc_compile_ok
      (fun k => nd (k + 5)) s5 lProl hs5_rip habs5
    rw [gcc_cops_len] at hleaf
    rcases hleaf with ⟨hrip_mid, hrsp_mid, hmem_mid, habs_mid⟩
    rcases habs_mid with ⟨hnh_mid, hnf_mid, hregs_mid, _, _⟩
    generalize hsMid : runX64 gccAlignedImg {n_spill_insns} (fun k => nd (k + 5)) s5 = sMid at hrip_mid hrsp_mid hmem_mid hnh_mid hnf_mid hregs_mid hsplit2
    have hrip_mid' : sMid.rip = {epil_off} := hrip_mid
    have hrbp_mid : sMid.regs .rbp = rsp1 := by
      rw [hregs_mid .rbp, evalCollapsedOps_untouched_reg .rbp gccCops lProl rfl]
      rfl
    have hsaved_rbp : readMem64 sMid.mem rsp1 = regs0 .rbp := by
      have h8 : ∀ j, j < 8 → sMid.mem (rsp1 + BitVec.ofNat 64 j) = mem1 (rsp1 + BitVec.ofNat 64 j) := by
        intro j hj
        have hout_j : OutsideSpillRange (s5.regs .rsp) 8 (rsp1 + BitVec.ofNat 64 j) := by
          rw [hs5]; dsimp [regsProl, regUpd]
          exact saved_rbp_outside_realigned_spills (regs0 .rsp) j hj
        rw [hmem_mid _ hout_j, hs5]
      dsimp [readMem64]
      rw [h8 0 (by decide), h8 1 (by decide), h8 2 (by decide), h8 3 (by decide),
          h8 4 (by decide), h8 5 (by decide), h8 6 (by decide), h8 7 (by decide)]
      exact readMem64_writeMem64_same mem0 rsp1 (regs0 .rbp)
    have hd_leave : decodeX64 (fetchWindow16 gccAlignedImg.code {epil_off}) = .ok .leave64 1 := rfl
    have hd_ret   : decodeX64 (fetchWindow16 gccAlignedImg.code {epil_off + 1}) = .ok .ret 1 := rfl
    have hs_end : runX64 gccAlignedImg 2 (fun k => nd (k + (5 + {n_spill_insns}))) sMid =
        {{ sMid with rip := {epil_off + 1},
                    regs := regUpd (regUpd sMid.regs .rsp (regs0 .rsp)) .rbp (regs0 .rbp),
                    halted := true }} := by
      have se1 : stepX64 gccAlignedImg (nd (0 + (5 + {n_spill_insns}))) sMid =
          {{ sMid with rip := {epil_off + 1},
                      regs := regUpd (regUpd sMid.regs .rsp (regs0 .rsp)) .rbp (regs0 .rbp) }} := by
        dsimp [stepX64]
        rw [hnh_mid, hnf_mid, hrip_mid']; dsimp
        rw [hd_leave]; dsimp
        rw [hrbp_mid, hsaved_rbp]
        have hrsp_restore : rsp1 + 8#64 = regs0 .rsp := BitVec.sub_add_cancel (regs0 .rsp) 8#64
        rw [hrsp_restore]
      have se2 : stepX64 gccAlignedImg (nd (1 + (5 + {n_spill_insns})))
          {{ sMid with rip := {epil_off + 1},
                      regs := regUpd (regUpd sMid.regs .rsp (regs0 .rsp)) .rbp (regs0 .rbp) }} =
          {{ sMid with rip := {epil_off + 1},
                      regs := regUpd (regUpd sMid.regs .rsp (regs0 .rsp)) .rbp (regs0 .rbp),
                      halted := true }} := by
        dsimp [stepX64]
        rw [hnh_mid, hnf_mid]; dsimp
        rw [hd_ret]
      rw [runX64_succ, se1, runX64_succ, se2, runX64_zero]
    have hsf_eq : sf = {{ sMid with rip := {epil_off + 1},
                                   regs := regUpd (regUpd sMid.regs .rsp (regs0 .rsp)) .rbp (regs0 .rbp),
                                   halted := true }} := by
      dsimp [sf]; rw [hsplit1, hsplit2, hs_end]
    rw [hsf_eq]; dsimp only
    refine ⟨rfl, hnf_mid, ?_, ?_, ?_, ?_⟩
    · rw [regUpd_ne _ (by decide : Reg.rsp ≠ .rbp), regUpd_eq]
    · exact regUpd_eq _ .rbp _
    · rw [regUpd_ne _ (by decide : Reg.rax ≠ .rbp), regUpd_ne _ (by decide : Reg.rax ≠ .rsp)]
      exact hregs_mid .rax
    · intro a hnot_env
      have hout_a : OutsideSpillRange (s5.regs .rsp) 8 a := by
        rw [hs5]; dsimp [regsProl, regUpd]
        exact realigned_frame_envelope_separation (regs0 .rsp) a 64 8 (by decide) (by decide) hnot_env
      rw [hmem_mid a hout_a, hs5]; dsimp [mem1]
      apply writeMem64_byte_ne
      intro k hk heq
      subst heq
      apply hnot_env
      unfold InStackEnvelope
      have hsub_k : regs0 .rsp - ((regs0 .rsp - 8#64) + BitVec.ofNat 64 k) = BitVec.ofNat 64 (8 - k) := by
        apply (BitVec.sub_eq_iff_eq_add).mpr
        have h8k : BitVec.ofNat 64 (8 - k) + BitVec.ofNat 64 k = 8#64 := by
          rw [← BitVec.ofNat_add, Nat.sub_add_cancel (Nat.le_of_lt hk)]
        rw [← BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 - k)) _,
            BitVec.add_assoc, h8k, BitVec.sub_add_cancel]
      dsimp only
      rw [hsub_k, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.sub_le 8 k) (by decide : 8 < 16)) (by decide))]
      exact ⟨Nat.succ_le_of_lt (Nat.sub_pos_of_lt hk), Nat.le_trans (Nat.sub_le 8 k) (by decide)⟩

/-! ## Part 1B: Real `gcc 15.2.0 -O2` PIC `.rela.rodata` Jump Table (`S + A - P`) + `notrack jmp rax` -/

{sw_chunk_defs}
def gccSwitchImg : X64ObjImage := {{ code := {sw_tree_expr} }}

def gccRodataCorrect : List UInt8 := {fmt_byte_list(rodata_bytes_correct)}
def gccRodataBuggy   : List UInt8 := {fmt_byte_list(rodata_bytes_buggy)}

def overlayRodata (tbl : List UInt8) (baseMem : ByteMem) : ByteMem :=
  fun a =>
    match listGet? tbl ((a - 0x10000#64).toNat) with
    | some b => u8ToBV8 b
    | none   => baseMem a

theorem overlayRodata_at (tbl : List UInt8) (baseMem : ByteMem) (a : BitVec 64) (off : Nat) (b : UInt8)
    (hoff : (a - 0x10000#64).toNat = off)
    (hget : listGet? tbl off = some b) :
    overlayRodata tbl baseMem a = u8ToBV8 b := by
  unfold overlayRodata; rw [hoff, hget]

def initSwitchRegs (op x y : BitVec 64) : Reg → BitVec 64 :=
  regUpd (regUpd (regUpd (fun _ => 0#64) .rdx y) .rsi x) .rdi op

def mkSwitchState (tbl : List UInt8) (baseMem : ByteMem) (op : Nat) (x y : BitVec 64) : X64State :=
  {{ rip := 0,
    regs := initSwitchRegs (BitVec.ofNat 64 op) x y,
    flags := {{}},
    mem := overlayRodata tbl baseMem }}

theorem gcc_pic_switch8_entries_0_to_3_concrete :
    let s (op : Nat) := mkSwitchState gccRodataCorrect (fun _ => 0#8) op 10#64 3#64
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 0)).rip = {resolved_targets[0]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 1)).rip = {resolved_targets[1]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 2)).rip = {resolved_targets[2]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 3)).rip = {resolved_targets[3]} :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem gcc_pic_switch8_entries_4_to_7_concrete :
    let s (op : Nat) := mkSwitchState gccRodataCorrect (fun _ => 0#8) op 10#64 3#64
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 4)).rip = {resolved_targets[4]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 5)).rip = {resolved_targets[5]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 6)).rip = {resolved_targets[6]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) (s 7)).rip = {resolved_targets[7]} :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Universal symbolic `.rela.rodata` `S + A - P` + `notrack jmp rax` + demonic `imul` proof
    over arbitrary `baseMem : ByteMem`, `x y : BitVec 64`, and `nd : Nat → UndefFlags` (`op = 1`)! -/
theorem gcc_pic_switch8_case1_symbolic_verified
    (baseMem : ByteMem) (x y : BitVec 64) (nd : Nat → UndefFlags) :
    let sf := runX64 gccSwitchImg 12 nd (mkSwitchState gccRodataCorrect baseMem 1 x y)
    sf.halted = true ∧ sf.fault = false ∧
    sf.regs .rax = 0x9E3779B97F4A7C15#64 * (x - y) := by
  intro sf
  have sw0  : decodeX64 (fetchWindow16 gccSwitchImg.code 0)  = .ok .endbr64 4 := rfl
  have sw4  : decodeX64 (fetchWindow16 gccSwitchImg.code 4)  = .ok (.aluImm32 .cmp .rdi 7#32) 3 := rfl
  have sw7  : decodeX64 (fetchWindow16 gccSwitchImg.code 7)  = .ok (.jccRel .a 159#64) 6 := rfl
  have sw13 : decodeX64 (fetchWindow16 gccSwitchImg.code 13) = .ok (.lea64 .rcx (.ripRel 65516#64)) 7 := rfl
  have sw20 : decodeX64 (fetchWindow16 gccSwitchImg.code 20) = .ok (.movRR32 .rdi .rdi) 2 := rfl
  have sw22 : decodeX64 (fetchWindow16 gccSwitchImg.code 22) = .ok (.load32Sext .rax (.baseDisp .rcx (some (.rdi, 4)) 0#64)) 4 := rfl
  have sw26 : decodeX64 (fetchWindow16 gccSwitchImg.code 26) = .ok (.aluRR64 .add .rax .rcx) 3 := rfl
  have sw29 : decodeX64 (fetchWindow16 gccSwitchImg.code 29) = .ok (.jmpReg .rax) 3 := rfl
  have c88  : decodeX64 (fetchWindow16 gccSwitchImg.code 88) = .ok (.movImm64 .rax 0x9E3779B97F4A7C15#64) 10 := rfl
  have c98  : decodeX64 (fetchWindow16 gccSwitchImg.code 98) = .ok (.aluRR64 .sub .rsi .rdx) 3 := rfl
  have c101 : decodeX64 (fetchWindow16 gccSwitchImg.code 101) = .ok (.imulRR64 .rax .rsi) 4 := rfl
  have c105 : decodeX64 (fetchWindow16 gccSwitchImg.code 105) = .ok .ret 1 := rfl
  have hja1 : evalCond .a (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2 = false := rfl
  have hrod1 : readMem32Sext64 (overlayRodata gccRodataCorrect baseMem)
                 (0x10000#64 + 1#64 * BitVec.ofNat 64 4 + 0#64) = 0xFFFFFFFFFFFF0058#64 := by
    have had : (0x10000#64 + 1#64 * BitVec.ofNat 64 4 + 0#64) = 0x10004#64 := rfl
    have hb0 := overlayRodata_at gccRodataCorrect baseMem (0x10004#64 + 0#64) 4 0x58 rfl rfl
    have hb1 := overlayRodata_at gccRodataCorrect baseMem (0x10004#64 + 1#64) 5 0x00 rfl rfl
    have hb2 := overlayRodata_at gccRodataCorrect baseMem (0x10004#64 + 2#64) 6 0xFF rfl rfl
    have hb3 := overlayRodata_at gccRodataCorrect baseMem (0x10004#64 + 3#64) 7 0xFF rfl rfl
    rw [had]
    unfold readMem32Sext64
    rw [hb0, hb1, hb2, hb3]
    rfl
  let m := overlayRodata gccRodataCorrect baseMem
  let r0 := initSwitchRegs 1#64 x y
  have step1 : stepX64 gccSwitchImg (nd 0) (mkSwitchState gccRodataCorrect baseMem 1 x y) =
      {{ rip := 4, regs := r0, flags := {{}}, mem := m }} := by
    dsimp [mkSwitchState, stepX64]; rw [sw0]
  have step2 : stepX64 gccSwitchImg (nd 1) {{ rip := 4, regs := r0, flags := {{}}, mem := m }} =
      {{ rip := 7, regs := r0, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw4]; rfl
  have step3 : stepX64 gccSwitchImg (nd 2)
      {{ rip := 7, regs := r0, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 13, regs := r0, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw7]; dsimp; rw [hja1]; rfl
  let r4 := regUpd r0 .rcx 0x10000#64
  have step4 : stepX64 gccSwitchImg (nd 3)
      {{ rip := 13, regs := r0, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 20, regs := r4, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw13]; rfl
  let r5 := regUpd r4 .rdi 1#64
  have step5 : stepX64 gccSwitchImg (nd 4)
      {{ rip := 20, regs := r4, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 22, regs := r5, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw20]; rfl
  let r6 := regUpd r5 .rax 0xFFFFFFFFFFFF0058#64
  have step6 : stepX64 gccSwitchImg (nd 5)
      {{ rip := 22, regs := r5, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 26, regs := r6, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw22]; dsimp [evalAddr]
    have ha6 : r5 .rcx + r5 .rdi * BitVec.ofNat 64 4 + 0#64 = 0x10000#64 + 1#64 * BitVec.ofNat 64 4 + 0#64 := rfl
    rw [ha6, hrod1]
  let r7 := regUpd r6 .rax 88#64
  let fl7 := (evalAluFlags64 .add 0xFFFFFFFFFFFF0058#64 0x10000#64 (nd 6)).2
  have step7 : stepX64 gccSwitchImg (nd 6)
      {{ rip := 26, regs := r6, flags := (evalAluFlags32 .cmp 1#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 29, regs := r7, flags := fl7, mem := m }} := by
    have hadd7 : (0xFFFFFFFFFFFF0058#64 : BitVec 64) + 0x10000#64 = 88#64 := rfl
    have hr6 : r6 .rax = 0xFFFFFFFFFFFF0058#64 ∧ r6 .rcx = 0x10000#64 := ⟨rfl, rfl⟩
    dsimp [stepX64]; rw [sw26]; dsimp [aluWritesDst]
    rw [hr6.1, hr6.2]
    change ({{ rip := 29, regs := regUpd r6 .rax (0xFFFFFFFFFFFF0058#64 + 0x10000#64), flags := fl7, mem := m }} : X64State) = _
    rw [hadd7]
  have step8 : stepX64 gccSwitchImg (nd 7) {{ rip := 29, regs := r7, flags := fl7, mem := m }} =
      {{ rip := 88, regs := r7, flags := fl7, mem := m }} := by
    have hrip8 : (88#64 : BitVec 64).toNat = 88 := rfl
    have hr7 : r7 .rax = 88#64 := rfl
    dsimp [stepX64]; rw [sw29]; dsimp; rw [hr7, hrip8]
  let r9 := regUpd r7 .rax 0x9E3779B97F4A7C15#64
  have step9 : stepX64 gccSwitchImg (nd 8) {{ rip := 88, regs := r7, flags := fl7, mem := m }} =
      {{ rip := 98, regs := r9, flags := fl7, mem := m }} := by
    dsimp [stepX64]; rw [c88]
  let r10 := regUpd r9 .rsi (x - y)
  let fl10 := (evalAluFlags64 .sub x y (nd 9)).2
  have step10 : stepX64 gccSwitchImg (nd 9) {{ rip := 98, regs := r9, flags := fl7, mem := m }} =
      {{ rip := 101, regs := r10, flags := fl10, mem := m }} := by
    dsimp [stepX64]; rw [c98]; dsimp [aluWritesDst]
    have hs_xy : r9 .rsi = x ∧ r9 .rdx = y := ⟨rfl, rfl⟩
    rw [hs_xy.1, hs_xy.2]; rfl
  let r11 := regUpd r10 .rax (0x9E3779B97F4A7C15#64 * (x - y))
  let fl11 := (evalImul64 0x9E3779B97F4A7C15#64 (x - y) (nd 10)).2
  have step11 : stepX64 gccSwitchImg (nd 10) {{ rip := 101, regs := r10, flags := fl10, mem := m }} =
      {{ rip := 105, regs := r11, flags := fl11, mem := m }} := by
    dsimp [stepX64]; rw [c101]; dsimp
    have hi_xy : r10 .rax = 0x9E3779B97F4A7C15#64 ∧ r10 .rsi = x - y := ⟨rfl, rfl⟩
    rw [hi_xy.1, hi_xy.2]; rfl
  have step12 : stepX64 gccSwitchImg (nd 11) {{ rip := 105, regs := r11, flags := fl11, mem := m }} =
      {{ rip := 105, regs := r11, flags := fl11, mem := m, halted := true }} := by
    dsimp [stepX64]; rw [c105]
  have hsf : sf = {{ rip := 105, regs := r11, flags := fl11, mem := m, halted := true }} := by
    dsimp [sf]
    rw [runX64_succ, step1, runX64_succ, step2, runX64_succ, step3, runX64_succ, step4,
        runX64_succ, step5, runX64_succ, step6, runX64_succ, step7, runX64_succ, step8,
        runX64_succ, step9, runX64_succ, step10, runX64_succ, step11, runX64_succ, step12,
        runX64_zero]
  rw [hsf]; exact ⟨rfl, rfl, rfl⟩

/-- Universal symbolic `ja` default-branch proof (`op = 8`) over arbitrary `baseMem`, `x`, `y`, `nd`! -/
theorem gcc_pic_switch8_default_symbolic_verified
    (baseMem : ByteMem) (x y : BitVec 64) (nd : Nat → UndefFlags) :
    let sf := runX64 gccSwitchImg 6 nd (mkSwitchState gccRodataCorrect baseMem 8 x y)
    sf.halted = true ∧ sf.fault = false ∧ sf.regs .rax = x ^^^ y := by
  intro sf
  have sw0   : decodeX64 (fetchWindow16 gccSwitchImg.code 0)   = .ok .endbr64 4 := rfl
  have sw4   : decodeX64 (fetchWindow16 gccSwitchImg.code 4)   = .ok (.aluImm32 .cmp .rdi 7#32) 3 := rfl
  have sw7   : decodeX64 (fetchWindow16 gccSwitchImg.code 7)   = .ok (.jccRel .a 159#64) 6 := rfl
  have d172  : decodeX64 (fetchWindow16 gccSwitchImg.code 172) = .ok (.movRR64 .rax .rsi) 3 := rfl
  have d175  : decodeX64 (fetchWindow16 gccSwitchImg.code 175) = .ok (.aluRR64 .xor .rax .rdx) 3 := rfl
  have d178  : decodeX64 (fetchWindow16 gccSwitchImg.code 178) = .ok .ret 1 := rfl
  have hja8  : evalCond .a (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2 = true := rfl
  let m := overlayRodata gccRodataCorrect baseMem
  let r0 := initSwitchRegs 8#64 x y
  have st1 : stepX64 gccSwitchImg (nd 0) (mkSwitchState gccRodataCorrect baseMem 8 x y) =
      {{ rip := 4, regs := r0, flags := {{}}, mem := m }} := by
    dsimp [mkSwitchState, stepX64]; rw [sw0]
  have st2 : stepX64 gccSwitchImg (nd 1) {{ rip := 4, regs := r0, flags := {{}}, mem := m }} =
      {{ rip := 7, regs := r0, flags := (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw4]; rfl
  have st3 : stepX64 gccSwitchImg (nd 2)
      {{ rip := 7, regs := r0, flags := (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 172, regs := r0, flags := (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [sw7]; dsimp; rw [hja8]; rfl
  let r4 := regUpd r0 .rax x
  have st4 : stepX64 gccSwitchImg (nd 3)
      {{ rip := 172, regs := r0, flags := (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 175, regs := r4, flags := (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2, mem := m }} := by
    dsimp [stepX64]; rw [d172]; rfl
  let r5 := regUpd r4 .rax (x ^^^ y)
  let fl5 := (evalAluFlags64 .xor x y (nd 4)).2
  have st5 : stepX64 gccSwitchImg (nd 4)
      {{ rip := 175, regs := r4, flags := (evalAluFlags32 .cmp 8#32 7#32 (nd 1)).2, mem := m }} =
      {{ rip := 178, regs := r5, flags := fl5, mem := m }} := by
    dsimp [stepX64]; rw [d175]; dsimp [aluWritesDst]
    have hx : r4 .rax = x ∧ r4 .rdx = y := ⟨rfl, rfl⟩
    rw [hx.1, hx.2]; rfl
  have st6 : stepX64 gccSwitchImg (nd 5) {{ rip := 178, regs := r5, flags := fl5, mem := m }} =
      {{ rip := 178, regs := r5, flags := fl5, mem := m, halted := true }} := by
    dsimp [stepX64]; rw [d178]
  have hsf : sf = {{ rip := 178, regs := r5, flags := fl5, mem := m, halted := true }} := by
    dsimp [sf]
    rw [runX64_succ, st1, runX64_succ, st2, runX64_succ, st3,
        runX64_succ, st4, runX64_succ, st5, runX64_succ, st6, runX64_zero]
  rw [hsf]; exact ⟨rfl, rfl, rfl⟩

/-- Negative-control theorem (`gcc_pic_switch8_unadjusted_addend_corrupts`):
    Using raw `.rela.rodata` addend `A_1` (`0x5c`) without subtracting entry offset `4 * 1`
    causes `notrack jmp rax` at step 8 to jump 4 bytes INTO the middle of Case 1's 10-byte
    `movabs` immediate (`rip = 92` instead of `88`)! -/
theorem gcc_pic_switch8_unadjusted_addend_corrupts :
    let sGood := mkSwitchState gccRodataCorrect (fun _ => 0#8) 1 10#64 3#64
    let sBug  := mkSwitchState gccRodataBuggy   (fun _ => 0#8) 1 10#64 3#64
    (runX64 gccSwitchImg 8 (fun _ => {{}}) sGood).rip = {resolved_targets[1]} ∧
    (runX64 gccSwitchImg 8 (fun _ => {{}}) sBug).rip  = {resolved_targets[1] + 4} :=
  ⟨rfl, rfl⟩

end GccRealObjectProofs
"""
    return lean_src, meta


# ============================================================================
# Suite 2 Generator: Demonic `RFLAGS` Cliff vs. Backward `DeadFlagCollapse`
# ============================================================================

def gen_64insn_leaf_bytes(n_insns: int = 64, seed_off: int = 0) -> list[int]:
    """Generate `n_insns` variable-length (`3..10` byte, ~4.72 B/insn) x86-64 instructions
    mixing `movabs` (10B), `[rsp+disp]` loads/stores (4-5B), `imul`/`shl`/`shr` (4B),
    and `xor`/`add` (3B)."""
    bs: list[int] = []
    for idx in range(n_insns):
        g = idx // 8
        kind = idx % 8
        slot = (g + seed_off) % 8
        disp = slot * 8
        c_imm = 0x9E3779B97F4A7C15 ^ ((g + seed_off + 1) * 0x10001)
        if kind == 0:
            bs.extend([0x49, 0xB8] + list(c_imm.to_bytes(8, "little")))
        elif kind == 1:
            bs.extend([0x4C, 0x31, 0xC0])
        elif kind == 2:
            bs.extend([0x48, 0x0F, 0xAF, 0xC6])
        elif kind == 3:
            bs.extend([0x48, 0xC1, 0xE0, 0x07])
        elif kind == 4:
            bs.extend([0x48, 0x89, 0x04, 0x24] if disp == 0 else [0x48, 0x89, 0x44, 0x24, disp])
        elif kind == 5:
            bs.extend([0x48, 0xC1, 0xE8, 0x0B])
        elif kind == 6:
            bs.extend([0x48, 0x8B, 0x0C, 0x24] if disp == 0 else [0x48, 0x8B, 0x4C, 0x24, disp])
        else:
            bs.extend([0x48, 0x01, 0xC8])
    return bs


def gen_demonic_case_split_lean(mod_name: str, k_steps: int) -> str:
    """Naive per-step demonic undefined-flag case-splitting (`4^K` branches when splitting
    2 undefined flag bits `zf` and `af` per `imul` instruction without `DeadFlagCollapse`)."""
    bs: list[int] = []
    for _ in range(k_steps):
        bs.extend([0x48, 0x0F, 0xAF, 0xC6])  # imul rax, rsi (4B)
    split_tac = "\n".join(
        f"  cases (nd {i}).zf <;> cases (nd {i}).af" for i in range(k_steps)
    )
    return f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base

namespace {mod_name}
open ByteX86

def imulChainImg : X64ObjImage := {{ code := .leaf {fmt_byte_list(bs)} }}

def specImulPow : Nat → BitVec 64 → BitVec 64 → BitVec 64
  | 0, a, _ => a
  | k + 1, a, b => specImulPow k (a * b) b

theorem naive_demonic_split_{k_steps}
    (nd : Nat → UndefFlags) (a b : BitVec 64) (m : ByteMem) :
    let s0 : X64State := {{
      rip := 0,
      regs := fun r => if r == .rax then a else if r == .rsi then b else 0#64,
      flags := {{}},
      mem := m
    }}
    (runX64 imulChainImg {k_steps} nd s0).rip = {4 * k_steps} ∧
    (runX64 imulChainImg {k_steps} nd s0).regs .rax = specImulPow {k_steps} a b := by
{split_tac}
  all_goals exact ⟨rfl, rfl⟩

end {mod_name}
"""


def gen_uncollapsed_whnf_lean(mod_name: str, n_insns: int) -> str:
    """Direct symbolic stepping without `DeadFlagCollapse` (`0` `set_option`, default 200k heartbeats)."""
    bs = gen_64insn_leaf_bytes(n_insns)
    return f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base

namespace {mod_name}
open ByteX86

def rawLeafImg : X64ObjImage := {{ code := .leaf {fmt_byte_list(bs)} }}

theorem uncollapsed_whnf_{n_insns}
    (nd : Nat → UndefFlags) (s0 : X64State)
    (hrip : s0.rip = 0) (hnh : s0.halted = false) (hnf : s0.fault = false) :
    (runX64 rawLeafImg {n_insns} nd s0).rip = {len(bs)} ∧
    (runX64 rawLeafImg {n_insns} nd s0).fault = false := by
  cases s0 with
  | mk rip regs flags mem halted fault =>
    dsimp at hrip hnh hnf
    subst hrip hnh hnf
    exact ⟨rfl, rfl⟩

end {mod_name}
"""


def gen_collapsed_leaf_lean(mod_name: str, n_insns: int, cops_expr: str) -> str:
    bs = gen_64insn_leaf_bytes(n_insns)
    return f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base

namespace {mod_name}
open ByteX86

def leafBytes : List UInt8 := {fmt_byte_list(bs)}
def leafImg : X64ObjImage := {{ code := .leaf leafBytes }}

def leafCops : List CollapsedOp := {cops_expr}

theorem h_comp : compileByteLeaf 8 FlagMask.dead leafBytes = some (FlagMask.dead, leafCops) := rfl
theorem h_len  : lenTR leafCops = {n_insns} := rfl

theorem collapsed_leaf_{n_insns}_verified
    (nd : Nat → UndefFlags) (s0 : X64State) (l0 : LiftedX64State)
    (hrip : s0.rip = 0)
    (habs : AbstractsLeaf 8 FlagMask.dead s0 l0) :
    let sf := runX64 leafImg {n_insns} nd s0
    sf.rip = {len(bs)} ∧
    sf.regs .rsp = s0.regs .rsp ∧
    (∀ a, OutsideSpillRange (s0.regs .rsp) 8 a → sf.mem a = s0.mem a) ∧
    AbstractsLeaf 8 FlagMask.dead sf (evalCollapsedOps leafCops l0) := by
  have h := checkByteLeaf_sound (maxSlots := 8) (img := leafImg)
    (by decide : 8 * 8 < 2 ^ 64) (checkLeafBytesAt_here leafBytes)
    h_comp nd s0 l0 hrip habs
  rw [h_len, Nat.zero_add] at h
  exact h

end {mod_name}
"""


# ============================================================================
# Suite 3 Generator: Naive `O(S * P)` ByteMem Aliasing vs. `PrivateStackSep`
# ============================================================================

def gen_naive_aliasing_lean(mod_name: str, n_spills: int, n_ptrs: int) -> str:
    """Baseline without `PrivateStackSep`: preserving `P` caller 8-byte pointers across
    `S` byte-addressed stack stores requires `S * P` pairwise `readMem64_writeMem64_disjoint` rewrites."""
    ptr_params = " ".join(f"(p{j} : BitVec 64)" for j in range(n_ptrs))
    disj_hyps = "\n    ".join(
        f"(hd_{s}_{j} : ∀ b1, b1 < 8 → ∀ b2, b2 < 8 → p{j} + BitVec.ofNat 64 b1 ≠ spillSlotAddr rsp {s % 8} + BitVec.ofNat 64 b2)"
        for s in range(n_spills)
        for j in range(n_ptrs)
    )
    mem_lets = "\n  ".join(
        f"let m{s + 1} := writeMem64 m{s} (spillSlotAddr rsp {s % 8}) v"
        for s in range(n_spills)
    )
    concl = " ∧\n    ".join(f"readMem64 (finalMem m0 rsp v) p{j} = readMem64 m0 p{j}" for j in range(n_ptrs))

    proof_items: list[str] = []
    for j in range(n_ptrs):
        rws = ", ".join(
            f"readMem64_writeMem64_disjoint _ p{j} (spillSlotAddr rsp {s % 8}) v hd_{s}_{j}"
            for s in reversed(range(n_spills))
        )
        proof_items.append(f"(by dsimp only [finalMem]; rw [{rws}])")
    nested_proof = proof_items[-1]
    for item in reversed(proof_items[:-1]):
        nested_proof = f"And.intro {item}\n    ({nested_proof})"

    return f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import ByteX86Base

namespace {mod_name}
open ByteX86

def finalMem (m0 : ByteMem) (rsp v : BitVec 64) : ByteMem :=
  {mem_lets}
  m{n_spills}

theorem naive_flat_aliasing_{n_spills}_{n_ptrs}
    (m0 : ByteMem) (rsp v : BitVec 64)
    {ptr_params}
    {disj_hyps} :
    {concl} :=
  {nested_proof}

end {mod_name}
"""


def gen_private_stack_sep_lean(mod_name: str, n_spills: int, n_ptrs: int, cops_expr: str) -> str:
    """`PrivateStackSep` + `checkByteLeaf_sound`: `S` real byte-decoded `[rsp + disp]` stores
    discharge all `P` caller `readMem64` preservation obligations in `O(S + P)` (`1` envelope
    check per caller pointer independent of `S`!)."""
    bs: list[int] = []
    for s in range(n_spills):
        disp = (s % 8) * 8
        if disp == 0:
            bs.extend([0x48, 0x89, 0x04, 0x24])
        else:
            bs.extend([0x48, 0x89, 0x44, 0x24, disp])
    ptr_params = " ".join(f"(p{j} : BitVec 64)" for j in range(n_ptrs))
    env_hyps = "\n    ".join(
        f"(henv_{j} : ∀ k, k < 8 → ¬ InStackEnvelope rspEntry 103 (p{j} + BitVec.ofNat 64 k))"
        for j in range(n_ptrs)
    )
    concl = " ∧\n    ".join(f"readMem64 sf.mem p{j} = readMem64 s0.mem p{j}" for j in range(n_ptrs))
    ptr_proofs = [f"preserve_read64_outside p{j} henv_{j}" for j in range(n_ptrs)]
    nested = ptr_proofs[-1]
    for item in reversed(ptr_proofs[:-1]):
        nested = f"And.intro ({item}) ({nested})"

    return f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base

namespace {mod_name}
open ByteX86

def spillOnlyBytes : List UInt8 := {fmt_byte_list(bs)}
def spillOnlyImg : X64ObjImage := {{ code := .leaf spillOnlyBytes }}

def spillCops : List CollapsedOp := {cops_expr}

theorem h_comp : compileByteLeaf 8 FlagMask.dead spillOnlyBytes = some (FlagMask.dead, spillCops) := rfl
theorem h_len  : lenTR spillCops = {n_spills} := rfl

theorem private_stack_sep_{n_spills}_{n_ptrs}
    (nd : Nat → UndefFlags) (rspEntry : BitVec 64) (s0 : X64State) (l0 : LiftedX64State)
    (hrip : s0.rip = 0)
    (hrsp : s0.regs .rsp = ((rspEntry - 8#64) &&& 0xFFFFFFFFFFFFFFE0#64) - 64#64)
    (habs : AbstractsLeaf 8 FlagMask.dead s0 l0)
    {ptr_params}
    {env_hyps} :
    let sf := runX64 spillOnlyImg {n_spills} nd s0
    {concl} := by
  intro sf
  have hleaf := checkByteLeaf_sound (maxSlots := 8) (img := spillOnlyImg)
    (by decide : 8 * 8 < 2 ^ 64) (checkLeafBytesAt_here spillOnlyBytes)
    h_comp nd s0 l0 hrip habs
  rw [h_len] at hleaf
  have hmem := hleaf.2.2.1
  have preserve_read64_outside : ∀ (p : BitVec 64),
      (∀ k, k < 8 → ¬ InStackEnvelope rspEntry 103 (p + BitVec.ofNat 64 k)) →
      readMem64 sf.mem p = readMem64 s0.mem p := by
    intro p hp
    have hbyte : ∀ k, k < 8 → sf.mem (p + BitVec.ofNat 64 k) = s0.mem (p + BitVec.ofNat 64 k) := by
      intro k hk
      apply hmem
      rw [hrsp]
      exact realigned_frame_envelope_separation rspEntry (p + BitVec.ofNat 64 k) 64 8
        (by decide) (by decide) (hp k hk)
    dsimp [readMem64]
    rw [hbyte 0 (by decide), hbyte 1 (by decide), hbyte 2 (by decide), hbyte 3 (by decide),
        hbyte 4 (by decide), hbyte 5 (by decide), hbyte 6 (by decide), hbyte 7 (by decide)]
  exact {nested}

end {mod_name}
"""


# ============================================================================
# Suite 4 Generator: Sharded Variable-Length `ByteShardedTreeLift` Scaling
# ============================================================================

def build_balanced_tree_expr(leaves_names: list[tuple[str, int]]) -> tuple[str, list[str], int]:
    """Build balanced `ByteCodeTree` expression + closed `O(log B)` `checkLeafBytesAt` proof terms."""
    def helper(items: list[tuple[str, int]]) -> tuple[str, list[tuple[int, str]], int]:
        n = len(items)
        if n == 1:
            nm, sz = items[0]
            return f"(.leaf {nm})", [(0, f"(checkLeafBytesAt_here {nm})")], sz
        mid = n // 2
        l_expr, l_prfs, l_sz = helper(items[:mid])
        r_expr, r_prfs, r_sz = helper(items[mid:])
        prfs: list[tuple[int, str]] = []
        for sub_off, p in l_prfs:
            prfs.append((sub_off, f"(checkLeafBytesAt_goLeft (lsz := {l_sz}) (base := {sub_off}) rfl {p})"))
        for sub_off, p in r_prfs:
            cur_off = l_sz + sub_off
            prfs.append((cur_off, f"(checkLeafBytesAt_goRight (lsz := {l_sz}) (base := {cur_off}) (subBase := {sub_off}) rfl rfl {p})"))
        return f"(.node {l_sz} {l_expr} {r_expr})", prfs, l_sz + r_sz

    expr, tagged_prfs, tot = helper(leaves_names)
    return expr, [p for _, p in tagged_prfs], tot


def run_sharded_byte_lift_point(td: Path, env: dict[str, str], base_flags: list[str], n_insns: int) -> tuple[dict[str, object], tuple[str, str, str]]:
    assert n_insns % 64 == 0
    n_leaves = n_insns // 64
    sub = td / f"sharded_{n_insns}"
    sub.mkdir(exist_ok=True)
    sub_env = dict(env)
    sub_env["LEAN_PATH"] = f"{sub}:{env['LEAN_PATH']}"

    leaves_bytes = [gen_64insn_leaf_bytes(64, seed_off=i) for i in range(n_leaves)]
    witness_map = precompute_collapsed_ops_batch(td, env, {f"l{i}": leaves_bytes[i] for i in range(n_leaves)})
    leaves_meta = [(f"leafBytes_{i}", len(leaves_bytes[i])) for i in range(n_leaves)]
    tree_expr, paths, total_bytes = build_balanced_tree_expr(leaves_meta)

    offsets: list[int] = []
    acc = 0
    for _, sz in leaves_meta:
        offsets.append(acc)
        acc += sz

    common_name = f"ShardedCommon_{n_insns}"
    leaf_defs = "\n".join(
        f"def leafBytes_{i} : List UInt8 := {fmt_byte_list(leaves_bytes[i])}"
        for i in range(n_leaves)
    )
    common_src = f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base

namespace {common_name}
open ByteX86

{leaf_defs}

def fullImg : X64ObjImage := {{ code := {tree_expr} }}

def SegmentVerified (startRip endRip steps : Nat) (f : LiftedX64State → LiftedX64State) : Prop :=
  ∀ (nd : Nat → UndefFlags) (s : X64State) (l : LiftedX64State),
    s.rip = startRip →
    AbstractsLeaf 8 FlagMask.dead s l →
    let sf := runX64 fullImg steps nd s
    sf.rip = endRip ∧
    sf.regs .rsp = s.regs .rsp ∧
    (∀ a, OutsideSpillRange (s.regs .rsp) 8 a → sf.mem a = s.mem a) ∧
    AbstractsLeaf 8 FlagMask.dead sf (f l)

theorem SegmentVerified_seq {{r0 r1 r2 n1 n2 n3 : Nat}} {{f1 f2 : LiftedX64State → LiftedX64State}}
    (h1 : SegmentVerified r0 r1 n1 f1)
    (h2 : SegmentVerified r1 r2 n2 f2)
    (hn : n1 + n2 = n3) :
    SegmentVerified r0 r2 n3 (fun l => f2 (f1 l)) := by
  subst hn
  intro nd s l hrip habs
  rcases h1 nd s l hrip habs with ⟨hr1, hrsp1, hmem1, habs1⟩
  rcases h2 (fun k => nd (k + n1)) (runX64 fullImg n1 nd s) (f1 l) hr1 habs1 with ⟨hr2, hrsp2, hmem2, habs2⟩
  dsimp only
  rw [runX64_add fullImg n1 n2 nd s]
  refine ⟨hr2, ?_, ?_, habs2⟩
  · rw [hrsp2, hrsp1]
  · intro a hout
    have hout1 : OutsideSpillRange ((runX64 fullImg n1 nd s).regs .rsp) 8 a := by
      rw [hrsp1]; exact hout
    rw [hmem2 a hout1, hmem1 a hout]

end {common_name}
"""
    (sub / f"{common_name}.lean").write_text(common_src, encoding="utf-8")

    # Group leaves into shards of up to 5 leaves (`320` instructions per shard)
    leaves_per_shard = 5
    shard_groups = [
        list(range(i, min(i + leaves_per_shard, n_leaves)))
        for i in range(0, n_leaves, leaves_per_shard)
    ]

    total_wall = 0.0
    total_cpu = 0.0
    max_rss = 0.0
    total_olean = 0

    rc_c = run_timed_lean(base_flags + ["-R", str(sub), "-o", str(sub / f"{common_name}.olean"), str(sub / f"{common_name}.lean")], sub_env)
    assert rc_c["rc"] == 0, f"{common_name} failed: {rc_c['stdout']} {rc_c['stderr_tail']}"
    common_wall = float(rc_c["wall_s"])
    total_wall += common_wall
    total_cpu += float(rc_c["cpu_s"] or 0.0)
    max_rss = max(max_rss, float(rc_c["rss_mb"] or 0.0))
    total_olean += (sub / f"{common_name}.olean").stat().st_size

    max_shard_wall = 0.0
    shard_mods: list[str] = []
    for s_idx, grp in enumerate(shard_groups):
        s_mod = f"ByteShard_{n_insns}_{s_idx}"
        shard_mods.append(s_mod)
        leaf_blocks: list[str] = []
        for li in grp:
            b0 = offsets[li]
            b1 = b0 + leaves_meta[li][1]
            leaf_blocks.append(f"""
def cops_{li} : List CollapsedOp := {witness_map[f"l{li}"]}

theorem hcomp_{li} : compileByteLeaf 8 FlagMask.dead leafBytes_{li} = some (FlagMask.dead, cops_{li}) := rfl
theorem hlen_{li}  : lenTR cops_{li} = 64 := rfl
theorem hb1_{li}   : {b0} + lenTR leafBytes_{li} = {b1} := rfl

theorem leaf_{li}_ok : SegmentVerified {b0} {b1} 64 (evalCollapsedOps cops_{li}) := by
  intro nd s l hrip habs
  have h := checkByteLeaf_sound (maxSlots := 8) (img := fullImg) (leafBase := {b0})
    (by decide : 8 * 8 < 2 ^ 64)
    {paths[li]}
    hcomp_{li} nd s l hrip habs
  rw [hlen_{li}, hb1_{li}] at h
  exact h
""")
        seq_expr = f"leaf_{grp[0]}_ok"
        fn_expr = f"(evalCollapsedOps cops_{grp[0]})"
        for li in grp[1:]:
            seq_expr = f"(SegmentVerified_seq {seq_expr} leaf_{li}_ok rfl)"
            fn_expr = f"(fun l => evalCollapsedOps cops_{li} ({fn_expr} l))"
        start_b = offsets[grp[0]]
        end_b = offsets[grp[-1]] + leaves_meta[grp[-1]][1]
        steps_s = 64 * len(grp)
        shard_src = f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base
import {common_name}

namespace {s_mod}
open ByteX86 {common_name}
{"".join(leaf_blocks)}
def shardFn : LiftedX64State → LiftedX64State := {fn_expr}

theorem shard_ok : SegmentVerified {start_b} {end_b} {steps_s} shardFn := by
  unfold shardFn
  exact {seq_expr}

end {s_mod}
"""
        (sub / f"{s_mod}.lean").write_text(shard_src, encoding="utf-8")
        rs = run_timed_lean(base_flags + ["-R", str(sub), "-o", str(sub / f"{s_mod}.olean"), str(sub / f"{s_mod}.lean")], sub_env)
        assert rs["rc"] == 0, f"{s_mod} failed: {rs['stdout']} {rs['stderr_tail']}"
        total_wall += float(rs["wall_s"])
        max_shard_wall = max(max_shard_wall, float(rs["wall_s"]))
        total_cpu += float(rs["cpu_s"] or 0.0)
        max_rss = max(max_rss, float(rs["rss_mb"] or 0.0))
        total_olean += (sub / f"{s_mod}.olean").stat().st_size

    top_mod = f"ByteShardedTop_{n_insns}"
    imports = "\n".join(f"import {m}" for m in shard_mods)
    seq_top = f"{shard_mods[0]}.shard_ok"
    fn_top = f"{shard_mods[0]}.shardFn"
    for m in shard_mods[1:]:
        seq_top = f"(SegmentVerified_seq {seq_top} {m}.shard_ok rfl)"
        fn_top = f"(fun l => {m}.shardFn ({fn_top} l))"
    top_src = f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base
import {common_name}
{imports}

namespace {top_mod}
open ByteX86 {common_name}

def topSpecFn : LiftedX64State → LiftedX64State := {fn_top}

theorem top_verified : SegmentVerified 0 {total_bytes} {n_insns} topSpecFn := by
  unfold topSpecFn
  exact {seq_top}

end {top_mod}
"""
    (sub / f"{top_mod}.lean").write_text(top_src, encoding="utf-8")
    rt = run_timed_lean(base_flags + ["-R", str(sub), "-o", str(sub / f"{top_mod}.olean"), str(sub / f"{top_mod}.lean")], sub_env)
    assert rt["rc"] == 0, f"{top_mod} failed: {rt['stdout']} {rt['stderr_tail']}"
    top_wall = float(rt["wall_s"])
    total_wall += top_wall
    total_cpu += float(rt["cpu_s"] or 0.0)
    max_rss = max(max_rss, float(rt["rss_mb"] or 0.0))
    total_olean += (sub / f"{top_mod}.olean").stat().st_size

    # Symlink `.olean` files into top `td` so batch `ReplayAudit` finds them in `LEAN_PATH`
    for ol in sub.glob("*.olean"):
        target = td / ol.name
        if not target.exists():
            shutil.copy2(ol, target)

    return {
        "n_insns": n_insns,
        "total_bytes": total_bytes,
        "n_leaves": n_leaves,
        "n_shards": len(shard_mods),
        "compile_wall_sum_s": round(total_wall, 4),
        "compile_cpu_sum_s": round(total_cpu, 4),
        "common_wall_s": round(common_wall, 4),
        "max_shard_wall_s": round(max_shard_wall, 4),
        "top_wall_s": round(top_wall, 4),
        "critical_path_wall_s": round(common_wall + max_shard_wall + top_wall, 4),
        "max_rss_mb": round(max_rss, 2),
        "olean_sum_bytes": total_olean,
    }, (top_mod, f"{top_mod}.top_verified", "ByteX86Base")


# ============================================================================
# Suite 5 Generator: Decidable Loop-Invariant-Free `checkSfiObject` Scaling
# ============================================================================

def gen_sfi_bundle_32b(b_idx: int, n_bundles: int) -> list[int]:
    """Generate a 32-byte cyclic SFI x86-64 bundle (`8` variable-length instructions = `32` bytes)."""
    is_last = (b_idx == n_bundles - 1)
    if is_last:
        # Final bundle: sandboxed store + xor + vzeroupper + NOPs + trailing `ret` at byte 31!
        # 2 + 5 + 3 + 3 + 8 + 7 + 3 + 1 = 32 bytes (8 instructions)
        b = (
            [0x89, 0xC0]                                  # mov eax, eax (2B)
            + [0x49, 0x89, 0x4C, 0x06, 0x20]              # mov [r14+rax*1+0x20], rcx (5B)
            + [0x48, 0x89, 0xC8]                          # mov rax, rcx (3B)
            + [0x48, 0x31, 0xD0]                          # xor rax, rdx (3B)
            + [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]  # 8B NOP
            + [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]        # 7B NOP
            + [0xC5, 0xF8, 0x77]                          # vzeroupper (3B)
            + [0xC3]                                      # ret (1B at off=31)
        )
    elif b_idx % 3 == 0:
        # Entry + sandboxed load + imul + shl + xor + add + 7B NOP = 32B (8 instructions)
        b = (
            [0xF3, 0x0F, 0x1E, 0xFA]                      # endbr64 (4B)
            + [0x89, 0xD2]                                # mov edx, edx (2B)
            + [0x49, 0x8B, 0x44, 0x16, 0x08]              # mov rax, [r14+rdx*1+8] (5B)
            + [0x48, 0x0F, 0xAF, 0xC6]                    # imul rax, rsi (4B)
            + [0x48, 0xC1, 0xE0, 0x03]                    # shl rax, 3 (4B)
            + [0x48, 0x31, 0xC1]                          # xor rcx, rax (3B)
            + [0x48, 0x01, 0xF1]                          # add rcx, rsi (3B)
            + [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]  # 7B NOP
        )
    elif b_idx % 3 == 1:
        # Sandboxed store + backward cyclic loop `jb` (`bBase - 32` at `off+len = 20` -> `rel = -52 = 0xCC`)!
        # 2 + 5 + 4 + 7 + 2 + 3 + 4 + 5 = 32B (8 instructions)
        b = (
            [0x89, 0xC8]                                  # mov eax, ecx (2B)
            + [0x49, 0x89, 0x4C, 0x06, 0x10]              # mov [r14+rax*1+0x10], rcx (5B)
            + [0x48, 0x83, 0xC2, 0x08]                    # add rdx, 8 (4B)
            + [0x48, 0x81, 0xFA, 0x00, 0x10, 0x00, 0x00]  # cmp rdx, 0x1000 (7B)
            + [0x72, 0xCC]                                # jb -52 -> jumps to previous bundle start! (2B)
            + [0x48, 0x31, 0xD1]                          # xor rcx, rdx (3B)
            + [0x48, 0xC1, 0xE9, 0x05]                    # shr rcx, 5 (4B)
            + [0x0F, 0x1F, 0x44, 0x00, 0x00]              # 5B NOP
        )
    else:
        # Masked indirect jump (`and eax, 0xE0; jmp rax`) + forward jump (`jmp +13` -> `bBase + 32`)!
        # 3 + 3 + 5 + 2 + 4 + 2 + 7 + 6 = 32B (8 instructions)
        b = (
            [0x48, 0x89, 0xC8]                            # mov rax, rcx (3B)
            + [0x48, 0x31, 0xF0]                          # xor rax, rsi (3B)
            + [0x25, 0xE0, 0x00, 0x00, 0x00]              # and eax, 0xE0 (5B)
            + [0xFF, 0xE0]                                # jmp rax (2B)
            + [0x48, 0x83, 0xC1, 0x01]                    # add rcx, 1 (4B)
            + [0xEB, 0x0D]                                # jmp +13 -> next bundle start (2B)
            + [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]  # 7B NOP
            + [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]        # 6B NOP
        )
    assert len(b) == 32
    return b


def gen_monolithic_sfi_lean(mod_name: str, n_insns: int) -> str:
    assert n_insns % 8 == 0
    n_bundles = n_insns // 8
    total_bytes = n_bundles * 32
    all_bytes = [x for i in range(n_bundles) for x in gen_sfi_bundle_32b(i, n_bundles)]
    return f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base
import ByteX86Sfi

namespace {mod_name}
open ByteX86

def sfiMonoImg : X64ObjImage := {{ code := .leaf {fmt_byte_list(all_bytes)} }}

theorem sfi_mono_{n_insns}_ok : checkSfiObject {total_bytes} sfiMonoImg = true := rfl

end {mod_name}
"""


def run_sharded_sfi_point(td: Path, env: dict[str, str], base_flags: list[str], n_insns: int) -> tuple[dict[str, object], tuple[str, str, str]]:
    """Sharded homomorphic `checkSfiSubtree_node` + `checkSfiObject_preserves_rust_host_safety`."""
    assert n_insns % 128 == 0
    n_bundles = n_insns // 8
    bundles_per_leaf = 16  # 128 instructions = 512 bytes per leaf
    n_leaves = n_bundles // bundles_per_leaf
    total_bytes = n_bundles * 32

    leaves_bytes = [
        [x for b in range(li * bundles_per_leaf, (li + 1) * bundles_per_leaf) for x in gen_sfi_bundle_32b(b, n_bundles)]
        for li in range(n_leaves)
    ]

    # Group up to 8 leaves (`1,024` instructions = `4,096` bytes) per shard module
    leaves_per_shard = 8
    shard_groups = [
        list(range(i, min(i + leaves_per_shard, n_leaves)))
        for i in range(0, n_leaves, leaves_per_shard)
    ]

    total_wall = 0.0
    total_cpu = 0.0
    max_rss = 0.0
    total_olean = 0

    max_shard_wall = 0.0
    shard_infos: list[tuple[str, int, int]] = []  # (mod_name, start_byte, byte_len)

    def build_local_sfi_tree(indices: list[int]) -> tuple[str, str, int, int]:
        if len(indices) == 1:
            li = indices[0]
            b0 = li * 512
            b1 = b0 + 512
            return f"(.leaf sfiLeaf_{li})", f"sfiLeaf_{li}_ok", b0, 512
        mid = len(indices) // 2
        lt, lp, lb0, lsz = build_local_sfi_tree(indices[:mid])
        rt, rp, rb0, rsz = build_local_sfi_tree(indices[mid:])
        assert lb0 + lsz == rb0
        tree_s = f"(.node {lsz} {lt} {rt})"
        prf_s = f"(checkSfiSubtree_node rfl rfl {lp} {rp})"
        return tree_s, prf_s, lb0, lsz + rsz

    for s_idx, grp in enumerate(shard_groups):
        s_mod = f"SfiShard_{n_insns}_{s_idx}"
        leaf_decls: list[str] = []
        for li in grp:
            b0 = li * 512
            b1 = b0 + 512
            leaf_decls.append(f"""
def sfiLeaf_{li} : List UInt8 := {fmt_byte_list(leaves_bytes[li])}
theorem sfiLeaf_{li}_ok : checkSfiSubtree {total_bytes} {b0} {b1} (.leaf sfiLeaf_{li}) = true := rfl
""")
        stree, sprf, sb0, ssz = build_local_sfi_tree(grp)
        s_src = f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base
import ByteX86Sfi

namespace {s_mod}
open ByteX86
{"".join(leaf_decls)}
def shardTree : ByteCodeTree := {stree}

theorem shard_sfi_ok : checkSfiSubtree {total_bytes} {sb0} {sb0 + ssz} shardTree = true :=
  {sprf}

end {s_mod}
"""
        (td / f"{s_mod}.lean").write_text(s_src, encoding="utf-8")
        rs = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{s_mod}.olean"), str(td / f"{s_mod}.lean")], env)
        assert rs["rc"] == 0, f"{s_mod} failed: {rs['stdout']} {rs['stderr_tail']}"
        total_wall += float(rs["wall_s"])
        max_shard_wall = max(max_shard_wall, float(rs["wall_s"]))
        total_cpu += float(rs["cpu_s"] or 0.0)
        max_rss = max(max_rss, float(rs["rss_mb"] or 0.0))
        total_olean += (td / f"{s_mod}.olean").stat().st_size
        shard_infos.append((s_mod, sb0, ssz))

    def build_top_sfi_tree(infos: list[tuple[str, int, int]]) -> tuple[str, str, int, int]:
        if len(infos) == 1:
            m, b0, sz = infos[0]
            return f"{m}.shardTree", f"{m}.shard_sfi_ok", b0, sz
        mid = len(infos) // 2
        lt, lp, lb0, lsz = build_top_sfi_tree(infos[:mid])
        rt, rp, rb0, rsz = build_top_sfi_tree(infos[mid:])
        assert lb0 + lsz == rb0
        tree_s = f"(.node {lsz} {lt} {rt})"
        prf_s = f"(checkSfiSubtree_node rfl rfl {lp} {rp})"
        return tree_s, prf_s, lb0, lsz + rsz

    top_tree, top_prf, tb0, tsz = build_top_sfi_tree(shard_infos)
    assert tb0 == 0 and tsz == total_bytes
    top_mod = f"SfiTop_{n_insns}"
    imports = "\n".join(f"import {m}" for m, _, _ in shard_infos)
    top_src = f"""prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.List.Basic
import ByteX86Base
import ByteX86Sfi
{imports}

namespace {top_mod}
open ByteX86

def sfiImg : X64ObjImage := {{ code := {top_tree} }}

theorem sfi_subtree_ok : checkSfiSubtree {total_bytes} 0 {total_bytes} sfiImg.code = true :=
  {top_prf}

theorem sfi_obj_ok : checkSfiObject {total_bytes} sfiImg = true := by
  dsimp [checkSfiObject]
  rw [sfi_subtree_ok]
  rfl

theorem sfi_host_safety_{n_insns}
    (s0 : X64State)
    (hrip0 : s0.rip < {total_bytes}) (hmod0 : s0.rip % 32 = 0) (hnf0 : s0.fault = false) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags),
      let sf := runX64 sfiImg steps nd s0
      sf.fault = false ∧
      sf.regs .r14 = s0.regs .r14 ∧
      sf.regs .rsp = s0.regs .rsp ∧
      (∀ r, isHostProtectedReg r = true → sf.regs r = s0.regs r) ∧
      (∀ a, OutsideSandboxArena (s0.regs .r14) a → sf.mem a = s0.mem a) ∧
      (sf.halted = false → sf.rip < {total_bytes}) :=
  checkSfiObject_preserves_rust_host_safety sfi_obj_ok s0 hrip0 hmod0 hnf0

end {top_mod}
"""
    (td / f"{top_mod}.lean").write_text(top_src, encoding="utf-8")
    rt = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{top_mod}.olean"), str(td / f"{top_mod}.lean")], env)
    assert rt["rc"] == 0, f"{top_mod} failed: {rt['stdout']} {rt['stderr_tail']}"
    top_wall = float(rt["wall_s"])
    total_wall += top_wall
    total_cpu += float(rt["cpu_s"] or 0.0)
    max_rss = max(max_rss, float(rt["rss_mb"] or 0.0))
    total_olean += (td / f"{top_mod}.olean").stat().st_size

    return {
        "n_insns": n_insns,
        "n_bundles": n_bundles,
        "total_bytes": total_bytes,
        "n_shards": len(shard_infos),
        "compile_wall_sum_s": round(total_wall, 4),
        "compile_cpu_sum_s": round(total_cpu, 4),
        "max_shard_wall_s": round(max_shard_wall, 4),
        "top_wall_s": round(top_wall, 4),
        "critical_path_wall_s": round(max_shard_wall + top_wall, 4),
        "max_rss_mb": round(max_rss, 2),
        "olean_sum_bytes": total_olean,
    }, (top_mod, f"{top_mod}.sfi_host_safety_{n_insns}", "ByteX86Sfi")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--canary", action="store_true", help="Run 1 fast end-to-end point per suite")
    args = ap.parse_args()

    ensure_cgroup_wrapper()

    base_flags = ["-DElab.async=false", "-Ddebug.skipKernelTC=false", "-j1", "-M2048"]
    lean_ver = subprocess.check_output([str(LEAN), "--version"], text=True).splitlines()[0]
    gcc_ver = subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0]

    results: dict[str, object] = {
        "toolchains": {"lean": lean_ver, "gcc": gcc_ver, "flags": base_flags},
    }
    replay_jobs: list[tuple[str, str, str]] = []
    entry_by_mod: dict[str, dict[str, object]] = {}

    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)
        env = dict(os.environ)
        env["LEAN_PATH"] = str(td)

        # Copy ByteX86Base.lean and ByteX86Sfi.lean into td and compile both cleanly
        for fn in ("ByteX86Base.lean", "ByteX86Sfi.lean"):
            shutil.copy2(HERE / fn, td / fn)

        print("=== Compiling Foundation Modules (ByteX86Base & ByteX86Sfi) ===", flush=True)
        r_base = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / "ByteX86Base.olean"), str(td / "ByteX86Base.lean")], env)
        assert r_base["rc"] == 0, f"ByteX86Base failed: {r_base['stdout']} {r_base['stderr_tail']}"
        r_sfi = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / "ByteX86Sfi.olean"), str(td / "ByteX86Sfi.lean")], env)
        assert r_sfi["rc"] == 0, f"ByteX86Sfi failed: {r_sfi['stdout']} {r_sfi['stderr_tail']}"

        results["foundation"] = {
            "ByteX86Base": {
                "wall_s": r_base["wall_s"], "cpu_s": r_base["cpu_s"],
                "rss_mb": r_base["rss_mb"], "olean_bytes": (td / "ByteX86Base.olean").stat().st_size,
            },
            "ByteX86Sfi": {
                "wall_s": r_sfi["wall_s"], "cpu_s": r_sfi["cpu_s"],
                "rss_mb": r_sfi["rss_mb"], "olean_bytes": (td / "ByteX86Sfi.olean").stat().st_size,
            },
        }
        replay_jobs.append(("ByteX86Base", "ByteX86.checkByteLeaf_sound", "Init"))
        replay_jobs.append(("ByteX86Sfi", "ByteX86.checkSfiObject_preserves_rust_host_safety", "ByteX86Base"))
        entry_by_mod["ByteX86Base"] = results["foundation"]["ByteX86Base"]
        entry_by_mod["ByteX86Sfi"] = results["foundation"]["ByteX86Sfi"]

        # Suite 1: Real `gcc 15.2.0 -O2` `.o` Byte-Level Functional Proofs
        print("=== Suite 1: Real GCC 15.2.0 -O2 .o Functional Proofs ===", flush=True)
        gcc_src, gcc_meta = build_gcc_real_object_lean(td, env)
        (td / "GccRealObjectProofs.lean").write_text(gcc_src, encoding="utf-8")
        r_gcc = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / "GccRealObjectProofs.olean"), str(td / "GccRealObjectProofs.lean")], env)
        assert r_gcc["rc"] == 0, f"GccRealObjectProofs failed:\n{r_gcc['stdout']}\n{r_gcc['stderr_tail']}"
        s1_row = {
            **gcc_meta,
            "wall_s": r_gcc["wall_s"],
            "cpu_s": r_gcc["cpu_s"],
            "rss_mb": r_gcc["rss_mb"],
            "olean_bytes": (td / "GccRealObjectProofs.olean").stat().st_size,
        }
        results["suite1_gcc_real_objects"] = s1_row
        replay_jobs.append(("GccRealObjectProofs", "GccRealObjectProofs.gcc_aligned_frame_mix_full_verified", "ByteX86Base"))
        entry_by_mod["GccRealObjectProofs"] = s1_row
        print(f"  GccRealObjectProofs wall={r_gcc['wall_s']}s rss={r_gcc['rss_mb']}MB", flush=True)

        # Suite 2: Demonic RFLAGS Cliff vs. Backward DeadFlagCollapse
        print("=== Suite 2: Demonic RFLAGS Cliff vs. DeadFlagCollapse ===", flush=True)
        k_list = [1, 2] if args.canary else [1, 2, 3, 4]
        demonic_rows = []
        for k in k_list:
            m = f"DemonicSplit_{k}"
            (td / f"{m}.lean").write_text(gen_demonic_case_split_lean(m, k), encoding="utf-8")
            rk = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{m}.olean"), str(td / f"{m}.lean")], env, timeout=90)
            row = {
                "k_imul_insns": k,
                "subgoals_4_pow_k": 4 ** k,
                "rc": rk["rc"],
                "timed_out": rk["timed_out"],
                "wall_s": rk["wall_s"],
                "cpu_s": rk["cpu_s"],
                "rss_mb": rk["rss_mb"],
                "olean_bytes": (td / f"{m}.olean").stat().st_size if rk["rc"] == 0 else None,
            }
            if rk["rc"] == 0:
                replay_jobs.append((m, f"{m}.naive_demonic_split_{k}", "ByteX86Base"))
                entry_by_mod[m] = row
            else:
                row["error_excerpt"] = (rk["stdout"] or rk["stderr_tail"])[:240]
            demonic_rows.append(row)
            print(f"  DemonicSplit K={k} (4^K={4**k}) rc={rk['rc']} wall={rk['wall_s']}s", flush=True)

        whnf_list = [1, 8] if args.canary else [1, 2, 4, 8, 16]
        whnf_rows = []
        for l_ins in whnf_list:
            m = f"UncollapsedWhnf_{l_ins}"
            (td / f"{m}.lean").write_text(gen_uncollapsed_whnf_lean(m, l_ins), encoding="utf-8")
            rw = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{m}.olean"), str(td / f"{m}.lean")], env, timeout=60)
            row = {
                "n_insns": l_ins,
                "byte_len": len(gen_64insn_leaf_bytes(l_ins)),
                "rc": rw["rc"],
                "timed_out": rw["timed_out"],
                "wall_s": rw["wall_s"],
                "cpu_s": rw["cpu_s"],
                "rss_mb": rw["rss_mb"],
                "olean_bytes": (td / f"{m}.olean").stat().st_size if rw["rc"] == 0 else None,
            }
            if rw["rc"] != 0:
                row["error_excerpt"] = (rw["stdout"] or rw["stderr_tail"]).splitlines()[0][:200]
            whnf_rows.append(row)
            print(f"  UncollapsedWhnf L={l_ins} rc={rw['rc']} wall={rw['wall_s']}s", flush=True)

        col_mod = "CollapsedLeaf64"
        col_w = precompute_collapsed_ops_batch(td, env, {"c64": gen_64insn_leaf_bytes(64)})["c64"]
        (td / f"{col_mod}.lean").write_text(gen_collapsed_leaf_lean(col_mod, 64, col_w), encoding="utf-8")
        rc64 = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{col_mod}.olean"), str(td / f"{col_mod}.lean")], env)
        assert rc64["rc"] == 0, f"CollapsedLeaf64 failed: {rc64['stdout']}"
        col_row = {
            "n_insns": 64,
            "byte_len": len(gen_64insn_leaf_bytes(64)),
            "rc": 0,
            "wall_s": rc64["wall_s"],
            "cpu_s": rc64["cpu_s"],
            "rss_mb": rc64["rss_mb"],
            "olean_bytes": (td / f"{col_mod}.olean").stat().st_size,
        }
        replay_jobs.append((col_mod, f"{col_mod}.collapsed_leaf_64_verified", "ByteX86Base"))
        entry_by_mod[col_mod] = col_row
        results["suite2_flag_collapse"] = {
            "demonic_4_pow_k_splits": demonic_rows,
            "uncollapsed_whnf_symbolic": whnf_rows,
            "collapsed_leaf_64": col_row,
        }
        print(f"  CollapsedLeaf64 (276B) wall={rc64['wall_s']}s", flush=True)

        # Suite 3: Naive `O(S * P)` ByteMem Aliasing vs. `PrivateStackSep`
        print("=== Suite 3: Naive ByteMem Aliasing vs. PrivateStackSep ===", flush=True)
        sp_pairs = [(16, 4)] if args.canary else [(16, 4), (16, 16), (32, 16), (32, 32), (64, 16), (64, 32)]
        s3_rows = []
        for n_s, n_p in sp_pairs:
            mn = f"NaiveAlias_{n_s}_{n_p}"
            mp = f"PrivStackSep_{n_s}_{n_p}"
            spill_bs_tmp: list[int] = []
            for s_i in range(n_s):
                d_i = (s_i % 8) * 8
                spill_bs_tmp.extend([0x48, 0x89, 0x04, 0x24] if d_i == 0 else [0x48, 0x89, 0x44, 0x24, d_i])
            sp_w = precompute_collapsed_ops_batch(td, env, {"sp": spill_bs_tmp})["sp"]
            (td / f"{mn}.lean").write_text(gen_naive_aliasing_lean(mn, n_s, n_p), encoding="utf-8")
            (td / f"{mp}.lean").write_text(gen_private_stack_sep_lean(mp, n_s, n_p, sp_w), encoding="utf-8")
            rn = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{mn}.olean"), str(td / f"{mn}.lean")], env, timeout=90)
            rp = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{mp}.olean"), str(td / f"{mp}.lean")], env, timeout=90)
            assert rp["rc"] == 0, f"{mp} failed: {rp['stdout']} {rp['stderr_tail']}"
            naive_sub = {
                "rc": rn["rc"],
                "wall_s": rn["wall_s"],
                "cpu_s": rn["cpu_s"],
                "rss_mb": rn["rss_mb"],
                "olean_bytes": (td / f"{mn}.olean").stat().st_size if rn["rc"] == 0 else None,
            }
            if rn["rc"] == 0:
                replay_jobs.append((mn, f"{mn}.naive_flat_aliasing_{n_s}_{n_p}", "ByteX86Base"))
                entry_by_mod[mn] = naive_sub
            else:
                naive_sub["error_excerpt"] = (rn["stdout"] or rn["stderr_tail"]).splitlines()[0][:200]
            priv_sub = {
                "rc": rp["rc"],
                "wall_s": rp["wall_s"],
                "cpu_s": rp["cpu_s"],
                "rss_mb": rp["rss_mb"],
                "olean_bytes": (td / f"{mp}.olean").stat().st_size,
            }
            replay_jobs.append((mp, f"{mp}.private_stack_sep_{n_s}_{n_p}", "ByteX86Base"))
            entry_by_mod[mp] = priv_sub
            s3_rows.append({
                "spills": n_s,
                "caller_ptrs": n_p,
                "pairwise_obligations": n_s * n_p,
                "naive_flat_aliasing": naive_sub,
                "private_stack_sep": priv_sub,
            })
            print(f"  (S={n_s}, P={n_p}, S*P={n_s*n_p}): naive={rn['wall_s']}s (rc={rn['rc']}) vs PrivStackSep={rp['wall_s']}s", flush=True)
        results["suite3_stack_separation"] = s3_rows

        # Suite 4: Sharded Byte-Decoded `ByteShardedTreeLift` Scaling
        print("=== Suite 4: Sharded Variable-Length ByteShardedTreeLift Scaling ===", flush=True)
        n_lift_list = [64, 512] if args.canary else [64, 256, 512, 1024, 2560, 5120]
        s4_rows = []
        for n_ins in n_lift_list:
            row, rjob = run_sharded_byte_lift_point(td, env, base_flags, n_ins)
            replay_jobs.append(rjob)
            entry_by_mod[rjob[0]] = row
            s4_rows.append(row)
            print(f"  ByteShardedTreeLift N={n_ins:5d} ({row['total_bytes']:5d}B): sum_wall={row['compile_wall_sum_s']}s top_wall={row['top_wall_s']}s", flush=True)
        results["suite4_byte_sharded_scaling"] = s4_rows

        # Suite 5: Decidable Loop-Invariant-Free `checkSfiObject` Scaling
        print("=== Suite 5: Decidable Loop-Invariant-Free Binary SFI Scaling ===", flush=True)
        mono_sfi_list = [256] if args.canary else [64, 128, 256, 512]
        mono_sfi_rows = []
        for n_ins in mono_sfi_list:
            mm = f"SfiMono_{n_ins}"
            (td / f"{mm}.lean").write_text(gen_monolithic_sfi_lean(mm, n_ins), encoding="utf-8")
            rm = run_timed_lean(base_flags + ["-R", str(td), "-o", str(td / f"{mm}.olean"), str(td / f"{mm}.lean")], env, timeout=60)
            mrow = {
                "n_insns": n_ins,
                "total_bytes": (n_ins // 8) * 32,
                "rc": rm["rc"],
                "wall_s": rm["wall_s"],
                "cpu_s": rm["cpu_s"],
                "rss_mb": rm["rss_mb"],
                "olean_bytes": (td / f"{mm}.olean").stat().st_size if rm["rc"] == 0 else None,
            }
            if rm["rc"] == 0:
                replay_jobs.append((mm, f"{mm}.sfi_mono_{n_ins}_ok", "ByteX86Sfi"))
                entry_by_mod[mm] = mrow
            else:
                mrow["error_excerpt"] = (rm["stdout"] or rm["stderr_tail"]).splitlines()[0][:200]
            mono_sfi_rows.append(mrow)
            print(f"  SfiMono N={n_ins:5d} rc={rm['rc']} wall={rm['wall_s']}s", flush=True)

        sharded_sfi_list = [256, 1024] if args.canary else [256, 1024, 2560, 5120, 10240]
        sharded_sfi_rows = []
        for n_ins in sharded_sfi_list:
            row, rjob = run_sharded_sfi_point(td, env, base_flags, n_ins)
            replay_jobs.append(rjob)
            entry_by_mod[rjob[0]] = row
            sharded_sfi_rows.append(row)
            print(f"  SfiSharded N={n_ins:5d} ({row['total_bytes']:5d}B): sum_wall={row['compile_wall_sum_s']}s top_wall={row['top_wall_s']}s", flush=True)
        results["suite5_sfi_containment_scaling"] = {
            "monolithic_rfl": mono_sfi_rows,
            "sharded_subtree_node": sharded_sfi_rows,
        }

        # Batch Standalone `(level := .private)` Kernel Replay Audit
        print(f"=== Standalone Private-Level Kernel Replay ({len(replay_jobs)} modules) ===", flush=True)
        (td / "ReplayAudit.lean").write_text(REPLAY_AUDIT_LEAN, encoding="utf-8")
        jobs_path = td / "replay_jobs.txt"
        jobs_path.write_text("\n".join(f"{m} {t} {b}" for m, t, b in replay_jobs) + "\n", encoding="utf-8")
        rr = run_timed_lean(["--run", str(td / "ReplayAudit.lean"), str(jobs_path)], env, timeout=720)
        assert rr["rc"] == 0, f"ReplayAudit crashed:\n{rr['stdout']}\n{rr['stderr_tail']}"
        parsed = parse_replay_output(rr["stdout"])
        for m, _, _ in replay_jobs:
            assert m in parsed and parsed[m]["replay_rc"] == 0, f"Replay failed for {m}: {parsed.get(m)}"
            entry_by_mod[m].update(parsed[m])
            print(f"  REPLAY_OK {m:28s} replay={parsed[m]['replay_ms']:4d}ms consts={parsed[m]['replayed_consts']:4d} ax={parsed[m]['axioms']}", flush=True)

    if not args.canary:
        out_path = HERE / "byte_x86_scaling_and_sfi_results.json"
        out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
        digest = hashlib.sha256(out_path.read_bytes()).hexdigest()
        print(f"Wrote {out_path.name} (sha256={digest[:16]}...)", flush=True)
    else:
        print("CANARY_ALL_PASSED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
