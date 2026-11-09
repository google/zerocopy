#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import os
from pathlib import Path
import subprocess
import time

LEAN_ROOT = "/home/user/.elan/toolchains/leanprover--lean4---v4.34.1"
LEAN_BIN = f"{LEAN_ROOT}/bin/lean"
WORKDIR = str(Path(__file__).resolve().parent)
LEAN_ENV = {
    **os.environ,
    "LEAN_PATH": WORKDIR,
    "LEAN_SYSROOT": LEAN_ROOT,
    "PATH": f"{LEAN_ROOT}/bin:" + os.environ.get("PATH", ""),
}
MASK64 = (1 << 64) - 1
MOD64 = 1 << 64

HEADER = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""


def step_py(instr, s):
  pc, r0, r1, r2, r3, flag = s
  op = instr[0]
  if op == "addCheckedImm":
    _, dst, src, imm = instr
    val = {0: r0, 1: r1, 2: r2, 3: r3}[src]
    ov = (val + imm) >= MOD64
    res = (val + imm) & MASK64
    regs = [r0, r1, r2, r3]
    regs[dst] = res
    return (pc + 1, regs[0], regs[1], regs[2], regs[3], ov)
  elif op == "assertNotFlag":
    assert not flag
    return (pc + 1, r0, r1, r2, r3, flag)
  elif op == "xor":
    _, dst, s1, s2 = instr
    regs = [r0, r1, r2, r3]
    regs[dst] = regs[s1] ^ regs[s2]
    return (pc + 1, regs[0], regs[1], regs[2], regs[3], flag)
  elif op == "shl":
    _, dst, src, amt = instr
    regs = [r0, r1, r2, r3]
    regs[dst] = (regs[src] << amt) & MASK64
    return (pc + 1, regs[0], regs[1], regs[2], regs[3], flag)
  elif op == "add":
    _, dst, s1, s2 = instr
    regs = [r0, r1, r2, r3]
    regs[dst] = (regs[s1] + regs[s2]) & MASK64
    return (pc + 1, regs[0], regs[1], regs[2], regs[3], flag)
  else:
    raise ValueError(f"Unknown op: {op}")


def reg_lean(r):
  return f".r{r}"


def instr_lean(instr):
  op = instr[0]
  if op == "addCheckedImm":
    _, dst, src, imm = instr
    return f".addCheckedImm {reg_lean(dst)} {reg_lean(src)} {imm}#64"
  elif op == "assertNotFlag":
    return ".assertNotFlag"
  elif op == "xor":
    _, dst, s1, s2 = instr
    return f".xor {reg_lean(dst)} {reg_lean(s1)} {reg_lean(s2)}"
  elif op == "shl":
    _, dst, src, amt = instr
    return f".shl {reg_lean(dst)} {reg_lean(src)} {amt}"
  elif op == "add":
    _, dst, s1, s2 = instr
    return f".add {reg_lean(dst)} {reg_lean(s1)} {reg_lean(s2)}"
  else:
    raise ValueError(op)


def state_lean(s):
  pc, r0, r1, r2, r3, flag = s
  fl_str = "true" if flag else "false"
  return f"⟨{pc}, {r0}#64, {r1}#64, {r2}#64, {r3}#64, {fl_str}⟩"


def build_program(n):
  assert n % 5 == 0
  num_idioms = n // 5
  prog = []
  for j in range(num_idioms):
    imm = (j % 7) + 1
    # Keep values bounded inside 32 bits periodically or let r0 wrap?
    # Wait: addCheckedImm checks that r0 + imm < 2^64.
    # Since shl shifts by 3 and adds to r0, after ~20 blocks r0 could exceed 2^64
    # UNLESS we mask or shift right or keep r2 small!
    # Wait: in our 5-instruction idiom in BenchmarkProofStrategies.lean:
    #   .addCheckedImm .r0 .r0 imm
    #   .assertNotFlag
    #   .xor .r1 .r0 .r2
    #   .shl .r2 .r1 3
    #   .add .r0 .r0 .r2
    # Let's check when r0 + imm could overflow 2^64 if r0 grows by ~8x each idiom!
    # After 21 idioms, 8^21 = 2^63, so at idiom 22 r0 could wrap 2^64 and if it lands
    # at 2^64 - 1, r0 + imm could overflow!
    # Let's check in Python whether r0 + imm EVER overflows for j in 0..100!
    prog.extend([
        ("addCheckedImm", 0, 0, imm),
        ("assertNotFlag",),
        ("xor", 1, 0, 2),
        ("shl", 2, 1, 3),
        ("add", 0, 0, 2),
    ])
  s0 = (0, 7, 0, 3, 0, False)
  states = [s0]
  curr = s0
  for instr in prog:
    curr = step_py(instr, curr)
    states.append(curr)
  return prog, states


def compile_lean(lean_file, olean_file):
  t0 = time.perf_counter()
  res = subprocess.run(
      [
          LEAN_BIN,
          "-DElab.async=false",
          "-Ddebug.skipKernelTC=false",
          "-o",
          olean_file,
          lean_file,
      ],
      cwd=WORKDIR,
      env=LEAN_ENV,
      capture_output=True,
      text=True,
  )
  t1 = time.perf_counter()
  if res.returncode != 0:
    raise RuntimeError(f"Failed compiling {lean_file}:\n{res.stderr}\n{res.stdout}")
  return (t1 - t0) * 1000.0


def measure_kernel_batch(base_mod, target_mods):
  res = subprocess.run(
      [LEAN_BIN, "--run", "MeasureKernel.lean", base_mod] + target_mods,
      cwd=WORKDIR,
      env=LEAN_ENV,
      capture_output=True,
      text=True,
  )
  if res.returncode != 0:
    raise RuntimeError(
        f"Failed MeasureKernel {base_mod} {target_mods}:\n{res.stderr}\n{res.stdout}"
    )
  out_map = {}
  for line in res.stdout.strip().splitlines():
    kv = {}
    for part in line.split():
      k, v = part.split("=")
      kv[k] = v
    out_map[kv["MOD"]] = {
        "replay_us": int(kv["REPLAY_US"]),
        "replay_ms": float(kv["REPLAY_MS"]),
        "decls": int(kv["DECLS"]),
        "dag_nodes": int(kv["DAG_NODES"]),
        "tree_nodes": int(kv["TREE_NODES"]),
    }
  return out_map


def generate_and_run():
  ns = [10, 25, 50, 100, 250, 500]
  results = []

  for n in ns:
    prog, states = build_program(n)
    s0 = states[0]
    v_final = states[-1][1]  # s_N.r0

    base_mod = f"SuiteA_Base_{n}"
    base_file = os.path.join(WORKDIR, f"{base_mod}.lean")
    base_olean = os.path.join(WORKDIR, f"{base_mod}.olean")

    instrs_str = ",\n  ".join(instr_lean(i) for i in prog)
    # Also define blocks of size 5 for Arch 5 (or up to 10 instructions per block)
    blk_size = 5
    num_blks = n // blk_size
    blk_defs = []
    for b in range(num_blks):
      b_instrs = ", ".join(instr_lean(i) for i in prog[b * blk_size : (b + 1) * blk_size])
      blk_defs.append(f"def blk_{b} : List Trusted.Instr := [{b_instrs}]")
    blk_defs_str = "\n".join(blk_defs)

    with open(base_file, "w") as f:
      f.write(
          HEADER
          + f"""import BenchmarkProofStrategies

def prog_{n} : List Trusted.Instr := [
  {instrs_str}
]

def s0_{n} : Trusted.State := {state_lean(s0)}
def v_{n} : BitVec 64 := {v_final}#64

{blk_defs_str}
"""
      )
    compile_lean(base_file, base_olean)

    # 1. Arch 1a: Flat Small-Step Reach.step
    arch1a_mod = f"SuiteA_Arch1a_{n}"
    arch1a_file = os.path.join(WORKDIR, f"{arch1a_mod}.lean")
    arch1a_olean = os.path.join(WORKDIR, f"{arch1a_mod}.olean")
    term = f"Trusted.Reach.done {state_lean(states[n])} v_{n} rfl"
    for k in range(n - 1, -1, -1):
      s_k = state_lean(states[k]) if k > 0 else f"s0_{n}"
      s_k1 = state_lean(states[k + 1])
      term = f"Trusted.Reach.step {s_k} {s_k1} v_{n} rfl (\n  {term})"
    with open(arch1a_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  Theory.Reach_imp_VerifiedFrom (
    {term}
  )
"""
      )

    # 2. Arch 1b: Anneal PR #81 nested-lambda continuation safeAndEnsures_of_step
    arch1b_mod = f"SuiteA_Arch1b_{n}"
    arch1b_file = os.path.join(WORKDIR, f"{arch1b_mod}.lean")
    arch1b_olean = os.path.join(WORKDIR, f"{arch1b_mod}.olean")
    term1b = f"Theory.safeAndEnsures_of_ret rfl hr_{n} rfl"
    for k in range(n - 1, -1, -1):
      s_k1 = state_lean(states[k + 1])
      term1b = (
          f"Theory.safeAndEnsures_of_step (s' := {s_k1}) rfl hr_{k} (fun _"
          f" hr_{k+1} =>\n  {term1b})"
      )
    with open(arch1b_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  fun _ _ hr_0 =>
    {term1b}
"""
      )

    # 3. Arch 2: Pre-Proved Functional / let-Sharing Instruction Lemmas (SuffixReach)
    arch2_mod = f"SuiteA_Arch2_{n}"
    arch2_file = os.path.join(WORKDIR, f"{arch2_mod}.lean")
    arch2_olean = os.path.join(WORKDIR, f"{arch2_mod}.olean")
    lets2 = [f"let st_0 : Trusted.State := s0_{n}"]
    for k in range(1, n + 1):
      lets2.append(f"let st_{k} : Trusted.State := {state_lean(states[k])}")
    lets2_str = "\n    ".join(lets2)
    term2 = f"Theory.SuffixReach.nil st_{n}"
    for k in range(n - 1, -1, -1):
      step_app = f"Theory.step_instr _ _ st_{k} st_{k+1} v_{n} rfl"
      term2 = f"{step_app} (\n      {term2})"
    with open(arch2_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  Theory.Reach_imp_VerifiedFrom (
    {lets2_str}
    Theory.SuffixReach_imp_Reach prog_{n} st_0 v_{n} rfl (
      {term2}
    )
  )
"""
      )

    # 4. Arch 3: Pre-Proved Fused 5-Instruction Idiom Schema (step_idiom5)
    arch3_mod = f"SuiteA_Arch3_{n}"
    arch3_file = os.path.join(WORKDIR, f"{arch3_mod}.lean")
    arch3_olean = os.path.join(WORKDIR, f"{arch3_mod}.olean")
    lets3 = [f"let st_0 : Trusted.State := s0_{n}"]
    for b in range(1, num_blks + 1):
      lets3.append(
          f"let st_{b * 5} : Trusted.State := {state_lean(states[b * 5])}"
      )
    lets3_str = "\n    ".join(lets3)
    term3 = f"Theory.SuffixReach.nil st_{n}"
    for b in range(num_blks - 1, -1, -1):
      imm = (b % 7) + 1
      k0 = b * 5
      k1 = (b + 1) * 5
      term3 = (
          f"Theory.step_idiom5 {imm}#64 _ st_{k0} st_{k1} v_{n} rfl (\n     "
          f" {term3})"
      )
    with open(arch3_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  Theory.Reach_imp_VerifiedFrom (
    {lets3_str}
    Theory.SuffixReach_imp_Reach prog_{n} st_0 v_{n} rfl (
      {term3}
    )
  )
"""
      )

    # 5. Arch 4: Monolithic Full-Function Computational Reflection via rfl
    arch4_mod = f"SuiteA_Arch4_{n}"
    arch4_file = os.path.join(WORKDIR, f"{arch4_mod}.lean")
    arch4_olean = os.path.join(WORKDIR, f"{arch4_mod}.olean")
    with open(arch4_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  Theory.Reach_imp_VerifiedFrom
    (Theory.evalProg_sound prog_{n} s0_{n} v_{n} rfl rfl)
"""
      )

    # 6. Arch 5: Compositional Cut-Point / Block-Modular Reflection (evalBlock_step)
    arch5_mod = f"SuiteA_Arch5_{n}"
    arch5_file = os.path.join(WORKDIR, f"{arch5_mod}.lean")
    arch5_olean = os.path.join(WORKDIR, f"{arch5_mod}.olean")
    # Use 5-instruction basic blocks blk_0 .. blk_{num_blks-1}
    term5 = f"Theory.SuffixReach.nil st_{n}"
    for b in range(num_blks - 1, -1, -1):
      k0 = b * 5
      k1 = (b + 1) * 5
      term5 = (
          f"Theory.evalBlock_step blk_{b} _ st_{k0} st_{k1} v_{n} rfl (\n     "
          f" {term5})"
      )
    with open(arch5_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  Theory.Reach_imp_VerifiedFrom (
    {lets3_str}
    Theory.SuffixReach_imp_Reach prog_{n} st_0 v_{n} rfl (
      {term5}
    )
  )
"""
      )

    # 7. Arch 6: cv_trans Fast Nat-Encoded Kernel Domain Reflection (evalCvProg_sound)
    arch6_mod = f"SuiteA_Arch6_{n}"
    arch6_file = os.path.join(WORKDIR, f"{arch6_mod}.lean")
    arch6_olean = os.path.join(WORKDIR, f"{arch6_mod}.olean")
    with open(arch6_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_prog : Trusted.VerifiedFrom prog_{n} s0_{n} v_{n} :=
  Theory.Reach_imp_VerifiedFrom
    (Theory.evalCvProg_sound prog_{n} s0_{n} v_{n} rfl rfl)
"""
      )

    archs = [
        ("Arch 1a (Flat Reach.step)", arch1a_mod, arch1a_file, arch1a_olean),
        ("Arch 1b (Anneal Cont-Lambda)", arch1b_mod, arch1b_file, arch1b_olean),
        ("Arch 2 (Suffix + let-Share)", arch2_mod, arch2_file, arch2_olean),
        ("Arch 3 (Fused 5-Instr Idiom)", arch3_mod, arch3_file, arch3_olean),
        ("Arch 4 (Monolithic BitVec rfl)", arch4_mod, arch4_file, arch4_olean),
        ("Arch 5 (Cut-Point Block rfl)", arch5_mod, arch5_file, arch5_olean),
        ("Arch 6 (cv_trans GMP Nat rfl)", arch6_mod, arch6_file, arch6_olean),
    ]

    elab_times = {}
    for arch_label, mod, lfile, ofile in archs:
      elab_times[mod] = compile_lean(lfile, ofile)

    km_map = measure_kernel_batch(base_mod, [mod for _, mod, _, _ in archs])

    for arch_label, mod, lfile, ofile in archs:
      elab_ms = elab_times[mod]
      olean_bytes = os.path.getsize(ofile)
      km = km_map[mod]
      row = {
          "n": n,
          "arch": arch_label,
          "elab_ms": round(elab_ms, 2),
          "replay_ms": km["replay_ms"],
          "replay_us": km["replay_us"],
          "olean_bytes": olean_bytes,
          "decls": km["decls"],
          "dag_nodes": km["dag_nodes"],
          "tree_nodes": km["tree_nodes"],
      }
      results.append(row)
      print(
          f"N={n:3d} | {arch_label:30s} | elab={elab_ms:7.1f}ms |"
          f" replay={km['replay_ms']:7.3f}ms ({km['replay_us']:6d}us) |"
          f" olean={olean_bytes:7d}B | DAG={km['dag_nodes']:6d} |"
          f" TREE={km['tree_nodes']:8d}",
          flush=True,
      )

  out_json = os.path.join(WORKDIR, "suite_a_results.json")
  with open(out_json, "w") as f:
    json.dump(results, f, indent=2)
  print(f"Saved Suite A results to {out_json}")


if __name__ == "__main__":
  generate_and_run()
