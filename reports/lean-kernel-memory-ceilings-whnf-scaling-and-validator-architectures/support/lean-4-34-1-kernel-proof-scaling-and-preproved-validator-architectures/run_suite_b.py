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

HEADER = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""


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


def run_suite_b1_diamonds():
  """Compare Arch 4 (2^D path split reflection) vs Arch 5 (O(D) diamond_converge_step) across D in {2, 4, 6, 8, 10}."""
  ds = [2, 4, 6, 8, 10]
  results = []

  for d in ds:
    base_mod = f"SuiteB_DiamondBase_{d}"
    base_file = os.path.join(WORKDIR, f"{base_mod}.lean")
    base_olean = os.path.join(WORKDIR, f"{base_mod}.olean")

    # Each diamond k in 0..d-1 has two 5-instruction arms blkT_k and blkF_k
    # Both arms advance pc by 5, add 10#64 to r0, and zero r1, r2.
    arm_defs = []
    for k in range(d):
      a1 = (k % 4) + 1
      a2 = 10 - a1
      b1 = (k % 3) + 2
      b2 = 10 - b1
      arm_defs.append(
          f"def blkT_{k} : List Trusted.Instr := [.addImm .r0 .r0 {a1}#64,"
          f" .addImm .r0 .r0 {a2}#64, .xor .r1 .r1 .r1, .shl .r2 .r1 3, .add"
          " .r0 .r0 .r2]"
      )
      arm_defs.append(
          f"def blkF_{k} : List Trusted.Instr := [.addImm .r0 .r0 {b1}#64,"
          f" .addImm .r0 .r0 {b2}#64, .sub .r1 .r1 .r1, .shr .r2 .r1 2, .add"
          " .r0 .r0 .r2]"
      )
    arm_defs_str = "\n".join(arm_defs)

    cond_params = " ".join(f"(c_{k} : Bool)" for k in range(d))
    cond_args = " ".join(f"c_{k}" for k in range(d))
    prog_rhs = "[] "
    for k in range(d - 1, -1, -1):
      prog_rhs = f"((if c_{k} then blkT_{k} else blkF_{k}) ++ {prog_rhs})"
    final_r0 = 7 + 10 * d

    with open(base_file, "w") as f:
      f.write(
          HEADER
          + f"""import BenchmarkProofStrategies

{arm_defs_str}

def prog_diamond_{d} {cond_params} : List Trusted.Instr :=
  {prog_rhs}

def s0_d_{d} : Trusted.State := ⟨0, 7#64, 0#64, 0#64, 0#64, false⟩
def v_d_{d} : BitVec 64 := {final_r0}#64
"""
      )
    compile_lean(base_file, base_olean)

    # Arch 5: O(D) Compositional Cut-Point Diamond Convergence
    arch5_mod = f"SuiteB_Diamond_Arch5_{d}"
    arch5_file = os.path.join(WORKDIR, f"{arch5_mod}.lean")
    arch5_olean = os.path.join(WORKDIR, f"{arch5_mod}.olean")
    lets5 = [f"let st_0 : Trusted.State := s0_d_{d}"]
    for k in range(1, d + 1):
      lets5.append(
          f"let st_{k} : Trusted.State := ⟨{5 * k}, {7 + 10 * k}#64, 0#64,"
          " 0#64, 0#64, false⟩"
      )
    lets5_str = "\n    ".join(lets5)
    term5 = f"Theory.SuffixReach.nil st_{d}"
    for k in range(d - 1, -1, -1):
      term5 = (
          f"Theory.diamond_converge_step c_{k} blkT_{k} blkF_{k} _ st_{k}"
          f" st_{k+1} v_d_{d} rfl rfl (\n      {term5})"
      )
    with open(arch5_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_diamond {cond_params} :
    Trusted.VerifiedFrom (prog_diamond_{d} {cond_args}) s0_d_{d} v_d_{d} :=
  Theory.Reach_imp_VerifiedFrom (
    {lets5_str}
    Theory.SuffixReach_imp_Reach (prog_diamond_{d} {cond_args}) st_0 v_d_{d} rfl (
      {term5}
    )
  )
"""
      )

    # Arch 4: 2^D Path-Split Full-Function Reflection
    arch4_mod = f"SuiteB_Diamond_Arch4_{d}"
    arch4_file = os.path.join(WORKDIR, f"{arch4_mod}.lean")
    arch4_olean = os.path.join(WORKDIR, f"{arch4_mod}.olean")

    def build_cases_tree(idx):
      indent = "  " * (idx + 2)
      if idx == d:
        return (
            f"{indent}Theory.evalProg_sound (prog_diamond_{d} {cond_args})"
            f" s0_d_{d} v_d_{d} rfl rfl"
        )
      body_t = build_cases_tree(idx + 1)
      body_f = build_cases_tree(idx + 1)
      return (
          f"{indent}Bool.casesOn (motive := fun b => Trusted.Reach"
          f" (prog_diamond_{d}"
          f" {' '.join(('b' if j == idx else f'c_{j}') for j in range(d))})"
          f" s0_d_{d} v_d_{d}) c_{idx}\n{body_f}\n{body_t}"
      )

    # Even cleaner: use tactic `cases c_0 <;> cases c_1 <;> ... <;> exact Theory.evalProg_sound ... rfl rfl`
    cases_chain = " <;> ".join(f"cases c_{k}" for k in range(d))
    with open(arch4_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 40000000

theorem verified_diamond {cond_params} :
    Trusted.VerifiedFrom (prog_diamond_{d} {cond_args}) s0_d_{d} v_d_{d} := by
  apply Theory.Reach_imp_VerifiedFrom
  {cases_chain} <;> exact Theory.evalProg_sound _ s0_d_{d} v_d_{d} rfl rfl
"""
      )

    t_elab5 = compile_lean(arch5_file, arch5_olean)
    t_elab4 = compile_lean(arch4_file, arch4_olean)
    km_map = measure_kernel_batch(base_mod, [arch4_mod, arch5_mod])

    for label, mod, ofile, elab_ms in [
        ("Arch 4 (Monolithic 2^D Path Split)", arch4_mod, arch4_olean, t_elab4),
        ("Arch 5 (Cut-Point O(D) Diamond Join)", arch5_mod, arch5_olean, t_elab5),
    ]:
      km = km_map[mod]
      olean_bytes = os.path.getsize(ofile)
      row = {
          "suite": "B1_Diamonds",
          "param": d,
          "paths": 1 << d,
          "arch": label,
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
          f"Diamonds D={d:2d} (2^D={1<<d:4d}) | {label:36s} |"
          f" elab={elab_ms:7.1f}ms | replay={km['replay_ms']:7.3f}ms"
          f" ({km['replay_us']:6d}us) | olean={olean_bytes:7d}B |"
          f" DAG={km['dag_nodes']:6d} | TREE={km['tree_nodes']:8d}",
          flush=True,
      )
  return results


def run_suite_b2_calls_and_loops():
  """Compare Arch 4 vs Arch 5 on multi-call programs (K calls to 20-instr callee) and loops."""
  results = []
  base_mod = "SuiteB_CallLoopBase"
  base_file = os.path.join(WORKDIR, f"{base_mod}.lean")
  base_olean = os.path.join(WORKDIR, f"{base_mod}.olean")

  # 20-instruction callee that adds 5#64 twenty times (= 100#64) to r0 and advances pc by 20
  callee_instrs = ",\n  ".join([".addImm .r0 .r0 5#64"] * 20)
  with open(base_file, "w") as f:
    f.write(
        HEADER
        + f"""import BenchmarkProofStrategies

def callee20 : List Trusted.Instr := [
  {callee_instrs}
]

def callee20Spec (s : Trusted.State) : Trusted.State :=
  ⟨s.pc + 20, s.r0 + 100#64, s.r1, s.r2, s.r3, s.flag⟩

theorem callee20_summary (s : Trusted.State) :
    Theory.evalBlock callee20 s = some (callee20Spec s) := by
  cases s with
  | mk pc r0 r1 r2 r3 flag =>
    dsimp [callee20, callee20Spec, Theory.evalBlock, Theory.stepInstrStrict,
      Trusted.stepInstr, Trusted.State.getReg, Trusted.State.setRegNext]
    simp only [BitVec.add_assoc]
    rfl

def loopBody5 : List Trusted.Instr := [
  .addImm .r0 .r0 1#64,
  .addImm .r0 .r0 2#64,
  .addImm .r0 .r0 1#64,
  .addImm .r0 .r0 2#64,
  .addImm .r0 .r0 1#64
]

def loopR0 : Nat → BitVec 64
  | 0 => 0#64
  | i + 1 => loopR0 i + 7#64

def loopInv (i : Nat) : Trusted.State :=
  ⟨5 * i, loopR0 i, 0#64, 0#64, 0#64, false⟩

theorem loopBody5_step (i : Nat) :
    Theory.evalBlock loopBody5 (loopInv i) = some (loopInv (i + 1)) := by
  dsimp [loopBody5, loopInv, loopR0, Theory.evalBlock, Theory.stepInstrStrict,
    Trusted.stepInstr, Trusted.State.getReg, Trusted.State.setRegNext]
  simp only [BitVec.add_assoc]
  rfl
"""
    )
  compile_lean(base_file, base_olean)

  # Multi-call K in {2, 5, 10, 20} (total instructions = 20 * K in {40, 100, 200, 400})
  for k in [2, 5, 10, 20]:
    cbase_mod = f"SuiteB_CallBase_{k}"
    cbase_file = os.path.join(WORKDIR, f"{cbase_mod}.lean")
    cbase_olean = os.path.join(WORKDIR, f"{cbase_mod}.olean")
    prog_rhs = "[]"
    for _ in range(k):
      prog_rhs = f"(callee20 ++ {prog_rhs})"
    with open(cbase_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

def prog_call_{k} : List Trusted.Instr := {prog_rhs}
def s0_call_{k} : Trusted.State := ⟨0, 7#64, 0#64, 0#64, 0#64, false⟩
def v_call_{k} : BitVec 64 := {7 + 100 * k}#64
"""
      )
    compile_lean(cbase_file, cbase_olean)

    arch4_mod = f"SuiteB_Call_Arch4_{k}"
    arch4_file = os.path.join(WORKDIR, f"{arch4_mod}.lean")
    arch4_olean = os.path.join(WORKDIR, f"{arch4_mod}.olean")
    with open(arch4_file, "w") as f:
      f.write(
          HEADER
          + f"""import {cbase_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_call : Trusted.VerifiedFrom prog_call_{k} s0_call_{k} v_call_{k} :=
  Theory.Reach_imp_VerifiedFrom
    (Theory.evalProg_sound prog_call_{k} s0_call_{k} v_call_{k} rfl rfl)
"""
      )

    arch5_mod = f"SuiteB_Call_Arch5_{k}"
    arch5_file = os.path.join(WORKDIR, f"{arch5_mod}.lean")
    arch5_olean = os.path.join(WORKDIR, f"{arch5_mod}.olean")
    term5 = "Theory.SuffixReach.nil _"
    for _ in range(k):
      term5 = f"Theory.call_summary_sound callee20_summary _ _ v_call_{k} (\n      {term5})"
    with open(arch5_file, "w") as f:
      f.write(
          HEADER
          + f"""import {cbase_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_call : Trusted.VerifiedFrom prog_call_{k} s0_call_{k} v_call_{k} :=
  Theory.Reach_imp_VerifiedFrom (
    Theory.SuffixReach_imp_Reach prog_call_{k} s0_call_{k} v_call_{k} rfl (
      {term5}
    )
  )
"""
      )

    t4 = compile_lean(arch4_file, arch4_olean)
    t5 = compile_lean(arch5_file, arch5_olean)
    km_map = measure_kernel_batch(cbase_mod, [arch4_mod, arch5_mod])
    for label, mod, ofile, elab_ms in [
        ("Arch 4 (Monolithic Inlined Call rfl)", arch4_mod, arch4_olean, t4),
        ("Arch 5 (Pre-Proved Call Summary)", arch5_mod, arch5_olean, t5),
    ]:
      km = km_map[mod]
      olean_bytes = os.path.getsize(ofile)
      row = {
          "suite": "B2_MultiCall",
          "param": k,
          "instrs": 20 * k,
          "arch": label,
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
          f"Calls K={k:2d} ({20*k:3d} instrs) | {label:36s} |"
          f" elab={elab_ms:7.1f}ms | replay={km['replay_ms']:7.3f}ms"
          f" ({km['replay_us']:6d}us) | olean={olean_bytes:7d}B |"
          f" DAG={km['dag_nodes']:6d} | TREE={km['tree_nodes']:8d}",
          flush=True,
      )

  # Symbolic & bounded loop M in {10, 50, 100} + Symbolic M : Nat
  for m in [10, 50, 100]:
    lbase_mod = f"SuiteB_LoopBase_{m}"
    lbase_file = os.path.join(WORKDIR, f"{lbase_mod}.lean")
    lbase_olean = os.path.join(WORKDIR, f"{lbase_mod}.olean")
    with open(lbase_file, "w") as f:
      f.write(
          HEADER
          + f"""import {base_mod}

def prog_loop_{m} : List Trusted.Instr := Theory.loopCode {m} loopBody5 ++ []
def s0_loop_{m} : Trusted.State := loopInv 0
def v_loop_{m} : BitVec 64 := (loopInv {m}).r0
"""
      )
    compile_lean(lbase_file, lbase_olean)

    arch4_mod = f"SuiteB_Loop_Arch4_{m}"
    arch4_file = os.path.join(WORKDIR, f"{arch4_mod}.lean")
    arch4_olean = os.path.join(WORKDIR, f"{arch4_mod}.olean")
    with open(arch4_file, "w") as f:
      f.write(
          HEADER
          + f"""import {lbase_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_loop : Trusted.VerifiedFrom prog_loop_{m} s0_loop_{m} v_loop_{m} :=
  Theory.Reach_imp_VerifiedFrom
    (Theory.evalProg_sound prog_loop_{m} s0_loop_{m} v_loop_{m} rfl rfl)
"""
      )

    arch5_mod = f"SuiteB_Loop_Arch5_{m}"
    arch5_file = os.path.join(WORKDIR, f"{arch5_mod}.lean")
    arch5_olean = os.path.join(WORKDIR, f"{arch5_mod}.olean")
    with open(arch5_file, "w") as f:
      f.write(
          HEADER
          + f"""import {lbase_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_loop : Trusted.VerifiedFrom prog_loop_{m} s0_loop_{m} v_loop_{m} :=
  Theory.Reach_imp_VerifiedFrom (
    Theory.SuffixReach_imp_Reach prog_loop_{m} s0_loop_{m} v_loop_{m} rfl
      (Theory.loop_summary_sound loopInv loopBody5_step {m} [] v_loop_{m}
        (Theory.SuffixReach.nil (loopInv {m})))
  )
"""
      )

    t4 = compile_lean(arch4_file, arch4_olean)
    t5 = compile_lean(arch5_file, arch5_olean)
    km_map = measure_kernel_batch(lbase_mod, [arch4_mod, arch5_mod])
    for label, mod, ofile, elab_ms in [
        ("Arch 4 (Monolithic Unrolled Loop rfl)", arch4_mod, arch4_olean, t4),
        ("Arch 5 (Pre-Proved Loop Summary)", arch5_mod, arch5_olean, t5),
    ]:
      km = km_map[mod]
      olean_bytes = os.path.getsize(ofile)
      row = {
          "suite": "B3_Loops",
          "param": m,
          "instrs": 5 * m,
          "arch": label,
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
          f"Loop M={m:3d} ({5*m:3d} instrs) | {label:36s} |"
          f" elab={elab_ms:7.1f}ms | replay={km['replay_ms']:7.3f}ms"
          f" ({km['replay_us']:6d}us) | olean={olean_bytes:7d}B |"
          f" DAG={km['dag_nodes']:6d} | TREE={km['tree_nodes']:8d}",
          flush=True,
      )

  # Symbolic trip count M : Nat (Arch 5 ONLY; Arch 4 cannot verify symbolic loops!)
  sym_mod = "SuiteB_Loop_Arch5_Symbolic"
  sym_file = os.path.join(WORKDIR, f"{sym_mod}.lean")
  sym_olean = os.path.join(WORKDIR, f"{sym_mod}.olean")
  with open(sym_file, "w") as f:
    f.write(
        HEADER
        + f"""import {base_mod}

theorem verified_symbolic_loop (m : Nat) :
    Trusted.VerifiedFrom (Theory.loopCode m loopBody5 ++ []) (loopInv 0) ((loopInv m).r0) :=
  Theory.Reach_imp_VerifiedFrom (
    Theory.SuffixReach_imp_Reach (Theory.loopCode m loopBody5 ++ []) (loopInv 0) ((loopInv m).r0) rfl
      (Theory.loop_summary_sound loopInv loopBody5_step m [] ((loopInv m).r0)
        (Theory.SuffixReach.nil (loopInv m)))
  )
"""
    )
  t_sym = compile_lean(sym_file, sym_olean)
  km_sym = measure_kernel_batch(base_mod, [sym_mod])[sym_mod]
  olean_sym = os.path.getsize(sym_olean)
  row_sym = {
      "suite": "B3_Loops",
      "param": "symbolic_m",
      "instrs": "5*m",
      "arch": "Arch 5 (Pre-Proved Loop Summary, Symbolic m)",
      "elab_ms": round(t_sym, 2),
      "replay_ms": km_sym["replay_ms"],
      "replay_us": km_sym["replay_us"],
      "olean_bytes": olean_sym,
      "decls": km_sym["decls"],
      "dag_nodes": km_sym["dag_nodes"],
      "tree_nodes": km_sym["tree_nodes"],
  }
  results.append(row_sym)
  print(
      f"Loop M=sym (5*m instrs) | {'Arch 5 (Symbolic Loop Summary)':36s} |"
      f" elab={t_sym:7.1f}ms | replay={km_sym['replay_ms']:7.3f}ms"
      f" ({km_sym['replay_us']:6d}us) | olean={olean_sym:7d}B |"
      f" DAG={km_sym['dag_nodes']:6d} | TREE={km_sym['tree_nodes']:8d}",
      flush=True,
  )
  return results


if __name__ == "__main__":
  r1 = run_suite_b1_diamonds()
  r2 = run_suite_b2_calls_and_loops()
  out_json = os.path.join(WORKDIR, "suite_b_results.json")
  with open(out_json, "w") as f:
    json.dump(r1 + r2, f, indent=2)
  print(f"Saved Suite B results to {out_json}")
