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

LEAN_ROOT = "/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1"
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
# those terms.
""".replace("# those terms.", "-- those terms.")


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
    raise RuntimeError(
        f"Failed compiling {lean_file}:\n{res.stderr}\n{res.stdout}"
    )
  return (t1 - t0) * 1000.0


def compile_lean_expect_failure(lean_file, olean_file):
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
  if res.returncode == 0:
    raise RuntimeError(
        f"ERROR: Negative canary {lean_file} unexpectedly compiled!"
    )
  return {
      "file": os.path.basename(lean_file),
      "failed_as_expected": True,
      "returncode": res.returncode,
      "time_ms": round((t1 - t0) * 1000.0, 2),
      "error_excerpt": (res.stdout + "\n" + res.stderr).strip().splitlines()[0]
      if (res.stdout + res.stderr).strip()
      else "failed",
  }


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
        "mod_decls": int(kv["MOD_DECLS"]),
        "mod_dag_nodes": int(kv["MOD_DAG_NODES"]),
        "mod_tree_nodes": int(kv["MOD_TREE_NODES"]),
        "replayed_mods": int(kv["REPLAYED_MODS"]),
    }
  return out_map


def step_intra_py(conds, instr, state):
  body_name, pc, r0, r1, r2, r3, flag, stack = state
  regs = [r0, r1, r2, r3]
  op = instr[0]
  if op == "add":
    _, dst, s1, s2 = instr
    regs[dst] = (regs[s1] + regs[s2]) & MASK64
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "sub":
    _, dst, s1, s2 = instr
    regs[dst] = (regs[s1] - regs[s2]) & MASK64
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "xor":
    _, dst, s1, s2 = instr
    regs[dst] = regs[s1] ^ regs[s2]
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "band":
    _, dst, s1, s2 = instr
    regs[dst] = regs[s1] & regs[s2]
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "shl":
    _, dst, src, amt = instr
    regs[dst] = (regs[src] << amt) & MASK64
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "shr":
    _, dst, src, amt = instr
    regs[dst] = (regs[src] >> amt) & MASK64
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "addImm":
    _, dst, src, imm = instr
    regs[dst] = (regs[src] + imm) & MASK64
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  elif op == "addCheckedImm":
    _, dst, src, imm = instr
    val = regs[src]
    ov = (val + imm) >= MOD64
    regs[dst] = (val + imm) & MASK64
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], ov, stack)
  elif op == "assertNotFlag":
    assert not flag, "assertNotFlag trapped!"
    return (body_name, pc + 1, r0, r1, r2, r3, flag, stack)
  elif op == "selectImm":
    _, cond_idx, dst, imm_t, imm_f = instr
    cval = conds[cond_idx] if cond_idx < len(conds) else conds[4]
    regs[dst] = imm_t if cval else imm_f
    return (body_name, pc + 1, regs[0], regs[1], regs[2], regs[3], flag, stack)
  else:
    raise ValueError(f"Unknown intra op: {op}")


def simulate_trace(prog_map, body_name, conds=(False, False, False, False, False)):
  s0 = (body_name, 0, 7, 0, 3, 0, False, ())
  states = [s0]
  curr = s0
  while True:
    bname, pc, r0, r1, r2, r3, flag, stack = curr
    instrs = prog_map[bname]
    if pc < len(instrs):
      instr = instrs[pc]
      if instr[0] == "call":
        _, callee_key = instr
        callee_bname = callee_key
        frame = (bname, pc + 1, r1, r2, r3)
        curr = (callee_bname, 0, r0, r1, 0, 0, False, (frame,) + stack)
        states.append(curr)
      else:
        curr = step_intra_py(conds, instr, curr)
        states.append(curr)
    else:
      if not stack:
        return states, r0
      frame = stack[0]
      rest_stack = stack[1:]
      ret_bname, ret_pc, sv_r1, sv_r2, sv_r3 = frame
      curr = (ret_bname, ret_pc, r0, sv_r1, sv_r2, sv_r3, False, rest_stack)
      states.append(curr)


def reg_lean(r):
  return f".r{r}"


def instr_lean(instr):
  op = instr[0]
  if op in ("add", "sub", "xor", "band"):
    _, dst, s1, s2 = instr
    return f".{op} {reg_lean(dst)} {reg_lean(s1)} {reg_lean(s2)}"
  elif op in ("shl", "shr"):
    _, dst, src, amt = instr
    return f".{op} {reg_lean(dst)} {reg_lean(src)} {amt}"
  elif op in ("addImm", "addCheckedImm"):
    _, dst, src, imm = instr
    return f".{op} {reg_lean(dst)} {reg_lean(src)} {imm}#64"
  elif op == "assertNotFlag":
    return ".assertNotFlag"
  elif op == "selectImm":
    _, cond_idx, dst, imm_t, imm_f = instr
    return f".selectImm {cond_idx} {reg_lean(dst)} {imm_t}#64 {imm_f}#64"
  elif op == "call":
    _, fn_str = instr
    return f'.call "{fn_str}"'
  else:
    raise ValueError(f"Unknown instr: {instr}")


def stack_lean(stack, body_expr_map):
  if not stack:
    return "[]"
  items = []
  for ret_bname, ret_pc, sv_r1, sv_r2, sv_r3 in stack:
    b_expr = body_expr_map[ret_bname]
    items.append(f"⟨{b_expr}, {ret_pc}, {sv_r1}#64, {sv_r2}#64, {sv_r3}#64⟩")
  return "[" + ", ".join(items) + "]"


def state_lean(s, body_expr_map):
  bname, pc, r0, r1, r2, r3, flag, stack = s
  fl_str = "true" if flag else "false"
  b_expr = body_expr_map[bname]
  stk_str = stack_lean(stack, body_expr_map)
  return f"⟨{b_expr}, {pc}, {r0}#64, {r1}#64, {r2}#64, {r3}#64, {fl_str}, {stk_str}⟩"


def build_core_callee_py(imm1, imm2):
  return [
      ("addCheckedImm", 0, 0, imm1),
      ("assertNotFlag",),
      ("xor", 1, 0, 1),
      ("shl", 2, 1, 3),
      ("add", 0, 0, 2),
      ("addImm", 0, 0, imm2),
      ("xor", 1, 0, 2),
      ("shr", 2, 1, 2),
      ("add", 0, 0, 2),
      ("add", 0, 0, 1),
  ]


def build_idiom_prog_py(imms):
  prog = []
  for imm in imms:
    prog.extend([
        ("addCheckedImm", 0, 0, imm),
        ("assertNotFlag",),
        ("xor", 1, 0, 2),
        ("shl", 2, 1, 3),
        ("add", 0, 0, 2),
    ])
  return prog


def build_diamond_blk_py(k, a1, a2, b1, b2):
  return [
      ("selectImm", k, 1, a1, b1),
      ("selectImm", k, 2, a2, b2),
      ("add", 1, 1, 2),
      ("add", 0, 0, 1),
      ("xor", 1, 1, 1),
      ("xor", 2, 2, 2),
  ]


def build_crate_data():
  fn_names = [
      "core::mem::size_of",
      "core::num::usize::checked_add",
      "core::num::NonZeroUsize::new",
      "core::option::Option::unwrap_or",
      "zerocopy::util::validate_cast_layout",
      "zerocopy::ptr::try_cast_into_header",
      "zerocopy::layout::compute_padding_and_stride",
      "zerocopy::layout::align_up_mask_mix",
      "zerocopy::validity::check_enum_discriminants",
      "zerocopy::slice::validate_slice_elements_loop",
  ]

  # (a) 4 core callees (10 instructions each)
  core_params = [
      (fn_names[0], 8, 16),
      (fn_names[1], 4, 12),
      (fn_names[2], 1, 8),
      (fn_names[3], 2, 24),
  ]
  prog_map = {}
  for name, imm1, imm2 in core_params:
    prog_map[name] = build_core_callee_py(imm1, imm2)

  # (a)+(b) 2 multi-call callers invoking the 4 core helpers (4 calls + 4 intra instrs = 52 dynamic steps each)
  prog_map[fn_names[4]] = [
      ("call", fn_names[0]),
      ("addImm", 1, 0, 3),
      ("call", fn_names[1]),
      ("shr", 0, 0, 4),
      ("call", fn_names[2]),
      ("shr", 0, 0, 4),
      ("call", fn_names[3]),
      ("addImm", 0, 0, 5),
  ]
  prog_map[fn_names[5]] = [
      ("call", fn_names[3]),
      ("addImm", 1, 0, 5),
      ("call", fn_names[2]),
      ("shr", 0, 0, 4),
      ("call", fn_names[1]),
      ("shr", 0, 0, 4),
      ("call", fn_names[0]),
      ("addImm", 0, 0, 9),
  ]

  # (b) 2 straight-line 100-instruction bit-manipulation / layout functions (20 x 5-instr idioms each)
  imms_f6 = [(j % 7) + 1 for j in range(20)]
  imms_f7 = [(j % 5) + 2 for j in range(20)]
  prog_map[fn_names[6]] = build_idiom_prog_py(imms_f6)
  prog_map[fn_names[7]] = build_idiom_prog_py(imms_f7)

  # (c) 1 chained CFG diamond function (D = 5 diamonds, 2^5 = 32 paths, 6 instrs/diamond = 30 instrs)
  diamonds_f8 = []
  prog_f8 = []
  for k in range(5):
    a1 = k + 1
    a2 = 10 - a1
    b1 = k + 2
    b2 = 10 - b1
    dblk = build_diamond_blk_py(k, a1, a2, b1, b2)
    diamonds_f8.append((k, a1, a2, b1, b2, dblk))
    prog_f8.extend(dblk)
  prog_map[fn_names[8]] = prog_f8

  # (d) 1 counted loop function (M = 20 iterations x 5 instrs = 100 instrs)
  loop_body5 = [
      ("addImm", 0, 0, 1),
      ("addImm", 0, 0, 2),
      ("addImm", 0, 0, 1),
      ("addImm", 0, 0, 2),
      ("addImm", 0, 0, 1),
  ]
  prog_map[fn_names[9]] = loop_body5 * 20

  body_expr_map = {fn_names[i]: f"body_f{i}" for i in range(10)}

  return {
      "fn_names": fn_names,
      "core_params": core_params,
      "prog_map": prog_map,
      "imms_f6": imms_f6,
      "imms_f7": imms_f7,
      "diamonds_f8": diamonds_f8,
      "body_expr_map": body_expr_map,
  }


def generate_crate_mir(data):
  fn_names = data["fn_names"]
  prog_map = data["prog_map"]
  imms_f7 = data["imms_f7"]
  diamonds_f8 = data["diamonds_f8"]

  lines = [HEADER, "import UnifiedEndToEndStack\n", "open Trusted Theory\n"]

  # 1. Define body_f0 .. body_f9
  for i, (_, imm1, imm2) in enumerate(data["core_params"]):
    lines.append(
        f"def body_f{i} : List Instr := mkCoreCalleeBody {imm1}#64 {imm2}#64"
    )

  for i in (4, 5, 6):
    instrs_str = ",\n  ".join(instr_lean(ins) for ins in prog_map[fn_names[i]])
    lines.append(f"def body_f{i} : List Instr := [\n  {instrs_str}\n]")

  imms_f7_str = ", ".join(f"{imm}#64" for imm in imms_f7)
  lines.append(f"def imms_f7 : List (BitVec 64) := [{imms_f7_str}]")
  lines.append("def body_f7 : List Instr := buildIdiomProg imms_f7")

  for k, a1, a2, b1, b2, dblk in diamonds_f8:
    d_str = ", ".join(instr_lean(ins) for ins in dblk)
    lines.append(f"def dblk_f8_{k} : List Instr := [{d_str}]")
  lines.append(
      "def body_f8 : List Instr := dblk_f8_0 ++ (dblk_f8_1 ++ (dblk_f8_2 ++"
      " (dblk_f8_3 ++ (dblk_f8_4 ++ []))))"
  )

  lines.append("def body_f9 : List Instr := loopCode 20 loopBody5 ++ []\n")

  # 2. Define crateProg : MirProg
  prog_entries = ",\n  ".join(
      f'("{fn_names[i]}", body_f{i})' for i in range(10)
  )
  lines.append(f"def crateProg : MirProg := [\n  {prog_entries}\n]\n")

  # 3. Define expected return values v_f0 .. v_f9 and side conditions scs_0 .. scs_9
  expected_vals = []
  for i in range(10):
    _, r0_out = simulate_trace(prog_map, fn_names[i])
    expected_vals.append(r0_out)
    lines.append(f"def v_f{i} : BitVec 64 := {r0_out}#64")

  lines.append("")
  for i in range(10):
    p1 = 1000 * (i + 1)
    p2 = p1 + 128
    sc1 = f".disjoint {p1} 64 {p2} 64"
    if i % 2 == 0:
      off = 64 * (i + 1) + 5
      out = 64 * (i + 1) + 16
      sc2 = f".aligned {off} 16 {out}"
    else:
      off = 32 * (i + 1)
      tot = off + 128
      sc2 = f".subrange {off} 64 {tot}"
    lines.append(f"def scs_{i} : List SideCondSpec := [{sc1}, {sc2}]")

  lines.append("")
  for i in range(10):
    lines.append(f"""def fnSpec_{i} : FunctionSpec MirLang where
  name := "{fn_names[i]}"
  prog := (crateProg, body_f{i})
  specs := [mkSpec v_f{i}]
  specWellFormed := fun _ => AllSideCondsHold scs_{i}
""")

  fn_list_str = ", ".join(f"fnSpec_{i}" for i in range(10))
  tcb_list_str = ",\n    ".join(
      f".rustcLowering fnSpec_{i}.name fnSpec_{i}.prog" for i in range(10)
  )
  lines.append(f"""def crate10 : Crate MirLang MirLang π_id where
  functions := [{fn_list_str}]
  tcb := [
    {tcb_list_str}
  ]
""")

  crate_mir_file = os.path.join(WORKDIR, "CrateMir.lean")
  crate_mir_olean = os.path.join(WORKDIR, "CrateMir.olean")
  with open(crate_mir_file, "w") as f:
    f.write("\n".join(lines))
  elab_ms = compile_lean(crate_mir_file, crate_mir_olean)
  print(f"Compiled CrateMir.lean in {elab_ms:.1f} ms", flush=True)
  data["expected_vals"] = expected_vals


def build_cont_lambda_chain(states, v_expr, body_expr_map):
  n = len(states) - 1
  term = f"safeAndEnsures_of_ret rfl hr_{n} rfl"
  for k in range(n - 1, -1, -1):
    s_next = state_lean(states[k + 1], body_expr_map)
    term = (
        f"safeAndEnsures_of_step (s' := {s_next}) rfl hr_{k} (fun _"
        f" hr_{k+1} =>\n      {term})"
    )
  return term


def build_caller_record_chain(prog_map, caller_name, v_expr, body_expr_map):
  """Builds Stage 0/1 proof for f_4 or f_5 using inlineCoreCall12_record and { s with ... } record updates."""
  states, _ = simulate_trace(prog_map, caller_name)
  caller_instrs = prog_map[caller_name]
  # Map each caller instruction idx in 0..7 to its start index in `states`
  # Call instructions take 12 transitions in `states`; non-call instructions take 1 transition.
  cursor = 0
  step_chunks = []
  for pc_idx, ins in enumerate(caller_instrs):
    if ins[0] == "call":
      chunk = states[cursor : cursor + 13]
      step_chunks.append(("call", pc_idx, chunk))
      cursor += 12
    else:
      chunk = states[cursor : cursor + 2]
      step_chunks.append(("intra", pc_idx, chunk))
      cursor += 1
  assert cursor == len(states) - 1

  term = "safeAndEnsures_of_ret rfl hr_8 rfl"
  for idx in range(len(step_chunks) - 1, -1, -1):
    kind, pc_idx, chunk = step_chunks[idx]
    s_after = chunk[-1]
    _, _, r0_a, r1_a, r2_a, _, _, _ = s_after
    if kind == "call":
      mid_states = " ".join(
          f"(s{m} := {state_lean(chunk[m], body_expr_map)})"
          for m in range(1, 12)
      )
      v_out = r0_a
      rfls = " ".join(["rfl"] * 12)
      term = (
          f"inlineCoreCall12_record {mid_states}"
          f" (vOut := {v_out}#64) {rfls} hr_{idx} (fun _ hr_{idx+1} =>\n     "
          f" {term})"
      )
    else:
      term = (
          f"step_record (r0' := {r0_a}#64) (r1' := {r1_a}#64) (r2' :="
          f" {r2_a}#64) rfl hr_{idx} (fun _ hr_{idx+1} =>\n      {term})"
      )

  return term


def generate_stage0_and_stage1_proof(data):
  """Generates Stage0_Proof.lean (used for both Stage 0 on FoundationBase and Stage 1 on UnifiedEndToEndStack)."""
  fn_names = data["fn_names"]
  prog_map = data["prog_map"]
  body_expr_map = data["body_expr_map"]

  lines = [
      HEADER,
      "import CrateMir\n",
      "open Trusted Theory\n",
      "set_option maxRecDepth 200000",
      "set_option maxHeartbeats 40000000\n",
  ]

  # 1. 20 side-condition lemmas proved via `omega`
  for i in range(10):
    p1 = 1000 * (i + 1)
    p2 = p1 + 128
    lines.append(
        f"""theorem side_cond_{i}_0 : (SideCondSpec.disjoint {p1} 64 {p2} 64).holds := by
  dsimp [SideCondSpec.holds, IntervalsDisjoint, ADDR_MASK]
  omega
"""
    )
    if i % 2 == 0:
      off = 64 * (i + 1) + 5
      out = 64 * (i + 1) + 16
      lines.append(
          f"""theorem side_cond_{i}_1 : (SideCondSpec.aligned {off} 16 {out}).holds := by
  dsimp [SideCondSpec.holds, AlignedRoundUp]
  omega
"""
      )
    else:
      off = 32 * (i + 1)
      sublen = 64
      totallen = off + 128
      lines.append(
          f"""theorem side_cond_{i}_1 : (SideCondSpec.subrange {off} {sublen} {totallen}).holds := by
  dsimp [SideCondSpec.holds, SymbolicSubrange]
  intro base
  omega
"""
      )
    lines.append(f"""theorem all_side_conds_{i} : AllSideCondsHold scs_{i} :=
  ⟨side_cond_{i}_0, ⟨side_cond_{i}_1, trivial⟩⟩
""")

  # 2. Function body proofs for f_0..f_3, f_6, f_7, f_9 using continuation lambdas
  for i in (0, 1, 2, 3, 6, 7, 9):
    states, _ = simulate_trace(prog_map, fn_names[i])
    chain_str = build_cont_lambda_chain(states, f"v_f{i}", body_expr_map)
    lines.append(f"""theorem verified_body_f{i} (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f{i}) v_f{i} :=
  fun _ _ hr_0 =>
    {chain_str}
""")

  # 3. Function body proofs for f_4, f_5 using inlined calls + { s with ... } record updates
  for i in (4, 5):
    caller_chain = build_caller_record_chain(
        prog_map, fn_names[i], f"v_f{i}", body_expr_map
    )
    lines.append(f"""theorem verified_body_f{i} (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f{i}) v_f{i} :=
  fun _ _ hr_0 =>
    {caller_chain}
""")

  # 4. Function body proof for f_8 (D=5 diamonds = 32 paths with continuation lambdas)
  path_thms = []
  for mask in range(32):
    conds = tuple(bool((mask >> b) & 1) for b in range(5))
    b_strs = ["true" if c else "false" for c in conds]
    env_str = f"⟨{', '.join(b_strs)}⟩"
    states, _ = simulate_trace(prog_map, fn_names[8], conds=conds)
    chain_str = build_cont_lambda_chain(states, "v_f8", body_expr_map)
    pname = f"verified_f8_path_{mask}"
    path_thms.append(pname)
    lines.append(f"""theorem {pname} :
    VerifiedFrom crateProg {env_str} (entryState body_f8) v_f8 :=
  fun _ _ hr_0 =>
    {chain_str}
""")

  def build_bool_cases(bit_idx, prefix_bits):
    if bit_idx == 5:
      mask = sum((1 << b) if prefix_bits[b] else 0 for b in range(5))
      return f"exact verified_f8_path_{mask} n out hReach"
    indent = "  " * (bit_idx + 2)
    f_branch = build_bool_cases(bit_idx + 1, prefix_bits + [False])
    t_branch = build_bool_cases(bit_idx + 1, prefix_bits + [True])
    return (
        f"cases c{bit_idx} with\n{indent}| false =>\n{indent} "
        f" {f_branch}\n{indent}| true =>\n{indent}  {t_branch}"
    )

  cases_tree_str = build_bool_cases(0, [])
  lines.append(f"""theorem verified_body_f8 (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f8) v_f8 := by
  intro n out hReach
  rcases q with ⟨c0, c1, c2, c3, c4⟩
  {cases_tree_str}
""")

  # 5. Shards with `by decide` TCB lookup + CrateTheorem
  for i in range(10):
    lines.append(f"""theorem shard_s0_{i} : ShardCert crate10 fnSpec_{i} :=
  mkShardCert rfl rfl (by decide) verified_body_f{i} all_side_conds_{i}
""")

  shards_cons = ".nil"
  for i in range(9, -1, -1):
    shards_cons = f"(.cons shard_s0_{i} {shards_cons})"

  lines.append(f"""theorem verify_crate10 : CrateTheorem crate10 :=
  verify_crate_of_shards π_id_mono {shards_cons}
""")

  s0_file = os.path.join(WORKDIR, "Stage0_Proof.lean")
  s0_olean = os.path.join(WORKDIR, "Stage0_Proof.olean")
  with open(s0_file, "w") as f:
    f.write("\n".join(lines))
  elab_ms = compile_lean(s0_file, s0_olean)
  print(f"Compiled Stage0_Proof.lean in {elab_ms:.1f} ms", flush=True)
  return elab_ms, os.path.getsize(s0_olean)


def build_suffix_step_chain(states, v_expr, body_expr_map):
  n = len(states) - 1
  lets = [f"let st_0 : State := {state_lean(states[0], body_expr_map)}"]
  for k in range(1, n + 1):
    lets.append(
        f"let st_{k} : State := {state_lean(states[k], body_expr_map)}"
    )
  lets_str = "\n    ".join(lets)
  term = f"SuffixReach.nil st_{n} rfl"
  for k in range(n - 1, -1, -1):
    term = f"step_instr _ _ st_{k} st_{k+1} {v_expr} rfl (\n      {term})"
  return lets_str, term


def build_caller_flat_chain(prog_map, caller_name, v_expr, body_expr_map):
  """Builds Stage 2 flat-tuple `SuffixReach` proof for f_4 or f_5 (inlined calls, no `{ s with ... }`)."""
  states, _ = simulate_trace(prog_map, caller_name)
  caller_instrs = prog_map[caller_name]
  lets = [
      f"let st_{k} : State := {state_lean(s, body_expr_map)}"
      for k, s in enumerate(states)
  ]
  lets_str = "\n    ".join(lets)

  cursor = 0
  chunks = []
  for ins in caller_instrs:
    if ins[0] == "call":
      chunks.append(("call", ins[1], cursor, cursor + 12))
      cursor += 12
    else:
      chunks.append(("intra", None, cursor, cursor + 1))
      cursor += 1
  assert cursor == len(states) - 1

  term = f"SuffixReach.nil st_{cursor} rfl"
  for kind, fn_str, c_start, c_end in reversed(chunks):
    if kind == "call":
      mid_args = " ".join(f"st_{m}" for m in range(c_start, c_end + 1))
      rfls = " ".join(["rfl"] * 14)
      term = (
          f'inlineCoreCall12_flat "{fn_str}" _ {mid_args} {v_expr} {rfls} (\n  '
          f"    {term})"
      )
    else:
      term = (
          f"step_instr _ _ st_{c_start} st_{c_end} {v_expr} rfl (\n     "
          f" {term})"
      )
  return lets_str, term


def tcb_structural_lean(idx):
  term = "(.head _)"
  for _ in range(idx):
    term = f"(.tail _ {term})"
  return term


def generate_stage2_proof(data):
  """Generates Stage2_Proof.lean (Flat-tuple State.casesOn, let-sharing, structural TCB, batch side-cond rfl)."""
  fn_names = data["fn_names"]
  prog_map = data["prog_map"]
  body_expr_map = data["body_expr_map"]

  lines = [
      HEADER,
      "import CrateMir\n",
      "open Trusted Theory\n",
      "set_option maxRecDepth 200000",
      "set_option maxHeartbeats 40000000\n",
  ]

  # 1. f_0..f_3, f_6, f_7, f_9 using contiguous let-shared SuffixReach + step_instr
  for i in (0, 1, 2, 3, 6, 7, 9):
    states, _ = simulate_trace(prog_map, fn_names[i])
    lets_str, term = build_suffix_step_chain(states, f"v_f{i}", body_expr_map)
    lines.append(f"""theorem verified_body_f{i} (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f{i}) v_f{i} :=
  Reach_imp_VerifiedFrom (
    {lets_str}
    SuffixReach_imp_Reach crateProg q body_f{i} st_0 v_f{i} rfl rfl (
      {term}
    )
  )
""")

  # 2. f_4, f_5 using flat-tuple inlineCoreCall12_flat (eliminating { s with ... } O(6^K) tree blowup)
  for i in (4, 5):
    lets_str, term = build_caller_flat_chain(
        prog_map, fn_names[i], f"v_f{i}", body_expr_map
    )
    lines.append(f"""theorem verified_body_f{i} (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f{i}) v_f{i} :=
  Reach_imp_VerifiedFrom (
    {lets_str}
    SuffixReach_imp_Reach crateProg q body_f{i} st_0 v_f{i} rfl rfl (
      {term}
    )
  )
""")

  # 3. f_8 (D=5 diamonds, 32 paths using SuffixReach + step_instr)
  for mask in range(32):
    conds = tuple(bool((mask >> b) & 1) for b in range(5))
    b_strs = ["true" if c else "false" for c in conds]
    env_str = f"⟨{', '.join(b_strs)}⟩"
    states, _ = simulate_trace(prog_map, fn_names[8], conds=conds)
    lets_str, term = build_suffix_step_chain(states, "v_f8", body_expr_map)
    lines.append(f"""theorem verified_f8_s2_path_{mask} :
    VerifiedFrom crateProg {env_str} (entryState body_f8) v_f8 :=
  Reach_imp_VerifiedFrom (
    {lets_str}
    SuffixReach_imp_Reach crateProg {env_str} body_f8 st_0 v_f8 rfl rfl (
      {term}
    )
  )
""")

  def build_bool_cases_s2(bit_idx, prefix_bits):
    if bit_idx == 5:
      mask = sum((1 << b) if prefix_bits[b] else 0 for b in range(5))
      return f"exact verified_f8_s2_path_{mask} n out hReach"
    indent = "  " * (bit_idx + 2)
    f_branch = build_bool_cases_s2(bit_idx + 1, prefix_bits + [False])
    t_branch = build_bool_cases_s2(bit_idx + 1, prefix_bits + [True])
    return (
        f"cases c{bit_idx} with\n{indent}| false =>\n{indent} "
        f" {f_branch}\n{indent}| true =>\n{indent}  {t_branch}"
    )

  cases_tree_s2 = build_bool_cases_s2(0, [])
  lines.append(f"""theorem verified_body_f8 (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f8) v_f8 := by
  intro n out hReach
  rcases q with ⟨c0, c1, c2, c3, c4⟩
  {cases_tree_s2}
""")

  # 4. Shards with structural .tail/.head TCB witnesses and checkSideCondBatch_sound rfl
  for i in range(10):
    tcb_wit = tcb_structural_lean(i)
    lines.append(f"""theorem shard_s2_{i} : ShardCert crate10 fnSpec_{i} :=
  mkShardCert rfl rfl {tcb_wit} verified_body_f{i} (checkSideCondBatch_sound rfl)
""")

  shards_cons = ".nil"
  for i in range(9, -1, -1):
    shards_cons = f"(.cons shard_s2_{i} {shards_cons})"

  lines.append(f"""theorem verify_crate10 : CrateTheorem crate10 :=
  verify_crate_of_shards π_id_mono {shards_cons}
""")

  s2_file = os.path.join(WORKDIR, "Stage2_Proof.lean")
  s2_olean = os.path.join(WORKDIR, "Stage2_Proof.olean")
  with open(s2_file, "w") as f:
    f.write("\n".join(lines))
  elab_ms = compile_lean(s2_file, s2_olean)
  print(f"Compiled Stage2_Proof.lean in {elab_ms:.1f} ms", flush=True)
  return elab_ms, os.path.getsize(s2_olean)


def build_stage3_fn_proofs(data):
  """Returns per-function theorem snippets for Stage 3 and Stage 4 (3-Layer Hybrid Theory Validators)."""
  fn_names = data["fn_names"]
  prog_map = data["prog_map"]
  body_expr_map = data["body_expr_map"]
  fn_snippets = {}

  # f_0..f_3: Layer 2 cv_trans GMP Nat reflection (`evalCvProg_sound rfl`)
  # Plus CalleeSummary instantiation (`mkCoreCalleeBody_summary`)
  callee_summary_defs = []
  for i, (name, imm1, imm2) in enumerate(data["core_params"]):
    callee_summary_defs.append(
        f"theorem summary_core_{i} : CalleeSummary crateProg"
        f' "{name}" (mkCoreCalleeSpec {imm1}#64 {imm2}#64) :=\n '
        f' mkCoreCalleeBody_summary crateProg "{name}" {imm1}#64 {imm2}#64 rfl'
    )
    tcb_wit = tcb_structural_lean(i)
    fn_snippets[i] = f"""theorem verified_body_f{i} (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f{i}) v_f{i} :=
  Reach_imp_VerifiedFrom (evalCvProg_sound crateProg q body_f{i} v_f{i} rfl)

theorem shard_{i} : ShardCert crate10 fnSpec_{i} :=
  mkShardCert rfl rfl {tcb_wit} verified_body_f{i} (checkSideCondBatch_sound rfl)
"""

  fn_to_summary_idx = {fn_names[i]: i for i in range(4)}

  # f_4, f_5: Layer 3 `call_summary_flat_step` (O(1) per call!) + `step_instr`
  for i in (4, 5):
    states, _ = simulate_trace(prog_map, fn_names[i])
    caller_instrs = prog_map[fn_names[i]]
    cursor = 0
    cut_states = [states[0]]
    steps_meta = []
    for ins in caller_instrs:
      if ins[0] == "call":
        cursor += 12
        cut_states.append(states[cursor])
        steps_meta.append(("call", fn_to_summary_idx[ins[1]]))
      else:
        cursor += 1
        cut_states.append(states[cursor])
        steps_meta.append(("intra", None))
    lets = [
        f"let st_{k} : State := {state_lean(s, body_expr_map)}"
        for k, s in enumerate(cut_states)
    ]
    lets_str = "\n    ".join(lets)
    term = f"SuffixReach.nil st_{len(cut_states)-1} rfl"
    for idx in range(len(steps_meta) - 1, -1, -1):
      kind, s_idx = steps_meta[idx]
      if kind == "call":
        term = (
            f"call_summary_flat_step summary_core_{s_idx} _ st_{idx}"
            f" st_{idx+1} v_f{i} rfl (\n      {term})"
        )
      else:
        term = (
            f"step_instr _ _ st_{idx} st_{idx+1} v_f{i} rfl (\n      {term})"
        )
    tcb_wit = tcb_structural_lean(i)
    fn_snippets[i] = f"""theorem verified_body_f{i} (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f{i}) v_f{i} :=
  Reach_imp_VerifiedFrom (
    {lets_str}
    SuffixReach_imp_Reach crateProg q body_f{i} st_0 v_f{i} rfl rfl (
      {term}
    )
  )

theorem shard_{i} : ShardCert crate10 fnSpec_{i} :=
  mkShardCert rfl rfl {tcb_wit} verified_body_f{i} (checkSideCondBatch_sound rfl)
"""

  # f_6: Layer 2 `evalCvProg_sound rfl` (100 instructions in 1 `cv_trans` GMP Nat step!)
  tcb_6 = tcb_structural_lean(6)
  fn_snippets[6] = f"""theorem verified_body_f6 (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f6) v_f6 :=
  Reach_imp_VerifiedFrom (evalCvProg_sound crateProg q body_f6 v_f6 rfl)

theorem shard_6 : ShardCert crate10 fnSpec_6 :=
  mkShardCert rfl rfl {tcb_6} verified_body_f6 (checkSideCondBatch_sound rfl)
"""

  # f_7: Layer 2 `evalIdiomPlan_sound` (hint-driven 5-instruction superinstruction validator!)
  states_7, _ = simulate_trace(prog_map, fn_names[7])
  st_end_7 = state_lean(states_7[-1], body_expr_map)
  tcb_7 = tcb_structural_lean(7)
  fn_snippets[7] = f"""theorem verified_body_f7 (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f7) v_f7 :=
  Reach_imp_VerifiedFrom (
    let st_end : State := {st_end_7}
    SuffixReach_imp_Reach crateProg q body_f7 (entryState body_f7) v_f7 rfl rfl
      (evalIdiomPlan_sound imms_f7 [] (entryState body_f7) st_end v_f7 rfl
        (SuffixReach.nil st_end rfl))
  )

theorem shard_7 : ShardCert crate10 fnSpec_7 :=
  mkShardCert rfl rfl {tcb_7} verified_body_f7 (checkSideCondBatch_sound rfl)
"""

  # f_8: Layer 3 `diamond_converge_step` (O(D) = 5 cut-point steps instead of 2^5 = 32 paths!)
  lets_8 = ["let st_0 : State := entryState body_f8"]
  for k in range(1, 6):
    lets_8.append(
        f"let st_{k} : State := ⟨body_f8, {6 * k}, {7 + 10 * k}#64, 0#64, 0#64,"
        " 0#64, false, []⟩"
    )
  lets_8_str = "\n    ".join(lets_8)
  term_8 = "SuffixReach.nil st_5 rfl"
  for k in range(4, -1, -1):
    term_8 = (
        f"diamond_converge_step crateProg q {k} dblk_f8_{k} _ st_{k} st_{k+1}"
        f" v_f8 rfl rfl (\n      {term_8})"
    )
  tcb_8 = tcb_structural_lean(8)
  fn_snippets[8] = f"""theorem verified_body_f8 (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f8) v_f8 :=
  Reach_imp_VerifiedFrom (
    {lets_8_str}
    SuffixReach_imp_Reach crateProg q body_f8 st_0 v_f8 rfl rfl (
      {term_8}
    )
  )

theorem shard_8 : ShardCert crate10 fnSpec_8 :=
  mkShardCert rfl rfl {tcb_8} verified_body_f8 (checkSideCondBatch_sound rfl)
"""

  # f_9: Layer 3 `loop_summary_sound` (M = 20 loop iterations = 100 instructions in 1 step!)
  tcb_9 = tcb_structural_lean(9)
  fn_snippets[9] = f"""theorem verified_body_f9 (q : BranchEnv) :
    VerifiedFrom crateProg q (entryState body_f9) v_f9 :=
  Reach_imp_VerifiedFrom (
    SuffixReach_imp_Reach crateProg q body_f9 (entryState body_f9) v_f9 rfl rfl
      (loop_summary_sound crateProg q (loopInv body_f9) (loopBody5_step body_f9)
        20 [] v_f9 (SuffixReach.nil (loopInv body_f9 20) rfl))
  )

theorem shard_9 : ShardCert crate10 fnSpec_9 :=
  mkShardCert rfl rfl {tcb_9} verified_body_f9 (checkSideCondBatch_sound rfl)
"""

  return callee_summary_defs, fn_snippets


def generate_stage3_and_stage4_proofs(data):
  callee_summary_defs, fn_snippets = build_stage3_fn_proofs(data)

  # Stage 3: Monolithic 10-function crate proof using 3-layer hybrid validators
  lines_s3 = [
      HEADER,
      "import CrateMir\n",
      "open Trusted Theory\n",
      "\n".join(callee_summary_defs),
      "",
  ]
  for i in range(10):
    lines_s3.append(fn_snippets[i])

  shards_cons = ".nil"
  for i in range(9, -1, -1):
    shards_cons = f"(.cons shard_{i} {shards_cons})"

  lines_s3.append(f"""theorem verify_crate10 : CrateTheorem crate10 :=
  verify_crate_of_shards π_id_mono {shards_cons}
""")

  s3_file = os.path.join(WORKDIR, "Stage3_Proof.lean")
  s3_olean = os.path.join(WORKDIR, "Stage3_Proof.olean")
  with open(s3_file, "w") as f:
    f.write("\n".join(lines_s3))
  elab_s3 = compile_lean(s3_file, s3_olean)
  print(f"Compiled Stage3_Proof.lean in {elab_s3:.1f} ms", flush=True)

  # Stage 4: Per-Function Sharded Modules (`Stage4_CalleeSummaries`, `Stage4_Shard_0 .. Stage4_Shard_9`, `Stage4_Root`)
  cs_file = os.path.join(WORKDIR, "Stage4_CalleeSummaries.lean")
  cs_olean = os.path.join(WORKDIR, "Stage4_CalleeSummaries.olean")
  with open(cs_file, "w") as f:
    f.write(
        HEADER
        + "import CrateMir\n\nopen Trusted Theory\n\n"
        + "\n\n".join(callee_summary_defs)
        + "\n"
    )
  compile_lean(cs_file, cs_olean)

  shard_elab_ms = {}
  shard_olean_bytes = {}
  for i in range(10):
    sh_mod = f"Stage4_Shard_{i}"
    sh_file = os.path.join(WORKDIR, f"{sh_mod}.lean")
    sh_olean = os.path.join(WORKDIR, f"{sh_mod}.olean")
    imp = "Stage4_CalleeSummaries" if i in (4, 5) else "CrateMir"
    with open(sh_file, "w") as f:
      f.write(
          HEADER
          + f"import {imp}\n\nopen Trusted Theory\n\n"
          + fn_snippets[i]
      )
    shard_elab_ms[i] = compile_lean(sh_file, sh_olean)
    shard_olean_bytes[i] = os.path.getsize(sh_olean)

  root_mod = "Stage4_Root"
  root_file = os.path.join(WORKDIR, f"{root_mod}.lean")
  root_olean = os.path.join(WORKDIR, f"{root_mod}.olean")
  imports_str = "\n".join(f"import Stage4_Shard_{i}" for i in range(10))
  with open(root_file, "w") as f:
    f.write(
        HEADER
        + f"""{imports_str}

open Trusted Theory

theorem verify_crate10 : CrateTheorem crate10 :=
  verify_crate_of_shards π_id_mono {shards_cons}
"""
    )
  elab_root = compile_lean(root_file, root_olean)
  root_olean_bytes = os.path.getsize(root_olean)

  # Build Stage4_Base_i for each i in 0..9 (importing CrateMir, Stage4_CalleeSummaries, and all Stage4_Shard_j for j != i)
  for i in range(10):
    base_i_mod = f"Stage4_Base_{i}"
    base_i_file = os.path.join(WORKDIR, f"{base_i_mod}.lean")
    base_i_olean = os.path.join(WORKDIR, f"{base_i_mod}.olean")
    other_imps = "\n".join(
        f"import Stage4_Shard_{j}" for j in range(10) if j != i
    )
    with open(base_i_file, "w") as f:
      f.write(
          HEADER
          + f"import Stage4_CalleeSummaries\n{other_imps}\n"
      )
    compile_lean(base_i_file, base_i_olean)

  return (
      elab_s3,
      os.path.getsize(s3_olean),
      shard_elab_ms,
      shard_olean_bytes,
      elab_root,
      root_olean_bytes,
  )


def run_negative_canaries():
  """Generates and tests 5 negative `.lean` files that MUST fail compilation (Task 2)."""
  canaries = [
      (
          "NegativeCanary1_Overflow.lean",
          """import UnifiedEndToEndStack
open Trusted Theory

def badBody1 : List Instr := [.addCheckedImm .r0 .r0 0xFFFFFFFFFFFFFFFF#64, .assertNotFlag]

theorem false_overflow_verified (q : BranchEnv) :
    Reach [] q (entryState badBody1) 6#64 :=
  evalCvProg_sound [] q badBody1 6#64 rfl
""",
      ),
      (
          "NegativeCanary2_SideCondOverlap.lean",
          """import UnifiedEndToEndStack
open Trusted Theory

theorem false_overlapping_intervals :
    AllSideCondsHold [.disjoint 100 16 115 16] :=
  checkSideCondBatch_sound rfl
""",
      ),
      (
          "NegativeCanary3_CalleePrecond.lean",
          """import CrateMir
open Trusted Theory

def badCaller : List Instr := [.call "core::num::usize::checked_add"]
def sOverflow : State := ⟨badCaller, 0, 0xFFFFFFFFFFFFFFFD#64, 0#64, 0#64, 0#64, false, []⟩
def sAfterBad : State := ⟨badCaller, 1, 0#64, 0#64, 0#64, 0#64, false, []⟩

theorem false_callee_summary_step (q : BranchEnv) :
    SuffixReach crateProg q badCaller sOverflow 0#64 :=
  call_summary_flat_step
    (mkCoreCalleeBody_summary crateProg "core::num::usize::checked_add" 4#64 12#64 rfl)
    [] sOverflow sAfterBad 0#64 rfl (SuffixReach.nil sAfterBad rfl)
""",
      ),
      (
          "NegativeCanary4_BrokenMirLangCall.lean",
          """import CrateMir
open Trusted Theory

theorem false_broken_mirlang_call :
    evalStep [("__entry", body_f4)] defaultBranchEnv (entryState body_f4) =
      .step (entryState body_f4) := rfl
""",
      ),
      (
          "NegativeCanary5_DivergentDiamond.lean",
          """import UnifiedEndToEndStack
open Trusted Theory

def badDiamond : List Instr := [.selectImm 0 .r0 10#64 11#64]
def s0Bad : State := entryState badDiamond
def sJoinBad : State := ⟨badDiamond, 1, 10#64, 0#64, 3#64, 0#64, false, []⟩

theorem false_divergent_diamond (q : BranchEnv) :
    SuffixReach [] q (badDiamond ++ []) s0Bad 10#64 :=
  diamond_converge_step [] q 0 badDiamond [] s0Bad sJoinBad 10#64 rfl rfl
    (SuffixReach.nil sJoinBad rfl)
""",
      ),
  ]

  canary_results = []
  for fname, content in canaries:
    fpath = os.path.join(WORKDIR, fname)
    opath = os.path.join(WORKDIR, fname.replace(".lean", ".olean"))
    with open(fpath, "w") as f:
      f.write(HEADER + content)
    res = compile_lean_expect_failure(fpath, opath)
    canary_results.append(res)
    print(
        f"Negative Canary {fname:38s} | Failed as expected"
        f" (rc={res['returncode']}, {res['time_ms']} ms)",
        flush=True,
    )
  return canary_results


def main():
  data = build_crate_data()

  # Ensure UnifiedEndToEndStack and Stage0_FoundationBase are compiled and timed
  fbase_path = os.path.join(WORKDIR, "Stage0_FoundationBase.lean")
  if not os.path.exists(fbase_path):
    with open(fbase_path, "w") as f:
      f.write(
          HEADER
          + "\nimport Init.Data.BitVec.Basic\nimport Init.Data.Nat.Bitwise.Lemmas\n"
      )
  t_theory_elab = compile_lean(
      os.path.join(WORKDIR, "UnifiedEndToEndStack.lean"),
      os.path.join(WORKDIR, "UnifiedEndToEndStack.olean"),
  )
  compile_lean(
      os.path.join(WORKDIR, "Stage0_FoundationBase.lean"),
      os.path.join(WORKDIR, "Stage0_FoundationBase.olean"),
  )
  t_mir_elab = time.perf_counter()
  generate_crate_mir(data)
  t_mir_elab = (time.perf_counter() - t_mir_elab) * 1000.0

  theory_olean_bytes = os.path.getsize(
      os.path.join(WORKDIR, "UnifiedEndToEndStack.olean")
  )
  mir_olean_bytes = os.path.getsize(os.path.join(WORKDIR, "CrateMir.olean"))

  elab_s0, olean_s0 = generate_stage0_and_stage1_proof(data)
  elab_s2, olean_s2 = generate_stage2_proof(data)
  (
      elab_s3,
      olean_s3,
      shard_elab_ms,
      shard_olean_bytes,
      elab_root,
      root_olean_bytes,
  ) = generate_stage3_and_stage4_proofs(data)

  # Measure Stage 0: Base = Stage0_FoundationBase, Target = Stage0_Proof (replays UnifiedEndToEndStack + CrateMir + Stage0_Proof)
  km_s0 = measure_kernel_batch("Stage0_FoundationBase", ["Stage0_Proof"])[
      "Stage0_Proof"
  ]

  # Measure Stage 1, Stage 2, Stage 3: Base = UnifiedEndToEndStack, Target = Stage0_Proof, Stage2_Proof, Stage3_Proof (replays CrateMir + Proof)
  km_s123 = measure_kernel_batch(
      "UnifiedEndToEndStack", ["Stage0_Proof", "Stage2_Proof", "Stage3_Proof"]
  )
  km_s1 = km_s123["Stage0_Proof"]
  km_s2 = km_s123["Stage2_Proof"]
  km_s3 = km_s123["Stage3_Proof"]

  # Measure Stage 4 across all 10 modified functions (Base = Stage4_Base_i, Target = Stage4_Root, replaying Stage4_Shard_i + Stage4_Root)
  s4_per_shard = []
  for i in range(10):
    km_i = measure_kernel_batch(f"Stage4_Base_{i}", ["Stage4_Root"])[
        "Stage4_Root"
    ]
    row_i = {
        "shard_idx": i,
        "fn_name": data["fn_names"][i],
        "elab_ms": round(shard_elab_ms[i] + elab_root, 2),
        "shard_elab_ms": round(shard_elab_ms[i], 2),
        "root_elab_ms": round(elab_root, 2),
        "replay_ms": km_i["replay_ms"],
        "replay_us": km_i["replay_us"],
        "olean_bytes": shard_olean_bytes[i] + root_olean_bytes,
        "shard_olean_bytes": shard_olean_bytes[i],
        "root_olean_bytes": root_olean_bytes,
        "decls": km_i["decls"],
        "dag_nodes": km_i["dag_nodes"],
        "tree_nodes": km_i["tree_nodes"],
    }
    s4_per_shard.append(row_i)

  # Primary Stage 4 row: Shard 9 (the counted loop function) + Root CrateTheorem
  km_s4_primary = s4_per_shard[9]

  stages = [
      {
          "stage": "Stage 0 (Current Anneal Baseline: Theory in locals + Cont-Lambda + {s with} + Inlined Calls + omega + decide)",
          "short_label": "Stage 0 (Baseline)",
          "elab_ms": round(t_theory_elab + elab_s0, 2),
          "proof_only_elab_ms": round(elab_s0, 2),
          "replay_ms": km_s0["replay_ms"],
          "replay_us": km_s0["replay_us"],
          "olean_bytes": theory_olean_bytes + mir_olean_bytes + olean_s0,
          "proof_only_olean_bytes": olean_s0,
          "decls": km_s0["decls"],
          "dag_nodes": km_s0["dag_nodes"],
          "tree_nodes": km_s0["tree_nodes"],
          "proof_mod_decls": km_s0["mod_decls"],
          "proof_mod_dag_nodes": km_s0["mod_dag_nodes"],
          "proof_mod_tree_nodes": km_s0["mod_tree_nodes"],
      },
      {
          "stage": "Stage 1 (+ Two-Stage Pre-Audited Theory in base; Mir + Stage 0 Proof replayed)",
          "short_label": "Stage 1 (+ Pre-Audited Theory in base)",
          "elab_ms": round(elab_s0, 2),
          "proof_only_elab_ms": round(elab_s0, 2),
          "replay_ms": km_s1["replay_ms"],
          "replay_us": km_s1["replay_us"],
          "olean_bytes": mir_olean_bytes + olean_s0,
          "proof_only_olean_bytes": olean_s0,
          "decls": km_s1["decls"],
          "dag_nodes": km_s1["dag_nodes"],
          "tree_nodes": km_s1["tree_nodes"],
          "proof_mod_decls": km_s1["mod_decls"],
          "proof_mod_dag_nodes": km_s1["mod_dag_nodes"],
          "proof_mod_tree_nodes": km_s1["mod_tree_nodes"],
      },
      {
          "stage": "Stage 2 (+ Flat-Tuple State.casesOn + Contiguous let-Sharing + Structural .tail/.head TCB + Batch Side-Cond rfl)",
          "short_label": "Stage 2 (+ Flat-Tuple, let-Share, Structural TCB, Side-Cond rfl)",
          "elab_ms": round(elab_s2, 2),
          "proof_only_elab_ms": round(elab_s2, 2),
          "replay_ms": km_s2["replay_ms"],
          "replay_us": km_s2["replay_us"],
          "olean_bytes": mir_olean_bytes + olean_s2,
          "proof_only_olean_bytes": olean_s2,
          "decls": km_s2["decls"],
          "dag_nodes": km_s2["dag_nodes"],
          "tree_nodes": km_s2["tree_nodes"],
          "proof_mod_decls": km_s2["mod_decls"],
          "proof_mod_dag_nodes": km_s2["mod_dag_nodes"],
          "proof_mod_tree_nodes": km_s2["mod_tree_nodes"],
      },
      {
          "stage": "Stage 3 (+ 3-Layer Hybrid Theory Validators: cv_trans Nat rfl + IdiomPlan + diamond_converge_step + CalleeSummary + loop_summary_sound)",
          "short_label": "Stage 3 (+ 3-Layer Hybrid Theory Validators)",
          "elab_ms": round(elab_s3, 2),
          "proof_only_elab_ms": round(elab_s3, 2),
          "replay_ms": km_s3["replay_ms"],
          "replay_us": km_s3["replay_us"],
          "olean_bytes": mir_olean_bytes + olean_s3,
          "proof_only_olean_bytes": olean_s3,
          "decls": km_s3["decls"],
          "dag_nodes": km_s3["dag_nodes"],
          "tree_nodes": km_s3["tree_nodes"],
          "proof_mod_decls": km_s3["mod_decls"],
          "proof_mod_dag_nodes": km_s3["mod_dag_nodes"],
          "proof_mod_tree_nodes": km_s3["mod_tree_nodes"],
      },
      {
          "stage": "Stage 4 (+ Per-Function ShardCert Incremental Sharding: 9/10 Unchanged Shards in base, 1 Modified Shard + Root CrateTheorem)",
          "short_label": "Stage 4 (+ Incremental 1/10 ShardCert + Root)",
          "elab_ms": km_s4_primary["elab_ms"],
          "proof_only_elab_ms": km_s4_primary["elab_ms"],
          "replay_ms": km_s4_primary["replay_ms"],
          "replay_us": km_s4_primary["replay_us"],
          "olean_bytes": km_s4_primary["olean_bytes"],
          "proof_only_olean_bytes": km_s4_primary["olean_bytes"],
          "decls": km_s4_primary["decls"],
          "dag_nodes": km_s4_primary["dag_nodes"],
          "tree_nodes": km_s4_primary["tree_nodes"],
          "proof_mod_decls": km_s4_primary["decls"],
          "proof_mod_dag_nodes": km_s4_primary["dag_nodes"],
          "proof_mod_tree_nodes": km_s4_primary["tree_nodes"],
      },
  ]

  base_replay_us = stages[0]["replay_us"]
  base_elab_ms = stages[0]["elab_ms"]
  base_dag = stages[0]["dag_nodes"]
  base_tree = stages[0]["tree_nodes"]
  base_olean = stages[0]["olean_bytes"]

  print("\n=== UNIFIED 5-STAGE END-TO-END BENCHMARK RESULTS ===")
  for st in stages:
    st["replay_speedup_vs_s0"] = round(base_replay_us / st["replay_us"], 2)
    st["elab_speedup_vs_s0"] = round(base_elab_ms / st["elab_ms"], 2)
    st["dag_reduction_vs_s0"] = round(base_dag / st["dag_nodes"], 2)
    st["tree_reduction_vs_s0"] = round(base_tree / st["tree_nodes"], 2)
    st["olean_reduction_vs_s0"] = round(base_olean / st["olean_bytes"], 2)
    print(
        f"{st['short_label']:58s} | elab={st['elab_ms']:7.1f}ms"
        f" ({st['elab_speedup_vs_s0']:6.2f}x) | replay={st['replay_ms']:8.3f}ms"
        f" ({st['replay_speedup_vs_s0']:7.2f}x) | olean={st['olean_bytes']:8d}B"
        f" | DECLS={st['decls']:4d} | DAG={st['dag_nodes']:6d} |"
        f" TREE={st['tree_nodes']:10d}",
        flush=True,
    )

  print("\n=== STAGE 4 PER-SHARD INCREMENTAL REPLAY BREAKDOWN (SHARDS 0..9) ===")
  for row in s4_per_shard:
    sp = round(base_replay_us / row["replay_us"], 2)
    print(
        f"Shard {row['shard_idx']} ({row['fn_name']:46s}) |"
        f" elab={row['elab_ms']:6.1f}ms | replay={row['replay_ms']:6.3f}ms"
        f" ({row['replay_us']:4d}us, {sp:7.2f}x vs S0) |"
        f" olean={row['olean_bytes']:6d}B | DECLS={row['decls']:2d} |"
        f" DAG={row['dag_nodes']:4d} | TREE={row['tree_nodes']:5d}",
        flush=True,
    )

  print("\n=== NEGATIVE SOUNDNESS CANARIES (COMPILATION REJECTION TESTS) ===")
  canary_results = run_negative_canaries()

  out_json = os.path.join(WORKDIR, "unified_benchmark_results.json")
  with open(out_json, "w") as f:
    json.dump(
        {
            "stages": stages,
            "stage4_per_shard": s4_per_shard,
            "negative_canaries": canary_results,
        },
        f,
        indent=2,
    )
  print(f"\nSaved full benchmark results to {out_json}", flush=True)


if __name__ == "__main__":
  main()
