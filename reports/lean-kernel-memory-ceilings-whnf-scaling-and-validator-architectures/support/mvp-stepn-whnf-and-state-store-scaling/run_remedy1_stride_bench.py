#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Benchmark Q-C1 Remedy 1: Coarse multi-step witness strides B in {1, 2, 4, 6, 8}
(both unforced stepN and CPS spine-forced stepN/runForced) on Starnix
apply_endianness with zero changes to Trusted.Mvp.Semantics."""

import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HOME = Path.home()
TOOLCHAIN_BIN = (
    HOME
    / ".cache/anneal/toolchain"
    / "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a/lean/bin"
)
LEAN = str(TOOLCHAIN_BIN / "lean")
BRAIN_ROOT = HOME / "<scratch-dir>"
STAGE_SRC = BRAIN_ROOT / "scratch/mvp-investigations/task3/profile_stage"
TRACK_C_DIR = BRAIN_ROOT / "scratch/reference-research/track_c"
WORK_DIR = TRACK_C_DIR / "remedy1_stage"

HEADER = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""

STRIDE_HELPERS = """private def stepN : Nat → Body → State → Option State
  | 0, _, s => some s
  | n + 1, body, s =>
      match step body s with
      | .next s' => stepN n body s'
      | _ => none

private theorem stepN_executes :
    ∀ {n : Nat} {body : Body} {s s' : State} {retVal : Word},
      stepN n body s = some s' →
      Executes body s' retVal →
      Executes body s retVal
  | 0, _, _, _, _, h, exec => by
      injection h with h'
      subst h'
      exact exec
  | n + 1, body, s, s', retVal, h, exec => by
      unfold stepN at h
      cases hStep : step body s with
      | next mid =>
          rw [hStep] at h
          exact .next hStep (stepN_executes h exec)
      | ret _ =>
          rw [hStep] at h
          contradiction
      | fault _ =>
          rw [hStep] at h
          contradiction

"""

FORCED_HELPERS = """private def forceList (xs : List Slot) (k : List Slot → α) : α :=
  match xs with
  | [] => k []
  | a :: as => forceList as (fun as' => k (a :: as'))

private theorem forceList_eq (xs : List Slot) (k : List Slot → α) :
    forceList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons a as ih => exact ih (fun as' => k (a :: as'))

private def forceNat (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => forceNat m (fun m' => k (m' + 1))

private theorem forceNat_eq (n : Nat) (k : Nat → α) :
    forceNat n k = k n := by
  induction n generalizing k with
  | zero => rfl
  | succ m ih => exact ih (fun m' => k (m' + 1))

private def forceState (s : State) (k : State → α) : α :=
  forceNat s.block (fun b =>
    forceNat s.statement (fun st =>
      forceList s.locals (fun locs =>
        k ⟨b, st, locs⟩)))

private theorem forceState_eq (s : State) (k : State → α) :
    forceState s k = k s := by
  unfold forceState
  rw [forceNat_eq, forceNat_eq, forceList_eq]

private def stepNForced : Nat → Body → State → Option State
  | 0, _, s => some s
  | n + 1, body, s =>
      match step body s with
      | .next s' => forceState s' (stepNForced n body)
      | _ => none

private theorem stepNForced_executes :
    ∀ {n : Nat} {body : Body} {s s' : State} {retVal : Word},
      stepNForced n body s = some s' →
      Executes body s' retVal →
      Executes body s retVal
  | 0, _, _, _, _, h, exec => by
      injection h with h'
      subst h'
      exact exec
  | n + 1, body, s, s', retVal, h, exec => by
      unfold stepNForced at h
      cases hStep : step body s with
      | next mid =>
          rw [hStep] at h
          dsimp only at h
          rw [forceState_eq] at h
          exact .next hStep (stepNForced_executes h exec)
      | ret _ =>
          rw [hStep] at h
          contradiction
      | fault _ =>
          rw [hStep] at h
          contradiction

private def runForced (body : Body) : Nat → State → Option Word
  | 0, _ => none
  | fuel + 1, state =>
      match step body state with
      | .next nextState => forceState nextState (runForced body fuel)
      | .ret value => some value
      | .fault _ => none

private theorem runForced_executes :
    ∀ {body : Body} {fuel : Nat} {start : State} {value : Word},
      runForced body fuel start = some value →
      Executes body start value
  | _, 0, _, _, h => by contradiction
  | body, fuel + 1, start, value, h => by
      unfold runForced at h
      cases hStep : step body start with
      | next nextState =>
          rw [hStep] at h
          dsimp only at h
          rw [forceState_eq] at h
          exact .next hStep (runForced_executes h)
      | ret retVal =>
          rw [hStep] at h
          injection h with hEq
          subst hEq
          exact .ret hStep
      | fault _ =>
          rw [hStep] at h
          contradiction

"""


def trace_path(body, flag, width):
  markers = set()
  for block in body["blocks"]:
    for stmt in block["statements"]:
      if stmt["kind"] in ("storage_live", "storage_dead"):
        markers.add(stmt["local"])
  locals_ = [
      ("dead" if i in markers else "uninit", None)
      for i in range(len(body["local_tys"]))
  ]
  locals_[1:4] = [
      ("value", (str(flag), flag)),
      ("value", (str(width), width)),
      ("value", ("value", None)),
  ]
  block = position = 0
  states = []

  def operand(op):
    kind = op["kind"]
    if kind == "constant":
      return str(op["bits"]), op["bits"]
    index = op["local"]
    assert locals_[index][0] == "value", (index, locals_[index])
    value = locals_[index][1]
    if kind == "move":
      locals_[index] = ("uninit", None)
    else:
      assert kind == "copy"
    return value

  def rvalue(rv):
    kind = rv["kind"]
    if kind == "use":
      return operand(rv["operand"])
    if kind == "discriminant":
      index = rv["local"]
      assert locals_[index][0] == "value"
      value = locals_[index][1][1]
      table = body["local_tys"][index]["discriminants"]
      return str(table[value]), table[value]
    assert kind == "binary"
    left, _ = operand(rv["left"])
    right, right_known = operand(rv["right"])
    op = rv["op"]
    if op == "bit_and":
      return f"({left} &&& {right})", None
    if op == "bit_or":
      return f"({left} ||| {right})", None
    assert op in ("shl", "shr") and right_known is not None
    amount = right_known % 64
    operator = "<<<" if op == "shl" else ">>>"
    return f"({left} {operator} ({amount} : Nat))", None

  while True:
    states.append((block, position, copy.deepcopy(locals_)))
    current = body["blocks"][block]
    if position < len(current["statements"]):
      stmt = current["statements"][position]
      kind = stmt["kind"]
      if kind == "assign":
        result = rvalue(stmt["value"])
        locals_[stmt["local"]] = ("value", result)
      elif kind == "storage_live":
        locals_[stmt["local"]] = ("uninit", None)
      elif kind == "storage_dead":
        locals_[stmt["local"]] = ("dead", None)
      else:
        assert kind == "nop"
      position += 1
      continue
    term = current["terminator"]
    if term["kind"] == "ret":
      break
    if term["kind"] == "goto":
      block = term["block"]
    else:
      assert term["kind"] == "switch_int"
      _, key = operand(term["operand"])
      assert key is not None
      block = dict(term["targets"]).get(key, term["otherwise"])
    position = 0

  label = ("be" if flag else "le") + str(8 << width)
  if flag:
    output = f"swap{8 << width} value"
  elif width == 3:
    output = "value"
  else:
    output = f"value &&& {(1 << (8 << width)) - 1}"
  return label, output, states


def format_state_def(label, idx, b, p, slots):
  source = f"private def {label}_state{idx} (value : Word) : State :=\n  ⟨{b}, {p}, [\n"
  terms = [f".value {x[1][0]}" if x[0] == "value" else "." + x[0] for x in slots]
  for j in range(0, len(terms), 5):
    source += "    " + ", ".join(terms[j : j + 5])
    if j + 5 < len(terms):
      source += ","
    source += "\n"
  source += "  ]⟩\n\n"
  return source


def generate_module(body, stride, forced=False):
  parts = []
  total_states = 0
  total_suffix_theorems = 0
  for flag in (0, 1):
    for width in range(4):
      label, output, states = trace_path(body, flag, width)
      last = len(states) - 1
      if stride == 1 and not forced:
        # Exact baseline B=1
        source = ""
        for i, (b, p, slots) in enumerate(states):
          source += format_state_def(label, i, b, p, slots)
          total_states += 1
        source += f"""private theorem {label}_suffix{last} (value : Word) :
    Executes sourceBody ({label}_state{last} value) ({output}) :=
  .ret (by rfl)

"""
        total_suffix_theorems += 1
        for i in range(last - 1, -1, -1):
          source += f"""private theorem {label}_suffix{i} (value : Word) :
    Executes sourceBody ({label}_state{i} value) ({output}) :=
  .next (by rfl) ({label}_suffix{i + 1} value)

"""
          total_suffix_theorems += 1
        source += f"""theorem {label} (value : Word) :
    Safe sourceBody [{flag}, {width}, value] ∧
      Returns sourceBody [{flag}, {width}, value] ({output}) := by
  have start : initial sourceBody [{flag}, {width}, value] =
      {label}_state0 value := by rfl
  have execution : Executes sourceBody
      (initial sourceBody [{flag}, {width}, value]) ({output}) := by
    rw [start]
    exact {label}_suffix0 value
  exact ⟨executes_safe execution, executes_returns execution⟩

"""
        parts.append(source)
      elif stride == "whole":
        # Emit only state0 + path theorem using runForced_executes
        b0, p0, slots0 = states[0]
        source = format_state_def(label, 0, b0, p0, slots0)
        total_states += 1
        fuel = len(states)
        source += f"""set_option maxRecDepth 100000 in
theorem {label} (value : Word) :
    Safe sourceBody [{flag}, {width}, value] ∧
      Returns sourceBody [{flag}, {width}, value] ({output}) := by
  have start : initial sourceBody [{flag}, {width}, value] =
      {label}_state0 value := by rfl
  have execution : Executes sourceBody
      (initial sourceBody [{flag}, {width}, value]) ({output}) := by
    rw [start]
    exact runForced_executes (body := sourceBody) (fuel := {fuel})
      (start := {label}_state0 value) (value := ({output})) rfl
  exact ⟨executes_safe execution, executes_returns execution⟩

"""
        parts.append(source)
      else:
        checkpoints = list(range(0, len(states), stride))
        source = ""
        for idx in checkpoints:
          b, p, slots = states[idx]
          source += format_state_def(label, idx, b, p, slots)
          total_states += 1
        c_last = checkpoints[-1]
        rem_fuel = (last - c_last) + 1
        run_thm = "runForced_executes" if forced else "run_executes"
        step_thm = "stepNForced_executes" if forced else "stepN_executes"
        opt_prefix = "set_option maxRecDepth 100000 in\n" if forced else ""
        source += f"""{opt_prefix}private theorem {label}_suffix{c_last} (value : Word) :
    Executes sourceBody ({label}_state{c_last} value) ({output}) :=
  {run_thm} (body := sourceBody) (fuel := {rem_fuel})
    (start := {label}_state{c_last} value) (value := ({output})) rfl

"""
        total_suffix_theorems += 1
        for k in range(len(checkpoints) - 2, -1, -1):
          c_curr = checkpoints[k]
          c_next = checkpoints[k + 1]
          step_cnt = c_next - c_curr
          source += f"""{opt_prefix}private theorem {label}_suffix{c_curr} (value : Word) :
    Executes sourceBody ({label}_state{c_curr} value) ({output}) :=
  {step_thm} (n := {step_cnt}) (by rfl) ({label}_suffix{c_next} value)

"""
          total_suffix_theorems += 1
        source += f"""theorem {label} (value : Word) :
    Safe sourceBody [{flag}, {width}, value] ∧
      Returns sourceBody [{flag}, {width}, value] ({output}) := by
  have start : initial sourceBody [{flag}, {width}, value] =
      {label}_state0 value := by rfl
  have execution : Executes sourceBody
      (initial sourceBody [{flag}, {width}, value]) ({output}) := by
    rw [start]
    exact {label}_suffix0 value
  exact ⟨executes_safe execution, executes_returns execution⟩

"""
        parts.append(source)

  prelude_block = """prelude
import InitialCache

namespace ProductionSteps

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

"""
  if forced or stride == "whole":
    helper_block = FORCED_HELPERS
  elif stride == 1:
    helper_block = ""
  else:
    helper_block = STRIDE_HELPERS

  full_text = HEADER + prelude_block + helper_block + "".join(parts) + "end ProductionSteps\n"
  return full_text, total_states, total_suffix_theorems


def setup_work_dir():
  if WORK_DIR.exists():
    shutil.rmtree(WORK_DIR)
  WORK_DIR.mkdir(parents=True)
  shutil.copytree(STAGE_SRC / "target-lib", WORK_DIR / "target-lib")
  shutil.copytree(STAGE_SRC / "target-src", WORK_DIR / "target-src")
  shutil.copytree(STAGE_SRC / "capture", WORK_DIR / "capture")
  for p in STAGE_SRC.glob("*.setup.json"):
    txt = p.read_text().replace(str(STAGE_SRC), str(WORK_DIR))
    (WORK_DIR / p.name).write_text(txt)
  for name in ["request-target-audit.json", "TrustedBoundaryInstrumented.lean"]:
    txt = (STAGE_SRC / name).read_text().replace(str(STAGE_SRC), str(WORK_DIR))
    (WORK_DIR / name).write_text(txt)


def run_timed_cmd(cmd, cwd):
  wrapped = [
      "/usr/bin/time",
      "-f",
      "TIME_ELAPSED=%e TIME_RSS_KB=%M",
      "anneal-lean-run",
      "--mode",
      "file",
      "--concurrency",
      "4",
      "--",
  ] + cmd
  t0 = time.perf_counter()
  proc = subprocess.run(
      wrapped, cwd=cwd, capture_output=True, text=True, check=False
  )
  wall_s = time.perf_counter() - t0
  m_rss = re.search(r"TIME_RSS_KB=(\d+)", proc.stderr)
  rss_kb = int(m_rss.group(1)) if m_rss else 0
  return proc.returncode, wall_s, rss_kb, proc.stdout, proc.stderr


def main():
  setup_work_dir()
  capture_json = json.loads((WORK_DIR / "capture" / "capture.json").read_text())
  body = capture_json["program"]["bodies"][0]

  configs = [
      {"stride": 1, "forced": False, "label": "B=1 (baseline)"},
      {"stride": 2, "forced": False, "label": "B=2 (unforced stepN)"},
      {"stride": 4, "forced": False, "label": "B=4 (unforced stepN)"},
      {"stride": 6, "forced": False, "label": "B=6 (unforced stepN)"},
      {"stride": 8, "forced": False, "label": "B=8 (unforced stepN)"},
      {"stride": 8, "forced": True, "label": "B=8 (CPS spine-forced stepN)"},
      {"stride": "whole", "forced": True, "label": "B=whole (CPS spine-forced runForced)"},
  ]
  out_file = TRACK_C_DIR / "remedy1_stride_bench.json"
  existing_by_label = {}
  if out_file.exists():
    for r in json.loads(out_file.read_text()).get("results", []):
      if not r.get("forced", False):
        existing_by_label[r["label"]] = r

  results = []

  for cfg in configs:
    stride = cfg["stride"]
    forced = cfg["forced"]
    label = cfg["label"]
    if label in existing_by_label:
      print(f"=== Reusing cached {label} ===", flush=True)
      results.append(existing_by_label[label])
      continue
    print(f"=== Testing {label} ===", flush=True)
    lean_text, num_states, num_suffixes = generate_module(body, stride, forced)
    prod_steps_lean = WORK_DIR / "target-src" / "ProductionSteps.lean"
    prod_steps_olean = WORK_DIR / "target-lib" / "ProductionSteps.olean"
    prod_steps_lean.write_text(lean_text)
    line_count = len(lean_text.splitlines())

    # 1. Compile ProductionSteps.lean
    rc, comp_s, comp_rss_kb, out, err = run_timed_cmd(
        [
            LEAN,
            "--setup",
            str(WORK_DIR / "ProductionSteps.setup.json"),
            "-o",
            str(prod_steps_olean),
            str(prod_steps_lean),
        ],
        cwd=WORK_DIR,
    )
    if rc != 0:
      print(f"{label} failed compilation:\n{out}\n{err}")
      results.append({
          "label": label,
          "stride": stride,
          "forced": forced,
          "status": "compile_failed",
          "lines": line_count,
          "state_defs": num_states,
          "suffix_theorems": num_suffixes,
          "compile_wall_s": round(comp_s, 4),
          "compile_peak_rss_kb": comp_rss_kb,
      })
      continue

    olean_bytes = prod_steps_olean.stat().st_size

    # 2. Recompile ProductionClaims.lean and Proof.lean
    for mod in ["ProductionClaims", "Proof"]:
      rc_m, _, _, out_m, err_m = run_timed_cmd(
          [
              LEAN,
              "--setup",
              str(WORK_DIR / f"{mod}.setup.json"),
              "-o",
              str(WORK_DIR / "target-lib" / f"{mod}.olean"),
              str(WORK_DIR / "target-src" / f"{mod}.lean"),
          ],
          cwd=WORK_DIR,
      )
      assert rc_m == 0, f"Failed {mod}: {out_m} {err_m}"

    # 3. Run TrustedBoundaryInstrumented.lean target-audit
    res_json_path = WORK_DIR / f"result_B_{stride}_{forced}.json"
    rc_a, audit_s, audit_rss_kb, out_a, err_a = run_timed_cmd(
        [
            LEAN,
            "-j1",
            "-M2048",
            "--run",
            str(WORK_DIR / "TrustedBoundaryInstrumented.lean"),
            str(WORK_DIR / "request-target-audit.json"),
            str(res_json_path),
        ],
        cwd=WORK_DIR,
    )
    assert rc_a == 0, f"Audit failed for {label}: {out_a} {err_a}"
    audit_res = json.loads(res_json_path.read_text())
    assert audit_res["ok"] is True

    inst = audit_res["result"]["instrumentedTimings"]
    ps_mod_stats = None
    for m in inst.get("perModuleReplay", []):
      if m["module"] == "ProductionSteps":
        ps_mod_stats = m
        break

    row = {
        "label": label,
        "stride": stride,
        "forced": forced,
        "status": "ok",
        "lines": line_count,
        "state_defs": num_states,
        "suffix_theorems": num_suffixes,
        "path_theorems": 8,
        "production_steps_total_module_decls": (
            ps_mod_stats["totalModuleDecls"] if ps_mod_stats else None
        ),
        "production_steps_replayed_decls": (
            ps_mod_stats["replayedDecls"] if ps_mod_stats else None
        ),
        "production_steps_replay_ms": (
            round(ps_mod_stats["replayNanos"] / 1e6, 2) if ps_mod_stats else None
        ),
        "olean_bytes": olean_bytes,
        "compile_wall_s": round(comp_s, 4),
        "compile_peak_rss_kb": comp_rss_kb,
        "kernel_replay_all_ms": round(inst["kernelReplayAllNanos"] / 1e6, 2),
        "total_replayed_declarations": audit_res["result"]["replayedDeclarations"],
        "total_audit_body_ms": round(inst["totalTargetAuditBodyNanos"] / 1e6, 2),
        "total_audit_wall_s": round(audit_s, 4),
        "total_audit_peak_rss_kb": audit_rss_kb,
    }
    print(json.dumps(row, indent=2), flush=True)
    results.append(row)

  out_file = TRACK_C_DIR / "remedy1_stride_bench.json"
  out_file.write_text(
      json.dumps(
          {
              "benchmark": "Q-C1_Remedy1_ProductionSteps_Stride",
              "lean_version": "4.34.1",
              "target": "Starnix apply_endianness (8 paths, 246 total steps)",
              "results": results,
          },
          indent=2,
      )
      + "\n"
  )
  print(f"Saved results to {out_file}")


if __name__ == "__main__":
  main()
