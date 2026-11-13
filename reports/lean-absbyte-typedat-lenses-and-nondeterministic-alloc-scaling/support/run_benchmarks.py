#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Single-pass microsecond-accurate benchmark runner for MemoryLensAndScalingProbe.lean."""

import json
import os
import shutil
import subprocess
import time
from pathlib import Path

SUPPORT_DIR = Path(__file__).resolve().parent
PROBE_PATH = SUPPORT_DIR / "MemoryLensAndScalingProbe.lean"
ANNEAL_LEAN_RUN = os.environ.get(
    "ANNEAL_LEAN_RUN", shutil.which("anneal-lean-run") or "anneal-lean-run"
)

LEAN_V428 = os.environ.get("LEAN_V428", "lean")
LEAN_V434 = os.environ.get(
    "LEAN_V434",
    str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"),
)


def stamp(tag: str) -> str:
  return f'#eval show IO Unit from do let t ← IO.monoNanosNow; IO.println s!"STAMP:{tag}:{{t}}"\n'


def gen_sched_list(k: int) -> str:
  pairs = []
  for i in range(k):
    rem = (k - 1 - i) % 3
    if rem == 0:
      pairs.append("(x, y)")
    elif rem == 1:
      pairs.append("(y, z)")
    else:
      pairs.append("(z, x)")
  return "[" + ", ".join(pairs) + "]"


def build_benchmark_lean_source() -> str:
  text = PROBE_PATH.read_text()
  marker = "/-- Unrolled 15-step symbolic mutation proof"
  prefix = text[: text.index(marker)]

  blocks = [prefix]
  blocks.append("""
theorem packU32_extract_simp (v : UInt32) :
    packU32 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v := by
  have h0 : (v >>> 0).toUInt8 = v.toUInt8 := by simp
  rw [← h0]
  exact packU32_extract v
""")

  # 1. Approach B (loop / schedule engine) for K in [1, 2, 3, 4, 5, 10, 15, 20, 25, 30]
  for k in [1, 2, 3, 4, 5, 10, 15, 20, 25, 30]:
    name = f"approachB_loop_{k}"
    blocks.append(stamp(f"start_{name}"))
    blocks.append(f"""
set_option maxHeartbeats 200000 in
theorem {name} (x y z : UInt32) :
    let sched := mkSymbolicSchedule x y z {k}
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  obtain ⟨mem', h_run, _, h_r0, h_r1⟩ :=
    runPairMutSteps_spec sched (mkEntryMemory x y) x y (entryMemory_satisfies_PairMutInv x y)
  exact ⟨mem', h_run, h_r0, h_r1⟩
""")
    blocks.append(stamp(f"end_{name}"))

  # 2. Approach B (unrolled CPS step-by-step) for K in [1, 2, 3, 4, 5, 10, 15, 20, 25, 30]
  for k in [1, 2, 3, 4, 5, 10, 15, 20, 25, 30]:
    name = f"approachB_unrolled_{k}"
    sched_str = gen_sched_list(k)
    steps_code = "\n".join(
        f"  apply step_runPairMutSteps _ _ _ _ _ _ h{i-1}; intro m{i} h{i}"
        for i in range(1, k + 1)
    )
    blocks.append(stamp(f"start_{name}"))
    blocks.append(f"""
set_option maxHeartbeats 200000 in
theorem {name} (x y z : UInt32) :
    let sched := {sched_str}
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  have h0 := entryMemory_satisfies_PairMutInv x y
{steps_code}
  exact finish_runPairMutSteps m{k} _ _ h{k}
""")
    blocks.append(stamp(f"end_{name}"))

  # 3. Approach A2 (Byte-list & BorrowTree unfolding WITH -UInt32.toUInt8_add, -UInt32.toUInt8_xor, packU32_extract_simp)
  for k in [1, 2, 3, 4, 5, 6, 8, 10]:
    name = f"approachA2_{k}"
    sched_str = gen_sched_list(k)
    blocks.append(stamp(f"start_{name}"))
    blocks.append(f"""
set_option maxHeartbeats 200000 in
theorem {name} (x y z : UInt32) :
    let sched := {sched_str}
    match runPairMutSteps (mkEntryMemory x y) sched with
    | none => False
    | some mem' =>
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  simp [-UInt32.toUInt8_add, -UInt32.toUInt8_xor,
    runPairMutSteps, stepPairMut, mkEntryMemory, entryBorrowTree8, entryProt, mutTag,
    pairAllocId, BorrowTree.performAccessRange, BorrowTree.findAncestors, findAncestorsNodes,
    updateNodeRange, mapOption, LocationState.performAccess, performPermAccess,
    childRead, childWrite, foreignRead, foreignWrite, nodeRel, hasTag,
    Memory.findAlloc, Memory.updateAlloc, findAllocList, updateAllocList,
    Memory.readTyped, Memory.writeTyped, u32Codec, encodeU32LE, decodeU32LE,
    readSlice, writeSlice, List.replicate, packU32_extract_simp, specPairSteps, specPairStep]
""")
    blocks.append(stamp(f"end_{name}"))

  # 4. Approach A1 (Default simp where UInt32.toUInt8_add breaks byte-0 roundtrip collapse -> O(4^K) AST blowup)
  for k in [1, 2, 3, 4]:
    name = f"approachA1_{k}"
    sched_str = gen_sched_list(k)
    blocks.append(stamp(f"start_{name}"))
    blocks.append(f"""
set_option maxHeartbeats 200000 in
theorem {name} (x y z : UInt32) :
    let sched := {sched_str}
    match runPairMutSteps (mkEntryMemory x y) sched with
    | none => False
    | some mem' =>
      mem'.readTyped pairAllocId 0 u32Codec = mem'.readTyped pairAllocId 0 u32Codec := by
  simp [runPairMutSteps, stepPairMut, mkEntryMemory, entryBorrowTree8, entryProt, mutTag,
    pairAllocId, BorrowTree.performAccessRange, BorrowTree.findAncestors, findAncestorsNodes,
    updateNodeRange, mapOption, LocationState.performAccess, performPermAccess,
    childRead, childWrite, foreignRead, foreignWrite, nodeRel, hasTag,
    Memory.findAlloc, Memory.updateAlloc, findAllocList, updateAllocList,
    Memory.readTyped, Memory.writeTyped, u32Codec, encodeU32LE, decodeU32LE,
    readSlice, writeSlice, List.replicate]
""")
    blocks.append(stamp(f"end_{name}"))

  # 5. N=10 nondeterministic stack allocations timing
  blocks.append(stamp("start_alloc10"))
  blocks.append("""
set_option maxHeartbeats 200000 in
theorem bench_alloc10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt32) :
    wpComp (alloc10AndCompute x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (fun res => res = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9) := by
  unfold alloc10AndCompute
  apply wp_stepAllocAndAccess [] 0 0 x0 _ _ (by decide) (by decide); intro as1 hb1
  apply wp_stepAllocAndAccess as1 1 32 x1 _ _ hb1 (by decide); intro as2 hb2
  apply wp_stepAllocAndAccess as2 2 64 x2 _ _ hb2 (by decide); intro as3 hb3
  apply wp_stepAllocAndAccess as3 3 96 x3 _ _ hb3 (by decide); intro as4 hb4
  apply wp_stepAllocAndAccess as4 4 128 x4 _ _ hb4 (by decide); intro as5 hb5
  apply wp_stepAllocAndAccess as5 5 160 x5 _ _ hb5 (by decide); intro as6 hb6
  apply wp_stepAllocAndAccess as6 6 192 x6 _ _ hb6 (by decide); intro as7 hb7
  apply wp_stepAllocAndAccess as7 7 224 x7 _ _ hb7 (by decide); intro as8 hb8
  apply wp_stepAllocAndAccess as8 8 256 x8 _ _ hb8 (by decide); intro as9 hb9
  apply wp_stepAllocAndAccess as9 9 288 x9 _ _ hb9 (by decide); intro _as10 _hb10
  rfl
""")
  blocks.append(stamp("end_alloc10"))
  blocks.append("\nend MemoryLensAndScalingProbe\n")
  return "".join(blocks)


def run_pass(lean_bin: str, file_path: Path, extra_args: list[str] | None = None) -> dict:
  cmd = [
      "/usr/bin/time",
      "-f",
      "TIME_STAT wall=%e user=%U sys=%S rss_kb=%M",
      ANNEAL_LEAN_RUN,
      "--mode",
      "file",
      "--concurrency",
      "4",
      "--",
      lean_bin,
      *(extra_args or []),
      str(file_path),
  ]
  t0 = time.monotonic()
  proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120.0, check=False)
  wall = time.monotonic() - t0
  stdout = proc.stdout or ""
  stderr = proc.stderr or ""
  user_s = None
  sys_s = None
  rss_kb = None
  for line in stderr.splitlines():
    if line.startswith("TIME_STAT "):
      parts = dict(kv.split("=") for kv in line.split()[1:])
      wall = float(parts["wall"])
      user_s = float(parts["user"])
      sys_s = float(parts["sys"])
      rss_kb = int(parts["rss_kb"])

  stamps = {}
  for line in stdout.splitlines():
    if line.startswith("STAMP:"):
      _, tag, ns_str = line.split(":")
      stamps[tag] = int(ns_str)

  durations_ms = {}
  for tag, start_ns in stamps.items():
    if tag.startswith("start_"):
      name = tag[len("start_") :]
      end_ns = stamps.get(f"end_{name}")
      if end_ns is not None:
        durations_ms[name] = round((end_ns - start_ns) / 1e6, 2)

  errors = [
      l for l in (stdout + "\n" + stderr).splitlines() if "error:" in l
  ]
  return {
      "rc": proc.returncode,
      "wall_s": round(wall, 3),
      "user_s": user_s,
      "sys_s": sys_s,
      "rss_mb": round(rss_kb / 1024.0, 1) if rss_kb is not None else None,
      "durations_ms": durations_ms,
      "errors": errors,
  }


def main() -> None:
  bench_file = SUPPORT_DIR / "_SinglePassBench.lean"
  bench_file.write_text(build_benchmark_lean_source())
  results = {"probe_full": {}, "single_pass_j1": {}}

  for label, lean_bin in [("v4.28.0-rc1", LEAN_V428), ("v4.34.1", LEAN_V434)]:
    print(f"=== Full MemoryLensAndScalingProbe.lean on {label} ===", flush=True)
    results["probe_full"][label] = run_pass(lean_bin, PROBE_PATH)
    print(results["probe_full"][label], flush=True)

    print(f"=== Single-pass -j1 benchmark suite on {label} ===", flush=True)
    results["single_pass_j1"][label] = run_pass(lean_bin, bench_file, extra_args=["-j1"])
    print(json.dumps(results["single_pass_j1"][label], indent=2), flush=True)

  if bench_file.exists():
    bench_file.unlink()

  out_path = SUPPORT_DIR / "benchmark_results.json"
  out_path.write_text(json.dumps(results, indent=2))
  print(f"Saved results to {out_path}", flush=True)


if __name__ == "__main__":
  main()
