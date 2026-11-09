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


def run_side_conditions():
  base_mod = "ProbeSideConditionReflection"
  base_file = os.path.join(WORKDIR, f"{base_mod}.lean")
  base_olean = os.path.join(WORKDIR, f"{base_mod}.olean")
  compile_lean(base_file, base_olean)

  # 20 interval disjointness obligations
  intervals = []
  for i in range(20):
    p1 = 0x1000_0000 + i * 0x1000
    n1 = 64 + (i % 8) * 16
    p2 = p1 + 512
    n2 = 128
    intervals.append((p1, n1, p2, n2))

  # 15 alignment round-up obligations
  alignments = []
  for i in range(15):
    align = 1 << ((i % 4) + 2)  # 4, 8, 16, 32
    off = 100 + i * 37
    out = ((off + align - 1) // align) * align
    alignments.append((off, align, out))

  # 15 symbolic-base subrange obligations
  subranges = []
  for i in range(15):
    off = 16 + i * 24
    sublen = 32 + (i % 5) * 8
    totallen = off + sublen + 64
    subranges.append((off, sublen, totallen))

  # 1. Strategy A: `omega` on all 50 obligations
  omega_mod = "SideCond_Omega50"
  omega_file = os.path.join(WORKDIR, f"{omega_mod}.lean")
  omega_olean = os.path.join(WORKDIR, f"{omega_mod}.olean")
  omega_lines = [HEADER + f"import {base_mod}\n\nopen Trusted\n"]
  for idx, (p1, n1, p2, n2) in enumerate(intervals):
    omega_lines.append(
        f"theorem sc_disj_{idx} : IntervalsDisjoint {p1} {n1} {p2} {n2} := by"
        " unfold IntervalsDisjoint ADDR_MASK; omega"
    )
  for idx, (off, align, out) in enumerate(alignments):
    omega_lines.append(
        f"theorem sc_align_{idx} : AlignedRoundUp {off} {align} {out} := by"
        " unfold AlignedRoundUp; omega"
    )
  for idx, (off, sublen, totallen) in enumerate(subranges):
    omega_lines.append(
        f"theorem sc_sub_{idx} : SymbolicSubrange {off} {sublen} {totallen} :="
        " by unfold SymbolicSubrange; intro base; omega"
    )
  with open(omega_file, "w") as f:
    f.write("\n".join(omega_lines) + "\n")

  # 2. Strategy B: `decide` on 35 ground obligations + `omega` on 15 symbolic obligations
  dec_mod = "SideCond_DecideOmega50"
  dec_file = os.path.join(WORKDIR, f"{dec_mod}.lean")
  dec_olean = os.path.join(WORKDIR, f"{dec_mod}.olean")
  dec_lines = [HEADER + f"import {base_mod}\n\nopen Trusted\n"]
  for idx, (p1, n1, p2, n2) in enumerate(intervals):
    dec_lines.append(
        f"theorem sc_disj_{idx} : IntervalsDisjoint {p1} {n1} {p2} {n2} := by"
        " unfold IntervalsDisjoint ADDR_MASK; decide"
    )
  for idx, (off, align, out) in enumerate(alignments):
    dec_lines.append(
        f"theorem sc_align_{idx} : AlignedRoundUp {off} {align} {out} := by"
        " unfold AlignedRoundUp; decide"
    )
  for idx, (off, sublen, totallen) in enumerate(subranges):
    dec_lines.append(
        f"theorem sc_sub_{idx} : SymbolicSubrange {off} {sublen} {totallen} :="
        " by unfold SymbolicSubrange; intro base; omega"
    )
  with open(dec_file, "w") as f:
    f.write("\n".join(dec_lines) + "\n")

  # 3. Strategy C: Pre-Proved `Theory` Reflection Checkers + `rfl` on all 50 obligations
  refl_mod = "SideCond_Refl50"
  refl_file = os.path.join(WORKDIR, f"{refl_mod}.lean")
  refl_olean = os.path.join(WORKDIR, f"{refl_mod}.olean")
  refl_lines = [HEADER + f"import {base_mod}\n\nopen Trusted Theory\n"]
  for idx, (p1, n1, p2, n2) in enumerate(intervals):
    refl_lines.append(
        f"theorem sc_disj_{idx} : IntervalsDisjoint {p1} {n1} {p2} {n2} :="
        " checkIntervalDisjoint_sound rfl"
    )
  for idx, (off, align, out) in enumerate(alignments):
    refl_lines.append(
        f"theorem sc_align_{idx} : AlignedRoundUp {off} {align} {out} :="
        " checkAlignedRoundUp_sound rfl"
    )
  for idx, (off, sublen, totallen) in enumerate(subranges):
    refl_lines.append(
        f"theorem sc_sub_{idx} : SymbolicSubrange {off} {sublen} {totallen} :="
        " checkSymbolicSubrange_sound rfl"
    )
  with open(refl_file, "w") as f:
    f.write("\n".join(refl_lines) + "\n")

  # 4. Bundled 50-interval batch: `checkIntervalBatch_sound rfl` vs `omega`
  batch50 = []
  for i in range(50):
    p1 = 0x2000_0000 + i * 0x1000
    n1 = 64 + (i % 8) * 16
    p2 = p1 + 512
    n2 = 128
    batch50.append(f"({p1}, {n1}, {p2}, {n2})")
  batch50_str = ",\n  ".join(batch50)

  bbase_mod = "SideCond_BatchBase50"
  bbase_file = os.path.join(WORKDIR, f"{bbase_mod}.lean")
  bbase_olean = os.path.join(WORKDIR, f"{bbase_mod}.olean")
  with open(bbase_file, "w") as f:
    f.write(
        HEADER
        + f"""import {base_mod}

def batch50 : List (Nat × Nat × Nat × Nat) := [
  {batch50_str}
]
"""
    )
  compile_lean(bbase_file, bbase_olean)

  brefl_mod = "SideCond_BatchRefl50"
  brefl_file = os.path.join(WORKDIR, f"{brefl_mod}.lean")
  brefl_olean = os.path.join(WORKDIR, f"{brefl_mod}.olean")
  with open(brefl_file, "w") as f:
    f.write(
        HEADER
        + f"""import {bbase_mod}

theorem verified_batch50 : Theory.AllIntervalsDisjoint batch50 :=
  Theory.checkIntervalBatch_sound rfl
"""
    )

  bomega_mod = "SideCond_BatchOmega50"
  bomega_file = os.path.join(WORKDIR, f"{bomega_mod}.lean")
  bomega_olean = os.path.join(WORKDIR, f"{bomega_mod}.olean")
  with open(bomega_file, "w") as f:
    f.write(
        HEADER
        + f"""import {bbase_mod}

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem verified_batch50 : Theory.AllIntervalsDisjoint batch50 := by
  dsimp [batch50, Theory.AllIntervalsDisjoint]
  repeat' refine And.intro (by unfold Trusted.IntervalsDisjoint Trusted.ADDR_MASK; omega) ?_
  exact trivial
"""
    )

  t_omega = compile_lean(omega_file, omega_olean)
  t_dec = compile_lean(dec_file, dec_olean)
  t_refl = compile_lean(refl_file, refl_olean)
  km_50 = measure_kernel_batch(base_mod, [omega_mod, dec_mod, refl_mod])

  t_bomega = compile_lean(bomega_file, bomega_olean)
  t_brefl = compile_lean(brefl_file, brefl_olean)
  km_batch = measure_kernel_batch(bbase_mod, [bomega_mod, brefl_mod])

  results = []
  for label, mod, ofile, elab_ms, kmap in [
      (
          "50 Decls: Standard `omega` Tactic",
          omega_mod,
          omega_olean,
          t_omega,
          km_50,
      ),
      (
          "50 Decls: Hybrid `decide` + `omega`",
          dec_mod,
          dec_olean,
          t_dec,
          km_50,
      ),
      (
          "50 Decls: Pre-Proved `Theory` Reflection (`rfl`)",
          refl_mod,
          refl_olean,
          t_refl,
          km_50,
      ),
      (
          "50 Bundled Intervals: `omega` Tactic",
          bomega_mod,
          bomega_olean,
          t_bomega,
          km_batch,
      ),
      (
          "50 Bundled Intervals: `checkIntervalBatch_sound rfl`",
          brefl_mod,
          brefl_olean,
          t_brefl,
          km_batch,
      ),
  ]:
    km = kmap[mod]
    olean_bytes = os.path.getsize(ofile)
    row = {
        "strategy": label,
        "mod": mod,
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
        f"{label:52s} | elab={elab_ms:7.1f}ms | replay={km['replay_ms']:7.3f}ms"
        f" ({km['replay_us']:6d}us) | olean={olean_bytes:7d}B |"
        f" DECLS={km['decls']:2d} | DAG={km['dag_nodes']:6d} |"
        f" TREE={km['tree_nodes']:8d}",
        flush=True,
    )

  out_json = os.path.join(WORKDIR, "side_condition_results.json")
  with open(out_json, "w") as f:
    json.dump(results, f, indent=2)
  print(f"Saved side-condition results to {out_json}")


if __name__ == "__main__":
  run_side_conditions()
