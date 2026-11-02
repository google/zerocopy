#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible Lean 4.34.1 benchmark and diagnostic suite for prelude traps."""

import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


def find_lean_bin() -> str:
    candidate = (
        Path.home()
        / ".elan"
        / "toolchains"
        / "leanprover--lean4---v4.34.1"
        / "bin"
        / "lean"
    )
    if candidate.exists():
        return str(candidate)
    which_lean = shutil.which("lean")
    if which_lean:
        return which_lean
    raise RuntimeError("Lean 4.34.1 binary not found")


def sanitize_output(text: str, tmp_path: str) -> str:
    cleaned = text.replace(tmp_path, "<probe>.lean")
    cleaned = re.sub(r"/[^\s:]+/[^\s:]+\.lean", "<probe>.lean", cleaned)
    return cleaned.strip()


def run_lean_snippet(lean_bin: str, code: str, timeout_s: float = 30.0) -> dict:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", delete=False, encoding="utf-8"
    ) as tmp:
        tmp.write(code)
        tmp_path = tmp.name
    try:
        t0 = time.perf_counter()
        proc = subprocess.run(
            [lean_bin, tmp_path],
            capture_output=True,
            text=True,
            timeout=timeout_s,
            check=False,
        )
        elapsed_ms = round((time.perf_counter() - t0) * 1000.0, 2)
        out = sanitize_output(
            (proc.stdout or "") + "\n" + (proc.stderr or ""), tmp_path
        )
        status = "ok" if proc.returncode == 0 else "error"
        if "maximum recursion depth has been reached" in out:
            status = "maxRecDepth"
        return {
            "returncode": proc.returncode,
            "status": status,
            "elapsed_ms": elapsed_ms,
            "output": out,
        }
    except subprocess.TimeoutExpired:
        return {
            "returncode": -1,
            "status": "timeout",
            "elapsed_ms": round(timeout_s * 1000.0, 2),
            "output": "timeout",
        }
    finally:
        Path(tmp_path).unlink(missing_ok=True)


HEX_PREAMBLE = """prelude
import Init.NotationExtra

def rv64HexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3'
  | 4  => '4' | 5  => '5' | 6  => '6' | 7  => '7'
  | 8  => '8' | 9  => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _  => 'f'

def bytesToHexChars (bs : List Nat) : List Char :=
  bs.foldr
    (fun b acc => rv64HexDigit (b / 16) :: rv64HexDigit (b % 16) :: acc)
    []
"""


def build_string_oflist_probe(mode: str, n_chars: int) -> str:
    n_bytes = n_chars // 2
    has_odd_prefix = (n_chars % 2) == 1
    lit_str = "9" * n_chars
    char_elems = ", ".join(["'9'"] * n_chars)
    odd_prefix = "'9' :: " if has_odd_prefix else ""

    if mode == "rfl_flat_literal":
        return f"""prelude
import Init.NotationExtra

theorem probe : String.ofList [{char_elems}] = "{lit_str}" := rfl
"""
    if mode == "rfl_hex_literal":
        return (
            HEX_PREAMBLE
            + f"""
theorem probe :
    String.ofList ({odd_prefix}bytesToHexChars (List.replicate {n_bytes} 0x99)) =
      "{lit_str}" := rfl
"""
        )
    if mode == "congrArg_hex_literal":
        return (
            HEX_PREAMBLE
            + f"""
theorem probe :
    String.ofList ({odd_prefix}bytesToHexChars (List.replicate {n_bytes} 0x99)) =
      "{lit_str}" :=
  congrArg String.ofList rfl
"""
        )
    if mode == "congrArg_chunked_oflist":
        chunk_bytes = 32
        full_chunks = n_bytes // chunk_bytes
        rem_bytes = n_bytes % chunk_bytes
        lhs_chunks = (
            f"List.replicate {full_chunks} (List.replicate {chunk_bytes} 0x99)"
        )
        rhs_chunks = f"List.replicate {full_chunks} (List.replicate {chunk_bytes * 2} '9')"
        if rem_bytes > 0:
            lhs_chunks += f" ++ [List.replicate {rem_bytes} 0x99]"
            rhs_chunks += f" ++ [List.replicate {rem_bytes * 2} '9']"
        return (
            HEX_PREAMBLE
            + f"""
def encodeChunkedHex (chunks : List (List Nat)) : String :=
  String.ofList ({odd_prefix}chunks.foldr (fun c acc => bytesToHexChars c ++ acc) [])

def expectedChunkedHexChars (chunks : List (List Char)) : String :=
  String.ofList ({odd_prefix}chunks.foldr (fun c acc => c ++ acc) [])

theorem probe :
    encodeChunkedHex ({lhs_chunks}) =
      expectedChunkedHexChars ({rhs_chunks}) :=
  congrArg String.ofList rfl
"""
        )
    raise ValueError(f"Unknown mode: {mode}")


def benchmark_string_oflist(lean_bin: str) -> dict:
    baseline = run_lean_snippet(
        lean_bin, "prelude\nimport Init.NotationExtra\n"
    )
    sizes = [32, 56, 58, 64, 70, 74, 75, 80, 82, 118, 125, 126, 256, 512, 1042, 2048]
    modes = [
        "rfl_hex_literal",
        "rfl_flat_literal",
        "congrArg_hex_literal",
        "congrArg_chunked_oflist",
    ]
    rows = []
    for n in sizes:
        row = {"n_chars": n, "n_bytes": n // 2, "modes": {}}
        for mode in modes:
            res = run_lean_snippet(
                lean_bin, build_string_oflist_probe(mode, n)
            )
            row["modes"][mode] = {
                "status": res["status"],
                "elapsed_ms": res["elapsed_ms"],
            }
        rows.append(row)

    thresholds = {}
    for label, code_fn, rng in [
        (
            "rfl_flat_literal_max_n_chars",
            lambda k: build_string_oflist_probe("rfl_flat_literal", k),
            [80, 81, 82, 83],
        ),
        (
            "congrArg_flat_literal_max_n_chars",
            lambda k: (
                "prelude\nimport Init.NotationExtra\ntheorem probe :"
                f" String.ofList [{', '.join([chr(39)+'9'+chr(39)]*k)}] ="
                f' "{"9"*k}" := congrArg String.ofList rfl\n'
            ),
            [124, 125, 126, 127],
        ),
        (
            "rfl_hex_literal_max_n_chars",
            lambda k: build_string_oflist_probe("rfl_hex_literal", k),
            [54, 56, 57, 58, 60],
        ),
        (
            "congrArg_hex_literal_max_n_chars",
            lambda k: build_string_oflist_probe("congrArg_hex_literal", k),
            [123, 124, 125, 126],
        ),
    ]:
        thresholds[label] = [
            {
                "n_chars": k,
                "status": run_lean_snippet(lean_bin, code_fn(k))["status"],
            }
            for k in rng
        ]

    return {
        "baseline_startup_ms": baseline["elapsed_ms"],
        "scaling_table": rows,
        "exact_thresholds": thresholds,
    }


def benchmark_option_and_pipeline(lean_bin: str) -> dict:
    # 1. Lazy unforced `ite` Option accumulator with symbolic initial state `env0`
    # (`e.hasFVar == true` disables `useWHNFCache` in `Lean/Meta/WHNF.lean:1058`,
    # exposing the exact O(2^N) thunk duplication when `acc` is referenced in
    # both the `ite` condition and the `then` branch without matching `acc` first).
    lazy_rows = []
    for n in [6, 8, 10, 12, 14, 15, 16]:
        code = f"""prelude
import Init.NotationExtra

structure State where
  wm : Nat
  env : Nat → Nat

def checkLazy (env0 : Nat → Nat) (n : Nat) : Option Nat :=
  let res : Option State :=
    @Nat.rec (fun _ => Option State) (some ⟨0, env0⟩)
      (fun idx acc =>
        if (match acc with | some s => s.wm == idx | none => false) = true then
          match acc with | some s => some ⟨s.wm + 1, s.env⟩ | none => none
        else none)
      n
  match res with
  | some s => some s.wm
  | none => none

set_option diagnostics true in
set_option diagnostics.threshold 1 in
theorem probe (env0 : Nat → Nat) : checkLazy env0 {n} = some {n} := rfl
"""
        res = run_lean_snippet(lean_bin, code, timeout_s=20.0)
        m_nat_rec = re.search(r"\[reduction\] Nat\.rec\s*↦\s*(\d+)", res["output"])
        m_opt_rec = re.search(r"\[reduction\] Option\.rec\s*↦\s*(\d+)", res["output"])
        m_beq = re.search(r"\[reduction\] BEq\.beq\s*↦\s*(\d+)", res["output"])
        lazy_rows.append(
            {
                "n_steps": n,
                "status": res["status"],
                "elapsed_ms": res["elapsed_ms"],
                "reduction_nat_rec": (
                    int(m_nat_rec.group(1)) if m_nat_rec else None
                ),
                "reduction_option_rec": (
                    int(m_opt_rec.group(1)) if m_opt_rec else None
                ),
                "reduction_beq": int(m_beq.group(1)) if m_beq else None,
            }
        )

    strict_fvar_rows = []
    for n in [6, 8, 10, 12, 14, 16, 64, 128]:
        code = f"""prelude
import Init.NotationExtra

structure State where
  wm : Nat
  env : Nat → Nat

def checkStrict (env0 : Nat → Nat) (n : Nat) : Option Nat :=
  let res : Option State :=
    @Nat.rec (fun _ => Option State) (some ⟨0, env0⟩)
      (fun idx acc =>
        match acc with
        | none => none
        | some s =>
          if (s.wm == idx) = true then some ⟨s.wm + 1, s.env⟩ else none)
      n
  match res with
  | some s => some s.wm
  | none => none

set_option diagnostics true in
set_option diagnostics.threshold 1 in
theorem probe (env0 : Nat → Nat) : checkStrict env0 {n} = some {n} := rfl
"""
        res = run_lean_snippet(lean_bin, code, timeout_s=20.0)
        m_nat_rec = re.search(r"\[reduction\] Nat\.rec\s*↦\s*(\d+)", res["output"])
        m_opt_rec = re.search(r"\[reduction\] Option\.rec\s*↦\s*(\d+)", res["output"])
        m_beq = re.search(r"\[reduction\] BEq\.beq\s*↦\s*(\d+)", res["output"])
        strict_fvar_rows.append(
            {
                "n_steps": n,
                "status": res["status"],
                "elapsed_ms": res["elapsed_ms"],
                "reduction_nat_rec": (
                    int(m_nat_rec.group(1)) if m_nat_rec else None
                ),
                "reduction_option_rec": (
                    int(m_opt_rec.group(1)) if m_opt_rec else None
                ),
                "reduction_beq": int(m_beq.group(1)) if m_beq else None,
            }
        )

    # 2. Monolithic spine-strict `checkSyntheticPipeline` (2 passes x N steps)
    strict_monolithic_rows = []
    for n in [64, 128, 170, 171, 256, 512, 1024]:
        code = f"""prelude
import Init.NotationExtra

def checkSyntheticBlock (n : Nat) : Bool :=
  let res : Option Nat :=
    @Nat.rec (fun _ => Option Nat) (some 0)
      (fun idx acc =>
        match acc with
        | none => none
        | some w => if w == idx then some (w + 1) else none)
      n
  match res with
  | some finalW => finalW == n
  | none => false

def checkSyntheticPipeline (n : Nat) : Bool :=
  checkSyntheticBlock n && checkSyntheticBlock n

set_option diagnostics true in
theorem probe : checkSyntheticPipeline {n} = true := rfl
"""
        res = run_lean_snippet(lean_bin, code)
        m_nat_rec = re.search(r"Nat\.rec\s*↦\s*(\d+)", res["output"])
        strict_monolithic_rows.append(
            {
                "n_steps": n,
                "status": res["status"],
                "elapsed_ms": res["elapsed_ms"],
                "nat_rec_unfoldings": (
                    int(m_nat_rec.group(1)) if m_nat_rec else None
                ),
            }
        )

    # 3. Compositional per-block `List.foldr` (`checkMultiBlockPipeline_cons`)
    # using 64-instruction basic blocks across N in {64, 256, 512, 1024}
    compositional_rows = []
    for n in [64, 256, 512, 1024]:
        block_size = 64
        n_blocks = n // block_size
        blocks_list = "[" + ", ".join([str(block_size)] * n_blocks) + "]"
        chain_proof = "rfl"
        for _ in range(n_blocks):
            chain_proof = (
                f"(checkMultiBlockPipeline_cons bench_block64 {chain_proof})"
            )

        code = f"""prelude
import Init.NotationExtra

def checkSyntheticBlock (n : Nat) : Bool :=
  let res : Option Nat :=
    @Nat.rec (fun _ => Option Nat) (some 0)
      (fun idx acc =>
        match acc with
        | none => none
        | some w => if w == idx then some (w + 1) else none)
      n
  match res with
  | some finalW => finalW == n
  | none => false

def checkSyntheticPipeline (n : Nat) : Bool :=
  checkSyntheticBlock n && checkSyntheticBlock n

theorem bench_block64 : checkSyntheticPipeline 64 = true := rfl

def checkMultiBlockPipeline (blocks : List Nat) : Bool :=
  blocks.foldr (fun b acc => checkSyntheticPipeline b && acc) true

theorem checkMultiBlockPipeline_cons {{b : Nat}} {{rest : List Nat}}
    (hb : checkSyntheticPipeline b = true)
    (hrest : checkMultiBlockPipeline rest = true) :
    checkMultiBlockPipeline (b :: rest) = true := by
  dsimp [checkMultiBlockPipeline]
  rw [hb]
  exact hrest

theorem probe :
    checkMultiBlockPipeline {blocks_list} = true :=
  {chain_proof}
"""
        res = run_lean_snippet(lean_bin, code)
        compositional_rows.append(
            {
                "n_steps": n,
                "n_blocks": n_blocks,
                "block_size": block_size,
                "status": res["status"],
                "elapsed_ms": res["elapsed_ms"],
            }
        )

    return {
        "lazy_ite_option_accumulator": lazy_rows,
        "strict_fvar_option_accumulator": strict_fvar_rows,
        "strict_monolithic_nat_rec": strict_monolithic_rows,
        "compositional_per_block_foldr": compositional_rows,
    }


def run_diagnostic_reproductions(lean_bin: str) -> dict:
    probes = {
        "q1_string_toUTF8_unknown_in_prelude": """prelude
import Init.NotationExtra
#check String.toUTF8
""",
        "q1_string_toUTF8_opaque_in_module": """module
public import Init
public theorem test_toUTF8 : "Hi".toUTF8.data.toList = [72, 105] := rfl
""",
        "q1_string_single_field_ctor_mismatch": """prelude
import Init.NotationExtra
def badStringToBytes (s : String) : List UInt8 :=
  match s with
  | ⟨⟨bytes⟩⟩ => bytes
""",
        "q2_string_oflist_75_chars_rfl_max_rec_depth": build_string_oflist_probe(
            "rfl_hex_literal", 75
        ),
        "q3_dsimp_beq_partial_unfolding_mismatch": """prelude
import Init.NotationExtra

abbrev LocalEnv := Nat → Option Nat

def updateLocal (locals : LocalEnv) (idx : Nat) (val : Option Nat) : LocalEnv :=
  fun k => if (k == idx) = true then val else locals k

theorem updateLocal_self_broken (locals : LocalEnv) (idx : Nat) (val : Option Nat) :
    updateLocal locals idx val idx = val := by
  dsimp [updateLocal, (· == ·), BEq.beq]
  have h : decide (idx = idx) = true := decide_eq_true rfl
  rw [h]
""",
        "q4_list_rec_codegen_rejection": """prelude
import Init.NotationExtra

def sumViaListRec (xs : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun h _ ih => h + ih) xs
""",
        "q4_unsafe_rec_emission_inspection": """import Lean
open Lean Elab Command

def recDefSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + recDefSum xs

def foldrDefSum (xs : List Nat) : Nat :=
  xs.foldr (· + ·) 0

def natRecDefSum (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun k ih => k + ih) n

theorem recThmTrivial : List Nat → True
  | [] => True.intro
  | _ :: xs => recThmTrivial xs

#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in [``recDefSum, ``foldrDefSum, ``natRecDefSum, ``recThmTrivial] do
    let unsafeName := Name.str n "_unsafe_rec"
    let hasUnsafe := (env.checked.get.find? unsafeName).isSome
    IO.println s!"{n}: has_unsafe_rec={hasUnsafe}"
""",
        "q6_section_field_keyword_error": """prelude
import Init.NotationExtra

inductive SectionKind where | text | data

structure BadSymDef where
  name : Nat
  section : SectionKind
""",
        "q6_nat_lxor_and_tactic_unavailability": """prelude
import Init.NotationExtra

#check Nat.lxor
""",
    }
    results = {}
    for key, src in probes.items():
        res = run_lean_snippet(lean_bin, src)
        results[key] = {
            "returncode": res["returncode"],
            "status": res["status"],
            "output": res["output"],
        }
    return results


def main() -> None:
    lean_bin = find_lean_bin()
    support_dir = Path(__file__).resolve().parent
    probe_file = support_dir / "ProbePreludeTraps.lean"

    t0 = time.perf_counter()
    probe_proc = subprocess.run(
        [lean_bin, str(probe_file)],
        capture_output=True,
        text=True,
        check=False,
    )
    probe_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    if probe_proc.returncode != 0:
        raise RuntimeError(
            f"ProbePreludeTraps.lean failed:\n{probe_proc.stdout}\n{probe_proc.stderr}"
        )

    ver_proc = subprocess.run(
        [lean_bin, "--version"],
        capture_output=True,
        text=True,
        check=True,
    )

    results = {
        "lean_version": ver_proc.stdout.strip(),
        "positive_probe": {
            "path": "support/ProbePreludeTraps.lean",
            "returncode": probe_proc.returncode,
            "elapsed_ms": probe_ms,
        },
        "benchmark_1_string_oflist_scaling": benchmark_string_oflist(lean_bin),
        "benchmark_2_option_accumulator_and_pipeline": benchmark_option_and_pipeline(
            lean_bin
        ),
        "benchmark_3_diagnostic_reproductions": run_diagnostic_reproductions(
            lean_bin
        ),
    }

    out_path = support_dir / "benchmark_results.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path.name} successfully.")


if __name__ == "__main__":
    main()
