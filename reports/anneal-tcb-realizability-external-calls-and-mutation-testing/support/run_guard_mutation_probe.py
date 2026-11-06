#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Automated Semantic Guard-Mutation Canary Runner for Anneal's Trusted Models.

Systematically mutates safety, alignment, bounds, and polarity guards in
`StructuralExternalCallAndCanaries.lean` and invokes the Lean 4 kernel
(`-DElab.async=false -Ddebug.skipKernelTC=false`) on each mutant to verify that
`BoundaryCanarySuite` achieves a 100% mutation kill rate.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import tempfile
import sys

LEAN_BIN = os.environ.get("LEAN_BIN", "lean")

MUTATIONS = [
    {
        "id": "M01_alu_mod64_add_unbounded_nat",
        "guard": "alu_mod64_add",
        "quadrant": "Quadrant 2 (Target ISA ALU)",
        "description": "Replace 64-bit modular BitVec addition `(va + vb).toNat` with unbounded Nat `a + b` (reproducing X86Semantics.lean:212)",
        "target": "let res := (va + vb).toNat -- MUTATE_GUARD: alu_mod64_add",
        "replacement": "let res := a + b -- MUTATE_GUARD: alu_mod64_add",
        "expected_canary": "canary_pos_add64_wrap / canary_neg_add64_no_unbounded_nat",
    },
    {
        "id": "M02_alu_mod64_sub_truncating_nat",
        "guard": "alu_mod64_sub",
        "quadrant": "Quadrant 2 (Target ISA ALU)",
        "description": "Replace 64-bit modular BitVec subtraction `(va - vb).toNat` with truncating Nat `a - b` (reproducing X86Semantics.lean:213)",
        "target": "let res := (va - vb).toNat -- MUTATE_GUARD: alu_mod64_sub",
        "replacement": "let res := a - b -- MUTATE_GUARD: alu_mod64_sub",
        "expected_canary": "canary_pos_sub64_wrap / canary_neg_sub64_no_zero_truncation",
    },
    {
        "id": "M03_shift_mask64_shl_unmasked",
        "guard": "shift_mask64_check",
        "quadrant": "Quadrant 2 (Target ISA Shift/Flags)",
        "description": "Remove `% 64` (`cl & 0x3f`) shift-count mask on 64-bit `shlq` (reproducing X86Semantics.lean:221)",
        "target": "let c := b % 64 -- MUTATE_GUARD: shift_mask64_check",
        "replacement": "let c := b -- MUTATE_GUARD: shift_mask64_check",
        "expected_canary": "canary_pos_shl64_mask_and_flags",
    },
    {
        "id": "M04_shift_mask64_shr_unmasked",
        "guard": "shift_mask64_shr_check",
        "quadrant": "Quadrant 2 (Target ISA Shift)",
        "description": "Remove `% 64` (`cl & 0x3f`) shift-count mask on 64-bit `shrq` (reproducing X86Semantics.lean:222)",
        "target": "let c := b % 64 -- MUTATE_GUARD: shift_mask64_shr_check",
        "replacement": "let c := b -- MUTATE_GUARD: shift_mask64_shr_check",
        "expected_canary": "canary_neg_shift64_no_unmasked_count",
    },
    {
        "id": "M05_div_zero_guard_disabled",
        "guard": "div_zero_check",
        "quadrant": "Quadrant 1 / Quadrant 2 (Division Trap)",
        "description": "Weaken divide-by-zero `#DE` check `divisor == 0#64` to `false` (fail-open omission of hardware trap)",
        "target": "let divZero := divisor == 0#64 -- MUTATE_GUARD: div_zero_check",
        "replacement": "let divZero := false -- MUTATE_GUARD: div_zero_check",
        "expected_canary": "canary_neg_idiv64_div_zero_traps",
    },
    {
        "id": "M06_idiv_signed_overflow_guard_disabled",
        "guard": "idiv_overflow_check",
        "quadrant": "Quadrant 1 / Quadrant 2 (Signed Division Overflow Trap)",
        "description": "Weaken `INT64_MIN / -1` signed overflow `#DE` check to `false` (fail-open omission of hardware trap)",
        "target": "let sOverflow := dividend == 0x8000000000000000#64 && divisor == 0xffffffffffffffff#64 -- MUTATE_GUARD: idiv_overflow_check",
        "replacement": "let sOverflow := false -- MUTATE_GUARD: idiv_overflow_check",
        "expected_canary": "canary_neg_idiv64_intmin_overflow_traps",
    },
    {
        "id": "M07_slot_bounds_guard_disabled",
        "guard": "slot_bounds_check",
        "quadrant": "Quadrant 2 (Stack-Frame Bounds)",
        "description": "Weaken stack-frame bounds check `slotIdx < slotCount` to `true` (reproducing X86Semantics.lean:105-115 unbounded writeSlot)",
        "target": "let inBounds := slotIdx < slotCount -- MUTATE_GUARD: slot_bounds_check",
        "replacement": "let inBounds := true -- MUTATE_GUARD: slot_bounds_check",
        "expected_canary": "canary_neg_slot_write_out_of_bounds_traps",
    },
    {
        "id": "M08_rsp_align16_guard_disabled",
        "guard": "rsp_align16_check",
        "quadrant": "Quadrant 2 (System V AMD64 ABI Alignment)",
        "description": "Weaken 16-byte stack pointer alignment check `rsp % 16 == 0` at `call` to `true`",
        "target": "let aligned := rsp % 16 == 0 -- MUTATE_GUARD: rsp_align16_check",
        "replacement": "let aligned := true -- MUTATE_GUARD: rsp_align16_check",
        "expected_canary": "canary_neg_call_rsp_misaligned_traps",
    },
    {
        "id": "M09_callee_saved_guard_disabled",
        "guard": "callee_saved_check",
        "quadrant": "Quadrant 2 (System V AMD64 Callee-Saved Integrity)",
        "description": "Weaken callee-saved register preservation check `savedEntry == savedExit` at `ret` to `true`",
        "target": "let preserved := savedEntry == savedExit -- MUTATE_GUARD: callee_saved_check",
        "replacement": "let preserved := true -- MUTATE_GUARD: callee_saved_check",
        "expected_canary": "canary_neg_ret_callee_saved_clobbered_traps",
    },
    {
        "id": "M10_transmute_size_guard_disabled",
        "guard": "transmute_size_check",
        "quadrant": "Quadrant 1 / Quadrant 2 (Transmute Copy Size Check)",
        "description": "Weaken `transmute_copy` byte-size equality check `srcSz == dstSz` to `true`",
        "target": "let sizeMatch := srcSz == dstSz -- MUTATE_GUARD: transmute_size_check",
        "replacement": "let sizeMatch := true -- MUTATE_GUARD: transmute_size_check",
        "expected_canary": "canary_neg_transmute_copy_size_mismatch_traps",
    },
    {
        "id": "M11_adt_inv_guard_disabled",
        "guard": "adt_inv_check",
        "quadrant": "Quadrant 1 / Quadrant 2 (ADT Validity Invariant)",
        "description": "Weaken `bool` validity invariant check `byteVal < 2` (`AdtInv`) to `true`",
        "target": "let validBool := byteVal < 2 -- MUTATE_GUARD: adt_inv_check",
        "replacement": "let validBool := true -- MUTATE_GUARD: adt_inv_check",
        "expected_canary": "canary_neg_load_bool_invalid_discriminant_traps",
    },
    {
        "id": "M12_ctfe_no_unmodeled_guard_disabled",
        "guard": "ctfe_no_unmodeled_check",
        "quadrant": "Quadrant 4 (CTFE Negative-Polarity Vacuity Guard)",
        "description": "Weaken `noUnmodeled := isModeled` to `true` (allowing unmodeled CTFE instructions to silently trigger vacuous truth)",
        "target": "let noUnmodeled := isModeled -- MUTATE_GUARD: ctfe_no_unmodeled_check",
        "replacement": "let noUnmodeled := true -- MUTATE_GUARD: ctfe_no_unmodeled_check",
        "expected_canary": "canary_ctfe_polarity_guards",
    },
    {
        "id": "M13_ctfe_mono_admitted_forced_false",
        "guard": "ctfe_mono_admitted_check",
        "quadrant": "Quadrant 4 (Spurious CTFE Failure Vacuity)",
        "description": "Mutate `monoAdmitted := isModeled && constPassed` to `false` (spurious CTFE failure shrinking effectivePre to False)",
        "target": "let monoAdmitted := isModeled && constPassed -- MUTATE_GUARD: ctfe_mono_admitted_check",
        "replacement": "let monoAdmitted := false -- MUTATE_GUARD: ctfe_mono_admitted_check",
        "expected_canary": "canary_ctfe_polarity_guards",
    },
]


def run_lean(path: pathlib.Path) -> tuple[int, str]:
    proc = subprocess.run(
        [LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(path)],
        capture_output=True,
        text=True,
        check=False,
    )
    output = (proc.stdout + "\n" + proc.stderr).strip()
    return proc.returncode, output


def main() -> int:
    global LEAN_BIN
    base_dir = pathlib.Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description="Run BoundaryCanarySuite guard-mutation probe.")
    parser.add_argument("--lean-bin", default=LEAN_BIN, help="Path to Lean 4 binary (or set LEAN_BIN).")
    parser.add_argument("--target-file", type=pathlib.Path, default=base_dir / "StructuralExternalCallAndCanaries.lean")
    args = parser.parse_args()
    LEAN_BIN = args.lean_bin
    src_file = args.target_file.resolve()
    original_text = src_file.read_text(encoding="utf-8")

    # 1. Verify baseline passes
    rc_base, out_base = run_lean(src_file)
    if rc_base != 0:
        print(f"ERROR: Baseline file failed to verify (rc={rc_base}):\n{out_base}")
        return 1

    results = []
    killed_count = 0

    for m in MUTATIONS:
        if m["target"] not in original_text:
            print(f"ERROR: Target string not found for {m['id']}: {m['target']}")
            return 1
        mutated_text = original_text.replace(m["target"], m["replacement"], 1)
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", encoding="utf-8", delete=True
        ) as tmp:
            tmp.write(mutated_text)
            tmp.flush()
            rc, out = run_lean(pathlib.Path(tmp.name))

        killed = rc != 0
        if killed:
            killed_count += 1
        first_error = next(
            (line for line in out.splitlines() if "error:" in line),
            out.splitlines()[0] if out else "",
        )
        results.append(
            {
                "id": m["id"],
                "guard": m["guard"],
                "quadrant": m["quadrant"],
                "description": m["description"],
                "expected_canary": m["expected_canary"],
                "exit_code": rc,
                "killed": killed,
                "first_error": first_error,
            }
        )

    summary = {
        "baseline_file": str(src_file.name),
        "baseline_exit_code": rc_base,
        "total_mutations": len(MUTATIONS),
        "killed_mutations": killed_count,
        "survived_mutations": len(MUTATIONS) - killed_count,
        "kill_rate_percent": round(100.0 * killed_count / len(MUTATIONS), 2),
        "results": results,
    }

    json_path = base_dir / "guard_mutation_results.json"
    json_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    lines = [
        "================================================================================",
        "ANNEAL — AUTOMATED SEMANTIC GUARD-MUTATION PROBE REPORT",
        "================================================================================",
        f"Baseline Lean 4 verification (`{src_file.name}`): PASS (exit_code={rc_base})",
        f"Total guard mutations tested: {summary['total_mutations']}",
        f"Killed by BoundaryCanarySuite: {summary['killed_mutations']}",
        f"Survived:                      {summary['survived_mutations']}",
        f"Mutation kill rate:            {summary['kill_rate_percent']:.1f}%",
        "--------------------------------------------------------------------------------",
    ]
    for r in results:
        status = "KILLED" if r["killed"] else "SURVIVED"
        lines.append(
            f"[{status}] {r['id']} ({r['quadrant']})\n"
            f"  Guard:    {r['guard']} -> expected canary: {r['expected_canary']}\n"
            f"  Mutation: {r['description']}\n"
            f"  Kernel:   exit_code={r['exit_code']} | {r['first_error']}"
        )
    lines.append(
        "================================================================================"
    )
    report_txt = "\n".join(lines) + "\n"
    print(report_txt, end="")

    return 0 if killed_count == len(MUTATIONS) else 1


if __name__ == "__main__":
    sys.exit(main())
