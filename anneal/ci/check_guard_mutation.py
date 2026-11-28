# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Guard-mutation CI check for Anneal's MIR semantics, auditor, and capture.

Why this check exists
---------------------

Positive verification proofs and positive canary suites cannot catch an
accidental deletion or weakening of an undefined-behavior (UB) guard or policy
rejection branch. If a refactor drops division-by-zero checking, removes an
alignment check, disables a MIR capture refusal, or loosens an import
restriction, every positive proof still succeeds while unsound programs
silently become provable.

This script closes that blind spot by performing single-guard mutation testing
in temporary directories (never modifying the repository working tree):

1. Against the unmodified TCB sources, every negative refutation theorem in
   `ci/fixtures/guard_mutation/` must compile with zero errors, every negative
   header or boundary fixture must be rejected by `TrustedBoundary.lean` with
   a policy error (`exit 1`, `"category": "policy"`), and every negative
   `anneal-rustc-capture` witness or unit test must reject as expected.
2. For each cataloged guard, the runner disables only that guard inside a fresh
   `tempfile.TemporaryDirectory()` copy, confirms that the mutated TCB module
   and positive sanity checks still compile/pass cleanly (preventing syntax or
   type errors from masquerading as mutant kills), and verifies that the
   guard's targeted negative refutation fails with a proof/type error on the
   target theorem (or flips from reject to accept in `TrustedBoundary.lean` /
   `anneal-rustc-capture`, or breaks its targeted negative unit test).
3. The check exits `0` only if 100% of executed guards are killed.

What this check guarantees — and what it does NOT guarantee
-----------------------------------------------------------

- **Guarantees:** Every guard listed in `MIR_SEMANTICS_GUARDS`,
  `AUDIT_HEADER_GUARDS`, `AUDIT_BOUNDARY_GUARDS`, and `EXTRACT_GUARDS` is
  exercised by a targeted negative refutation, auditor/capture witness, or unit
  test whose outcome changes when that single guard is weakened. Most entries
  verify sole UB or admission gates; `EXTRACT_GUARDS` entries marked
  `allow_downstream_fallback=True` (`extract_reject_cleanup_block`,
  `extract_reject_uninstantiated_generic_fn`, and
  `extract_eval_required_consts`) pin diagnostic precedence ahead of downstream
  refusals, and `MIR_SEMANTICS_GUARDS` also includes lockstep fault-kind
  classification, Profile-v1 alignment, and function-level defense-in-depth
  guards labeled in their descriptions.
- **Does NOT guarantee:** Coverage of unmodeled Rust semantics, guards added to
  `Trusted/MirSemantics/`, `TrustedBoundary.lean`, or
  `trusted/rustc-capture/src/` without a catalog entry, or automatic GitHub
  Actions execution of `EXTRACT_GUARDS` until `--suite extract_guards` is wired
  into a `rustc-dev` CI job (invoking `--suite all` without a `rustc-dev`
  toolchain auto-skips `extract_guards`, while
  `run_anneal_check.sh guard-mutation` passes `--lean-only` explicitly; both
  record `extract_guards` in `skipped_suites`).

How to add a new guard
----------------------

Whenever a new UB check lands in `trusted/lean/Trusted/MirSemantics/`, a new
policy guard lands in `trusted/audit/TrustedBoundary.lean`, or a new admission
guard lands in `trusted/rustc-capture/src/`:

1. Add a minimal negative refutation theorem `refute_<guard_id>` in the
   corresponding `ci/fixtures/guard_mutation/*Refutations.lean` file (or a
   negative fixture/unit test for `AUDIT_HEADER_GUARDS`,
   `AUDIT_BOUNDARY_GUARDS`, or `EXTRACT_GUARDS`).
2. Add a matching `MirSemanticsGuard`, `AuditHeaderGuard`,
   `AuditBoundaryGuard`, or `ExtractGuard` entry below whose `anchor` matches
   the guard expression uniquely and whose `replacement` weakens only that
   guard while keeping the mutated source well-typed.
3. For Lean or auditor guards, run
   `python3 -I -B ci/check_guard_mutation.py --lean <path-to-lean>`; for
   `ExtractGuard` entries, run `python3 -I -B` on
   `ci/check_guard_mutation.py --suite extract_guards --rustc <pinned-rustc>`
   (since `--suite all` skips `extract_guards` when `rustc-dev` is absent) and
   confirm a 100% kill rate.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib


# Base trusted Lean modules compiled once into the shared baseline `.olean`
# directory. No cataloged mutant modifies these files, so every mutant reuses
# their precompiled `.olean` artifacts via left-to-right `LEAN_PATH`.
BASE_TRUSTED_MODULES: tuple[str, ...] = (
    "Trusted",
    "Trusted/MirAst/Types",
    "Trusted/MirAst/Places",
    "Trusted/MirAst/Rvalues",
    "Trusted/MirAst/Statements",
    "Trusted/MirAst/Terminators",
    "Trusted/MirAst/Body",
    "Trusted/MirAst",
    "Trusted/MirModel",
)

# Guard-bearing semantics modules in strict topological import order. When a
# guard mutates one of these modules, only that module and the modules
# reachable from it in `SEMANTICS_DOWNSTREAM` need to be recompiled for that
# mutant.
SEMANTICS_MODULES: tuple[str, ...] = (
    "Trusted/MirSemantics/Ops",
    "Trusted/MirSemantics/Enum",
    "Trusted/MirSemantics/Layout",
    "Trusted/MirSemantics/Memory",
    "Trusted/MirSemantics/Bytes",
    "Trusted/MirSemantics/CoreContracts",
    "Trusted/MirSemantics/AllocContracts",
    "Trusted/MirSemantics/State",
    "Trusted/MirSemantics/Step",
    "Trusted/MirSemantics/Boundary",
    "Trusted/MirSemantics/Contract",
)

# `Trusted/MirSemantics/*.lean` modules intentionally omitted from mutation
# coverage because they contain concrete canary programs/claims rather than
# guard branches (`CanaryFixtures.lean` is checked directly by Pass 1
# `Trusted.MirSemantics` canary proofs and Pass 2 `Trusted.Correspondence`).
NON_GUARD_SEMANTICS_MODULES: tuple[str, ...] = (
    "Trusted/MirSemantics/CanaryFixtures",
)

# Per-module rebuild closure (inclusive, in topological order) recompiled for
# each mutable semantics module. `Layout` and `Memory` intentionally prune
# `State`/`Step`/`Boundary`/`Contract`, and `Ops`..`Boundary` prune `Contract`
# because their dedicated sanity and refutation fixtures import at most
# `Boundary` / `Bytes` / `Memory`; `validate_catalog_invariants` enforces that
# no fixture or sanity module used by a guard transitively imports a downstream
# semantics module omitted from its rebuild list.
SEMANTICS_DOWNSTREAM: dict[str, tuple[str, ...]] = {
    "Trusted/MirSemantics/Ops": (
        "Trusted/MirSemantics/Ops",
        "Trusted/MirSemantics/Enum",
        "Trusted/MirSemantics/Layout",
        "Trusted/MirSemantics/Memory",
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/CoreContracts",
        "Trusted/MirSemantics/AllocContracts",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Enum": (
        "Trusted/MirSemantics/Enum",
        "Trusted/MirSemantics/Layout",
        "Trusted/MirSemantics/Memory",
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/CoreContracts",
        "Trusted/MirSemantics/AllocContracts",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Layout": (
        "Trusted/MirSemantics/Layout",
        "Trusted/MirSemantics/Memory",
        "Trusted/MirSemantics/Bytes",
    ),
    "Trusted/MirSemantics/Memory": (
        "Trusted/MirSemantics/Memory",
    ),
    "Trusted/MirSemantics/Bytes": (
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/CoreContracts",
        "Trusted/MirSemantics/AllocContracts",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/CoreContracts": (
        "Trusted/MirSemantics/CoreContracts",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/State": (
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/AllocContracts": (
        "Trusted/MirSemantics/AllocContracts",
        "Trusted/MirSemantics/Step",
    ),
    "Trusted/MirSemantics/Step": (
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Boundary": (
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Contract": (
        "Trusted/MirSemantics/Contract",
    ),
}

# Fixture helper modules compiled once against the baseline and rebuilt per
# mutant only when needed by that mutant's fixture.
FIXTURE_HELPERS_END_TO_END: tuple[str, ...] = (
    "GuardRefuteBase",
    "GuardRefuteWf",
)
FIXTURE_HELPERS_BOUNDARY: tuple[str, ...] = (
    "GuardRefuteBase",
)

# Error substrings that indicate a compiler crash, parse error, missing import,
# or resource exhaustion rather than a genuine proof refutation failure. Any
# mutant whose fixture fails with one of these is classified as an error rather
# than a kill so broken fixtures or crashes can never masquerade as kills.
NON_KILL_ERROR_MARKERS: tuple[str, ...] = (
    "unknown identifier",
    "unknown constant",
    "unknown module",
    "expected token",
    "unexpected token",
    "maximum recursion depth",
    "deterministic timeout",
    "heartbeat_limit_exceeded",
    "recursion_depth_exceeded",
    "PANIC",
    "internal exception",
    "invalid import",
)

# Diagnostic substrings produced by Lean 4 when a refutation theorem fails to
# type-check because the mutated semantics no longer rejects the UB program.
EXPECTED_PROOF_FAILURE_MARKERS: tuple[str, ...] = (
    "Type mismatch",
    "type mismatch",
    "has type",
    "rfl",
    "unsolved goals",
    "Function expected",
    "Application type mismatch",
    "failed to synthesize",
    "invalid field",
    "is not a valid",
)


@dataclass(frozen=True)
class MirSemanticsGuard:
    """Single-guard mutation entry targeting `Trusted/MirSemantics/`."""

    guard_id: str
    target_file: str
    target_module: str
    description: str
    anchor: str
    replacement: str
    fixture_module: str
    theorem_name: str
    sanity_module: str = "PositiveSanity"
    needs_wf_helper: bool = True


@dataclass(frozen=True)
class AuditHeaderGuard:
    """Single-guard mutation entry targeting `TrustedBoundary.lean` or `SpecPreflight.lean` headers."""

    guard_id: str
    target_file: str
    description: str
    anchor: str
    replacement: str
    negative_source: str


@dataclass(frozen=True)
class AuditBoundaryGuard:
    """Single-guard mutation entry for spec-preflight or target-audit."""

    guard_id: str
    target_file: str
    mode: str  # "spec-preflight" | "target-audit"
    description: str
    anchor: str
    replacement: str
    fixture_id: str


@dataclass(frozen=True)
class ExtractGuard:
    """Single-guard mutation entry targeting `trusted/rustc-capture/src/`."""

    guard_id: str
    target_file: str
    mode: str  # "capture" | "unit"
    description: str
    anchor: str
    replacement: str
    negative_source: str = ""
    capture_scope: str = "select"  # "select" | "crate" | "instantiate"
    select_root: str = "selected"
    instantiate_json: str = ""
    expected_baseline_status: str = "unsupported"
    expected_baseline_diagnostic: str = ""
    expected_fallback_diagnostic: str = ""
    allow_downstream_fallback: bool = False
    allow_unstable_features: tuple[str, ...] = ()
    stdlib_crate: str = ""
    unit_test_name: str = ""
    sanity_unit_test: str = (
        "extract::tests::use_retag_is_admitted_only_for_retag_noop_types"
    )


@dataclass(frozen=True)
class GuardResult:
    """Outcome of executing one guard-mutation check."""

    suite: str
    guard_id: str
    target_file: str
    status: str  # KILLED | SURVIVED | ERROR
    duration_sec: float
    detail: str


MIR_SEMANTICS_GUARDS: tuple[MirSemanticsGuard, ...] = (
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Ops.lean (17 UB, overflow, cast & op guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="ops_shift_unchecked_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Unchecked shift amount < 0 or >= bitWidth faults UB",
        anchor="    if overflow && op.isUnchecked then\n      .error .undefined",
        replacement="    if false then\n      .error .undefined",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_shift_unchecked_overflow",
    ),
    MirSemanticsGuard(
        guard_id="ops_div_rem_by_zero",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Integer division and remainder by zero fault UB",
        anchor="  if isDivOrRem && r == 0 then\n    .error .undefined",
        replacement="  if false then\n    .error .undefined",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_div_rem_by_zero",
    ),
    MirSemanticsGuard(
        guard_id="ops_signed_div_rem_min_neg1",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Signed INT_MIN / -1 and INT_MIN % -1 fault UB",
        anchor=(
            "  else if s && isDivOrRem && (l == signedMinInt w && r == Neg.neg 1) then\n"
            "    .error .undefined"
        ),
        replacement="  else if false then\n    .error .undefined",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_signed_div_rem_min_neg1",
    ),
    MirSemanticsGuard(
        guard_id="ops_arith_unchecked_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Unchecked integer add/sub/mul overflow faults UB",
        anchor=(
            "        if (hostOverflow || lossy) && op.isUnchecked then\n"
            "          .error .undefined"
        ),
        replacement="        if false then\n          .error .undefined",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_arith_unchecked_overflow",
    ),
    MirSemanticsGuard(
        guard_id="ops_scalar_wf_width_check",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="ScalarVal.wf enforces bits fit within width",
        anchor=(
            "noncomputable def wf (v : ScalarVal) : Bool :=\n"
            "  truncateBits v.width v.bits == v.bits"
        ),
        replacement="noncomputable def wf (_v : ScalarVal) : Bool :=\n  true",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_scalar_wf_width_check",
    ),
    MirSemanticsGuard(
        guard_id="ops_arith_host_overflow_signed",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="128-bit signed hostOverflow detects i128 unchecked overflow",
        anchor=(
            "        if s then\n"
            "          decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||\n"
            "            decide (result ≥ HPow.hPow (2 : Int) 127)"
        ),
        replacement="        if s then\n          false",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_arith_host_overflow_signed",
    ),
    MirSemanticsGuard(
        guard_id="ops_arith_host_overflow_unsigned",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="128-bit unsigned hostOverflow detects u128 unchecked overflow",
        anchor=(
            "        else\n"
            "          decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)"
        ),
        replacement="        else\n          false",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_arith_host_overflow_unsigned",
    ),
    MirSemanticsGuard(
        guard_id="ops_arith_with_overflow_flag",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="WithOverflow arithmetic returns accurate overflow boolean",
        anchor=(
            "        else if op.isOverflowing then\n"
            "          .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])"
        ),
        replacement=(
            "        else if op.isOverflowing then\n"
            "          .ok (.tuple [.scalar val, .bool false])"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_arith_with_overflow_flag",
    ),
    MirSemanticsGuard(
        guard_id="ops_binop_scalar_type_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Non-shift scalar BinOp rejects mismatched width/signedness",
        anchor=(
            "    else if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then\n"
            "      .error .unsupported"
        ),
        replacement="    else if false then\n      .error .unsupported",
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_binop_scalar_type_mismatch",
    ),
    MirSemanticsGuard(
        guard_id="ops_binop_scalar_unsupported_op",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Scalar evalBinOp rejects unsupported operators like offset",
        anchor=(
            "      | .addWithOverflow | .subWithOverflow | .mulWithOverflow =>\n"
            "        evalArithOp op w s lInt rInt\n"
            "      | _ => .error .unsupported"
        ),
        replacement=(
            "      | .addWithOverflow | .subWithOverflow | .mulWithOverflow =>\n"
            "        evalArithOp op w s lInt rInt\n"
            "      | _ => .ok (.scalar l)"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_binop_scalar_unsupported_op",
    ),
    MirSemanticsGuard(
        guard_id="ops_binop_bool_unsupported_op",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Bool evalBinOp rejects unsupported operators like add",
        anchor=(
            "    | .bitXor => .ok (.bool (bne l r))\n"
            "    | _ => .error .unsupported"
        ),
        replacement=(
            "    | .bitXor => .ok (.bool (bne l r))\n"
            "    | _ => .ok (.bool l)"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_binop_bool_unsupported_op",
    ),
    MirSemanticsGuard(
        guard_id="ops_binop_char_unsupported_op",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Char evalBinOp rejects non-comparison operators like add",
        anchor=(
            "    | .cmp => .ok (.ordering (cmpOrderingOfInt lInt rInt))\n"
            "    | _ => .error .unsupported"
        ),
        replacement=(
            "    | .cmp => .ok (.ordering (cmpOrderingOfInt lInt rInt))\n"
            "    | _ => .ok (.bool false)"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_binop_char_unsupported_op",
    ),
    MirSemanticsGuard(
        guard_id="ops_binop_mixed_operand_types",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="evalBinOp catch-all rejects mixed operand types (u32, bool)",
        anchor=(
            "    | _ => .error .unsupported\n"
            "  | _, _ => .error .unsupported\n\n"
            "/-- The `u128` intermediate"
        ),
        replacement=(
            "    | _ => .error .unsupported\n"
            "  | _, _ => .ok (.bool false)\n\n"
            "/-- The `u128` intermediate"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_binop_mixed_operand_types",
    ),
    MirSemanticsGuard(
        guard_id="ops_cast_int_to_char_above_u8",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="evalIntToIntCast to char rejects values > 255",
        anchor=(
            "    | .char =>\n"
            "      if Nat.ble bits 255 then\n"
            "        .ok (.char (Char.ofNat bits))\n"
            "      else\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .char =>\n"
            "      if true then\n"
            "        .ok (.char (Char.ofNat bits))\n"
            "      else\n"
            "        .error .unsupported"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_cast_int_to_char_above_u8",
    ),
    MirSemanticsGuard(
        guard_id="ops_cast_unsupported_target",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="evalIntToIntCast rejects non-int non-char target types",
        anchor=(
            "      else\n"
            "        .error .unsupported\n"
            "    | _ => .error .unsupported"
        ),
        replacement=(
            "      else\n"
            "        .error .unsupported\n"
            "    | _ => .ok (.bool false)"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_cast_unsupported_target",
    ),
    MirSemanticsGuard(
        guard_id="ops_unop_neg_unsigned",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="UnOp.neg rejects unsigned integer scalars",
        anchor=(
            "  | .neg, .scalar sv =>\n"
            "    let integer := decodeScalar sv\n"
            "    if sv.signed then"
        ),
        replacement=(
            "  | .neg, .scalar sv =>\n"
            "    let integer := decodeScalar sv\n"
            "    if true then"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_unop_neg_unsigned",
    ),
    MirSemanticsGuard(
        guard_id="ops_unop_unsupported_combo",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="evalUnOp rejects unsupported op/value combinations",
        anchor=(
            "    else\n"
            "      .error .unsupported\n"
            "  | _, _ => .error .unsupported"
        ),
        replacement=(
            "    else\n"
            "      .error .unsupported\n"
            "  | _, _ => .ok (.bool false)"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_unop_unsupported_combo",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Enum.lean (17 enum/validity/identity guards;
    # +1 Profile v2 overflow-pair pointee guard below = 18 total)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="enum_char_above_unicode_max",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="char scalar value > 0x10FFFF faults UB",
        anchor=(
            "noncomputable def isUnicodeScalar (n : Nat) : Bool :=\n"
            "  Nat.ble n 0x10ffff && !(Nat.ble 0xd800 n && Nat.ble n 0xdfff)"
        ),
        replacement=(
            "noncomputable def isUnicodeScalar (n : Nat) : Bool :=\n"
            "  !(Nat.ble 0xd800 n && Nat.ble n 0xdfff)"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_char_above_unicode_max",
    ),
    MirSemanticsGuard(
        guard_id="enum_char_surrogate_gap",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="char surrogate code point in [0xD800, 0xDFFF] faults UB",
        anchor=(
            "noncomputable def isUnicodeScalar (n : Nat) : Bool :=\n"
            "  Nat.ble n 0x10ffff && !(Nat.ble 0xd800 n && Nat.ble n 0xdfff)"
        ),
        replacement=(
            "noncomputable def isUnicodeScalar (n : Nat) : Bool :=\n"
            "  Nat.ble n 0x10ffff"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_char_surrogate_gap",
    ),
    MirSemanticsGuard(
        guard_id="enum_identity_empty_rejected",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="identityKey? rejects empty body identity",
        anchor=(
            "noncomputable def identityKey? (identity : String) : Option IdentityKey :=\n"
            "  match identity.toByteArray.data.toList with\n"
            "  | [] => none\n"
            "  | bs => some ⟨byteListTag 1 0 bs, bs⟩"
        ),
        replacement=(
            "noncomputable def identityKey? (identity : String) : Option IdentityKey :=\n"
            "  match identity.toByteArray.data.toList with\n"
            "  | [] => some ⟨0, []⟩\n"
            "  | bs => some ⟨byteListTag 1 0 bs, bs⟩"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_identity_empty_rejected",
    ),
    MirSemanticsGuard(
        guard_id="enum_identity_duplicate_rejected",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="identityRbInsertAux rejects duplicate body identities",
        anchor="    | .eq => none\n    | .gt =>",
        replacement="    | .eq => some (.node c l x xv r)\n    | .gt =>",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_identity_duplicate_rejected",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_nonempty",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted rejects 0-variant enums",
        anchor=(
            "noncomputable def enumAdmitted (ety : EnumTy) : Bool :=\n"
            "  !ety.discriminants.isEmpty &&"
        ),
        replacement=(
            "noncomputable def enumAdmitted (ety : EnumTy) : Bool :=\n"
            "  true &&"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_nonempty",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_variant_count_bound",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted enforces variant count < 2^32",
        anchor="    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&",
        replacement="    true &&",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_variant_count_bound",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_discr_fits_width",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted requires every discriminant fits discrWidth",
        anchor=(
            "    ety.discriminants.all\n"
            "      (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) &&"
        ),
        replacement="    true &&",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_discr_fits_width",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_discr_distinct",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted requires pairwise-distinct discriminants",
        anchor="    natListPairwiseNe ety.discriminants &&",
        replacement="    true &&",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_discr_distinct",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_zst_single_variant",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted requires .zeroSized enum to have 1 variant",
        anchor="    | .zeroSized => Nat.beq ety.discriminants.length 1",
        replacement="    | .zeroSized => true",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_zst_single_variant",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_scalar_tag_lossless",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted requires scalar tag roundtrip to be lossless",
        anchor=(
            "    | .scalar tagW tagS =>\n"
            "      ety.discriminants.all (fun d =>\n"
            "        let dBits := BitVec.ofNat 128 d\n"
            "        tagBitsToDiscrBits tagW tagS ety.discrWidth\n"
            "          (truncateBits tagW dBits) == dBits)"
        ),
        replacement="    | .scalar _ _ => true",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_scalar_tag_lossless",
    ),
    MirSemanticsGuard(
        guard_id="enum_ordering_invalid_tag_none",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="orderingOfTagBits returns none for tags outside {-1,0,1}",
        anchor=(
            "  else if Nat.beq bits 1 then\n"
            "    some .greater\n"
            "  else\n"
            "    none"
        ),
        replacement=(
            "  else if Nat.beq bits 1 then\n"
            "    some .greater\n"
            "  else\n"
            "    some .equal"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_ordering_invalid_tag_none",
    ),
    MirSemanticsGuard(
        guard_id="enum_val_ty_enum_variant_in_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="Val.ty? requires enumVal variant index < discriminants.length",
        anchor="    if enumAdmitted ety && Nat.blt v ety.discriminants.length then",
        replacement="    if enumAdmitted ety && true then",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_val_ty_enum_variant_in_bounds",
    ),
    MirSemanticsGuard(
        guard_id="enum_val_ty_overflow_pair_wf",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="Val.ty? enforces sv.wf on overflow-pair tuple scalars",
        anchor=(
            "  | .tuple [.scalar sv, .bool _] =>\n"
            "    if sv.wf then some (.tuple [.int sv.width sv.signed, .bool]) else none"
        ),
        replacement=(
            "  | .tuple [.scalar sv, .bool _] =>\n"
            "    some (.tuple [.int sv.width sv.signed, .bool])"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_val_ty_overflow_pair_wf",
    ),
    MirSemanticsGuard(
        guard_id="enum_check_args_length_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="checkArgsMatch rejects argument-count mismatches",
        anchor=(
            "  | v :: vs, ty :: tys => checkVal v ty && checkArgsMatch vs tys\n"
            "  | _, _ => false"
        ),
        replacement=(
            "  | v :: vs, ty :: tys => checkVal v ty && checkArgsMatch vs tys\n"
            "  | _, _ => true"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_check_args_length_mismatch",
    ),
    MirSemanticsGuard(
        guard_id="enum_supported_ty_reject_non_overflow_tuple",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedScalarOrUnitTy rejects non-overflow-pair tuples",
        anchor=(
            "  | .enum ety => enumAdmitted ety\n"
            "  | .tuple fs => isOverflowPairTy (.tuple fs)"
        ),
        replacement=(
            "  | .enum ety => enumAdmitted ety\n"
            "  | .tuple _ => true"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_supported_ty_reject_non_overflow_tuple",
    ),
    MirSemanticsGuard(
        guard_id="enum_supported_ty_reject_ref_ptr",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedScalarOrUnitTy rejects ref/rawPtr/unsupported",
        anchor=(
            "  | .enum ety => enumAdmitted ety\n"
            "  | .tuple fs => isOverflowPairTy (.tuple fs)\n"
            "  | _ => false"
        ),
        replacement=(
            "  | .enum ety => enumAdmitted ety\n"
            "  | .tuple fs => isOverflowPairTy (.tuple fs)\n"
            "  | _ => true"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_supported_ty_reject_ref_ptr",
    ),
    MirSemanticsGuard(
        guard_id="enum_live_uninit_scalar_enum_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="liveUninitSlot starts scalar-tagged enums uninitialized",
        anchor=(
            "  | .enum ety =>\n"
            "    if isZstEnumTy ety then .immediate (some (.enumVal ety 0))\n"
            "    else .immediate none"
        ),
        replacement=(
            "  | .enum ety =>\n"
            "    .immediate (some (.enumVal ety 0))"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_live_uninit_scalar_enum_uninit",
    ),
    # ------------------------------------------------------------------
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Layout.lean (8 alignment & admission guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="layout_unadmitted_enum_none",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="layoutOfTy returns none for unadmitted fieldless enums",
        anchor=(
            "  | .enum ety =>\n"
            "    if !enumAdmitted ety then\n"
            "      none"
        ),
        replacement=(
            "  | .enum ety =>\n"
            "    if false then\n"
            "      none"
        ),
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_unadmitted_enum_none",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_unsupported_ty_none",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="layoutOfTy returns none for unsupported types",
        anchor=(
            "  | .tuple [.int w _, .bool] => some (overflowPairLayout w)\n"
            "  | _ => none"
        ),
        replacement=(
            "  | .tuple [.int w _, .bool] => some (overflowPairLayout w)\n"
            "  | _ => some ⟨0, 0⟩"
        ),
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_unsupported_ty_none",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_int_i16_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="intLayout 2-byte alignment for i16/u16 (function-level; unobs. in v1)",
        anchor="  | .i16 => ⟨2, 1⟩",
        replacement="  | .i16 => ⟨2, 0⟩",
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_int_i16_align",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_int_i32_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="intLayout 4-byte alignment for i32/u32 (function-level; unobs. in v1)",
        anchor="  | .i32 => ⟨4, 2⟩",
        replacement="  | .i32 => ⟨4, 0⟩",
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_int_i32_align",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_int_i64_isize_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="intLayout 8-byte alignment for i64/isize (function-level; unobs. in v1)",
        anchor="  | .i64 | .isize => ⟨8, 3⟩",
        replacement="  | .i64 | .isize => ⟨8, 0⟩",
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_int_i64_isize_align",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_int_i128_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="intLayout 16-byte alignment for i128/u128 (function-level; unobs. in v1)",
        anchor="  | .i128 => ⟨16, 4⟩",
        replacement="  | .i128 => ⟨16, 0⟩",
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_int_i128_align",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_char_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="layoutOfTy 4-byte alignment for char (function-level; unobs. in v1)",
        anchor="  | .char => some ⟨4, 2⟩",
        replacement="  | .char => some ⟨4, 0⟩",
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_char_align",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="layout_overflow_pair_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="overflowPairLayout ABI alignment (function-level; unobs. in v1)",
        anchor=(
            "noncomputable def overflowPairLayout (w : IntWidth) : LayoutData :=\n"
            "  ⟨2 * (intLayout w).size, (intLayout w).alignLog2⟩"
        ),
        replacement=(
            "noncomputable def overflowPairLayout (w : IntWidth) : LayoutData :=\n"
            "  ⟨2 * (intLayout w).size, 0⟩"
        ),
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_overflow_pair_align",
        sanity_module="LayoutSanity",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Bytes.lean (28 validity, width, codec & UTF-8 guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="bytes_invalid_bool_value",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="bool scalar outside {0, 1} faults UB",
        anchor=(
            "      else if v == 1 then\n"
            "        .ok (.bool true)\n"
            "      else\n"
            "        .error .undefined"
        ),
        replacement=(
            "      else if v == 1 then\n"
            "        .ok (.bool true)\n"
            "      else\n"
            "        .ok (.bool true)"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_invalid_bool_value",
    ),
    MirSemanticsGuard(
        guard_id="bytes_invalid_char_surrogate",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit char rejects non-Unicode scalar values as UB",
        anchor=(
            "    else if isUnicodeScalar bits.toNat then\n"
            "      .ok (.char (Char.ofNat bits.toNat))\n"
            "    else\n"
            "      .error .undefined"
        ),
        replacement=(
            "    else if true then\n"
            "      .ok (.char (Char.ofNat bits.toNat))\n"
            "    else\n"
            "      .error .undefined"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_invalid_char_surrogate",
    ),
    MirSemanticsGuard(
        guard_id="bytes_invalid_ordering_tag",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="Ordering tag outside {-1_i8, 0, 1} faults UB",
        anchor=(
            "      match orderingOfTagBits bits.toNat with\n"
            "      | some ord => .ok (.ordering ord)\n"
            "      | none => .error .undefined"
        ),
        replacement=(
            "      match orderingOfTagBits bits.toNat with\n"
            "      | some ord => .ok (.ordering ord)\n"
            "      | none => .ok (.ordering .equal)"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_invalid_ordering_tag",
    ),
    MirSemanticsGuard(
        guard_id="bytes_invalid_enum_tag",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="Fieldless enum tag not matching any discriminant faults UB",
        anchor=(
            "        match findDiscrVariant? discrBits ety.discriminants with\n"
            "        | some v => .ok (.enumVal ety v)\n"
            "        | none => .error .undefined"
        ),
        replacement=(
            "        match findDiscrVariant? discrBits ety.discriminants with\n"
            "        | some v => .ok (.enumVal ety v)\n"
            "        | none => .ok (.enumVal ety 0)"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_invalid_enum_tag",
    ),
    MirSemanticsGuard(
        guard_id="bytes_uninit_memory_read",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="initBytes? rejects uninitialized bytes rather than zeroing",
        anchor=(
            "noncomputable def initBytes? : List AllocByte → Option (List UInt8)\n"
            "  | [] => some []\n"
            "  | .uninit :: _ => none"
        ),
        replacement=(
            "noncomputable def initBytes? : List AllocByte → Option (List UInt8)\n"
            "  | [] => some []\n"
            "  | .uninit :: rest =>\n"
            "    match initBytes? rest with\n"
            "    | some bs => some (0 :: bs)\n"
            "    | none => none"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_uninit_memory_read",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_int_width_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit int rejects scalar bits exceeding width",
        anchor=(
            "  | .int w s, .scalar bits =>\n"
            "    if truncateBits w bits != bits then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "  | .int w s, .scalar bits =>\n"
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_int_width_overflow",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_bool_width_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit bool rejects scalar bits exceeding 1 byte",
        anchor=(
            "  | .bool, .scalar bits =>\n"
            "    if truncateBits .i8 bits != bits then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "  | .bool, .scalar bits =>\n"
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_bool_width_overflow",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_char_width_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit char >32-bit lockstep-classifies as .unsupported",
        anchor=(
            "  | .char, .scalar bits =>\n"
            "    if truncateBits .i32 bits != bits then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "  | .char, .scalar bits =>\n"
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_char_width_overflow",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_ordering_width_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit ordering >8-bit lockstep-classifies as .unsupported",
        anchor=(
            "  | .ordering, .scalar bits =>\n"
            "    if truncateBits .i8 bits != bits then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "  | .ordering, .scalar bits =>\n"
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_ordering_width_overflow",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_zst_enum_requires_zst",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit enum zeroSized requires isZstEnumTy",
        anchor=(
            "  | .enum ety, .zeroSized =>\n"
            "    if isZstEnumTy ety then .ok (.enumVal ety 0) else .error .unsupported"
        ),
        replacement=(
            "  | .enum ety, .zeroSized =>\n"
            "    .ok (.enumVal ety 0)"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_zst_enum_requires_zst",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_scalar_lit_on_zst_enum",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit rejects ConstLit.scalar on .zeroSized enum",
        anchor=(
            "    match ety.tagRepr with\n"
            "    | .zeroSized => .error .unsupported"
        ),
        replacement=(
            "    match ety.tagRepr with\n"
            "    | .zeroSized => .ok (.enumVal ety 0)"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_scalar_lit_on_zst_enum",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_scalar_enum_width_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit scalar enum rejects tag bits exceeding tagW",
        anchor="      if !enumAdmitted ety || truncateBits tagW bits != bits then",
        replacement="      if !enumAdmitted ety || false then",
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_scalar_enum_width_overflow",
    ),
    MirSemanticsGuard(
        guard_id="bytes_const_mismatched_lit_kind",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit rejects mismatched type/literal combinations",
        anchor=(
            "        | none => .error .undefined\n"
            "  | _, _ => .error .unsupported"
        ),
        replacement=(
            "        | none => .error .undefined\n"
            "  | _, _ => .ok .unit"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_const_mismatched_lit_kind",
    ),
    MirSemanticsGuard(
        guard_id="bytes_encode_val_checks_type",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="encodeVal rejects invalid values (function-level defense-in-depth)",
        anchor=(
            "noncomputable def encodeVal (endian : TargetEndian) (ty : MirTy) (v : Val) :\n"
            "    Except FaultKind (List AllocByte) :=\n"
            "  if !checkVal v ty then\n"
            "    .error .unsupported"
        ),
        replacement=(
            "noncomputable def encodeVal (endian : TargetEndian) (ty : MirTy) (v : Val) :\n"
            "    Except FaultKind (List AllocByte) :=\n"
            "  if false then\n"
            "    .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_encode_val_checks_type",
    ),
    MirSemanticsGuard(
        guard_id="bytes_encode_overflow_pair_padding_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="encodeVal writes uninit padding bytes for overflow pairs",
        anchor="        List.replicate (w.byteSize - 1) AllocByte.uninit)",
        replacement="        List.replicate (w.byteSize - 1) (AllocByte.init 0 none))",
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_encode_overflow_pair_padding_uninit",
    ),
    MirSemanticsGuard(
        guard_id="bytes_decode_never_returns_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="decodeVal returns .ok none for uninhabited .never",
        anchor="  | .never => .ok none",
        replacement="  | .never => .ok (some .unit)",
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_decode_never_returns_uninit",
    ),
    MirSemanticsGuard(
        guard_id="bytes_decode_length_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="decodeVal checks byte length (function-level defense-in-depth)",
        anchor=(
            "      if !Nat.beq bytes.length layout.size then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "      if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_decode_length_mismatch",
    ),
    MirSemanticsGuard(
        guard_id="bytes_decode_overflow_pair_length_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="decodeVal checks overflow-pair size (function-level defense-in-depth)",
        anchor=(
            "    if !Nat.beq bytes.length (overflowPairLayout w).size then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_decode_overflow_pair_length_mismatch",
    ),
    MirSemanticsGuard(
        guard_id="bytes_decode_overflow_pair_uninit_bool",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="decodeVal returns .ok none when overflow-pair bytes are uninit",
        anchor=(
            "          | .ok boolVal => .ok (some (.tuple [intVal, boolVal]))\n"
            "      | _, _ => .ok none"
        ),
        replacement=(
            "          | .ok boolVal => .ok (some (.tuple [intVal, boolVal]))\n"
            "      | _, _ => .ok (some (.tuple [.scalar ⟨w, s, BitVec.ofNat 128 0⟩, .bool false]))"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_decode_overflow_pair_uninit_bool",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_two_byte_lead_min",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go rejects the overlong two-byte leads 0xC0 and 0xC1"
        ),
        anchor=(
            "    else if Nat.ble 0xC2 n && Nat.ble n 0xDF then validUtf8Go 1 0x80 0xBF rest"
        ),
        replacement=(
            "    else if Nat.ble 0xC0 n && Nat.ble n 0xDF then validUtf8Go 1 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_two_byte_lead_min",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_e0_overlong",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go narrows the second byte after 0xE0 to 0xA0..=0xBF"
        ),
        anchor=(
            "    else if Nat.beq n 0xE0 then validUtf8Go 2 0xA0 0xBF rest"
        ),
        replacement=(
            "    else if Nat.beq n 0xE0 then validUtf8Go 2 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_e0_overlong",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_ed_surrogate",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go narrows the second byte after 0xED to 0x80..=0x9F"
        ),
        anchor=(
            "    else if Nat.beq n 0xED then validUtf8Go 2 0x80 0x9F rest"
        ),
        replacement=(
            "    else if Nat.beq n 0xED then validUtf8Go 2 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_ed_surrogate",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_f0_overlong",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go narrows the second byte after 0xF0 to 0x90..=0xBF"
        ),
        anchor=(
            "    else if Nat.beq n 0xF0 then validUtf8Go 3 0x90 0xBF rest"
        ),
        replacement=(
            "    else if Nat.beq n 0xF0 then validUtf8Go 3 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_f0_overlong",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_f4_max",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go narrows the second byte after 0xF4 to 0x80..=0x8F"
        ),
        anchor=(
            "    else if Nat.beq n 0xF4 then validUtf8Go 3 0x80 0x8F rest"
        ),
        replacement=(
            "    else if Nat.beq n 0xF4 then validUtf8Go 3 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_f4_max",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_invalid_lead",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go rejects lone continuation bytes and leads 0xF5..=0xFF"
        ),
        anchor=(
            "    else if Nat.beq n 0xF4 then validUtf8Go 3 0x80 0x8F rest\n"
            "    else false"
        ),
        replacement=(
            "    else if Nat.beq n 0xF4 then validUtf8Go 3 0x80 0x8F rest\n"
            "    else true"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_invalid_lead",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_truncated",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go rejects input that ends inside a multi-byte sequence"
        ),
        anchor=(
            "  | _ + 1, _, _, [] => false"
        ),
        replacement=(
            "  | _ + 1, _, _, [] => true"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_truncated",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_continuation_hi",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go bounds continuation bytes above by 0xBF"
        ),
        anchor=(
            "    Nat.ble lo b.toNat && Nat.ble b.toNat hi && validUtf8Go k 0x80 0xBF rest"
        ),
        replacement=(
            "    Nat.ble lo b.toNat && validUtf8Go k 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_continuation_hi",
    ),
    MirSemanticsGuard(
        guard_id="bytes_utf8_continuation_lo",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "validUtf8Go bounds continuation bytes below by 0x80"
        ),
        anchor=(
            "    Nat.ble lo b.toNat && Nat.ble b.toNat hi && validUtf8Go k 0x80 0xBF rest"
        ),
        replacement=(
            "    Nat.ble b.toNat hi && validUtf8Go k 0x80 0xBF rest"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_utf8_continuation_lo",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Memory.lean (29 allocation/bounds/align/mut/
    # provenance guards; 6 additional Profile v2 memory guards follow = 35)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="mem_dealloc_nonzero_offset",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="deallocateStack rejects non-zero pointer offset as UB",
        anchor=(
            "noncomputable def deallocateStack (m : MemoryState) (place : MemPlace) :\n"
            "    Except FaultKind MemoryState :=\n"
            "  if !Nat.beq place.offset 0 then\n"
            "    .error .undefined"
        ),
        replacement=(
            "noncomputable def deallocateStack (m : MemoryState) (place : MemPlace) :\n"
            "    Except FaultKind MemoryState :=\n"
            "  if false then\n"
            "    .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_dealloc_nonzero_offset",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_dealloc_missing_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="deallocateStack rejects missing allocation id as UB",
        anchor=(
            "    match findAllocation place.allocId m.allocations with\n"
            "    | none => .error .undefined\n"
            "    | some a =>\n"
            "      if !a.live then\n"
            "        .error .undefined"
        ),
        replacement=(
            "    match findAllocation place.allocId m.allocations with\n"
            "    | none => .ok m\n"
            "    | some a =>\n"
            "      if !a.live then\n"
            "        .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_dealloc_missing_alloc",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_dealloc_use_after_free",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="deallocateStack rejects double-free on dead allocation as UB",
        anchor=(
            "      if !a.live then\n"
            "        .error .undefined\n"
            "      else\n"
            "        match a.mutability with\n"
            "        | .shared => .error .undefined"
        ),
        replacement=(
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        match a.mutability with\n"
            "        | .shared => .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_dealloc_use_after_free",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_dealloc_immutable",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="deallocateStack rejects immutable (.shared) allocation as UB",
        anchor=(
            "        match a.mutability with\n"
            "        | .shared => .error .undefined\n"
            "        | .mut =>\n"
            "          .ok { m with\n"
            "            allocations :=\n"
            "              replaceAllocation { a with live := false } m.allocations }"
        ),
        replacement=(
            "        match a.mutability with\n"
            "        | .shared => .ok m\n"
            "        | .mut =>\n"
            "          .ok { m with\n"
            "            allocations :=\n"
            "              replaceAllocation { a with live := false } m.allocations }"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_dealloc_immutable",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_missing_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="readBytes rejects missing allocation id as UB",
        anchor=(
            "  match findAllocation place.allocId m.allocations with\n"
            "  | none => .error .undefined\n"
            "  | some a =>\n"
            "    if Nat.beq size 0 then"
        ),
        replacement=(
            "  match findAllocation place.allocId m.allocations with\n"
            "  | none => .ok []\n"
            "  | some a =>\n"
            "    if Nat.beq size 0 then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_missing_alloc",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_use_after_free",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="readBytes rejects reading from deallocated allocation as UB",
        anchor=(
            "    else if !a.live || !isInBounds a place.offset size ||\n"
            "        !isAligned a place.offset alignLog2 then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok ((a.bytes.drop place.offset).take size)"
        ),
        replacement=(
            "    else if false || !isInBounds a place.offset size ||\n"
            "        !isAligned a place.offset alignLog2 then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok ((a.bytes.drop place.offset).take size)"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_use_after_free",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_out_of_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="readBytes rejects out-of-bounds read as UB",
        anchor=(
            "    else if !a.live || !isInBounds a place.offset size ||\n"
            "        !isAligned a place.offset alignLog2 then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok ((a.bytes.drop place.offset).take size)"
        ),
        replacement=(
            "    else if !a.live || false ||\n"
            "        !isAligned a place.offset alignLog2 then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok ((a.bytes.drop place.offset).take size)"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_out_of_bounds",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="readBytes rejects misaligned access as UB",
        anchor=(
            "    else if !a.live || !isInBounds a place.offset size ||\n"
            "        !isAligned a place.offset alignLog2 then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok ((a.bytes.drop place.offset).take size)"
        ),
        replacement=(
            "    else if !a.live || !isInBounds a place.offset size ||\n"
            "        false then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok ((a.bytes.drop place.offset).take size)"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_zst_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="readBytes rejects misaligned zero-size read as UB",
        anchor=(
            "    if Nat.beq size 0 then\n"
            "      if !isAligned a place.offset alignLog2 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok []"
        ),
        replacement=(
            "    if Nat.beq size 0 then\n"
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok []"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_zst_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_missing_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects missing allocation id as UB",
        anchor=(
            "  match findAllocation place.allocId m.allocations with\n"
            "  | none => .error .undefined\n"
            "  | some a =>\n"
            "    if Nat.beq bytes.length 0 then"
        ),
        replacement=(
            "  match findAllocation place.allocId m.allocations with\n"
            "  | none => .ok m\n"
            "  | some a =>\n"
            "    if Nat.beq bytes.length 0 then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_missing_alloc",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_use_after_free",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects writing to deallocated allocation as UB",
        anchor=(
            "    else if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "        !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "    else if false || !isInBounds a place.offset bytes.length ||\n"
            "        !isAligned a place.offset alignLog2 then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_use_after_free",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_out_of_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects out-of-bounds write as UB",
        anchor=(
            "    else if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "        !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "    else if !a.live || false ||\n"
            "        !isAligned a place.offset alignLog2 then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_out_of_bounds",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects misaligned write as UB",
        anchor=(
            "    else if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "        !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "    else if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "        false then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_readonly",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects writing to .shared allocation as UB",
        anchor=(
            "      match a.mutability with\n"
            "      | .shared => .error .undefined\n"
            "      | .mut =>\n"
            "        let bytes' :="
        ),
        replacement=(
            "      match a.mutability with\n"
            "      | .shared => .ok m\n"
            "      | .mut =>\n"
            "        let bytes' :="
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_readonly",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_zst_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects misaligned empty write as UB",
        anchor=(
            "    if Nat.beq bytes.length 0 then\n"
            "      if !isAligned a place.offset alignLog2 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok m"
        ),
        replacement=(
            "    if Nat.beq bytes.length 0 then\n"
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok m"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_zst_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_zst_alloc_align",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "readBytes rejects zero-size read above the "
            "allocation alignment as UB"
        ),
        anchor=(
            "    if Nat.beq size 0 then\n"
            "      if !isAligned a place.offset alignLog2 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok []"
        ),
        replacement=(
            "    if Nat.beq size 0 then\n"
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok []"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_zst_alloc_align",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_read_zst_dead_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "readBytes rejects misaligned zero-size read "
            "of a dead allocation as UB"
        ),
        anchor=(
            "    if Nat.beq size 0 then\n"
            "      if !isAligned a place.offset alignLog2 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok []"
        ),
        replacement=(
            "    if Nat.beq size 0 then\n"
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok []"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_zst_dead_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_uninit_zst_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeUninit rejects misaligned zero-size write as UB",
        anchor=(
            "    if Nat.beq bytes.length 0 then\n"
            "      if !isAligned a place.offset alignLog2 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok m"
        ),
        replacement=(
            "    if Nat.beq bytes.length 0 then\n"
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok m"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_uninit_zst_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_zst_missing_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "readBytes rejects zero-size read of a "
            "missing allocation id as UB"
        ),
        anchor=(
            "  match findAllocation place.allocId m.allocations with\n"
            "  | none => .error .undefined\n"
            "  | some a =>\n"
            "    if Nat.beq size 0 then"
        ),
        replacement=(
            "  match findAllocation place.allocId m.allocations with\n"
            "  | none => .ok []\n"
            "  | some a =>\n"
            "    if Nat.beq size 0 then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_zst_missing_alloc",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_align_alloc_align_check",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="isAligned requires allocation alignment >= access alignment",
        anchor=(
            "noncomputable def isAligned (a : Allocation) (offset alignLog2 : Nat) : Bool :=\n"
            "  Nat.ble alignLog2 a.alignLog2 &&\n"
            "    Nat.beq (Nat.mod offset (Nat.pow 2 alignLog2)) 0"
        ),
        replacement=(
            "noncomputable def isAligned (a : Allocation) (offset alignLog2 : Nat) : Bool :=\n"
            "  true &&\n"
            "    Nat.beq (Nat.mod offset (Nat.pow 2 alignLog2)) 0"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_align_alloc_align_check",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_align_offset_mod_check",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="isAligned requires offset % 2^alignLog2 == 0",
        anchor=(
            "noncomputable def isAligned (a : Allocation) (offset alignLog2 : Nat) : Bool :=\n"
            "  Nat.ble alignLog2 a.alignLog2 &&\n"
            "    Nat.beq (Nat.mod offset (Nat.pow 2 alignLog2)) 0"
        ),
        replacement=(
            "noncomputable def isAligned (a : Allocation) (offset alignLog2 : Nat) : Bool :=\n"
            "  Nat.ble alignLog2 a.alignLog2 &&\n"
            "    true"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_align_offset_mod_check",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_reserve_alloc_id_monotonic",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="reserveAllocId increments nextAllocId so ids never alias",
        anchor="  ({ m with nextAllocId := m.nextAllocId + 1 }, m.nextAllocId)",
        replacement="  ({ m with nextAllocId := m.nextAllocId }, m.nextAllocId)",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_reserve_alloc_id_monotonic",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_alloc_initializes_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="allocateStack fills fresh allocations with .uninit bytes",
        anchor="    bytes := List.replicate layout.size .uninit",
        replacement="    bytes := List.replicate layout.size (.init 0 none)",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_alloc_initializes_uninit",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_dealloc_marks_dead",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="deallocateStack sets live := false on the freed allocation",
        anchor="              replaceAllocation { a with live := false } m.allocations }",
        replacement="              replaceAllocation a m.allocations }",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_dealloc_marks_dead",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_in_bounds_includes_size",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="isInBounds checks offset + size <= bytes.length",
        anchor=(
            "noncomputable def isInBounds (a : Allocation) (offset size : Nat) : Bool :=\n"
            "  Nat.ble (offset + size) a.bytes.length"
        ),
        replacement=(
            "noncomputable def isInBounds (a : Allocation) (offset _size : Nat) : Bool :=\n"
            "  Nat.ble offset a.bytes.length"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_in_bounds_includes_size",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_uninit_marks_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeUninit writes .uninit bytes rather than zero bytes",
        anchor="  writeBytes m place alignLog2 (List.replicate size .uninit)",
        replacement="  writeBytes m place alignLog2 (List.replicate size (.init 0 none))",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_uninit_marks_uninit",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/State.lean (13 entry & storage-liveness guards,
    # 9 singleBodyStaticAdmitted guards, & 5 sysroot/call/init guards = 27)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="state_init_pointer_width_64",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState rejects non-64-bit pointerWidthBits",
        anchor="  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then",
        replacement="  if false || !Nat.beq p.mirProfileVersion 1 then",
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_pointer_width_64",
    ),
    MirSemanticsGuard(
        guard_id="state_init_mir_profile_v1",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState rejects non-v1 mirProfileVersion",
        anchor="  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then",
        replacement="  if !Nat.beq p.pointerWidthBits 64 || false then",
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_mir_profile_v1",
    ),
    MirSemanticsGuard(
        guard_id="state_init_empty_caller_mem",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState rejects non-empty callerMem",
        anchor="  else if !q.callerMem.allocations.isEmpty then\n    .error .unsupported",
        replacement="  else if false then\n    .error .unsupported",
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_empty_caller_mem",
    ),
    MirSemanticsGuard(
        guard_id="state_init_nonempty_blocks",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState rejects empty basicBlocks list",
        anchor=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some body =>\n"
            "      if false then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_nonempty_blocks",
    ),
    MirSemanticsGuard(
        guard_id="state_init_arg_count_lt_locals",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState requires argumentCount < locals.length",
        anchor=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_arg_count_lt_locals",
    ),
    MirSemanticsGuard(
        guard_id="state_init_storage_annotations_in_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState enforces storageAnnotationsInBounds",
        anchor=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_storage_annotations_in_bounds",
    ),
    MirSemanticsGuard(
        guard_id="state_storage_oob_marker_check",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="storageAnnotationsInBounds checks StorageLive/Dead < numLocals",
        anchor="      | .storageLive id | .storageDead id => Nat.blt id numLocals",
        replacement="      | .storageLive _ | .storageDead _ => true",
        fixture_module="StateRefutations",
        theorem_name="refute_state_storage_oob_marker_check",
    ),
    MirSemanticsGuard(
        guard_id="state_init_discriminant_types_valid",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState enforces discriminantTypesValid",
        anchor=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_discriminant_types_valid",
    ),
    MirSemanticsGuard(
        guard_id="state_discr_ordering_type_check",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="discriminantTypesValid enforces i8 destination for Ordering",
        anchor=(
            "              | .ordering =>\n"
            "                match getElem? body.locals dst.localId with\n"
            "                | some dstTy => MirTy.beq dstTy (.int .i8 true)"
        ),
        replacement=(
            "              | .ordering =>\n"
            "                match getElem? body.locals dst.localId with\n"
            "                | some _ => true"
        ),
        fixture_module="StateRefutations",
        theorem_name="refute_state_discr_ordering_type_check",
    ),
    MirSemanticsGuard(
        guard_id="state_init_cast_types_valid",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState enforces castTypesValid",
        anchor=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !castTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some body =>\n"
            "      if body.basicBlocks.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !Nat.blt body.argumentCount body.locals.length then\n"
            "        .error .unsupported\n"
            "      else if !storageAnnotationsInBounds body then\n"
            "        .error .unsupported\n"
            "      else if !discriminantTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported\n"
            "      else if !assertConditionTypesValid body then\n"
            "        .error .unsupported\n"
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_cast_types_valid",
    ),
    MirSemanticsGuard(
        guard_id="state_init_supported_local_types",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState requires all local types to be supported",
        anchor=(
            "      else if !body.locals.all isSupportedScalarOrUnitTy then\n"
            "        .error .unsupported"
        ),
        replacement="      else if false then\n        .error .unsupported",
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_supported_local_types",
    ),
    MirSemanticsGuard(
        guard_id="state_init_args_match_param_tys",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initState enforces checkArgsMatch on query arguments",
        anchor=(
            "        if !checkArgsMatch q.args paramTys then\n"
            "          .error .unsupported"
        ),
        replacement="        if false then\n          .error .unsupported",
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_args_match_param_tys",
    ),
    MirSemanticsGuard(
        guard_id="state_init_annotated_local_starts_dead",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initLocalsLoop initializes storage-annotated locals as .dead",
        anchor="        else if hasStorageAnnotation body idx then\n          .dead",
        replacement="        else if false then\n          .dead",
        fixture_module="StateRefutations",
        theorem_name="refute_state_init_annotated_local_starts_dead",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Step.lean (44 v1 UB, move-deinit, frame & admission
    # guards, 3 non-root call/return guards, & 17 Profile v2 guards = 64)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="step_copy_dead_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.copy of a .dead local faults UB",
        anchor=(
            "  | .copy place =>\n"
            "    match getElem? bodyLocals place.localId,\n"
            "        getElem? locals place.localId with\n"
            "    | some _, some .dead => .error .undefined"
        ),
        replacement=(
            "  | .copy place =>\n"
            "    match getElem? bodyLocals place.localId,\n"
            "        getElem? locals place.localId with\n"
            "    | some ty, some .dead => .ok (ty, some .unit, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_copy_dead_local",
    ),
    MirSemanticsGuard(
        guard_id="step_move_dead_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.move of a .dead local faults UB",
        anchor=(
            "  | .move place =>\n"
            "    match getElem? bodyLocals place.localId,\n"
            "        getElem? locals place.localId with\n"
            "    | some _, some .dead => .error .undefined"
        ),
        replacement=(
            "  | .move place =>\n"
            "    match getElem? bodyLocals place.localId,\n"
            "        getElem? locals place.localId with\n"
            "    | some ty, some .dead => .ok (ty, some .unit, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_move_dead_local",
    ),
    MirSemanticsGuard(
        guard_id="step_move_deinit_immediate",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.move deinitializes immediate non-ZST locals",
        anchor=(
            "        match setElem? locals place.localId (liveUninitSlot ty) with\n"
            "        | some locals' => .ok (ty, optVal, locals', mem)"
        ),
        replacement=(
            "        match some locals with\n"
            "        | some locals' => .ok (ty, optVal, locals', mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_move_deinit_immediate",
    ),
    MirSemanticsGuard(
        guard_id="step_move_deinit_indirect",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.move deinitializes indirect non-ZST locals in memory",
        anchor=(
            "          match deinitIndirect mem ty mplace with\n"
            "          | .ok mem' => .ok (ty, optVal, locals, mem')"
        ),
        replacement=(
            "          match (Except.ok mem : Except FaultKind MemoryState) with\n"
            "          | .ok mem' => .ok (ty, optVal, locals, mem')"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_move_deinit_indirect",
    ),
    MirSemanticsGuard(
        guard_id="step_prim_uninit_read",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalPrimitiveOperand rejects uninitialized local as UB",
        anchor=(
            "      match optVal with\n"
            "      | some v => .ok (v, locals', mem')\n"
            "      | none => .error .undefined"
        ),
        replacement=(
            "      match optVal with\n"
            "      | some v => .ok (v, locals', mem')\n"
            "      | none => .ok (.bool false, locals', mem')"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_prim_uninit_read",
    ),
    MirSemanticsGuard(
        guard_id="step_discriminant_uninit_enum",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalDiscriminantOfVal rejects uninitialized scalar enum as UB",
        anchor="    | .scalar _ _, none => .error .undefined",
        replacement=(
            "    | .scalar _ _, none =>\n"
            "      .ok (.scalar ⟨ety.discrWidth, ety.discrSigned, BitVec.ofNat 128 0⟩, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_discriminant_uninit_enum",
    ),
    MirSemanticsGuard(
        guard_id="step_discriminant_uninit_ordering",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalOrderingDiscriminantOfVal rejects uninitialized Ordering as UB",
        anchor=(
            "  match optVal with\n"
            "  | none => .error .undefined\n"
            "  | some (.ordering ord) =>"
        ),
        replacement=(
            "  match optVal with\n"
            "  | none => .ok (.scalar ⟨.i8, true, BitVec.ofNat 128 0⟩, locals, mem)\n"
            "  | some (.ordering ord) =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_discriminant_uninit_ordering",
    ),
    MirSemanticsGuard(
        guard_id="step_use_uninit_read",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue .use rejects uninitialized source local as UB",
        anchor=(
            "        match optVal with\n"
            "        | some v => .ok (v, locals₁, mem₁)\n"
            "        | none => .error .undefined"
        ),
        replacement=(
            "        match optVal with\n"
            "        | some v => .ok (v, locals₁, mem₁)\n"
            "        | none => .ok (.bool false, locals₁, mem₁)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_use_uninit_read",
    ),
    MirSemanticsGuard(
        guard_id="step_cast_uninit_read",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue (.cast .intToInt) rejects uninitialized source as UB",
        anchor=(
            "        match optVal with\n"
            "        | none => .error .undefined\n"
            "        | some v =>\n"
            "          match evalIntToIntCast v castTy with"
        ),
        replacement=(
            "        match optVal with\n"
            "        | none =>\n"
            "          match evalIntToIntCast (.bool false) castTy with\n"
            "          | .error k => .error k\n"
            "          | .ok res => .ok (res, locals₁, mem₁)\n"
            "        | some v =>\n"
            "          match evalIntToIntCast v castTy with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_cast_uninit_read",
    ),
    MirSemanticsGuard(
        guard_id="step_discriminant_dead_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue .discriminant rejects .dead local as UB",
        anchor=(
            "  | .discriminant place =>\n"
            "    match getElem? bodyLocals place.localId,\n"
            "        getElem? locals place.localId with\n"
            "    | some _, some .dead => .error .undefined"
        ),
        replacement=(
            "  | .discriminant place =>\n"
            "    match getElem? bodyLocals place.localId,\n"
            "        getElem? locals place.localId with\n"
            "    | some _, some .dead =>\n"
            "      .ok (.scalar ⟨.i8, true, BitVec.ofNat 128 0⟩, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_discriminant_dead_local",
    ),
    MirSemanticsGuard(
        guard_id="step_write_dead_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="writePlace rejects writing to a .dead destination local as UB",
        anchor=(
            "    match getElem? locals dstLocalId with\n"
            "    | none => .error .unsupported\n"
            "    | some .dead => .error .undefined"
        ),
        replacement=(
            "    match getElem? locals dstLocalId with\n"
            "    | none => .error .unsupported\n"
            "    | some .dead =>\n"
            "      match setElem? locals dstLocalId (.immediate (some val)) with\n"
            "      | some locals' => .ok (locals', mem)\n"
            "      | none => .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_write_dead_local",
    ),
    MirSemanticsGuard(
        guard_id="step_return_uninit_or_dead",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="TerminatorKind.return_ rejects uninitialized or dead _0 as UB",
        anchor="      | some (.immediate none) | some .dead => .fault .undefined",
        replacement=(
            "      | some (.immediate none) | some .dead =>\n"
            "        .done (.returned ⟨.unit, callerMem⟩)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_return_uninit_or_dead",
    ),
    MirSemanticsGuard(
        guard_id="step_return_indirect_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="TerminatorKind.return_ rejects uninitialized indirect _0 as UB",
        anchor=(
            "          match loadIndirect mem retTy mplace with\n"
            "          | .ok (some retVal) => .done (.returned ⟨retVal, callerMem⟩)\n"
            "          | .ok none => .fault .undefined"
        ),
        replacement=(
            "          match loadIndirect mem retTy mplace with\n"
            "          | .ok (some retVal) => .done (.returned ⟨retVal, callerMem⟩)\n"
            "          | .ok none => .done (.returned ⟨.unit, callerMem⟩)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_return_indirect_uninit",
    ),
    MirSemanticsGuard(
        guard_id="step_unreachable_terminator",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="TerminatorKind.unreachable faults UB",
        anchor="  | .unreachable =>\n    .fault .undefined",
        replacement="  | .unreachable =>\n    .done (.returned ⟨.unit, callerMem⟩)",
        fixture_module="StepRefutations",
        theorem_name="refute_step_unreachable_terminator",
    ),
    MirSemanticsGuard(
        guard_id="step_force_alloc_dead_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="forceAllocation rejects .dead local as UB",
        anchor=(
            "      match getElem? body.locals localId, getElem? frame.locals localId with\n"
            "      | some _, some .dead => .error .undefined"
        ),
        replacement=(
            "      match getElem? body.locals localId, getElem? frame.locals localId with\n"
            "      | some _, some .dead => .ok (s, ⟨0, 0⟩)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_force_alloc_dead_local",
    ),
    MirSemanticsGuard(
        guard_id="step_nonroot_return_uninit_or_dead",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalNonRootReturn rejects uninitialized or dead callee _0 as UB",
        anchor=(
            "      | some (.immediate (some retVal)) => .ok retVal\n"
            "      | some (.immediate none) | some .dead => .error .undefined"
        ),
        replacement=(
            "      | some (.immediate (some retVal)) => .ok retVal\n"
            "      | some (.immediate none) | some .dead =>\n"
            "        .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_nonroot_return_uninit_or_dead",
    ),
    MirSemanticsGuard(
        guard_id="step_nonroot_return_none_target",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalNonRootReturn faults UB when callee returns to target = none",
        anchor=(
            "                match callee.retTarget? with\n"
            "                | none => .fault .undefined\n"
            "                | some tgt =>"
        ),
        replacement=(
            "                match callee.retTarget? with\n"
            "                | none => .done (.returned ⟨.unit, ⟨[]⟩⟩)\n"
            "                | some tgt =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_nonroot_return_none_target",
    ),
    MirSemanticsGuard(
        guard_id="step_nonroot_return_indirect_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalNonRootReturn fails closed on .indirect callee locals",
        anchor="  if bb.cleanup || localsHaveIndirect callee.locals then",
        replacement="  if bb.cleanup then",
        fixture_module="StepRefutations",
        theorem_name="refute_step_nonroot_return_indirect_local",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/State.lean (3 sysroot UB + 2 call/init guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="state_sysroot_unchecked_add_ub",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="sysrootNumBinOp maps .uncheckedAdd to .addUnchecked (not wrapping .add)",
        anchor=(
            "noncomputable def sysrootNumBinOp : SysrootNumKind → BinOp\n"
            "  | .uncheckedAdd => .addUnchecked"
        ),
        replacement=(
            "noncomputable def sysrootNumBinOp : SysrootNumKind → BinOp\n"
            "  | .uncheckedAdd => .add"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_state_sysroot_unchecked_add_ub",
    ),
    MirSemanticsGuard(
        guard_id="state_sysroot_unchecked_sub_ub",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="sysrootNumBinOp maps .uncheckedSub to .subUnchecked (not wrapping .sub)",
        anchor="  | .uncheckedSub => .subUnchecked",
        replacement="  | .uncheckedSub => .sub",
        fixture_module="StepRefutations",
        theorem_name="refute_state_sysroot_unchecked_sub_ub",
    ),
    MirSemanticsGuard(
        guard_id="state_sysroot_unchecked_mul_ub",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="sysrootNumBinOp maps .uncheckedMul to .mulUnchecked (not wrapping .mul)",
        anchor="  | .uncheckedMul => .mulUnchecked",
        replacement="  | .uncheckedMul => .mul",
        fixture_module="StepRefutations",
        theorem_name="refute_state_sysroot_unchecked_mul_ub",
    ),
    MirSemanticsGuard(
        guard_id="state_calls_admitted_unsafe_callee",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="callsAdmitted rejects intra-crate .call targets that are unsafe fns",
        anchor=(
            "      | some calleeBody =>\n"
            "        !calleeBody.isUnsafe &&\n"
            "          callTargetAdmitted body bb calleeBody args dst target unwind"
        ),
        replacement=(
            "      | some calleeBody =>\n"
            "          callTargetAdmitted body bb calleeBody args dst target unwind"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_state_calls_admitted_unsafe_callee",
    ),
    MirSemanticsGuard(
        guard_id="state_v2_init_uses_entry_memory_for_args",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description=(
            "initStateV2 uses entryMemoryForArgsV2 so callee stack allocations "
            "cannot reuse dangling raw-pointer argument AllocIds"
        ),
        anchor="          let entryMem := entryMemoryForArgsV2 q.callerMem paramTys q.args",
        replacement="          let entryMem := entryMemoryWithCaller q.callerMem",
        fixture_module="StepRefutations",
        theorem_name="refute_state_v2_init_uses_entry_memory_for_args",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_copy_imm_reject_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.copy on immediate local rejects projections",
        anchor=(
            "    | some ty, some (.immediate optVal) =>\n"
            "      if !place.projection.isEmpty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        .ok (ty, optVal, locals, mem)"
        ),
        replacement=(
            "    | some ty, some (.immediate optVal) =>\n"
            "      if false then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        .ok (ty, optVal, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_copy_imm_reject_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_copy_indirect_reject_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.copy on indirect local rejects projections",
        anchor=(
            "    | some ty, some (.indirect mplace) =>\n"
            "      if !place.projection.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !tyOk ty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .ok optVal => .ok (ty, optVal, locals, mem)"
        ),
        replacement=(
            "    | some ty, some (.indirect mplace) =>\n"
            "      if false then\n"
            "        .error .unsupported\n"
            "      else if !tyOk ty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .ok optVal => .ok (ty, optVal, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_copy_indirect_reject_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_copy_indirect_tyok_before_load",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.copy on indirect local checks tyOk before memory read",
        anchor=(
            "      else if !tyOk ty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .ok optVal => .ok (ty, optVal, locals, mem)"
        ),
        replacement=(
            "      else if false then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .ok optVal => .ok (ty, optVal, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_copy_indirect_tyok_before_load",
    ),
    MirSemanticsGuard(
        guard_id="step_move_imm_reject_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.move on immediate local rejects projections",
        anchor=(
            "    | some ty, some (.immediate optVal) =>\n"
            "      if !place.projection.isEmpty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match setElem? locals place.localId (liveUninitSlot ty) with"
        ),
        replacement=(
            "    | some ty, some (.immediate optVal) =>\n"
            "      if false then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match setElem? locals place.localId (liveUninitSlot ty) with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_move_imm_reject_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_move_indirect_reject_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.move on indirect local rejects projections",
        anchor=(
            "    | some ty, some (.indirect mplace) =>\n"
            "      if !place.projection.isEmpty then\n"
            "        .error .unsupported\n"
            "      else if !tyOk ty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .error k => .error k\n"
            "        | .ok optVal =>\n"
            "          match deinitIndirect mem ty mplace with"
        ),
        replacement=(
            "    | some ty, some (.indirect mplace) =>\n"
            "      if false then\n"
            "        .error .unsupported\n"
            "      else if !tyOk ty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .error k => .error k\n"
            "        | .ok optVal =>\n"
            "          match deinitIndirect mem ty mplace with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_move_indirect_reject_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_move_indirect_tyok_before_load",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="Operand.move on indirect local checks tyOk before memory read",
        anchor=(
            "      else if !tyOk ty then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .error k => .error k\n"
            "        | .ok optVal =>\n"
            "          match deinitIndirect mem ty mplace with"
        ),
        replacement=(
            "      else if false then\n"
            "        .error .unsupported\n"
            "      else\n"
            "        match loadIndirect mem ty mplace with\n"
            "        | .error k => .error k\n"
            "        | .ok optVal =>\n"
            "          match deinitIndirect mem ty mplace with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_move_indirect_tyok_before_load",
    ),
    MirSemanticsGuard(
        guard_id="step_prim_operand_requires_primitive_ty",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalPrimitiveOperand rejects non-primitive-readable types",
        anchor=(
            "  | .ok (ty, optVal, locals', mem') =>\n"
            "    if !isPrimitiveReadableTy ty then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "  | .ok (ty, optVal, locals', mem') =>\n"
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_prim_operand_requires_primitive_ty",
    ),
    MirSemanticsGuard(
        guard_id="step_use_type_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue .use lockstep-classifies srcTy != dstTy before uninit",
        anchor="      if !(MirTy.beq srcTy dstTy) then\n        .error .unsupported",
        replacement="      if false then\n        .error .unsupported",
        fixture_module="StepRefutations",
        theorem_name="refute_step_use_type_mismatch",
    ),
    MirSemanticsGuard(
        guard_id="step_cast_requires_intlike_src",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue (.cast .intToInt) lockstep-classifies non-int-like srcTy",
        anchor="      if !isIntLikeTy srcTy then\n        .error .unsupported",
        replacement="      if false then\n        .error .unsupported",
        fixture_module="StepRefutations",
        theorem_name="refute_step_cast_requires_intlike_src",
    ),
    MirSemanticsGuard(
        guard_id="step_discriminant_imm_reject_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue .discriminant rejects projected immediate place",
        anchor=(
            "    | some srcTy, some (.immediate optVal) =>\n"
            "      if !place.projection.isEmpty then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some srcTy, some (.immediate optVal) =>\n"
            "      if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_discriminant_imm_reject_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_discriminant_indirect_reject_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue .discriminant rejects projected indirect place",
        anchor=(
            "    | some srcTy, some (.indirect mplace) =>\n"
            "      if !place.projection.isEmpty then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | some srcTy, some (.indirect mplace) =>\n"
            "      if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_discriminant_indirect_reject_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_write_place_check_val",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="writePlace enforces checkVal val dstTy",
        anchor=(
            "noncomputable def writePlace (locals : List LocalSlot) (mem : MemoryState)\n"
            "    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :\n"
            "    Except FaultKind (List LocalSlot × MemoryState) :=\n"
            "  if !checkVal val dstTy then\n"
            "    .error .unsupported"
        ),
        replacement=(
            "noncomputable def writePlace (locals : List LocalSlot) (mem : MemoryState)\n"
            "    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :\n"
            "    Except FaultKind (List LocalSlot × MemoryState) :=\n"
            "  if false then\n"
            "    .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_write_place_check_val",
    ),
    MirSemanticsGuard(
        guard_id="step_deallocate_local_indirect",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="deallocateLocal frees indirect stack allocation on StorageDead",
        anchor="  | .indirect mplace => deallocateStack mem mplace",
        replacement="  | .indirect _ => .ok mem",
        fixture_module="StepRefutations",
        theorem_name="refute_step_deallocate_local_indirect",
    ),
    MirSemanticsGuard(
        guard_id="step_storage_live_reinits_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="StorageLive resets already-live local to liveUninitSlot",
        anchor="        match setElem? frame.locals localId (liveUninitSlot localTy) with",
        replacement="        match some frame.locals with",
        fixture_module="StepRefutations",
        theorem_name="refute_step_storage_live_reinits_local",
    ),
    MirSemanticsGuard(
        guard_id="step_storage_dead_return_place",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="StorageDead 0 rejects deallocating return place _0",
        anchor=(
            "              callerMem\n"
            "              mem := mem'\n"
            "            }\n"
            "  | .storageDead localId =>\n"
            "    if Nat.beq localId 0 then\n"
            "      .fault .unsupported"
        ),
        replacement=(
            "              callerMem\n"
            "              mem := mem'\n"
            "            }\n"
            "  | .storageDead localId =>\n"
            "    if false then\n"
            "      .fault .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_storage_dead_return_place",
    ),
    MirSemanticsGuard(
        guard_id="step_assign_reject_dst_projection",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalStatement .assign rejects non-empty destination projection",
        anchor=(
            "  | .assign dst rvalue =>\n"
            "    if !dst.projection.isEmpty then\n"
            "      .fault .unsupported"
        ),
        replacement=(
            "  | .assign dst rvalue =>\n"
            "    if false then\n"
            "      .fault .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_assign_reject_dst_projection",
    ),
    MirSemanticsGuard(
        guard_id="step_statement_unsupported_faults",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="StatementKind.unsupported fails closed with .fault .unsupported",
        anchor=(
            "              callerMem\n"
            "              mem := memAfterWrite\n"
            "            }\n"
            "  | .unsupported => .fault .unsupported"
        ),
        replacement=(
            "              callerMem\n"
            "              mem := memAfterWrite\n"
            "            }\n"
            "  | .unsupported =>\n"
            "    .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], "
            "callerMem, mem }"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_statement_unsupported_faults",
    ),
    MirSemanticsGuard(
        guard_id="step_switch_int_case_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalSwitchBranches rejects case bits overflowing width w",
        anchor="    if truncateBits w caseBits != caseBits then\n      .error .unsupported",
        replacement="    if false then\n      .error .unsupported",
        fixture_module="StepRefutations",
        theorem_name="refute_step_switch_int_case_overflow",
    ),
    MirSemanticsGuard(
        guard_id="step_switch_bool_invalid_case",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalBoolSwitchBranches propagates invalid bool case faults",
        anchor=(
            "    | .ok (.bool true) =>\n"
            "      if discr then .ok target else evalBoolSwitchBranches discr otherwise rest\n"
            "    | .error k =>\n"
            "      .error k"
        ),
        replacement=(
            "    | .ok (.bool true) =>\n"
            "      if discr then .ok target else evalBoolSwitchBranches discr otherwise rest\n"
            "    | .error _ =>\n"
            "      evalBoolSwitchBranches discr otherwise rest"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_switch_bool_invalid_case",
    ),
    MirSemanticsGuard(
        guard_id="step_switch_char_invalid_case",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalCharSwitchBranches propagates invalid char case faults",
        anchor=(
            "      else\n"
            "        evalCharSwitchBranches discr otherwise rest\n"
            "    | .error k =>\n"
            "      .error k"
        ),
        replacement=(
            "      else\n"
            "        evalCharSwitchBranches discr otherwise rest\n"
            "    | .error _ =>\n"
            "      evalCharSwitchBranches discr otherwise rest"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_switch_char_invalid_case",
    ),
    MirSemanticsGuard(
        guard_id="step_return_in_cleanup_block",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="TerminatorKind.return_ rejects cleanup unwind blocks",
        anchor=(
            "  | .return_ =>\n"
            "    if bb.cleanup then\n"
            "      .fault .unsupported\n"
            "    else\n"
            "      match getElem? frame.locals 0 with"
        ),
        replacement=(
            "  | .return_ =>\n"
            "    if false then\n"
            "      .fault .unsupported\n"
            "    else\n"
            "      match getElem? frame.locals 0 with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_return_in_cleanup_block",
    ),
    MirSemanticsGuard(
        guard_id="step_switch_overflow_pair_nonempty_branches",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="switchInt on overflow pair rejects non-empty branch lists",
        anchor=(
            "          -- (which compares nothing) jumps to `otherwise`.\n"
            "          match targets.branches with\n"
            "          | [] => .ok targets.otherwise\n"
            "          | _ :: _ => .error .unsupported"
        ),
        replacement=(
            "          -- (which compares nothing) jumps to `otherwise`.\n"
            "          match targets.branches with\n"
            "          | [] => .ok targets.otherwise\n"
            "          | _ :: _ => .ok targets.otherwise"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_switch_overflow_pair_nonempty_branches",
    ),
    MirSemanticsGuard(
        guard_id="step_unsupported_terminators_fault",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "Unmodeled terminators "
            "(unwindResume/call/coreCall/sysrootCall/unsupported) fault"
        ),
        anchor=(
            "  | .unwindResume | .call _ _ _ _ _ | .coreCall _ _ _ _ _\n"
            "  | .sysrootCall _ _ _ _ _ | .unsupported =>\n"
            "    .fault .unsupported"
        ),
        replacement=(
            "  | .unwindResume | .call _ _ _ _ _ | .coreCall _ _ _ _ _\n"
            "  | .sysrootCall _ _ _ _ _ | .unsupported =>\n"
            "    .done (.returned ⟨.unit, callerMem⟩)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_unsupported_terminators_fault",
    ),
    MirSemanticsGuard(
        guard_id="step_oob_block_idx_faults",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalStep faults .unsupported on out-of-bounds blockIdx",
        anchor=(
            "      match getElem? body.basicBlocks frame.blockIdx with\n"
            "      | none => .fault .unsupported\n"
            "      | some bb =>\n"
            "        match getElem? bb.statements frame.stmtIdx with\n"
            "        | some stmt =>\n"
            "          attachCallers callers\n"
            "            (evalStatement body frame s.mem s.callerMem stmt)"
        ),
        replacement=(
            "      match getElem? body.basicBlocks frame.blockIdx with\n"
            "      | none => .done (.returned ⟨.unit, s.callerMem⟩)\n"
            "      | some bb =>\n"
            "        match getElem? bb.statements frame.stmtIdx with\n"
            "        | some stmt =>\n"
            "          attachCallers callers\n"
            "            (evalStatement body frame s.mem s.callerMem stmt)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_oob_block_idx_faults",
    ),
    MirSemanticsGuard(
        guard_id="step_operand_copy_oob_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalOperandToSlot .copy rejects out-of-bounds localId",
        anchor=(
            "        | .error k => .error k\n"
            "    | _, _ => .error .unsupported\n"
            "  | .move place =>"
        ),
        replacement=(
            "        | .error k => .error k\n"
            "    | _, _ => .ok (.unit, some .unit, locals, mem)\n"
            "  | .move place =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_operand_copy_oob_local",
    ),
    MirSemanticsGuard(
        guard_id="step_operand_move_oob_local",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalOperandToSlot .move rejects out-of-bounds localId",
        anchor=(
            "          | .error k => .error k\n"
            "    | _, _ => .error .unsupported\n"
            "  | .constant c =>"
        ),
        replacement=(
            "          | .error k => .error k\n"
            "    | _, _ => .ok (.unit, some .unit, locals, mem)\n"
            "  | .constant c =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_operand_move_oob_local",
    ),
    MirSemanticsGuard(
        guard_id="step_discriminant_non_enum_src",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue .discriminant rejects non-enum immediate source",
        anchor=(
            "        | .ordering => evalOrderingDiscriminantOfVal optVal locals mem\n"
            "        | _ => .error .unsupported\n"
            "    | some srcTy, some (.indirect mplace) =>"
        ),
        replacement=(
            "        | .ordering => evalOrderingDiscriminantOfVal optVal locals mem\n"
            "        | _ => .ok (.scalar ⟨.i8, false, BitVec.ofNat 128 0⟩, locals, mem)\n"
            "    | some srcTy, some (.indirect mplace) =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_discriminant_non_enum_src",
    ),
    MirSemanticsGuard(
        guard_id="step_rvalue_catchall_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalue catch-all rejects ref/addressOf/unsupported rvalues",
        anchor=(
            "  | _ => .error .unsupported\n\n"
            "/-- Write `val` into"
        ),
        replacement=(
            "  | _ => .ok (.unit, locals, mem)\n\n"
            "/-- Write `val` into"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_rvalue_catchall_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_assign_oob_dst",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalStatement .assign rejects out-of-bounds dst.localId",
        anchor=(
            "      match getElem? body.locals dst.localId with\n"
            "      | none => .fault .unsupported\n"
            "      | some dstTy =>\n"
            "        match evalRvalue body.locals frame.locals mem dstTy rvalue with"
        ),
        replacement=(
            "      match getElem? body.locals dst.localId with\n"
            "      | none =>\n"
            "        .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], "
            "callerMem, mem }\n"
            "      | some dstTy =>\n"
            "        match evalRvalue body.locals frame.locals mem dstTy rvalue with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_assign_oob_dst",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Boundary.lean (12 v1 judgment & admission guards
    # & 4 Profile v2 guards = 16 total; 9 singleBodyStaticAdmitted guards are
    # under State.lean above)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="boundary_wellformed_forbids_faults",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="WellFormed forbids reachable faults",
        anchor="  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))",
        replacement="  True",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_wellformed_forbids_faults",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_safe_fn_ignores_safety_pre",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyVerified ignores safetyPre for safe functions",
        anchor="    (body.isUnsafe = true → safetyPre args) →",
        replacement="    safetyPre args →",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_safe_fn_ignores_safety_pre",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_body_static_admitted",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyVerified requires BodyStaticAdmitted unconditionally",
        anchor="  BodyStaticAdmitted p body = true ∧",
        replacement="  True ∧",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_body_static_admitted",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Profile v2 memory, step, type-admission, and boundary guards (92 guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="mem_v2_ptr_add_null_nonzero",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="ptrAddInMem rejects nonzero offset on provenance-free (null) pointer as UB",
        anchor=(
            "    | none =>\n"
            "      if Nat.beq delta 0 then\n"
            "        .ok p\n"
            "      else\n"
            "        .error .undefined"
        ),
        replacement=(
            "    | none =>\n"
            "      if true then\n"
            "        .ok p\n"
            "      else\n"
            "        .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_ptr_add_null_nonzero",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_ptr_add_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="ptrAddInMem rejects offset past end of allocation as UB",
        anchor=(
            "      | some a =>\n"
            "        if !a.live || !Nat.ble (p.offsetBytes.toNat + delta) a.bytes.length then\n"
            "          .error .undefined"
        ),
        replacement=(
            "      | some a =>\n"
            "        if !a.live || false then\n"
            "          .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_ptr_add_oob",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_null",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceRefRawCheck and sliceFromRawPartsCheck reject null pointer "
            "even for zero-length slices as UB"
        ),
        anchor=(
            "    | none =>\n"
            "      if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 totalBytes then\n"
            "        .error .undefined"
        ),
        replacement=(
            "    | none =>\n"
            "      if false || Nat.blt 0 totalBytes then\n"
            "        .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_slice_null",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_readonly",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceRefRawCheck and sliceFromRawPartsCheck reject mutable slice "
            "over .shared allocation as UB"
        ),
        anchor=(
            "        else if isMut && !Mutability.beq a.mutability .mut then\n"
            "          .error .undefined"
        ),
        replacement=(
            "        else if false then\n"
            "          .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_slice_readonly",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="sliceFromRawPartsCheck rejects uninitialized bytes in slice span as UB",
        anchor=(
            "  | .ok (some a) =>\n"
            "    if !isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take totalBytes) then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok (.slicePtr p len)"
        ),
        replacement=(
            "  | .ok (some _) =>\n"
            "    if false then\n"
            "      .error .undefined\n"
            "    else\n"
            "      .ok (.slicePtr p len)"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_slice_uninit",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_get_unchecked_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="sliceGetUncheckedCheck rejects endOff > len out-of-bounds subslice as UB",
        anchor=(
            "    (len startOff endOff : Nat) (elemSize : Nat := 1) : Except FaultKind Val :=\n"
            "  if !Nat.ble startOff endOff || !Nat.ble endOff len then\n"
            "    .error .undefined"
        ),
        replacement=(
            "    (len startOff endOff : Nat) (elemSize : Nat := 1) : Except FaultKind Val :=\n"
            "  if !Nat.ble startOff endOff || false then\n"
            "    .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_slice_get_unchecked_oob",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_entry_byte_prov_fresh",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "entryMemoryWithCaller advances nextAllocId past provenance AllocIds "
            "stored inside caller allocation bytes"
        ),
        anchor=(
            "noncomputable def entryMemoryWithCaller (cm : CallerMemory) : MemoryState :=\n"
            "  { nextAllocId := Nat.max entryMemory.nextAllocId (maxAllocAndProvId cm.allocations + 1)"
        ),
        replacement=(
            "noncomputable def entryMemoryWithCaller (cm : CallerMemory) : MemoryState :=\n"
            "  { nextAllocId := Nat.max entryMemory.nextAllocId (maxAllocId cm.allocations + 1)"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_entry_byte_prov_fresh",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_entry_raw_ptr_arg_fresh",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "entryMemoryForArgsV2 advances nextAllocId past provenance AllocIds "
            "carried in raw-pointer parameters"
        ),
        anchor=(
            "  let base := entryMemoryWithCaller cm\n"
            "  if !tyListHasRawPtrV2 paramTys then\n"
            "    base"
        ),
        replacement=(
            "  let base := entryMemoryWithCaller cm\n"
            "  if true then\n"
            "    base"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_entry_raw_ptr_arg_fresh",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_entry_option_raw_ptr_ty",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "tyHasRawPtrV2 recurses through Option so Option<*const T> "
            "parameters advance the entry nextAllocId"
        ),
        anchor=(
            "    | .option e | .rangeTo e | .rangeFrom e | .range e => "
            "tyHasRawPtrV2 e\n"
        ),
        replacement=(
            "    | .option _ => false\n"
            "    | .rangeTo e | .rangeFrom e | .range e => tyHasRawPtrV2 e\n"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_entry_option_raw_ptr_ty",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_entry_option_raw_ptr_val",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "maxValPtrAllocId counts provenance AllocIds inside Some payloads"
        ),
        anchor="    | .optionVal (some v) => maxValPtrAllocId v\n",
        replacement="    | .optionVal (some _) => 0\n",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_entry_option_raw_ptr_val",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_get_unchecked_elem_size",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="sliceGetUncheckedCheck scales startOff by elemSize in ptrAddInMem",
        anchor="    match ptrAddInMem m elemSize p startOff with",
        replacement="    match ptrAddInMem m 1 p startOff with",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_slice_get_unchecked_elem_size",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_write_readonly",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "resolvePlaceDestV2 rejects dereference store through a .shared "
            "raw pointer as UB"
        ),
        anchor=(
            "        if isUnsizedTy pt || !MirTy.beq pt dstTy then\n"
            "          .error .unsupported\n"
            "        else if !Mutability.beq ptrMut .mut then\n"
            "          .error .undefined"
        ),
        replacement=(
            "        if isUnsizedTy pt || !MirTy.beq pt dstTy then\n"
            "          .error .unsupported\n"
            "        else if false then\n"
            "          .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_write_readonly",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_return_dangling_stack_ref",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalTerminatorV2 .return_ rejects returning a reference to a callee stack local as UB",
        anchor=(
            "          else if !refsStayInCallerMem callerMem retTy retVal ||\n"
            "              !refsValidInMem mem retTy retVal ||\n"
            "              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then\n"
            "            .fault .undefined"
        ),
        replacement=(
            "          else if false ||\n"
            "              !refsValidInMem mem retTy retVal ||\n"
            "              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then\n"
            "            .fault .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_return_dangling_stack_ref",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_offset_dst_type",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalRvalueV2 .offset rejects a destination type that differs "
            "from the pointer operand type"
        ),
        anchor=(
            "          if isUnsizedTy pt || !MirTy.beq dstTy lhsTy then\n"
            "            .error .unsupported"
        ),
        replacement=(
            "          if isUnsizedTy pt then\n"
            "            .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_offset_dst_type",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_range_to_in_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp validates the get_unchecked(..end) input slice "
            "at its own mutability"
        ),
        anchor=(
            "        match refValidInMem m inMut (.slice (.int w s)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat w.byteSize"
        ),
        replacement=(
            "        match refValidInMem m outMut (.slice (.int w s)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat w.byteSize"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_range_to_in_mut",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_range_from_in_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp validates the get_unchecked(start..) input slice "
            "at its own mutability"
        ),
        anchor=(
            "        match refValidInMem m inMut (.slice (.int w s)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat\n"
            "            w.byteSize"
        ),
        replacement=(
            "        match refValidInMem m outMut (.slice (.int w s)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat\n"
            "            w.byteSize"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_range_from_in_mut",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_range_in_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp validates the get_unchecked(start..end) input slice "
            "at its own mutability"
        ),
        anchor=(
            "        match refValidInMem m inMut (.slice (.int w s)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat endOff.toNat\n"
            "            w.byteSize"
        ),
        replacement=(
            "        match refValidInMem m outMut (.slice (.int w s)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat endOff.toNat\n"
            "            w.byteSize"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_range_in_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_range_from_elem_stride",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp scales get_unchecked(start..) pointer offset by "
            "the slice element byte size"
        ),
        anchor=(
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat\n"
            "            w.byteSize"
        ),
        replacement=(
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat\n"
            "            1"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_range_from_elem_stride",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_range_elem_stride",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp scales get_unchecked(start..end) pointer offset by "
            "the slice element byte size"
        ),
        anchor=(
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat endOff.toNat\n"
            "            w.byteSize"
        ),
        replacement=(
            "          sliceGetUncheckedCheck m p len.toNat startOff.toNat endOff.toNat\n"
            "            1"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_range_elem_stride",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_mem_size_of_unsupported_local_ty",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp .memSizeOf enforces isSupportedV2LocalTy rather "
            "than evaluating layoutOfTyV2 on unsupported local types"
        ),
        anchor=(
            "  | .memSizeOf ty, [] =>\n"
            "    if !MirTy.beq dstTy (.int .isize false) || isUnsizedTy ty ||\n"
            "        !isSupportedV2LocalTy ty then"
        ),
        replacement=(
            "  | .memSizeOf ty, [] =>\n"
            "    if !MirTy.beq dstTy (.int .isize false) || isUnsizedTy ty ||\n"
            "        false then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_mem_size_of_unsupported_local_ty",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_mem_size_of_isize_max",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp .memSizeOf rejects layouts of isize::MAX + 1 bytes "
            "or more instead of truncating them"
        ),
        anchor=(
            "        if !Nat.blt lay.size isizeMaxBytes then\n"
            "          .error .unsupported"
        ),
        replacement=(
            "        if false then\n"
            "          .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_mem_size_of_isize_max",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_int_from_le_bytes_array_len",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp .intFromLeBytes requires the byte array length to "
            "equal w.byteSize"
        ),
        anchor=(
            "  | .intFromLeBytes w s, [(.array (.int .i8 false) len, .array vs)] =>\n"
            "    if !Nat.beq len w.byteSize || !Nat.beq vs.length w.byteSize ||\n"
            "        !MirTy.beq dstTy (.int w s) then"
        ),
        replacement=(
            "  | .intFromLeBytes w s, [(.array (.int .i8 false) len, .array vs)] =>\n"
            "    if false ||\n"
            "        !MirTy.beq dstTy (.int w s) then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_int_from_le_bytes_array_len",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_index_in_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp validates the get_unchecked(idx) input slice at "
            "its own mutability"
        ),
        anchor=(
            "        match refValidInMem m inMut (.slice elem) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          let idx := (truncateBits .isize idxSv.bits).toNat"
        ),
        replacement=(
            "        match refValidInMem m outMut (.slice elem) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () =>\n"
            "          let idx := (truncateBits .isize idxSv.bits).toNat"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_index_in_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_index_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp .sliceGetUncheckedIndex rejects idx >= len as "
            ".undefined"
        ),
        anchor=(
            "          let idx := (truncateBits .isize idxSv.bits).toNat\n"
            "          if !Nat.blt idx len.toNat then\n"
            "            .error .undefined"
        ),
        replacement=(
            "          let idx := (truncateBits .isize idxSv.bits).toNat\n"
            "          if false then\n"
            "            .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_index_oob",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_get_unchecked_index_elem_stride",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp .sliceGetUncheckedIndex advances the element "
            "pointer by lay.size"
        ),
        anchor=(
            "              match ptrAddInMem m lay.size p idx with\n"
            "              | .error k => .error k\n"
            "              | .ok p' => .ok (.ptr p')"
        ),
        replacement=(
            "              match ptrAddInMem m 1 p idx with\n"
            "              | .error k => .error k\n"
            "              | .ok p' => .ok (.ptr p')"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_index_elem_stride",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_slice_subslice_in_mut",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execSliceSubslice validates the input slice reference at its own "
            "mutability"
        ),
        anchor=(
            "    match refValidInMem m inMut (.slice elem) (.slicePtr p len) with\n"
            "    | .error k => .error k\n"
            "    | .ok () =>\n"
            "      if !Nat.ble startOff endOff || !Nat.ble endOff len.toNat then"
        ),
        replacement=(
            "    match refValidInMem m reqMut (.slice elem) (.slicePtr p len) with\n"
            "    | .error k => .error k\n"
            "    | .ok () =>\n"
            "      if !Nat.ble startOff endOff || !Nat.ble endOff len.toNat then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_slice_subslice_in_mut",
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_slice_split_at_in_mut",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execSliceSplitAtOutcome validates the input slice reference at "
            "its own mutability"
        ),
        anchor=(
            "    match refValidInMem m inMut (.slice elem) (.slicePtr p len) with\n"
            "    | .error k => .fault k\n"
            "    | .ok () =>\n"
            "      if !Nat.ble mid len.toNat then"
        ),
        replacement=(
            "    match refValidInMem m reqMut (.slice elem) (.slicePtr p len) with\n"
            "    | .error k => .fault k\n"
            "    | .ok () =>\n"
            "      if !Nat.ble mid len.toNat then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_slice_split_at_in_mut",
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_i128_host_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "truncateScalarWithHostOverflow detects 128-bit mathematical "
            "overflow via intHostOverflow before BitVec 128 carrier truncation"
        ),
        anchor=(
            "  match truncateScalar w s value with\n"
            "  | .error k => .error k\n"
            "  | .ok (sv, truncOvf) => .ok (sv, intHostOverflow s value || truncOvf)"
        ),
        replacement=(
            "  match truncateScalar w s value with\n"
            "  | .error k => .error k\n"
            "  | .ok (sv, truncOvf) => .ok (sv, truncOvf)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_i128_host_overflow",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="enum_v2_overflow_pair_pointee",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedV2DataTy rejects overflow pairs as pointees or array elements",
        anchor=(
            "noncomputable def isSupportedV2DataTy : MirTy → Bool\n"
            "  | .array elem _ => isSupportedV2DataTy elem\n"
            "  | ty => !isOverflowPairTy ty && isSupportedScalarOrUnitTy ty"
        ),
        replacement=(
            "noncomputable def isSupportedV2DataTy : MirTy → Bool\n"
            "  | .array elem _ => isSupportedV2DataTy elem\n"
            "  | ty => true && isSupportedScalarOrUnitTy ty"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_v2_overflow_pair_pointee",
    ),
    MirSemanticsGuard(
        guard_id="enum_v2_sized_no_ref_tuple_pointee",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description=(
            "isSizedNoRefV2Ty and isSupportedV2LocalTy reject pointers to "
            "tuples and overflow pairs"
        ),
        anchor=(
            "  | .tuple _ | .array _ _ | .vec _ | .box _ | .ref _ _ | .rawPtr _ _ | .slice _\n"
        ),
        replacement=(
            "  | .tuple _ => true\n"
            "  | .array _ _ | .vec _ | .box _ | .ref _ _ | .rawPtr _ _ | .slice _\n"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_v2_overflow_pair_pointee",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_cast_const_to_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalPtrToPtrCastV2 rejects a *const T to *mut T cast, which "
            "could write to an immutable binding"
        ),
        anchor="    if isConstRawPtrTy srcTy && Mutability.beq castMut .mut then",
        replacement="    if false && Mutability.beq castMut .mut then",
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_ptr_cast_const_to_mut",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_resolves_destination_first",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalStatementV2 resolves an assignment's destination before "
            "evaluating its rvalue"
        ),
        anchor="          match writePlaceDestV2 locals1 mem1 dest dstTy val with",
        replacement=(
            "          match writePlaceV2 body.locals locals1 mem1 dst dstTy val with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_resolves_destination_first",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_raw_borrow_mut_through_const",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalAddressOfRvalueV2 rejects &raw mut *p through a *const T "
            "pointer as UB"
        ),
        anchor=(
            "        if Mutability.beq srcMut .shared && Mutability.beq reqMut .mut then\n"
            "          .error .undefined\n"
            "        else if !MirTy.beq dstTy (.rawPtr reqMut pt) then"
        ),
        replacement=(
            "        if false && Mutability.beq reqMut .mut then\n"
            "          .error .undefined\n"
            "        else if !MirTy.beq dstTy (.rawPtr reqMut pt) then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_raw_borrow_mut_through_const",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_partial_tuple_move_moved_field",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="readPlaceV2 rejects moving an already moved tuple field as UB",
        anchor=(
            "                  | none => .error .unsupported\n"
            "              | some _, some none => .error .undefined"
        ),
        replacement=(
            "                  | none => .error .unsupported\n"
            "              | some elemTy, some none => .ok (elemTy, some .unit, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_partial_tuple_move_moved_field",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_partial_tuple_copy_moved_field",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="readPlaceV2 rejects copying an already moved tuple field as UB",
        anchor=(
            "                else .ok (elemTy, some elemVal, locals, mem)\n"
            "              | some _, some none => .error .undefined"
        ),
        replacement=(
            "                else .ok (elemTy, some elemVal, locals, mem)\n"
            "              | some elemTy, some none => .ok (elemTy, some .unit, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_partial_tuple_copy_moved_field",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_partial_tuple_whole_read",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="readPlaceV2 rejects reading a partially moved tuple as a whole as UB",
        anchor=(
            "        | .dead => .error .undefined\n"
            "        | .partialTuple _ => .error .undefined\n"
            "        | .immediate optVal =>"
        ),
        replacement=(
            "        | .dead => .error .undefined\n"
            "        | .partialTuple _ => .ok (baseTy, some .unit, locals, mem)\n"
            "        | .immediate optVal =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_partial_tuple_whole_read",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assert_failure_faults",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .assert faults instead of continuing when an "
            "overflow check fails"
        ),
        anchor=(
            "        if b == expected then\n"
            "          jumpToBlock { frame with locals := locals1 } mem1 callerMem target\n"
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind\n"
            "            (extractCallerMemory callerMem mem1) hasLocalPanicHandler"
        ),
        replacement=(
            "        if true then\n"
            "          jumpToBlock { frame with locals := locals1 } mem1 callerMem target\n"
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind\n"
            "            (extractCallerMemory callerMem mem1) hasLocalPanicHandler"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assert_failure_faults",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_constant_index_min_len",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="constantIndexOffset rejects arrays shorter than minLen as UB",
        anchor=(
            "noncomputable def constantIndexOffset (len off minLen : Nat)\n"
            "    (fromEnd : Bool) : Except FaultKind Nat :=\n"
            "  if !Nat.ble minLen len then\n"
            "    .error .undefined"
        ),
        replacement=(
            "noncomputable def constantIndexOffset (len off minLen : Nat)\n"
            "    (fromEnd : Bool) : Except FaultKind Nat :=\n"
            "  if false then\n"
            "    .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_constant_index_min_len",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_constant_index_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="constantIndexOffset rejects out-of-bounds offset >= len as UB",
        anchor=(
            "  else\n"
            "    if !Nat.blt off len then\n"
            "      .error .undefined"
        ),
        replacement=(
            "  else\n"
            "    if false then\n"
            "      .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_constant_index_oob",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_read_deref_proj_raw_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="readDerefProjectedV2 enforces base-pointer alignment for raw sub-place reads",
        anchor=(
            "                if !isAligned a pv.offsetBytes.toNat ptLay.alignLog2 ||\n"
            "                    (isRef && (!a.live || !isInBounds a pv.offsetBytes.toNat ptLay.size)) ||"
        ),
        replacement=(
            "                if false ||\n"
            "                    (isRef && (!a.live || !isInBounds a pv.offsetBytes.toNat ptLay.size)) ||"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_read_deref_proj_raw_misaligned",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_read_deref_proj_no_prov_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "readDerefProjectedV2 enforces base-pointer alignment for "
            "provenance-free zero-size projected reads"
        ),
        anchor=(
            "              let badBaseAlign :=\n"
            "                !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 ptLay.alignLog2)) 0\n"
            "              let badRefBase :="
        ),
        replacement=(
            "              let badBaseAlign :=\n"
            "                false\n"
            "              let badRefBase :="
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_read_deref_proj_no_prov_misaligned",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_unsize_shared_to_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="CastKind.unsize rejects coercing & [T; N] to &mut [T] as UB",
        anchor=(
            "        | .ref srcMut (.array srcElem len), .ref dstMut (.slice dstElem), .ptr p =>\n"
            "          if !MirTy.beq srcElem dstElem || !Nat.blt len (Nat.pow 2 64) then\n"
            "            .error .unsupported\n"
            "          else if Mutability.beq srcMut .shared &&\n"
            "              Mutability.beq dstMut .mut then\n"
            "            .error .undefined"
        ),
        replacement=(
            "        | .ref srcMut (.array srcElem len), .ref dstMut (.slice dstElem), .ptr p =>\n"
            "          if !MirTy.beq srcElem dstElem || !Nat.blt len (Nat.pow 2 64) then\n"
            "            .error .unsupported\n"
            "          else if false then\n"
            "            .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_unsize_shared_to_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_unsize_src_mut_valid",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "CastKind.unsize validates source &mut [T; N] at srcMut before "
            "reborrowing as &[T]"
        ),
        anchor=(
            "            match refValidInMem mem1 srcMut (.array srcElem len) (.ptr p) with"
        ),
        replacement=(
            "            match refValidInMem mem1 dstMut (.array srcElem len) (.ptr p) with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_unsize_src_mut_valid",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_unsize_raw_shared_to_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="CastKind.unsize rejects coercing *const [T; N] to *mut [T] as UB",
        anchor=(
            "        | .rawPtr srcMut (.array srcElem len),\n"
            "          .rawPtr dstMut (.slice dstElem), .ptr p =>\n"
            "          if !MirTy.beq srcElem dstElem || !Nat.blt len (Nat.pow 2 64) then\n"
            "            .error .unsupported\n"
            "          else if Mutability.beq srcMut .shared &&\n"
            "              Mutability.beq dstMut .mut then\n"
            "            .error .undefined"
        ),
        replacement=(
            "        | .rawPtr srcMut (.array srcElem len),\n"
            "          .rawPtr dstMut (.slice dstElem), .ptr p =>\n"
            "          if !MirTy.beq srcElem dstElem || !Nat.blt len (Nat.pow 2 64) then\n"
            "            .error .unsupported\n"
            "          else if false then\n"
            "            .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_unsize_raw_shared_to_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_resolve_deref_proj_propagates_ub",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "resolvePlaceDestV2 propagates projectMemoryLayoutV2 .error .undefined "
            "faults on dereferenced projected stores"
        ),
        anchor=(
            "          match layoutOfTyV2 pt, projectMemoryLayoutV2 pt rest with\n"
            "          | none, _ => .error .unsupported\n"
            "          | _, .error k => .error k"
        ),
        replacement=(
            "          match layoutOfTyV2 pt, projectMemoryLayoutV2 pt rest with\n"
            "          | none, _ => .error .unsupported\n"
            "          | _, .error _ => .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_resolve_deref_proj_propagates_ub",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_read_indirect_proj_propagates_error",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "readPlaceV2 propagates projectMemoryLayoutV2 errors on indirect "
            "locals instead of falling back to a whole-local load"
        ),
        anchor=(
            "        | .indirect mplace =>\n"
            "          match projectMemoryLayoutV2 baseTy (.field idx fTy :: rest) with\n"
            "          | .error k => .error k"
        ),
        replacement=(
            "        | .indirect mplace =>\n"
            "          match projectMemoryLayoutV2 baseTy (.field idx fTy :: rest) with\n"
            "          | .error _ => .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_read_indirect_proj_propagates_error",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_resolve_local_proj_validates_first",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "resolvePlaceDestV2 validates projected immediate-local "
            "destinations before rvalue evaluation"
        ),
        anchor=(
            "    | some baseTy, some (.immediate _) =>\n"
            "      match validatePlaceProjV2 baseTy projs with\n"
            "      | .error k => .error k"
        ),
        replacement=(
            "    | some baseTy, some (.immediate _) =>\n"
            "      match validatePlaceProjV2 baseTy projs with\n"
            "      | .error _ => .ok (.localProj dst.localId baseTy projs)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_resolve_local_proj_validates_first",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_rodata_bytes_data_ty_only",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalOperandToSlotV2 restricts ConstLit.rodataBytes to "
            "isSupportedV2DataTy and fails closed on references"
        ),
        anchor=(
            "    | .rodataBytes bytes =>\n"
            "      if !isSupportedV2DataTy c.ty then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .rodataBytes bytes =>\n"
            "      if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_rodata_bytes_data_ty_only",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_rodata_ref_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRodataRefConstV2 rejects mutable &mut T reference over .rodata as unsupported",
        anchor=(
            "    | .ref reqMut pt, none =>\n"
            "      if isUnsizedTy pt then\n"
            "        .error .unsupported\n"
            "      else if Mutability.beq reqMut .mut then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .ref reqMut pt, none =>\n"
            "      if isUnsizedTy pt then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_rodata_ref_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_rodata_slice_ref_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRodataRefConstV2 rejects mutable &mut [T] slice reference over .rodata as unsupported",
        anchor=(
            "    | .ref reqMut (.slice elem), some len =>\n"
            "      if !Nat.blt len (Nat.pow 2 64) then\n"
            "        .error .unsupported\n"
            "      else if Mutability.beq reqMut .mut then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .ref reqMut (.slice elem), some len =>\n"
            "      if !Nat.blt len (Nat.pow 2 64) then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_rodata_slice_ref_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_rodata_raw_ptr_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRodataRefConstV2 rejects mutable *mut T raw pointer over .rodata as unsupported",
        anchor=(
            "    | .rawPtr reqMut pt, none =>\n"
            "      if isUnsizedTy pt then\n"
            "        .error .unsupported\n"
            "      else if Mutability.beq reqMut .mut then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .rawPtr reqMut pt, none =>\n"
            "      if isUnsizedTy pt then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_rodata_raw_ptr_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_rodata_raw_slice_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRodataRefConstV2 rejects mutable *mut [T] raw slice over .rodata as unsupported",
        anchor=(
            "    | .rawPtr reqMut (.slice _), some len =>\n"
            "      if !Nat.blt len (Nat.pow 2 64) then\n"
            "        .error .unsupported\n"
            "      else if Mutability.beq reqMut .mut then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .rawPtr reqMut (.slice _), some len =>\n"
            "      if !Nat.blt len (Nat.pow 2 64) then\n"
            "        .error .unsupported\n"
            "      else if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_rodata_raw_slice_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_array_eq_dangling_ref",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="CoreCallOp.arrayEq validates reference operands via refValidInMem",
        anchor=(
            "      match refValidInMem m m1 (.array elem len) (.ptr p1),\n"
            "          refValidInMem m m2 (.array elem len) (.ptr p2) with\n"
            "      | .error k, _ => .error k"
        ),
        replacement=(
            "      match (Except.ok () : Except FaultKind Unit),\n"
            "          refValidInMem m m2 (.array elem len) (.ptr p2) with\n"
            "      | .error k, _ => .error k"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_array_eq_dangling_ref",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_return_rodata_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalTerminatorV2 .return_ faults .unsupported when returning a callee .rodata ref or raw pointer",
        anchor=(
            "          if hasEscapingRodataPtr callerMem mem retTy retVal then\n"
            "            .fault .unsupported"
        ),
        replacement=(
            "          if false then\n"
            "            .fault .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_return_rodata_unsupported",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_ptr_or_ref_alloc_ids_option",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "ptrOrRefAllocIds recurses into a Some payload, so returning an "
            "Option of a pointer into callee .rodata faults .unsupported"
        ),
        anchor=(
            "    | .option inner, .optionVal (some innerV) => "
            "ptrOrRefAllocIds inner innerV"
        ),
        replacement="    | .option _, .optionVal (some _) => []",
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_return_rodata_option_ptr",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_slice_uninhabited_elem",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "refValidInMem rejects positive-length slices of uninhabited ZST "
            "or nested uninhabited element types as UB"
        ),
        anchor=(
            "          if Nat.blt 0 len.toNat && !isInhabitedV2Ty elem then\n"
            "            .error .undefined"
        ),
        replacement=(
            "          if Nat.blt 0 len.toNat && false then\n"
            "            .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_bytes_v2_slice_uninhabited_elem",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assert_abort_extract_caller_mem",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalTerminatorV2 .assert abort preserves pre-abort caller memory mutations",
        anchor=(
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind\n"
            "            (extractCallerMemory callerMem mem1) hasLocalPanicHandler"
        ),
        replacement=(
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind callerMem hasLocalPanicHandler"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assert_abort_extract_caller_mem",
    ),
    MirSemanticsGuard(
        guard_id="step_assert_optional_overflow_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalAssertFailure keeps optional overflow assertions as "
            ".fault .unsupported without overflowChecks"
        ),
        anchor="    if !overflowChecks || hasLocalPanicHandler then",
        replacement="    if hasLocalPanicHandler then",
        fixture_module="StepRefutations",
        theorem_name="refute_step_assert_optional_overflow_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_assert_checked_overflow_local_handler_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalAssertFailure keeps checked overflow assertions as "
            ".fault .unsupported under a crate-local #[panic_handler]"
        ),
        anchor="    if !overflowChecks || hasLocalPanicHandler then",
        replacement="    if !overflowChecks then",
        fixture_module="StepRefutations",
        theorem_name=(
            "refute_step_assert_checked_overflow_local_handler_unsupported"
        ),
    ),
    MirSemanticsGuard(
        guard_id="step_assert_local_panic_handler_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalAssertFailure keeps failing safe assertions as .fault .unsupported "
            "when the crate defines a crate-local #[panic_handler]"
        ),
        anchor=(
            "    if hasLocalPanicHandler then\n"
            "      .fault .unsupported\n"
            "    else"
        ),
        replacement=(
            "    if false then\n"
            "      .fault .unsupported\n"
            "    else"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_assert_local_panic_handler_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_assert_ptr_deref_undefined",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalAssertFailure maps .misalignedPtrDeref and .nullPtrDeref "
            "to .fault .undefined even under --panic abort"
        ),
        anchor=(
            "  | .misalignedPtrDeref | .nullPtrDeref => .fault .undefined\n"
            "  | .boundsCheck | .overflow .div | .overflow .rem\n"
            "  | .divByZero | .remByZero =>"
        ),
        replacement=(
            "  | .misalignedPtrDeref | .nullPtrDeref => .fault .unsupported\n"
            "  | .boundsCheck | .overflow .div | .overflow .rem\n"
            "  | .divByZero | .remByZero =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_assert_ptr_deref_undefined",
    ),
    MirSemanticsGuard(
        guard_id="step_assert_v1_failure_faults",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminator .assert routes failing conditions (b != expected) "
            "through evalAssertFailure rather than jumping to target"
        ),
        anchor=(
            "      | .bool b =>\n"
            "        if b == expected then\n"
            "          jumpToBlock { frame with locals := locals1 } mem1 callerMem target\n"
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind callerMem\n"
            "            hasLocalPanicHandler"
        ),
        replacement=(
            "      | .bool b =>\n"
            "        if true then\n"
            "          jumpToBlock { frame with locals := locals1 } mem1 callerMem target\n"
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind callerMem\n"
            "            hasLocalPanicHandler"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_assert_v1_failure_faults",
    ),
    MirSemanticsGuard(
        guard_id="step_assert_v1_non_bool_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminator .assert refuses non-bool condition operands "
            "with .fault .unsupported"
        ),
        anchor=(
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind callerMem\n"
            "            hasLocalPanicHandler\n"
            "      | _ => .fault .unsupported"
        ),
        replacement=(
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind callerMem\n"
            "            hasLocalPanicHandler\n"
            "      | _ =>\n"
            "        jumpToBlock { frame with locals := locals1 } mem1 callerMem target"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_assert_v1_non_bool_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assert_non_bool_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .assert refuses non-bool condition operands "
            "with .fault .unsupported"
        ),
        anchor=(
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind\n"
            "            (extractCallerMemory callerMem mem1) hasLocalPanicHandler\n"
            "            overflowChecks\n"
            "      | _ => .fault .unsupported"
        ),
        replacement=(
            "        else\n"
            "          evalAssertFailure msg panicStrategy unwind\n"
            "            (extractCallerMemory callerMem mem1) hasLocalPanicHandler\n"
            "            overflowChecks\n"
            "      | _ =>\n"
            "        jumpToBlock { frame with locals := locals1 } mem1 callerMem target"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assert_non_bool_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_use_overlap_ub",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAssignCopyHazardV2 rejects overlapping non-zero-sized "
            "BackendRepr::Memory or padded Assign Use copies as UB"
        ),
        anchor=(
            "  | .use (.copy src) | .use (.move src)\n"
            "  | .useRetag (.copy src) | .useRetag (.move src) =>\n"
            "    if !isMemoryCopyReprTyV2 dstTy then\n"
            "      .ok ()"
        ),
        replacement=(
            "  | .use (.copy src) | .use (.move src)\n"
            "  | .useRetag (.copy src) | .useRetag (.move src) =>\n"
            "    if true then\n"
            "      .ok ()"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_use_overlap_ub",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_aggregate_clobber_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAggregateCopyHazardLoopV2 fails closed with .unsupported when "
            "an earlier Aggregate field write overlaps a later operand"
        ),
        anchor=(
            "    if clobberedByEarlier then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_aggregate_clobber_unsupported",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_aggregate_range_clobber_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAssignCopyHazardV2 routes Range aggregates through the "
            "in-order field-write hazard loop"
        ),
        anchor=(
            "  | .aggregateRange elemTy startOp endOp =>\n"
            "    match copyReprOfTyV2 dstTy with"
        ),
        replacement=(
            "  | .aggregateRange elemTy startOp endOp =>\n"
            "    match (CopyReprV2.zst 0 : CopyReprV2) with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_aggregate_range_clobber_unsupported",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_range_field_span",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "normalizeImmProjPathV2 resolves Range field projections on "
            "immediate locals"
        ),
        anchor=(
            "    if !Nat.blt idx 2 || !MirTy.beq (.int .isize false) fTy then none"
        ),
        replacement=(
            "    if true then none"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_range_field_span",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_option_payload_span",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "normalizeImmProjPathV2 resolves Option payload projections on "
            "immediate locals"
        ),
        anchor=(
            "  | .option inner, .downcast 1 :: .field 0 fTy :: rest =>\n"
            "    if !MirTy.beq inner fTy then none"
        ),
        replacement=(
            "  | .option inner, .downcast 1 :: .field 0 fTy :: rest =>\n"
            "    if true then none"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_option_payload_span",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_aggregate_unresolved_operand_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAggregateCopyHazardLoopV2 fails closed on a non-constant "
            "operand whose source span is unresolved"
        ),
        anchor=(
            "    else if unresolved &&\n"
            "        (!writtenSpans.isEmpty || isMemoryCopyReprTyV2 fieldTy) then"
        ),
        replacement=(
            "    else if false &&\n"
            "        (!writtenSpans.isEmpty || isMemoryCopyReprTyV2 fieldTy) then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_aggregate_unresolved_operand_unsupported",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_aggregate_deref_ptr_clobber_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAggregateCopyHazardLoopV2 fails closed with .unsupported when "
            "an earlier Aggregate field write overlaps the pointer local read by "
            "a later .deref operand"
        ),
        anchor=(
            "    else if ptrClobberedByEarlier then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "    else if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_aggregate_deref_ptr_clobber_unsupported",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_aggregate_field_overlap_ub",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAggregateCopyHazardLoopV2 rejects overlapping "
            "BackendRepr::Memory Aggregate field writes as UB"
        ),
        anchor=(
            "        if selfOverlap && isMemoryCopyReprTyV2 fieldTy then\n"
            "          .error .undefined"
        ),
        replacement=(
            "        if false then\n"
            "          .error .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_aggregate_field_overlap_ub",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_assign_repeat_overlap_ub",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "checkAssignCopyHazardV2 rejects overlapping BackendRepr::Memory "
            "Rvalue.repeat_ initial element copies as UB"
        ),
        anchor=(
            "  | .repeat_ op elemTy count =>\n"
            "    if Nat.beq count 0 || !isMemoryCopyReprTyV2 elemTy then\n"
            "      .ok ()"
        ),
        replacement=(
            "  | .repeat_ op elemTy count =>\n"
            "    if true then\n"
            "      .ok ()"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_assign_repeat_overlap_ub",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_local_handler_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalCorePanicAbort keeps diverging core::panicking calls as "
            ".fault .unsupported when the crate defines a crate-local #[panic_handler]"
        ),
        anchor=(
            "  if hasLocalPanicHandler then\n"
            "    .fault .unsupported\n"
            "  else"
        ),
        replacement=(
            "  if false then\n"
            "    .fault .unsupported\n"
            "  else"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_local_handler_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_unwind_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalCorePanicAbort keeps diverging core::panicking calls as "
            ".fault .unsupported under --panic unwind"
        ),
        anchor=(
            "    match panicStrategy, unwind with\n"
            "    | .abort, .continue_ | .abort, .unreachable | .abort, .terminate =>\n"
            "      .done (.aborted callerMem)\n"
            "    | _, _ => .fault .unsupported"
        ),
        replacement=(
            "    match panicStrategy, unwind with\n"
            "    | .abort, .continue_ | .abort, .unreachable | .abort, .terminate\n"
            "    | .unwind, .continue_ =>\n"
            "      .done (.aborted callerMem)\n"
            "    | _, _ => .fault .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_unwind_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_abort_extract_caller_mem",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .coreCall .panicAbort preserves pre-abort caller "
            "memory mutations"
        ),
        anchor=(
            "          match validatePanicAbortArgs mem1 typedArgs with\n"
            "          | .error k => .fault k\n"
            "          | .ok () =>\n"
            "            evalCorePanicAbort panicStrategy unwind\n"
            "              (extractCallerMemory callerMem mem1) hasLocalPanicHandler"
        ),
        replacement=(
            "          match validatePanicAbortArgs mem1 typedArgs with\n"
            "          | .error k => .fault k\n"
            "          | .ok () =>\n"
            "            evalCorePanicAbort panicStrategy unwind callerMem hasLocalPanicHandler"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_abort_extract_caller_mem",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_abort_ref_valid",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "validatePanicAbortArgs re-validates refValidInMem on local &str "
            "operands passed to CoreCallOp.panicAbort"
        ),
        anchor=(
            "  | [(.ref .shared .str, .slicePtr p len)] =>\n"
            "    if !IntWidth.beq p.width .isize then\n"
            "      .error .unsupported\n"
            "    else\n"
            "      match refValidInMem m .shared .str (.slicePtr p len) with"
        ),
        replacement=(
            "  | [(.ref .shared .str, .slicePtr p len)] =>\n"
            "    if !IntWidth.beq p.width .isize then\n"
            "      .error .unsupported\n"
            "    else\n"
            "      match Except.ok () with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_abort_ref_valid",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_abort_non_utf8_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "validatePanicAbortArgs rejects non-UTF-8 &str operands passed to "
            "CoreCallOp.panicAbort as .error .unsupported"
        ),
        anchor=(
            "        if !strSliceUtf8InMem m p len then\n"
            "          .error .unsupported\n"
            "        else\n"
            "          .ok ()"
        ),
        replacement=(
            "        if false then\n"
            "          .error .unsupported\n"
            "        else\n"
            "          .ok ()"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_abort_non_utf8_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_metadata_str_dst_ty",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalRvalueV2 UnOp.ptrMetadata on &str requires usize destination "
            "type"
        ),
        anchor=(
            "      | .ref .shared .str, .slicePtr p len =>\n"
            "        if !MirTy.beq dstTy (.int .isize false) then\n"
            "          .error .unsupported"
        ),
        replacement=(
            "      | .ref .shared .str, .slicePtr p len =>\n"
            "        if false then\n"
            "          .error .unsupported"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_ptr_metadata_str_dst_ty",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_metadata_str_ref_valid",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalRvalueV2 UnOp.ptrMetadata on &str validates refValidInMem on "
            "the source string slice"
        ),
        anchor=(
            "          match refValidInMem mem1 .shared .str (.slicePtr p len) with\n"
            "          | .error k => .error k\n"
            "          | .ok () =>"
        ),
        replacement=(
            "          match Except.ok () with\n"
            "          | .error k => .error k\n"
            "          | .ok () =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_ptr_metadata_str_ref_valid",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_abort_eval_args",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .coreCall .panicAbort evaluates its &str "
            "argument before aborting so uninitialized local or rodata "
            "operands fault .undefined"
        ),
        anchor=(
            "        match evalArgOperandsV2 body.locals frame.locals mem args with\n"
            "        | .error k => .fault k\n"
            "        | .ok (typedArgs, _, mem1) =>"
        ),
        replacement=(
            "        match evalArgOperandsV2 body.locals frame.locals mem args with\n"
            "        | .error _ =>\n"
            "          evalCorePanicAbort panicStrategy unwind\n"
            "            (extractCallerMemory callerMem mem) hasLocalPanicHandler\n"
            "        | .ok (typedArgs, _, mem1) =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_abort_eval_args",
    ),
    MirSemanticsGuard(
        guard_id="step_v2_core_panic_abort_dead_dst_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .coreCall .panicAbort rejects dead ! destination "
            "locals as .fault .unsupported before aborting"
        ),
        anchor=(
            "      | some .never, some (.immediate _)\n"
            "      | some .never, some (.indirect _) =>"
        ),
        replacement=(
            "      | some .never, some (.immediate _)\n"
            "      | some .never, some (.indirect _)\n"
            "      | some .never, some .dead =>"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_core_panic_abort_dead_dst_unsupported",
    ),
    MirSemanticsGuard(
        guard_id="enum_v2_overflow_pair_vec_elem",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedV2LocalTy rejects Vec of overflow pairs",
        anchor=(
            "    | .vec elem => !isOverflowPairTy elem && isSupportedScalarOrUnitTy elem"
        ),
        replacement=(
            "    | .vec elem => true && isSupportedScalarOrUnitTy elem"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_v2_overflow_pair_vec_elem",
    ),
    MirSemanticsGuard(
        guard_id="enum_v2_overflow_pair_box_pointee",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedV2LocalTy rejects Box of an overflow pair",
        anchor=(
            "    | .box pt => !isOverflowPairTy pt && isSupportedScalarOrUnitTy pt"
        ),
        replacement=(
            "    | .box pt => true && isSupportedScalarOrUnitTy pt"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_v2_overflow_pair_box_pointee",
    ),
    MirSemanticsGuard(
        guard_id="enum_v2_overflow_pair_slice_elem",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedV2LocalTy rejects slices of overflow pairs",
        anchor=(
            "    | .ref _ (.slice elem) | .rawPtr _ (.slice elem) => isSizedNoRefV2Ty elem"
        ),
        replacement=(
            "    | .ref _ (.slice elem) | .rawPtr _ (.slice elem) => true"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_v2_overflow_pair_slice_elem",
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_wellformed_forbids_faults",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="WellFormedV2 forbids reachable faults",
        anchor="  (∀ k : FaultKind, ¬ ReachesResultV2 p q (.fault k))",
        replacement="  True",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_wellformed_forbids_faults",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_safe_fn_ignores_safety_pre",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyVerifiedV2 ignores safetyPre for safe functions",
        anchor="    (body.isUnsafe = true → safetyPre q) →",
        replacement="    safetyPre q →",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_safe_fn_ignores_safety_pre",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_body_static_admitted",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyVerifiedV2 requires BodyStaticAdmittedV2 unconditionally",
        anchor=(
            "  BodyStaticAdmittedV2 p body = true ∧\n"
            "  ∀ q : Query,\n"
            "    ValidEntryArgsV2 body q →\n"
            "    (body.isUnsafe = true → safetyPre q) →"
        ),
        replacement=(
            "  True ∧\n"
            "  ∀ q : Query,\n"
            "    ValidEntryArgsV2 body q →\n"
            "    (body.isUnsafe = true → safetyPre q) →"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_body_static_admitted",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_rejects_mixed_refs_and_raw_ptrs",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyStaticAdmittedV2 rejects bodies mixing refs and raw pointers",
        anchor="    !bodyMixesRefsAndRawPtrsV2 body &&",
        replacement="    true &&",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_rejects_mixed_refs_and_raw_ptrs",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_effect_mask_allow_abort_default",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="EffectMaskV2 defaults allowAbort to false",
        anchor=(
            "structure EffectMaskV2 where\n"
            "  allowAbort : Bool := false"
        ),
        replacement=(
            "structure EffectMaskV2 where\n"
            "  allowAbort : Bool := true"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_effect_mask_allow_abort_default",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_safe_contract_allow_abort_default",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="SafeContractV2 defaults effects.allowAbort to false",
        anchor=(
            "  behaviorPre : Query → Prop := fun _ => True\n"
            "  effects : EffectMaskV2 := { allowAbort := false }"
        ),
        replacement=(
            "  behaviorPre : Query → Prop := fun _ => True\n"
            "  effects : EffectMaskV2 := { allowAbort := true }"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_safe_contract_allow_abort_default",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_safe_contract_post_abort_default",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="SafeContractV2 defaults postAbort to False",
        anchor=(
            "  postReturn : Query → Out → Prop := fun _ _ => True\n"
            "  postAbort : Query → CallerMemory → Prop := fun _ _ => False"
        ),
        replacement=(
            "  postReturn : Query → Out → Prop := fun _ _ => True\n"
            "  postAbort : Query → CallerMemory → Prop := fun _ _ => True"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_safe_contract_post_abort_default",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Additional Profile v2 silent-saturation, aliasing, negative-offset,
    # slice/thin-ref validity, and provenance-free deref guards (61 guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="mem_v2_slice_get_unchecked_inverted",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceGetUncheckedCheck rejects inverted range startOff > endOff "
            "as UB rather than saturating subtraction"
        ),
        anchor=(
            "    (len startOff endOff : Nat) (elemSize : Nat := 1) : Except FaultKind Val :=\n"
            "  if !Nat.ble startOff endOff || !Nat.ble endOff len then\n"
            "    .error .undefined"
        ),
        replacement=(
            "    (len startOff endOff : Nat) (elemSize : Nat := 1) : Except FaultKind Val :=\n"
            "  if false || !Nat.ble endOff len then\n"
            "    .error .undefined"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_slice_get_unchecked_inverted",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_ptr_add_dead_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="ptrAddInMem rejects offset on a deallocated allocation as UB",
        anchor=(
            "      | some a =>\n"
            "        if !a.live || !Nat.ble (p.offsetBytes.toNat + delta) a.bytes.length then\n"
            "          .error .undefined"
        ),
        replacement=(
            "      | some a =>\n"
            "        if false || !Nat.ble (p.offsetBytes.toNat + delta) a.bytes.length then\n"
            "          .error .undefined"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_ptr_add_dead_alloc",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_no_prov_nonempty",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceFromRawPartsCheck rejects non-empty slice backed by a "
            "provenance-free pointer as UB"
        ),
        anchor=(
            "    | none =>\n"
            "      if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 totalBytes then\n"
            "        .error .undefined"
        ),
        replacement=(
            "    | none =>\n"
            "      if Nat.beq p.offsetBytes.toNat 0 || false then\n"
            "        .error .undefined"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_slice_no_prov_nonempty",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_no_prov_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceFromRawPartsCheck rejects misaligned zero-length slice "
            "backed by a provenance-free pointer as UB"
        ),
        anchor=(
            "      else if !Nat.beq\n"
            "          (Nat.mod p.offsetBytes.toNat (Nat.pow 2 elemAlignLog2)) 0 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok none"
        ),
        replacement=(
            "      else if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok none"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_slice_no_prov_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_dead_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceFromRawPartsCheck rejects a slice into a deallocated "
            "allocation as UB"
        ),
        anchor=(
            "        if !a.live || !isInBounds a p.offsetBytes.toNat totalBytes ||\n"
            "            !isAligned a p.offsetBytes.toNat elemAlignLog2 then\n"
            "          .error .undefined"
        ),
        replacement=(
            "        if false || !isInBounds a p.offsetBytes.toNat totalBytes ||\n"
            "            !isAligned a p.offsetBytes.toNat elemAlignLog2 then\n"
            "          .error .undefined"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_slice_dead_alloc",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceFromRawPartsCheck rejects out-of-bounds slice length as UB "
            "instead of allowing List.take truncation"
        ),
        anchor=(
            "        if !a.live || !isInBounds a p.offsetBytes.toNat totalBytes ||\n"
            "            !isAligned a p.offsetBytes.toNat elemAlignLog2 then\n"
            "          .error .undefined"
        ),
        replacement=(
            "        if !a.live || false ||\n"
            "            !isAligned a p.offsetBytes.toNat elemAlignLog2 then\n"
            "          .error .undefined"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_slice_oob",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_v2_slice_misaligned",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description=(
            "sliceFromRawPartsCheck rejects misaligned provenance-bearing "
            "slice as UB"
        ),
        anchor=(
            "        if !a.live || !isInBounds a p.offsetBytes.toNat totalBytes ||\n"
            "            !isAligned a p.offsetBytes.toNat elemAlignLog2 then\n"
            "          .error .undefined"
        ),
        replacement=(
            "        if !a.live || !isInBounds a p.offsetBytes.toNat totalBytes ||\n"
            "            false then\n"
            "          .error .undefined"
        ),
        fixture_module="ProfileV2MemoryRefutations",
        theorem_name="refute_mem_v2_slice_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_span_disjoint_overlap",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="spanDisjoint rejects overlapping mutable byte spans",
        anchor=(
            "  if !(m1 || m2) || Nat.beq n1 0 || Nat.beq n2 0 || !Nat.beq id1 id2 then\n"
            "    true\n"
            "  else\n"
            "    Nat.ble (s1 + n1) s2 || Nat.ble (s2 + n2) s1"
        ),
        replacement=(
            "  if !(m1 || m2) || Nat.beq n1 0 || Nat.beq n2 0 || !Nat.beq id1 id2 then\n"
            "    true\n"
            "  else\n"
            "    true"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_span_disjoint_overlap",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_span_disjoint_mut_vs_shared",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="spanDisjoint rejects &mut overlapping & (not only &mut vs &mut)",
        anchor=(
            "  if !(m1 || m2) || Nat.beq n1 0 || Nat.beq n2 0 || !Nat.beq id1 id2 then\n"
            "    true\n"
            "  else\n"
            "    Nat.ble (s1 + n1) s2 || Nat.ble (s2 + n2) s1"
        ),
        replacement=(
            "  if !(m1 && m2) || Nat.beq n1 0 || Nat.beq n2 0 || !Nat.beq id1 id2 then\n"
            "    true\n"
            "  else\n"
            "    Nat.ble (s1 + n1) s2 || Nat.ble (s2 + n2) s1"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_span_disjoint_mut_vs_shared",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_ref_valid_null_zst",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="refValidInMem rejects null thin reference even for ZST pointee",
        anchor=(
            "        | none =>\n"
            "          if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 lay.size then\n"
            "            .error .undefined"
        ),
        replacement=(
            "        | none =>\n"
            "          if false || Nat.blt 0 lay.size then\n"
            "            .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_ref_valid_null_zst",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_ref_valid_readonly_mut",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="refValidInMem rejects thin &mut T into a .shared allocation as UB",
        anchor=(
            "            else if Mutability.beq reqMut .mut &&\n"
            "                !Mutability.beq a.mutability .mut then\n"
            "              .error .undefined"
        ),
        replacement=(
            "            else if false then\n"
            "              .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_ref_valid_readonly_mut",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_ref_valid_uninit_pointee",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="refValidInMem rejects thin reference to uninitialized pointee as UB",
        anchor=(
            "              | .ok none => .error .undefined\n"
            "              | .error k => .error k\n"
            "  | _, _ => .error .unsupported"
        ),
        replacement=(
            "              | .ok none => .ok ()\n"
            "              | .error k => .error k\n"
            "  | _, _ => .error .unsupported"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_ref_valid_uninit_pointee",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_v2_array_elem_layout",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "encodeValV2 refuses arrays whose element type has no layoutOfTyV2"
        ),
        anchor=(
            "      if !(layoutOfTyV2 elem).isSome || !Nat.beq vs.length len then\n"
        ),
        replacement="      if !Nat.beq vs.length len then\n",
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_array_elem_layout",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="state_v2_init_invalid_entry_ref",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initStateV2 rejects invalid entry reference arguments as UB",
        anchor=(
            "          if !refsValidInMemList entryMem paramTys q.args ||\n"
            "              !spansPairwiseDisjoint (refAccessSpansList paramTys q.args) then\n"
            "            .error .undefined"
        ),
        replacement=(
            "          if false ||\n"
            "              !spansPairwiseDisjoint (refAccessSpansList paramTys q.args) then\n"
            "            .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_state_v2_init_invalid_entry_ref",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="state_v2_init_aliased_entry_refs",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="initStateV2 rejects overlapping mutable entry references as UB",
        anchor=(
            "          if !refsValidInMemList entryMem paramTys q.args ||\n"
            "              !spansPairwiseDisjoint (refAccessSpansList paramTys q.args) then\n"
            "            .error .undefined"
        ),
        replacement=(
            "          if !refsValidInMemList entryMem paramTys q.args ||\n"
            "              false then\n"
            "            .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_state_v2_init_aliased_entry_refs",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_usize_unchecked_sub_underflow",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "execCoreCallOp .usizeUncheckedSub rejects rhs > lhs as UB rather "
            "than saturating Nat subtraction to 0"
        ),
        anchor=(
            "    else if !Nat.ble rSv.bits.toNat lSv.bits.toNat then\n"
            "      .error .undefined"
        ),
        replacement=(
            "    else if false then\n"
            "      .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_usize_unchecked_sub_underflow",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_offset_neg_underflow",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalPtrOffsetV2 rejects negative offset before byte 0 as UB "
            "rather than saturating Nat subtraction to 0"
        ),
        anchor=(
            "              if !a.live || !Nat.ble p.offsetBytes.toNat a.bytes.length ||\n"
            "                  !Nat.ble delta p.offsetBytes.toNat then\n"
            "                .error .undefined"
        ),
        replacement=(
            "              if !a.live || !Nat.ble p.offsetBytes.toNat a.bytes.length ||\n"
            "                  false then\n"
            "                .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_ptr_offset_neg_underflow",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_offset_neg_start_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalPtrOffsetV2 rejects negative offset starting past end of "
            "allocation as UB"
        ),
        anchor=(
            "              if !a.live || !Nat.ble p.offsetBytes.toNat a.bytes.length ||\n"
            "                  !Nat.ble delta p.offsetBytes.toNat then\n"
            "                .error .undefined"
        ),
        replacement=(
            "              if !a.live || false ||\n"
            "                  !Nat.ble delta p.offsetBytes.toNat then\n"
            "                .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_ptr_offset_neg_start_oob",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_offset_neg_null",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalPtrOffsetV2 rejects negative offset on provenance-free pointer as UB",
        anchor=(
            "          match p.allocId with\n"
            "          | none => .error .undefined\n"
            "          | some aid =>"
        ),
        replacement=(
            "          match p.allocId with\n"
            "          | none => .ok (.ptr p)\n"
            "          | some aid =>"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_ptr_offset_neg_null",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_ptr_offset_neg_dead_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalPtrOffsetV2 rejects negative offset on dead allocation as UB",
        anchor=(
            "              if !a.live || !Nat.ble p.offsetBytes.toNat a.bytes.length ||\n"
            "                  !Nat.ble delta p.offsetBytes.toNat then\n"
            "                .error .undefined"
        ),
        replacement=(
            "              if false || !Nat.ble p.offsetBytes.toNat a.bytes.length ||\n"
            "                  !Nat.ble delta p.offsetBytes.toNat then\n"
            "                .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_ptr_offset_neg_dead_alloc",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_return_aliased_mut_refs",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .return_ rejects returning overlapping mutable "
            "reference spans as UB"
        ),
        anchor=(
            "          else if !refsStayInCallerMem callerMem retTy retVal ||\n"
            "              !refsValidInMem mem retTy retVal ||\n"
            "              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then\n"
            "            .fault .undefined"
        ),
        replacement=(
            "          else if !refsStayInCallerMem callerMem retTy retVal ||\n"
            "              !refsValidInMem mem retTy retVal ||\n"
            "              false then\n"
            "            .fault .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_return_aliased_mut_refs",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_return_invalid_ref",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalTerminatorV2 .return_ rejects returning a reference to an "
            "invalid pointee in caller memory as UB"
        ),
        anchor=(
            "          else if !refsStayInCallerMem callerMem retTy retVal ||\n"
            "              !refsValidInMem mem retTy retVal ||\n"
            "              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then\n"
            "            .fault .undefined"
        ),
        replacement=(
            "          else if !refsStayInCallerMem callerMem retTy retVal ||\n"
            "              false ||\n"
            "              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then\n"
            "            .fault .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_return_invalid_ref",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_use_retag_invalid_ref",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description="evalRvalueV2 .useRetag rejects invalid reference operands as UB",
        anchor=(
            "          if !refsValidInMem mem1 srcTy v then\n"
            "            .error .undefined"
        ),
        replacement=(
            "          if false then\n"
            "            .error .undefined"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_use_retag_invalid_ref",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_read_no_prov_non_zst",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "readPlaceV2 rejects dereference read of non-ZST through a "
            "provenance-free pointer as UB"
        ),
        anchor=(
            "                | none =>\n"
            "                  if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||\n"
            "                      !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then\n"
            "                    .error .undefined\n"
            "                  else\n"
            "                    match decodeValV2 profileV2TargetEndian pt [] with"
        ),
        replacement=(
            "                | none =>\n"
            "                  if Nat.beq pv.offsetBytes.toNat 0 || false ||\n"
            "                      !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then\n"
            "                    .error .undefined\n"
            "                  else\n"
            "                    match decodeValV2 profileV2TargetEndian pt [] with"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_read_no_prov_non_zst",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_write_no_prov_non_zst",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "writePlaceDestV2 rejects dereference store of non-ZST through a "
            "provenance-free pointer as UB"
        ),
        anchor=(
            "      | none =>\n"
            "        if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||\n"
            "            !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then\n"
            "          .error .undefined\n"
            "        else\n"
            "          match encodeValV2 profileV2TargetEndian pt val with"
        ),
        replacement=(
            "      | none =>\n"
            "        if Nat.beq pv.offsetBytes.toNat 0 || false ||\n"
            "            !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then\n"
            "          .error .undefined\n"
            "        else\n"
            "          match encodeValV2 profileV2TargetEndian pt val with"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_step_v2_write_no_prov_non_zst",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_arg_or_ret",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="isFakePtrMetadataLocalV2 rejects return place _0 and caller parameters",
        anchor=(
            "noncomputable def isFakePtrMetadataLocalV2 (body : Body)\n"
            "    (lid : LocalId) : Bool :=\n"
            "  Nat.blt body.argumentCount lid &&"
        ),
        replacement=(
            "noncomputable def isFakePtrMetadataLocalV2 (body : Body)\n"
            "    (lid : LocalId) : Bool :=\n"
            "  true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_arg_or_ret",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_requires_fake_assign",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="isFakePtrMetadataLocalV2 requires at least one .fakeAddressOf assignment",
        anchor=(
            "      body.basicBlocks.any (fun bb =>\n"
            "        bb.statements.any (stmtAssignsFakeAddressOfToV2 lid)) &&"
        ),
        replacement="      true &&",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_requires_fake_assign",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_non_metadata_use",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "stmtRespectsFakePtrMetadataLocalV2 rejects non-PtrMetadata reads "
            "or dereferences of fake metadata locals"
        ),
        anchor=(
            "    else if rvalueMentionsLocalV2 lid rv then\n"
            "      match rv with"
        ),
        replacement=(
            "    else if false then\n"
            "      match rv with"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_non_metadata_use",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_self_assign",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "fakeAddressOfTypesMatchV2 rejects self-referential "
            ".fakeAddressOf (*_lid) assignments"
        ),
        anchor=(
            "noncomputable def fakeAddressOfTypesMatchV2 (locals : List MirTy)\n"
            "    (dstId : LocalId) (src : Place) : Bool :=\n"
            "  !Nat.beq src.localId dstId &&"
        ),
        replacement=(
            "noncomputable def fakeAddressOfTypesMatchV2 (locals : List MirTy)\n"
            "    (dstId : LocalId) (src : Place) : Bool :=\n"
            "  true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_self_assign",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_overflow_pair",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "fakeAddressOfTypesMatchV2 rejects overflow-pair pointee types"
        ),
        anchor="        !isOverflowPairTy pt && MirTy.beq dstTy (.rawPtr .shared pt)",
        replacement="        true && MirTy.beq dstTy (.rawPtr .shared pt)",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_overflow_pair",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_requires_matching_pointee",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "fakeAddressOfTypesMatchV2 requires destination *const T pointee "
            "to match base pointee"
        ),
        anchor="        !isOverflowPairTy pt && MirTy.beq dstTy (.rawPtr .shared pt)",
        replacement="        !isOverflowPairTy pt && true",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_requires_matching_pointee",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_projected_dst",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "stmtRespectsFakePtrMetadataLocalV2 rejects projected assignments "
            "through a fake-metadata local"
        ),
        anchor=(
            "    if placeMentionsLocalV2 lid dst then\n"
            "      dst.projection.isEmpty &&\n"
            "        match rv with"
        ),
        replacement=(
            "    if placeMentionsLocalV2 lid dst then\n"
            "      true &&\n"
            "        match rv with"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_projected_dst",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_projected_ptr_meta_operand",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "stmtRespectsFakePtrMetadataLocalV2 requires .ptrMetadata operands "
            "on fake-metadata locals to have empty projections"
        ),
        anchor="        | .copy p | .move p => Nat.beq p.localId lid && p.projection.isEmpty",
        replacement="        | .copy p | .move p => Nat.beq p.localId lid && true",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_projected_ptr_meta_operand",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_fake_ptr_metadata_forbids_terminator_use",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "isFakePtrMetadataLocalV2 rejects fake-metadata locals mentioned "
            "by any terminator (e.g. coreCall args or dst)"
        ),
        anchor=(
            "          bb.statements.all\n"
            "            (stmtRespectsFakePtrMetadataLocalV2 body.locals lid) &&\n"
            "            !terminatorMentionsLocalV2 lid bb.terminator)"
        ),
        replacement=(
            "          bb.statements.all\n"
            "            (stmtRespectsFakePtrMetadataLocalV2 body.locals lid) &&\n"
            "            true)"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_fake_ptr_metadata_forbids_terminator_use",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_v2_body_fake_address_of_valid",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description=(
            "BodyStaticAdmittedV2 requires bodyFakeAddressOfValidV2 even on "
            "raw-pointer-only bodies"
        ),
        anchor=(
            "    !bodyMixesRefsAndRawPtrsV2 body &&\n"
            "    bodyFakeAddressOfValidV2 body &&"
        ),
        replacement=(
            "    !bodyMixesRefsAndRawPtrsV2 body &&\n"
            "    true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_v2_body_fake_address_of_valid",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_fake_address_of_ref_validity",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalFakeAddressOfRvalueV2 enforces refValidInMem on reference "
            "base locals"
        ),
        anchor=(
            "          match readSlot with\n"
            "          | .error k => .error k\n"
            "          | .ok none => .error .undefined\n"
            "          | .ok (some v) =>\n"
            "            match refValidInMem mem srcMut pt v with\n"
            "            | .error k => .error k\n"
            "            | .ok () => .ok (v, locals, mem)"
        ),
        replacement=(
            "          match readSlot with\n"
            "          | .error k => .error k\n"
            "          | .ok none => .error .undefined\n"
            "          | .ok (some v) => .ok (v, locals, mem)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_fake_address_of_ref_validity",
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_option_unwrap_refs_valid",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execCoreContractOp .optionUnwrap validates unwrapped Option<&T> "
            "reference payloads via refsValidInMem"
        ),
        anchor=(
            "      | some v =>\n"
            "        if !refsValidInMem m inner v then\n"
            "          .error .undefined\n"
            "        else\n"
            "          .ok (v, m)"
        ),
        replacement=(
            "      | some v =>\n"
            "        if false then\n"
            "          .error .undefined\n"
            "        else\n"
            "          .ok (v, m)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_option_unwrap_refs_valid",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_v2_option_discriminant_dst_ty",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalRvalueV2 .discriminant on projected Option checks dstTy is "
            "isize"
        ),
        anchor=(
            "        | .option _ =>\n"
            "          if !MirTy.beq dstTy (.int .isize true) then\n"
            "            .error .unsupported\n"
            "          else\n"
            "            evalOptionDiscriminantOfVal optVal locals1 mem1"
        ),
        replacement=(
            "        | .option _ =>\n"
            "          if false then\n"
            "            .error .unsupported\n"
            "          else\n"
            "            evalOptionDiscriminantOfVal optVal locals1 mem1"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_option_discriminant_dst_ty",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_next_power_of_two_overflow_trap",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execNextPowerOfTwo traps via corePanicTrap when self exceeds "
            "2^(BITS - 1)"
        ),
        anchor=(
            "  if Nat.blt (Nat.pow 2 (w.bitWidth - 1)) bits then\n"
            "    .error corePanicTrap"
        ),
        replacement=(
            "  if false then\n"
            "    .error corePanicTrap"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_next_power_of_two_overflow_trap",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_next_multiple_of_div_zero_trap",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description="execNextMultipleOf traps via corePanicTrap when rhs is 0",
        anchor=(
            "  if Nat.beq r 0 then\n"
            "    .error corePanicTrap"
        ),
        replacement=(
            "  if false then\n"
            "    .error corePanicTrap"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_next_multiple_of_div_zero_trap",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_next_multiple_of_overflow_trap",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execNextMultipleOf traps via corePanicTrap when the rounded "
            "result overflows w.bitWidth"
        ),
        anchor=(
            "    if Nat.ble (Nat.pow 2 w.bitWidth) res then\n"
            "      .error corePanicTrap"
        ),
        replacement=(
            "    if false then\n"
            "      .error corePanicTrap"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_next_multiple_of_overflow_trap",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_next_power_of_two_unsigned_only",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execCoreContractOp rejects signed operands on .numNextPowerOfTwo "
            "as .unsupported"
        ),
        anchor=(
            "  | .numNextPowerOfTwo w s, [(.int lw ls, .scalar lSv)] =>\n"
            "    if s || ls || !IntWidth.beq w lw || !MirTy.beq dstTy (.int w false) then"
        ),
        replacement=(
            "  | .numNextPowerOfTwo w s, [(.int lw ls, .scalar lSv)] =>\n"
            "    if false || !IntWidth.beq w lw || !MirTy.beq dstTy (.int w false) then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_next_power_of_two_unsigned_only",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_next_multiple_of_unsigned_only",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execCoreContractOp rejects signed operands on .numNextMultipleOf "
            "as .unsupported"
        ),
        anchor=(
            "  | .numNextMultipleOf w s,\n"
            "      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>\n"
            "    if s || ls || rs || !IntWidth.beq w lw || !IntWidth.beq w rw ||"
        ),
        replacement=(
            "  | .numNextMultipleOf w s,\n"
            "      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>\n"
            "    if false || !IntWidth.beq w lw || !IntWidth.beq w rw ||"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_next_multiple_of_unsigned_only",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_cmp_min_tie_break",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description="Ord::min returns self (lSv) when both operands decode equal",
        anchor="    else if decide (decodeScalar lSv ≤ decodeScalar rSv) then",
        replacement="    else if decide (decodeScalar lSv < decodeScalar rSv) then",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_cmp_min_tie_break",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_cmp_max_tie_break",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description="Ord::max returns other (rSv) when both operands decode equal",
        anchor="    else if decide (decodeScalar rSv < decodeScalar lSv) then",
        replacement="    else if decide (decodeScalar rSv ≤ decodeScalar lSv) then",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_cmp_max_tie_break",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_div_ceil_div_zero_trap",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description="execCoreContractOp .numDivCeil traps via corePanicTrap when rhs = 0",
        anchor=(
            "      if Nat.beq r 0 then\n"
            "        .error corePanicTrap\n"
            "      else\n"
            "        let d := Nat.div l r"
        ),
        replacement=(
            "      if false then\n"
            "        .error corePanicTrap\n"
            "      else\n"
            "        let d := Nat.div l r"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_div_ceil_div_zero_trap",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_div_ceil_unsigned_only",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execCoreContractOp rejects signed operands on .numDivCeil as "
            ".unsupported"
        ),
        anchor=(
            "  | .numDivCeil w s,\n"
            "      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>\n"
            "    if s || ls || rs || !IntWidth.beq w lw || !IntWidth.beq w rw ||"
        ),
        replacement=(
            "  | .numDivCeil w s,\n"
            "      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>\n"
            "    if false || !IntWidth.beq w lw || !IntWidth.beq w rw ||"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_div_ceil_unsigned_only",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_checked_shl_oob_none",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execCoreContractOp .numCheckedShl returns None when rhs >= BITS"
        ),
        anchor=(
            "      let amt := (truncateBits .i32 rSv.bits).toNat\n"
            "      if !Nat.blt amt w.bitWidth then\n"
            "        .ok (.optionVal none, m)"
        ),
        replacement=(
            "      let amt := (truncateBits .i32 rSv.bits).toNat\n"
            "      if false then\n"
            "        .ok (.optionVal none, m)"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_checked_shl_oob_none",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_leading_zeros_bit_test",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "leadingZerosFrom stops at the most-significant set bit for u32 "
            "and u64 leading_zeros"
        ),
        anchor="    if Nat.beq (Nat.land (Nat.shiftRight bits n) 1) 1 then 0",
        replacement="    if false then 0",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_leading_zeros_u32_u64",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_leading_zeros_width",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "numLeadingZeros scans w.bitWidth bits (64 for u64 vs 32 for u32)"
        ),
        anchor="      let count := leadingZerosFrom bits w.bitWidth",
        replacement="      let count := leadingZerosFrom bits 32",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_leading_zeros_u32_u64",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_count_ones_bit_count",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description="countOnesFrom accumulates each set bit across w.bitWidth",
        anchor="  | n + 1 => Nat.land bits 1 + countOnesFrom (Nat.shiftRight bits 1) n",
        replacement="  | n + 1 => countOnesFrom (Nat.shiftRight bits 1) n",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_count_ones",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_trailing_zeros_bit_test",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description="trailingZerosFrom stops at the least-significant set bit",
        anchor="    if Nat.beq (Nat.land bits 1) 1 then 0",
        replacement="    if false then 0",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_trailing_zeros",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_is_multiple_of_zero_rhs",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "numIsMultipleOf returns (self == 0) when rhs = 0 instead of "
            "returning false unconditionally"
        ),
        anchor="      if Nat.beq r 0 then .ok (.bool (Nat.beq l 0), m)",
        replacement="      if Nat.beq r 0 then .ok (.bool false, m)",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_is_multiple_of_zero_rhs",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_is_multiple_of_unsigned_only",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execCoreContractOp .numIsMultipleOf rejects signed integers as "
            ".unsupported"
        ),
        anchor=(
            "  | .numIsMultipleOf w s,\n"
            "      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>\n"
            "    if s || ls || rs || !IntWidth.beq w lw || !IntWidth.beq w rw ||"
        ),
        replacement=(
            "  | .numIsMultipleOf w s,\n"
            "      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>\n"
            "    if false || !IntWidth.beq w lw || !IntWidth.beq w rw ||"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_is_multiple_of_unsigned_only",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_split_at_mut_bounds_panic",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execSliceSplitAtOutcome returns .panic when mid > len instead of "
            "constructing out-of-bounds subslices"
        ),
        anchor=(
            "      if !Nat.ble mid len.toNat then\n"
            "        .panic"
        ),
        replacement=(
            "      if false then\n"
            "        .panic"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_split_at_mut_bounds_panic",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_split_at_mut_no_shared_upgrade",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execSliceSplitAtOutcome rejects upgrading a shared &[T] input "
            "slice into (&mut [T], &mut [T])"
        ),
        anchor=(
            "  else if Mutability.beq inMut .shared && Mutability.beq reqMut .mut then\n"
            "    .fault .undefined"
        ),
        replacement=(
            "  else if false then\n"
            "    .fault .undefined"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_split_at_mut_no_shared_upgrade",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_split_at_mut_suffix_offset_disjoint",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execSliceSplitAtOutcome advances the suffix pointer by mid "
            "elements so the prefix and suffix &mut spans are disjoint"
        ),
        anchor="          match ptrAddInMem m lay.size p mid with",
        replacement="          match ptrAddInMem m lay.size p 0 with",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_split_at_mut_suffix_offset_disjoint",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_split_at_mut_suffix_len_union",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execSliceSplitAtOutcome sets suffix length to len - mid so the "
            "union of prefix and suffix equals the input span"
        ),
        anchor="            let suffixVal := Val.slicePtr p' (UInt64.ofNat (len.toNat - mid))",
        replacement="            let suffixVal := Val.slicePtr p' len",
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_split_at_mut_suffix_len_union",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_array_subslice_len_u64_bound",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execArraySubslice rejects array lengths >= 2^64 before "
            "converting len to UInt64"
        ),
        anchor=(
            "noncomputable def execArraySubslice (m : MemoryState)\n"
            "    (reqMut inMut : Mutability) (elem : MirTy) (len : Nat) (p : PtrVal)\n"
            "    (startOff endOff : Nat) : Except FaultKind (Val × MemoryState) :=\n"
            "  if !isSizedNoRefV2Ty elem || !Nat.blt len (Nat.pow 2 64) then"
        ),
        replacement=(
            "noncomputable def execArraySubslice (m : MemoryState)\n"
            "    (reqMut inMut : Mutability) (elem : MirTy) (len : Nat) (p : PtrVal)\n"
            "    (startOff endOff : Nat) : Except FaultKind (Val × MemoryState) :=\n"
            "  if !isSizedNoRefV2Ty elem then"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_array_subslice_len_u64_bound",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_array_subslice_no_shared_upgrade",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execArraySubslice rejects upgrading a shared &[T; N] reference "
            "to &mut [T]"
        ),
        anchor=(
            "  if !isSizedNoRefV2Ty elem || !Nat.blt len (Nat.pow 2 64) then\n"
            "    .error .unsupported\n"
            "  else if Mutability.beq inMut .shared && Mutability.beq reqMut .mut then\n"
            "    .error .undefined\n"
            "  else\n"
            "    match refValidInMem m inMut (.array elem len) (.ptr p) with"
        ),
        replacement=(
            "  if !isSizedNoRefV2Ty elem || !Nat.blt len (Nat.pow 2 64) then\n"
            "    .error .unsupported\n"
            "  else if false then\n"
            "    .error .undefined\n"
            "  else\n"
            "    match refValidInMem m inMut (.array elem len) (.ptr p) with"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_array_subslice_no_shared_upgrade",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="core_contracts_array_subslice_ref_valid",
        target_file="trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
        target_module="Trusted/MirSemantics/CoreContracts",
        description=(
            "execArraySubslice validates the full &[T; N] array extent via "
            "refValidInMem before delegating to execSliceSubslice"
        ),
        anchor=(
            "    match refValidInMem m inMut (.array elem len) (.ptr p) with\n"
            "    | .error k => .error k\n"
            "    | .ok () =>\n"
            "      execSliceSubslice m reqMut inMut elem p (UInt64.ofNat len) startOff\n"
            "        endOff"
        ),
        replacement=(
            "    match Except.ok () with\n"
            "    | .error k => .error k\n"
            "    | .ok () =>\n"
            "      execSliceSubslice m reqMut inMut elem p (UInt64.ofNat len) startOff\n"
            "        endOff"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_core_contracts_array_subslice_ref_valid",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Profile v2 heap allocation (`Vec`/`Box`) guards (16 guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="alloc_vec_valid_unsupported_elem",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "vecValidInMem refuses an unsupported element type "
            "(isSupportedPointeeTy) with .unsupported"
        ),
        anchor=(
            "  if !isSupportedPointeeTy v.elem then\n"
            "    .error .unsupported\n"
            "  else\n"
            "    ownedHeapBufValidInMem m isMut v.elem v.ptr v.cap v.len"
        ),
        replacement=(
            "  if false then\n"
            "    .error .unsupported\n"
            "  else\n"
            "    ownedHeapBufValidInMem m isMut v.elem v.ptr v.cap v.len"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_vec_valid_unsupported_elem",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="alloc_box_valid_unsupported_slice_elem",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "boxValidInMem refuses Box<[T]> with an unsupported element type "
            "(isSupportedPointeeTy) with .unsupported"
        ),
        anchor=(
            "  | .slice elem =>\n"
            "    if !isSupportedPointeeTy elem then\n"
            "      .error .unsupported\n"
            "    else\n"
            "      boxPointeeValidInMem m isMut b.pointee b.ptr b.len"
        ),
        replacement=(
            "  | .slice elem =>\n"
            "    if false then\n"
            "      .error .unsupported\n"
            "    else\n"
            "      boxPointeeValidInMem m isMut b.pointee b.ptr b.len"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_box_valid_unsupported_slice_elem",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="alloc_vec_grow_cap_u64_bound",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "vecGrowCap fails (capacity-overflow panic) when minCap exceeds "
            "usize::MAX, including for zero-sized elements"
        ),
        anchor=(
            "  if !Nat.blt minCap u64Bound then\n"
            "    none\n"
            "  else if Nat.beq elemSize 0 then\n"
            "    some minCap"
        ),
        replacement=(
            "  if false then\n"
            "    none\n"
            "  else if Nat.beq elemSize 0 then\n"
            "    some minCap"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_vec_grow_cap_u64_bound",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="alloc_vec_grow_cap_doubled_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "vecGrowCap fails when the amortized doubled capacity exceeds "
            "isize::MAX bytes (isizeMaxBytes)"
        ),
        anchor=(
            "    if Nat.blt (doubled * elemSize) isizeMaxBytes &&\n"
            "        Nat.blt doubled u64Bound then\n"
            "      some doubled"
        ),
        replacement=(
            "    if true &&\n"
            "        Nat.blt doubled u64Bound then\n"
            "      some doubled"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_vec_grow_cap_doubled_overflow",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="alloc_vec_with_capacity_overflow",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "evalVecWithCapacity faults .unsupported (capacity-overflow "
            "panic) when capacity * size exceeds isize::MAX"
        ),
        anchor=(
            "      let totalBytes := cap.toNat * lay.size\n"
            "      if !Nat.blt totalBytes isizeMaxBytes then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "      let totalBytes := cap.toNat * lay.size\n"
            "      if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_vec_with_capacity_overflow",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="alloc_vec_index_oob",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "evalVecIndex faults .unsupported (bounds-check panic) when "
            "idx >= len, even inside the capacity"
        ),
        anchor=(
            "    if !Nat.blt idx.toNat v.len.toNat then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "    if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_vec_index_oob",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="alloc_retire_heap_buffer",
        target_file="trusted/lean/Trusted/MirSemantics/AllocContracts.lean",
        target_module="Trusted/MirSemantics/AllocContracts",
        description=(
            "retireHeapBuffer kills a reallocated buffer, so pointers into "
            "it lose provenance (stale reads fault)"
        ),
        anchor=(
            "  | some aid => deallocateStack m ⟨aid, p.offsetBytes.toNat⟩"
        ),
        replacement="  | some _ => .ok m",
        fixture_module="AllocRefutations",
        theorem_name="refute_alloc_retire_heap_buffer",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_zero_cap_ptr_null",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "zeroCapPtrValidInMem rejects a null provenance-free pointer for "
            "an empty heap buffer"
        ),
        anchor=(
            "    let align := Nat.pow 2 alignLog2\n"
            "    if Nat.beq p.offsetBytes.toNat 0 ||\n"
            "        !Nat.beq (Nat.mod p.offsetBytes.toNat align) 0 then"
        ),
        replacement=(
            "    let align := Nat.pow 2 alignLog2\n"
            "    if false ||\n"
            "        !Nat.beq (Nat.mod p.offsetBytes.toNat align) 0 then"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_zero_cap_ptr_null",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_heap_buf_len_gt_cap",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="heapBufValidInMem rejects len > cap as UB",
        anchor=(
            "      if !Nat.ble len.toNat cap.toNat then\n"
            "        .error .undefined\n"
            "      else\n"
            "        let capBytes := cap.toNat * lay.size"
        ),
        replacement=(
            "      if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        let capBytes := cap.toNat * lay.size"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_heap_buf_len_gt_cap",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_heap_buf_dead_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "heapBufValidInMem rejects a buffer in a dead (live = false) "
            "allocation as UB"
        ),
        anchor=(
            "              if !a.live || "
            "!isInBounds a p.offsetBytes.toNat capBytes ||\n"
        ),
        replacement=(
            "              if false || "
            "!isInBounds a p.offsetBytes.toNat capBytes ||\n"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_heap_buf_dead_alloc",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_heap_buf_cap_oob",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "heapBufValidInMem rejects cap * size bytes past the end of the "
            "allocation as UB"
        ),
        anchor=(
            "              if !a.live || "
            "!isInBounds a p.offsetBytes.toNat capBytes ||\n"
        ),
        replacement="              if !a.live || false ||\n",
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_heap_buf_cap_oob",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_heap_buf_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "heapBufValidInMem rejects uninitialized bytes in the len "
            "prefix as UB"
        ),
        anchor=(
            "                if !isSliceAllInit initSlice then\n"
            "                  .error .undefined\n"
            "                else if isIntMirTy elem then"
        ),
        replacement=(
            "                if false then\n"
            "                  .error .undefined\n"
            "                else if isIntMirTy elem then"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_heap_buf_uninit",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_owned_heap_buf_size",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "ownedHeapBufValidInMem requires the allocation size to be "
            "exactly cap * size bytes"
        ),
        anchor=(
            "                !Nat.beq a.bytes.length "
            "(cap.toNat * lay.size) ||\n"
        ),
        replacement="                false ||\n",
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_owned_heap_buf_size",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="bytes_box_pointee_slice_owned",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description=(
            "boxPointeeValidInMem requires a Box<[T]> to own its whole "
            "allocation (ownedHeapBufValidInMem)"
        ),
        anchor=(
            "  | .slice elem, some len => "
            "ownedHeapBufValidInMem m isMut elem p len len"
        ),
        replacement=(
            "  | .slice elem, some len => "
            "heapBufValidInMem m isMut elem p len len"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_bytes_box_pointee_slice_owned",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_box_as_ref_validity",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalCastKindV2 .boxAsRef checks refValidInMem of the "
            "dereferenced Box pointer"
        ),
        anchor=(
            "          match refValidInMem mem .shared pt ptrVal with\n"
            "          | .error k => .error k\n"
            "          | .ok () => .ok ptrVal"
        ),
        replacement=(
            "          match refValidInMem mem .shared pt ptrVal with\n"
            "          | .error _ => .ok ptrVal\n"
            "          | .ok () => .ok ptrVal"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_step_box_as_ref_validity",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="step_box_as_ref_pointee_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Step.lean",
        target_module="Trusted/MirSemantics/Step",
        description=(
            "evalCastKindV2 .boxAsRef refuses a cast to a reference with a "
            "different pointee type"
        ),
        anchor=(
            "    | .box pt, .boxPtr p optLen, .ref .shared castPt =>\n"
            "      if !MirTy.beq pt castPt then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "    | .box pt, .boxPtr p optLen, .ref .shared castPt =>\n"
            "      if false then\n"
            "        .error .unsupported"
        ),
        fixture_module="AllocRefutations",
        theorem_name="refute_step_box_as_ref_pointee_mismatch",
        sanity_module="AllocSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_satisfies_post_requires_wf",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="SatisfiesPost requires WellFormed p q",
        anchor="  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out",
        replacement="  True ∧ ∀ out : TerminalOut, Behavior p q out → post out",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_satisfies_post_requires_wf",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_satisfies_post_enforces_post",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="SatisfiesPost enforces post on every terminal output",
        anchor="  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out",
        replacement="  WellFormed p q ∧ True",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_satisfies_post_enforces_post",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_pointer_width",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted enforces 64-bit pointerWidthBits",
        anchor=(
            "noncomputable def singleBodyStaticAdmitted (p : Program) (body : Body) : Bool :=\n"
            "  Nat.beq p.pointerWidthBits 64 &&"
        ),
        replacement=(
            "noncomputable def singleBodyStaticAdmitted (p : Program) (body : Body) : Bool :=\n"
            "  true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_pointer_width",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_profile_v1",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted enforces mirProfileVersion = 1",
        anchor="    Nat.beq p.mirProfileVersion 1 &&",
        replacement="    true &&",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_profile_v1",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_nonempty_identity",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted requires non-empty body.identity",
        anchor=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    !stringIsEmpty body.identity &&"
        ),
        replacement=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_nonempty_identity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_nonempty_blocks",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted requires non-empty basicBlocks",
        anchor=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    !stringIsEmpty body.identity &&\n"
            "    !body.basicBlocks.isEmpty &&"
        ),
        replacement=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    !stringIsEmpty body.identity &&\n"
            "    true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_nonempty_blocks",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_arg_count_bound",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted requires argumentCount < locals.length",
        anchor=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    !stringIsEmpty body.identity &&\n"
            "    !body.basicBlocks.isEmpty &&\n"
            "    Nat.blt body.argumentCount body.locals.length &&"
        ),
        replacement=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    !stringIsEmpty body.identity &&\n"
            "    !body.basicBlocks.isEmpty &&\n"
            "    true &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_arg_count_bound",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_storage_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted enforces storageAnnotationsInBounds",
        anchor=(
            "    storageAnnotationsInBounds body &&\n"
            "    discriminantTypesValid body &&\n"
            "    castTypesValid body &&\n"
            "    assertConditionTypesValid body &&\n"
            "    body.locals.all isSupportedScalarOrUnitTy &&"
        ),
        replacement=(
            "    true &&\n"
            "    discriminantTypesValid body &&\n"
            "    castTypesValid body &&\n"
            "    assertConditionTypesValid body &&\n"
            "    body.locals.all isSupportedScalarOrUnitTy &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_storage_bounds",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_discr_types",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted enforces discriminantTypesValid",
        anchor=(
            "    discriminantTypesValid body &&\n"
            "    castTypesValid body &&\n"
            "    assertConditionTypesValid body &&\n"
            "    body.locals.all isSupportedScalarOrUnitTy &&"
        ),
        replacement=(
            "    true &&\n"
            "    castTypesValid body &&\n"
            "    assertConditionTypesValid body &&\n"
            "    body.locals.all isSupportedScalarOrUnitTy &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_discr_types",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_cast_types",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted enforces castTypesValid",
        anchor=(
            "    castTypesValid body &&\n"
            "    assertConditionTypesValid body &&\n"
            "    body.locals.all isSupportedScalarOrUnitTy &&"
        ),
        replacement=(
            "    true &&\n"
            "    assertConditionTypesValid body &&\n"
            "    body.locals.all isSupportedScalarOrUnitTy &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_cast_types",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_static_admitted_local_types",
        target_file="trusted/lean/Trusted/MirSemantics/State.lean",
        target_module="Trusted/MirSemantics/State",
        description="singleBodyStaticAdmitted enforces supported local types",
        anchor=(
            "    body.locals.all isSupportedScalarOrUnitTy &&\n"
            "    callsAdmitted p body"
        ),
        replacement=(
            "    true &&\n"
            "    callsAdmitted p body"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_static_admitted_local_types",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_body_verified_binds_body",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyVerified binds body to p.bodies[defId]",
        anchor=(
            "noncomputable def BodyVerified (p : Program) (defId : DefId) (body : Body)\n"
            "    (safetyPre : List Val → Prop) : Prop :=\n"
            "  getElem? p.bodies defId = some body ∧"
        ),
        replacement=(
            "noncomputable def BodyVerified (p : Program) (defId : DefId) (body : Body)\n"
            "    (safetyPre : List Val → Prop) : Prop :=\n"
            "  True ∧"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_body_verified_binds_body",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_program_verified_entry_in_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="ProgramVerified enforces entryDefId < bodies.length",
        anchor=(
            "  Nat.beq p.mirProfileVersion 1 = true ∧\n"
            "  !p.bodies.isEmpty = true ∧\n"
            "  Nat.blt p.entryDefId p.bodies.length = true ∧"
        ),
        replacement=(
            "  Nat.beq p.mirProfileVersion 1 = true ∧\n"
            "  !p.bodies.isEmpty = true ∧\n"
            "  True ∧"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_program_verified_entry_in_bounds",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_program_verified_unique_identities",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="ProgramVerified enforces bodiesHaveUniqueIdentities",
        anchor=(
            "  Nat.beq p.mirProfileVersion 1 = true ∧\n"
            "  !p.bodies.isEmpty = true ∧\n"
            "  Nat.blt p.entryDefId p.bodies.length = true ∧\n"
            "  bodiesHaveUniqueIdentities p.bodies = true ∧"
        ),
        replacement=(
            "  Nat.beq p.mirProfileVersion 1 = true ∧\n"
            "  !p.bodies.isEmpty = true ∧\n"
            "  Nat.blt p.entryDefId p.bodies.length = true ∧\n"
            "  True ∧"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_program_verified_unique_identities",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_program_verified_checks_all_bodies",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="ProgramVerified requires BodyVerified on every body",
        anchor=(
            "  (∀ (defId : DefId) (body : Body),\n"
            "    getElem? p.bodies defId = some body →\n"
            "    BodyVerified p defId body (specs.safety body.identity)) ∧"
        ),
        replacement="  True ∧",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_program_verified_checks_all_bodies",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_program_verified_checks_property",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="ProgramVerified enforces specs.property p",
        anchor=(
            "    BodyVerified p defId body (specs.safety body.identity)) ∧\n"
            "  specs.property p"
        ),
        replacement=(
            "    BodyVerified p defId body (specs.safety body.identity)) ∧\n"
            "  True"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_program_verified_checks_property",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_crate_theorem_requires_crate_scope",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="CrateTheorem enforces c.program.scope = .crate",
        anchor="  c.program.scope = .crate ∧ ProgramVerified c.program c.specs",
        replacement="  True ∧ ProgramVerified c.program c.specs",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_crate_theorem_requires_crate_scope",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_unit_theorem_requires_unit_scope",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="UnitTheorem enforces c.program.scope = .unit",
        anchor="  c.program.scope = .unit ∧ ProgramVerified c.program c.specs",
        replacement="  True ∧ ProgramVerified c.program c.specs",
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_unit_theorem_requires_unit_scope",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Contract.lean (23 contract & RB-index guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="contract_effective_safety_pre_unsafe_gate",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="effectiveSafetyPre ignores safetyPre on safe functions",
        anchor=(
            "noncomputable def FnContract.effectiveSafetyPre (c : FnContract)\n"
            "    (isUnsafe : Bool) (q : Query) : Prop :=\n"
            "  isUnsafe = true → c.safetyPre q"
        ),
        replacement=(
            "noncomputable def FnContract.effectiveSafetyPre (c : FnContract)\n"
            "    (isUnsafe : Bool) (q : Query) : Prop :=\n"
            "  c.safetyPre q"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_effective_safety_pre_unsafe_gate",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_effective_behavior_pre_safety",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="effectiveBehaviorPre includes effectiveSafetyPre",
        anchor=(
            "noncomputable def FnContract.effectiveBehaviorPre (c : FnContract)\n"
            "    (isUnsafe : Bool) (q : Query) : Prop :=\n"
            "  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q"
        ),
        replacement=(
            "noncomputable def FnContract.effectiveBehaviorPre (c : FnContract)\n"
            "    (isUnsafe : Bool) (q : Query) : Prop :=\n"
            "  True ∧ c.behaviorPre q"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_effective_behavior_pre_safety",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_effective_behavior_pre_behavior",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="effectiveBehaviorPre includes behaviorPre",
        anchor=(
            "noncomputable def FnContract.effectiveBehaviorPre (c : FnContract)\n"
            "    (isUnsafe : Bool) (q : Query) : Prop :=\n"
            "  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q"
        ),
        replacement=(
            "noncomputable def FnContract.effectiveBehaviorPre (c : FnContract)\n"
            "    (isUnsafe : Bool) (q : Query) : Prop :=\n"
            "  c.effectiveSafetyPre isUnsafe q ∧ True"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_effective_behavior_pre_behavior",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_safety_arg_pre_checks_pre",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="FnContract.safetyArgPre enforces c.safetyPre",
        anchor=(
            "noncomputable def FnContract.safetyArgPre (c : FnContract) : List Val → Prop :=\n"
            "  fun args => c.safetyPre { args := args }"
        ),
        replacement=(
            "noncomputable def FnContract.safetyArgPre (c : FnContract) : List Val → Prop :=\n"
            "  fun _ => True"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_safety_arg_pre_checks_pre",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_body_satisfied_binds_body",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="BodyContractSatisfied binds body to p.bodies[defId]",
        anchor=(
            "noncomputable def BodyContractSatisfied (p : Program) (defId : DefId)\n"
            "    (body : Body) (c : FnContract) : Prop :=\n"
            "  getElem? p.bodies defId = some body ∧"
        ),
        replacement=(
            "noncomputable def BodyContractSatisfied (p : Program) (defId : DefId)\n"
            "    (body : Body) (c : FnContract) : Prop :=\n"
            "  True ∧"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_body_satisfied_binds_body",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_body_satisfied_static_admitted",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="BodyContractSatisfied requires BodyStaticAdmitted unconditionally",
        anchor=(
            "  getElem? p.bodies defId = some body ∧\n"
            "  BodyStaticAdmitted p body = true ∧"
        ),
        replacement=(
            "  getElem? p.bodies defId = some body ∧\n"
            "  True ∧"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_body_satisfied_static_admitted",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_body_satisfied_enforces_safety_wf",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="BodyContractSatisfied requires WellFormed under effectiveSafetyPre",
        anchor="    (c.effectiveSafetyPre body.isUnsafe q → WellFormed ep q) ∧",
        replacement="    (c.effectiveSafetyPre body.isUnsafe q → True) ∧",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_body_satisfied_enforces_safety_wf",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_body_satisfied_post_return",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="BodyContractSatisfied enforces postReturn on normal return",
        anchor="        | .returned retOut => c.postReturn q retOut",
        replacement="        | .returned _ => True",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_body_satisfied_post_return",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_body_satisfied_forbids_abort",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="BodyContractSatisfied forbids .aborted outcomes",
        anchor="        | .aborted _ => False) ∧",
        replacement="        | .aborted _ => True) ∧",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_body_satisfied_forbids_abort",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_body_satisfied_terminates",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="BodyContractSatisfied forbids Diverges when terminates = true",
        anchor="      (c.effects.terminates = true → ¬ Diverges ep q))",
        replacement="      (c.effects.terminates = true → True))",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_body_satisfied_terminates",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_sig_matches_is_unsafe",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodyMatchesContractSignature checks body.isUnsafe == sig.isUnsafe",
        anchor="  (body.isUnsafe == sig.isUnsafe) &&",
        replacement="  true &&",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_sig_matches_is_unsafe",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_sig_matches_arg_count",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodyMatchesContractSignature checks argumentCount == sig.params.length",
        anchor="    Nat.beq body.argumentCount sig.params.length &&",
        replacement="    true &&",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_sig_matches_arg_count",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_sig_matches_params",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodyMatchesContractSignature checks parameter MirTy list equality",
        anchor="    MirTy.beqList ((body.locals.drop 1).take body.argumentCount) sig.params &&",
        replacement="    true &&",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_sig_matches_params",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_sig_matches_ret",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodyMatchesContractSignature checks return local MirTy equality",
        anchor=(
            "    match body.locals with\n"
            "    | retTy :: _ => MirTy.beq retTy sig.ret\n"
            "    | [] => false"
        ),
        replacement=(
            "    match body.locals with\n"
            "    | _ :: _ => true\n"
            "    | [] => false"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_sig_matches_ret",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_sig_rejects_empty_locals",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodyMatchesContractSignature rejects empty body.locals",
        anchor=(
            "    match body.locals with\n"
            "    | retTy :: _ => MirTy.beq retTy sig.ret\n"
            "    | [] => false"
        ),
        replacement=(
            "    match body.locals with\n"
            "    | retTy :: _ => MirTy.beq retTy sig.ret\n"
            "    | [] => true"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_sig_rejects_empty_locals",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_entry_matches_identity",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodySatisfiesContractEntry requires body.identity == e.identity",
        anchor="    stringBeq body.identity e.identity = true ∧",
        replacement="    True ∧",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_entry_matches_identity",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_entry_checks_signature",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodySatisfiesContractEntry checks e.signature when present",
        anchor=(
            "    (match e.signature with\n"
            "     | none => True\n"
            "     | some sig => bodyMatchesContractSignature body sig = true) ∧"
        ),
        replacement="    True ∧",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_entry_checks_signature",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_entry_require_inhabited",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="bodySatisfiesContractEntry requires ContractPreInhabited when requireInhabited = true",
        anchor="    (e.requireInhabited = true → ContractPreInhabited body e.contract)",
        replacement="    True",
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_entry_require_inhabited",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_entries_satisfied_head",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="ContractEntriesSatisfied checks the head ContractEntry",
        anchor=(
            "  | e :: rest =>\n"
            "    bodySatisfiesContractEntry p e ∧ ContractEntriesSatisfied p rest"
        ),
        replacement=(
            "  | _ :: rest =>\n"
            "    True ∧ ContractEntriesSatisfied p rest"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_entries_satisfied_head",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_entries_satisfied_tail",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="ContractEntriesSatisfied recurses over remaining entries",
        anchor=(
            "  | e :: rest =>\n"
            "    bodySatisfiesContractEntry p e ∧ ContractEntriesSatisfied p rest"
        ),
        replacement=(
            "  | e :: _ =>\n"
            "    bodySatisfiesContractEntry p e ∧ True"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_entries_satisfied_tail",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_specs_rejects_bad_identities",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="ContractSpecs fails closed on empty or duplicate identities",
        anchor=(
            "      property := fun p =>\n"
            "        (false = true) ∧ ContractEntriesSatisfied p entries }"
        ),
        replacement=(
            "      property := fun p =>\n"
            "        (true = true) ∧ ContractEntriesSatisfied p entries }"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_specs_rejects_bad_identities",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_specs_safety_dispatch",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="ContractSpecs.safety enforces the matched entry's safetyArgPre",
        anchor=(
            "        match contractEntryRbLookup tree id with\n"
            "        | some e => e.contract.safetyArgPre args\n"
            "        | none => True"
        ),
        replacement=(
            "        match contractEntryRbLookup tree id with\n"
            "        | some _ => True\n"
            "        | none => True"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_specs_safety_dispatch",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="contract_specs_checks_entries",
        target_file="trusted/lean/Trusted/MirSemantics/Contract.lean",
        target_module="Trusted/MirSemantics/Contract",
        description="ContractSpecs.property enforces ContractEntriesSatisfied",
        anchor=(
            "      property := fun p =>\n"
            "        (true = true) ∧ ContractEntriesSatisfied p entries }"
        ),
        replacement=(
            "      property := fun _ =>\n"
            "        (true = true) ∧ True }"
        ),
        fixture_module="ContractRefutations",
        theorem_name="refute_contract_specs_checks_entries",
        sanity_module="ContractSanity",
        needs_wf_helper=False,
    ),
)


AUDIT_HEADER_GUARDS: tuple[AuditHeaderGuard, ...] = (
    AuditHeaderGuard(
        guard_id="audit_header_reject_lean_import",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="isForbiddenPureImport rejects `import Lean` in target headers",
        anchor=(
            "  let r := m.getRoot\n"
            "  r == `Lean || r == `Lake ||"
        ),
        replacement=(
            "  let r := m.getRoot\n"
            "  false || r == `Lake ||"
        ),
        negative_source="import Lean\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_header_reject_lake_import",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="isForbiddenPureImport rejects `import Lake` in target headers",
        anchor=(
            "  let r := m.getRoot\n"
            "  r == `Lean || r == `Lake ||"
        ),
        replacement=(
            "  let r := m.getRoot\n"
            "  r == `Lean || false ||"
        ),
        negative_source="import Lake\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_header_reject_init_system_import",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="isForbiddenPureImport rejects `import Init.System.IO` in target headers",
        anchor="    m == `Init.System || (`Init.System).isPrefixOf m ||",
        replacement="    false ||",
        negative_source="import Init.System.IO\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_header_reject_std_uv_import",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="isForbiddenPureImport rejects `import Std.Internal.UV` in target headers",
        anchor="    m == `Std.Internal.UV || (`Std.Internal.UV).isPrefixOf m",
        replacement="    false",
        negative_source="import Std.Internal.UV\n",
    ),
    AuditHeaderGuard(
        guard_id="spec_preflight_reject_lean_import",
        target_file="trusted/audit/SpecPreflight.lean",
        description="SpecPreflight isForbiddenPureImport rejects `import Lean` in target headers",
        anchor=(
            "  let r := m.getRoot\n"
            "  r == `Lean || r == `Lake ||"
        ),
        replacement=(
            "  let r := m.getRoot\n"
            "  false || r == `Lake ||"
        ),
        negative_source="import Lean\n",
    ),
    AuditHeaderGuard(
        guard_id="spec_preflight_reject_lake_import",
        target_file="trusted/audit/SpecPreflight.lean",
        description="SpecPreflight isForbiddenPureImport rejects `import Lake` in target headers",
        anchor=(
            "  let r := m.getRoot\n"
            "  r == `Lean || r == `Lake ||"
        ),
        replacement=(
            "  let r := m.getRoot\n"
            "  r == `Lean || false ||"
        ),
        negative_source="import Lake\n",
    ),
    AuditHeaderGuard(
        guard_id="spec_preflight_reject_init_system_import",
        target_file="trusted/audit/SpecPreflight.lean",
        description="SpecPreflight isForbiddenPureImport rejects `import Init.System.IO` in target headers",
        anchor="    m == `Init.System || (`Init.System).isPrefixOf m ||",
        replacement="    false ||",
        negative_source="import Init.System.IO\n",
    ),
    AuditHeaderGuard(
        guard_id="spec_preflight_reject_std_uv_import",
        target_file="trusted/audit/SpecPreflight.lean",
        description="SpecPreflight isForbiddenPureImport rejects `import Std.Internal.UV` in target headers",
        anchor="    m == `Std.Internal.UV || (`Std.Internal.UV).isPrefixOf m",
        replacement="    false",
        negative_source="import Std.Internal.UV\n",
    ),
)


VALID_SPEC_BOUNDARY_FIXTURE_IDS: frozenset[str] = frozenset(
    {
        "spec_auto_implicit",
        "spec_bang_ident",
        "spec_dbg_trace",
        "spec_uv_open",
    }
)

VALID_TARGET_BOUNDARY_FIXTURE_IDS: frozenset[str] = frozenset(
    {
        "target_expected_true",
        "target_bad_theorem_type",
        "target_proof_sorry",
        "target_impl_by",
        "target_spec_transitive_dbg",
        "target_dup_library",
        "target_unsafe_rec_type_mismatch",
        "target_foundation_propext_hijack",
    }
)

AUDIT_BOUNDARY_GUARDS: tuple[AuditBoundaryGuard, ...] = (
    AuditBoundaryGuard(
        guard_id="spec_preflight_reject_auto_implicit",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="spec-preflight",
        description="validateSpecSetOption rejects `set_option autoImplicit true`",
        anchor='  else\n    fail s!"unsupported option {optName} in specification"',
        replacement="  else\n    pure ()",
        fixture_id="spec_auto_implicit",
    ),
    AuditBoundaryGuard(
        guard_id="spec_preflight_reject_bang_ident",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="spec-preflight",
        description="inspectSpecSyntax rejects bang helpers like `List.head!`",
        anchor="if hasForbiddenSpecIdentComponent cand || hasBangComponent cand then",
        replacement="if hasForbiddenSpecIdentComponent cand then",
        fixture_id="spec_bang_ident",
    ),
    AuditBoundaryGuard(
        guard_id="spec_preflight_reject_dbg_trace",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="spec-preflight",
        description=(
            "inspectSpecSyntax rejects `dbgTrace` identifier references"
        ),
        anchor=(
            "if forbiddenSpecIdentifiers.contains cand then\n"
            '        fail s!"disallowed identifier {val} in specification"'
        ),
        replacement=(
            "if false then\n"
            '        fail s!"disallowed identifier {val} in specification"'
        ),
        fixture_id="spec_dbg_trace",
    ),
    AuditBoundaryGuard(
        guard_id="spec_preflight_reject_uv_open",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="spec-preflight",
        description=(
            "rejectForbiddenSpecNamespace blocks `open Std.Internal.UV`"
        ),
        anchor=(
            "def rejectForbiddenSpecNamespace (how : String) (ns : Name) : "
            "IO Unit := do\n"
            "  if isForbiddenPureNamespace ns (banLeanRoot := true) then"
        ),
        replacement=(
            "def rejectForbiddenSpecNamespace (how : String) (ns : Name) : "
            "IO Unit := do\n"
            "  if false then"
        ),
        fixture_id="spec_uv_open",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_expected_mismatch",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "targetAudit enforces Expected isDefEq canonical root"
        ),
        anchor=(
            '  requireKernelEquality "compiled Expected comparison"\n'
            '    "compiled Expected body differs from the canonical root"\n'
            "    (Kernel.isDefEq checkedEnv {} expectedBody canonical)"
        ),
        replacement="  pure ()",
        fixture_id="target_expected_true",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_theorem_type",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "targetAudit enforces proof theorem type isDefEq canonical root"
        ),
        anchor=(
            '  requireKernelEquality "target theorem type comparison"\n'
            '    "target theorem type differs from Expected"\n'
            "    (Kernel.isDefEq checkedEnv {} theoremInfo.type canonical)"
        ),
        replacement="  pure ()",
        fixture_id="target_bad_theorem_type",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_proof_sorry",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "runTargetClosurePhase blocks sorryAx in Proof without allowSorry"
        ),
        anchor=(
            "if !inPhase1 && allowSorryInProof &&\n"
            "            role == .source .proof && "
            "!phase1Closure.contains n then"
        ),
        replacement=(
            "if !inPhase1 &&\n"
            "            role == .source .proof && "
            "!phase1Closure.contains n then"
        ),
        fixture_id="target_proof_sorry",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_compiler_override",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "targetAudit rejects @[implemented_by] on logical dependencies"
        ),
        anchor=(
            "if sourceOverrides.implementedBy.contains n ||\n"
            "        sourceOverrides.externDecls.contains n then"
        ),
        replacement="if sourceOverrides.externDecls.contains n then",
        fixture_id="target_impl_by",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_transitive_spec_dbg",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "targetAudit enforces transitive spec ban over Model helpers"
        ),
        anchor=(
            "if isForbiddenSpecTransitiveConst n then\n"
            '      fail s!"specification transitively references disallowed '
            'constant {n}"'
        ),
        replacement=(
            "if false then\n"
            '      fail s!"specification transitively references disallowed '
            'constant {n}"'
        ),
        fixture_id="target_spec_transitive_dbg",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_dup_library",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "verifyModuleHeaderInventory rejects intra-module duplicates"
        ),
        anchor=(
            "    if modSeen.contains ci.name then\n"
            '      fail s!"duplicate {dupLabel} {ci.name}"'
        ),
        replacement=(
            "    if false then\n"
            '      fail s!"duplicate {dupLabel} {ci.name}"'
        ),
        fixture_id="target_dup_library",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_unsafe_rec_type_mismatch",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "pairedSpecUnsafeRecParent? checks _unsafe_rec type and "
            "levelParams"
        ),
        anchor=(
            "def sameUnsafeRecHeader (unsafeCi parentCi : ConstantInfo) : "
            "Bool :=\n"
            "  unsafeCi.type == parentCi.type &&\n"
            "    unsafeCi.levelParams == parentCi.levelParams"
        ),
        replacement=(
            "def sameUnsafeRecHeader (unsafeCi parentCi : ConstantInfo) : "
            "Bool :=\n"
            "  true"
        ),
        fixture_id="target_unsafe_rec_type_mismatch",
    ),
    AuditBoundaryGuard(
        guard_id="target_audit_reject_foundation_propext_hijack",
        target_file="trusted/audit/TrustedBoundary.lean",
        mode="target-audit",
        description=(
            "targetAudit foundation loop rejects subsumed propext theorem"
        ),
        anchor=(
            "        if !sameConstantShape stored ci then\n"
            "          unless sameRealizedThmHeader stored ci do\n"
            '            fail s!"stored target declaration differs '
            '{ci.name}"\n'
            "          pendingSourceAlternates :=\n"
            "            pendingSourceAlternates.push (none, stored, ci)"
        ),
        replacement="        let _ := (stored, ci)",
        fixture_id="target_foundation_propext_hijack",
    ),
)

# Direct crate dependencies of `trusted/rustc-capture/Cargo.toml` needed to
# compile isolated single-guard mutants directly with `rustc` against the
# baseline Cargo `deps/` directory.
EXTRACT_DIRECT_DEPS: tuple[str, ...] = (
    "clap",
    "serde",
    "serde_json",
    "sha2",
    "tempfile",
)

EXTRACT_POSITIVE_SANITY_SOURCE: str = (
    "pub fn selected(x: u64) -> u64 {\n"
    "    x + 1\n"
    "}\n"
)

EXTRACT_GUARDS: tuple[ExtractGuard, ...] = (
    # ------------------------------------------------------------------
    # UB-preservation & compiler profile guards (capture.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_profile_require_mir_preserve_ub",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="unit",
        description="validate_profile_options requires -Zmir-preserve-ub",
        anchor=(
            "    if !opts.unstable_opts.mir_preserve_ub {\n"
            '        return Err("-Zmir-preserve-ub must be enabled during capture".into());\n'
            "    }"
        ),
        replacement=(
            "    if false {\n"
            '        return Err("-Zmir-preserve-ub must be enabled during capture".into());\n'
            "    }"
        ),
        unit_test_name=(
            "capture::tests::"
            "compiler_options_gate_requires_mir_preserve_ub_and_matching_crate_type_and_panic"
        ),
    ),
    ExtractGuard(
        guard_id="extract_profile_require_mir_opt_level_zero",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="unit",
        description="validate_profile_options requires -Zmir-opt-level=0",
        anchor="    if opts.unstable_opts.mir_opt_level != Some(0) {",
        replacement="    if false {",
        unit_test_name=(
            "capture::tests::"
            "compiler_options_gate_enforces_opt_level_debug_assertions_and_overflow_checks"
        ),
    ),
    ExtractGuard(
        guard_id="extract_profile_require_overflow_checks_no",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="unit",
        description=(
            "validate_profile_options enforces -Coverflow-checks matching "
            "expected_overflow_checks"
        ),
        anchor="    if opts.cg.overflow_checks != Some(expected_overflow_checks) {",
        replacement="    if false {",
        unit_test_name=(
            "capture::tests::"
            "compiler_options_gate_enforces_opt_level_debug_assertions_and_overflow_checks"
        ),
    ),
    ExtractGuard(
        guard_id="extract_profile_require_debug_assertions_no",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="unit",
        description="validate_profile_options requires -Cdebug-assertions=no",
        anchor=(
            "    if opts.debug_assertions {\n"
            '        return Err("-Cdebug-assertions=no is required during capture".into());\n'
            "    }"
        ),
        replacement=(
            "    if false {\n"
            '        return Err("-Cdebug-assertions=no is required during capture".into());\n'
            "    }"
        ),
        unit_test_name=(
            "capture::tests::"
            "compiler_options_gate_enforces_opt_level_debug_assertions_and_overflow_checks"
        ),
    ),
    ExtractGuard(
        guard_id="extract_profile_require_64bit_pointers",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="unit",
        description="checked_target_profile requires 64-bit pointer width",
        anchor=(
            "    match endian {\n"
            '        Endian::Little if pointer_bits == 64 => Ok((pointer_bits, "little")),\n'
            "        Endian::Little | Endian::Big => {\n"
            '            Err(Failure::unsupported('
            '"only 64-bit little-endian targets are modeled"))\n'
            "        }\n"
            "    }"
        ),
        replacement=(
            "    match endian {\n"
            '        Endian::Little => Ok((pointer_bits, "little")),\n'
            "        Endian::Big => {\n"
            '            Err(Failure::unsupported('
            '"only 64-bit little-endian targets are modeled"))\n'
            "        }\n"
            "    }"
        ),
        unit_test_name=(
            "capture::tests::target_profile_gate_requires_64_bit_little_endian"
        ),
    ),
    ExtractGuard(
        guard_id="extract_profile_require_little_endian",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="unit",
        description="checked_target_profile requires little-endian target",
        anchor=(
            "    match endian {\n"
            '        Endian::Little if pointer_bits == 64 => Ok((pointer_bits, "little")),\n'
            "        Endian::Little | Endian::Big => {\n"
            '            Err(Failure::unsupported('
            '"only 64-bit little-endian targets are modeled"))\n'
            "        }\n"
            "    }"
        ),
        replacement=(
            "    match endian {\n"
            '        Endian::Little | Endian::Big if pointer_bits == 64 => '
            'Ok((pointer_bits, "little")),\n'
            "        Endian::Little | Endian::Big => {\n"
            '            Err(Failure::unsupported('
            '"only 64-bit little-endian targets are modeled"))\n'
            "        }\n"
            "    }"
        ),
        unit_test_name=(
            "capture::tests::target_profile_gate_requires_64_bit_little_endian"
        ),
    ),
    # ------------------------------------------------------------------
    # Alignment, layout & codegen attribute guards (extract.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_reject_fn_alignment",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[rustc_align] function alignment",
        anchor=(
            "    if let Some(align) = alignment {\n"
            '        return Err(format!("function alignment {align:?} is unsupported"));\n'
            "    }"
        ),
        replacement="    let _ = alignment;",
        negative_source=(
            "#![feature(fn_align)]\n"
            "#[rustc_align(64)]\n"
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        allow_unstable_features=("fn_align",),
        expected_baseline_diagnostic="function alignment",
    ),
    ExtractGuard(
        guard_id="extract_reject_target_feature",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[target_feature] entry obligations",
        anchor=(
            "    if !target_features.is_empty() || *safe_target_features {\n"
            '        return Err("target-feature entry obligations are unsupported".into());\n'
            "    }"
        ),
        replacement="    let _ = (target_features, safe_target_features);",
        negative_source=(
            '#[cfg(not(target_arch = "x86_64"))]\n'
            'compile_error!(\n'
            '    "extract_reject_target_feature fixture requires x86_64"\n'
            ');\n'
            '#[cfg_attr(target_arch = "x86_64", '
            'target_feature(enable = "avx2"))]\n'
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        expected_baseline_diagnostic="target-feature entry obligations are unsupported",
    ),
    ExtractGuard(
        guard_id="extract_reject_linkage_attr",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[linkage] attributes",
        anchor=(
            "    if let Some(linkage) = linkage.or(*import_linkage) {\n"
            "        return Err(format!(\n"
            '            "linkage attribute {linkage:?} is unsupported: '
            'calls need not execute the captured body"\n'
            "        ));\n"
            "    }"
        ),
        replacement="    let _ = (linkage, import_linkage);",
        negative_source=(
            "#![feature(linkage)]\n"
            '#[linkage = "weak"]\n'
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        allow_unstable_features=("linkage",),
        expected_baseline_diagnostic="linkage attribute",
    ),
    ExtractGuard(
        guard_id="extract_reject_export_name",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[unsafe(export_name)] symbols",
        anchor=(
            "    if let Some(name) = symbol_name {\n"
            "        return Err(format!(\n"
            '            "exported symbol name `{name}` is unsupported: '
            'symbol obligations are unmodeled"\n'
            "        ));\n"
            "    }"
        ),
        replacement="    let _ = symbol_name;",
        negative_source=(
            '#[unsafe(export_name = "anneal_custom_sym")]\n'
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        expected_baseline_diagnostic="exported symbol name",
    ),
    ExtractGuard(
        guard_id="extract_reject_link_section",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[unsafe(link_section)] attributes",
        anchor=(
            "    if let Some(section) = link_section {\n"
            "        return Err(format!(\n"
            '            "link section `{section}` is unsupported: '
            'section obligations are unmodeled"\n'
            "        ));\n"
            "    }"
        ),
        replacement="    let _ = link_section;",
        negative_source=(
            '#[unsafe(link_section = ".text.anneal_mut")]\n'
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        expected_baseline_diagnostic="link section",
    ),
    ExtractGuard(
        guard_id="extract_reject_no_mangle_flag",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects unmodeled flags such as NO_MANGLE",
        anchor=(
            "    let unmodeled = flags.difference(allowed_flags);\n"
            "    if !unmodeled.is_empty() {\n"
            "        return Err(format!(\n"
            '            "codegen attribute flags {unmodeled:?} are unsupported"\n'
            "        ));\n"
            "    }"
        ),
        replacement="    let _ = (flags, allowed_flags);",
        negative_source=(
            "#[unsafe(no_mangle)]\n"
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        expected_baseline_diagnostic="codegen attribute flags",
    ),
    ExtractGuard(
        guard_id="extract_reject_force_inline",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[rustc_force_inline]",
        anchor=(
            "        InlineAttr::Force { .. } => {\n"
            '            return Err("forced inlining is unsupported".into());\n'
            "        }"
        ),
        replacement="        InlineAttr::Force { .. } => {}",
        negative_source=(
            "#![feature(no_core, lang_items, rustc_attrs)]\n"
            "#![allow(internal_features)]\n"
            "#![no_core]\n"
            '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
            '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
            '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
            '#[lang = "copy"] pub trait Copy {}\n'
            "impl Copy for u64 {}\n"
            "#[rustc_force_inline]\n"
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        stdlib_crate="core",
        expected_baseline_diagnostic="forced inlining is unsupported",
    ),
    ExtractGuard(
        guard_id="extract_reject_sanitizer_override",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[sanitize(...)] overrides",
        anchor=(
            "    if *sanitizers != SanitizerFnAttrs::default() {\n"
            '        return Err(format!("sanitizer settings {sanitizers:?} are unsupported"));\n'
            "    }"
        ),
        replacement="    let _ = sanitizers;",
        negative_source=(
            "#![feature(sanitize)]\n"
            '#[sanitize(address = "off")]\n'
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        allow_unstable_features=("sanitize",),
        expected_baseline_diagnostic="sanitizer settings",
    ),
    ExtractGuard(
        guard_id="extract_reject_patchable_function_entry",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="codegen_attrs rejects #[patchable_function_entry] nops",
        anchor=(
            "    if patchable_function_entry.is_some() {\n"
            '        return Err("patchable function entries are unsupported".into());\n'
            "    }"
        ),
        replacement="    let _ = patchable_function_entry;",
        negative_source=(
            "#![feature(patchable_function_entry)]\n"
            "#[patchable_function_entry(prefix_nops = 1, entry_nops = 1)]\n"
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        allow_unstable_features=("patchable_function_entry",),
        expected_baseline_diagnostic="patchable function entries are unsupported",
    ),
    # ------------------------------------------------------------------
    # Type, enum & discriminant guards (extract.rs, ir.rs, capture.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_ir_reject_overflow_pair_pointee",
        target_file="trusted/rustc-capture/src/ir.rs",
        mode="capture",
        description=(
            "ir::is_supported_v2_data rejects overflow pairs"
        ),
        anchor=(
            "    pub fn is_supported_v2_data(&self) -> bool {\n"
            "        match self {\n"
            "            Self::Array { elem, .. } => elem.is_supported_v2_data(),\n"
            "            Self::OverflowPair(_) => false,"
        ),
        replacement=(
            "    pub fn is_supported_v2_data(&self) -> bool {\n"
            "        match self {\n"
            "            Self::Array { elem, .. } => elem.is_supported_v2_data(),\n"
            "            Self::OverflowPair(_) => true,"
        ),
        negative_source="pub fn selected(_p: &(u8, bool)) -> u64 { 0 }\n",
        expected_baseline_diagnostic="outside the Profile v2 type fragment",
    ),
    ExtractGuard(
        guard_id="extract_reject_enum_with_payload",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="extract::ty rejects enums whose variants carry fields",
        anchor=(
            "            if adt\n"
            "                .variants()\n"
            "                .iter()\n"
            "                .any(|variant| !variant.fields.is_empty())\n"
            "            {\n"
            '                return Err(format!("enum payloads are unsupported: {t:?}"));\n'
            "            }"
        ),
        replacement="            let _ = adt.variants();",
        negative_source=(
            "pub enum Z {\n"
            "    A(()),\n"
            "    B(()),\n"
            "}\n"
            "pub fn selected(x: Z) -> Z { x }\n"
        ),
        expected_baseline_diagnostic="enum payloads are unsupported",
    ),
    ExtractGuard(
        guard_id="extract_reject_enum_id_collision",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="capture",
        description="check_admitted_enum_collisions rejects duplicate local enum keys",
        anchor=(
            "        if defs.len() > 1 {\n"
            "            return Err(Failure::unsupported(format!(\n"
            '                "enum identity collision: {} and {} share id {id}",\n'
            "                tcx.def_path_str(defs[0]),\n"
            "                tcx.def_path_str(defs[1]),\n"
            "            )));\n"
            "        }"
        ),
        replacement="        let _ = (tcx, defs);",
        negative_source=(
            "pub fn outer() {\n"
            "    {\n"
            "        pub enum E { A, B }\n"
            "        pub fn selected(x: E) -> u8 {\n"
            "            match x { E::A => 0, E::B => 1 }\n"
            "        }\n"
            "    }\n"
            "    { enum E { C, D } }\n"
            "}\n"
        ),
        select_root="outer::selected",
        expected_baseline_diagnostic="enum identity collision",
    ),
    ExtractGuard(
        guard_id="extract_ir_reject_invalid_enum_const_tag",
        target_file="trusted/rustc-capture/src/ir.rs",
        mode="unit",
        description="ir::validate_constant rejects enum tag not matching any variant",
        anchor=(
            "                if !ety.discriminants.contains(&discr) {\n"
            "                    return Err(format!(\n"
            '                        "enum tag constant {bits:#x} '
            'does not match any declared variant"\n'
            "                    ));\n"
            "                }"
        ),
        replacement="                let _ = discr;",
        unit_test_name=(
            "extract::tests::"
            "body_constructor_rejects_storage_dead_return_place_and_invalid_constants"
        ),
    ),
    ExtractGuard(
        guard_id="extract_ir_reject_enum_tag_width_overflow",
        target_file="trusted/rustc-capture/src/ir.rs",
        mode="unit",
        description="ir::validate_constant rejects enum tag exceeding tag width",
        anchor=(
            "                if *bits > tag.width.mask() {\n"
            "                    return Err(format!(\n"
            '                        "enum tag constant {bits:#x} '
            'exceeds {}-bit tag width",\n'
            "                        tag.width.bits()\n"
            "                    ));\n"
            "                }"
        ),
        replacement="                let _ = tag.width.mask();",
        unit_test_name=(
            "extract::tests::"
            "body_constructor_rejects_storage_dead_return_place_and_invalid_constants"
        ),
    ),
    # ------------------------------------------------------------------
    # PlaceMention & retag guards (extract.rs, ir.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_reject_place_mention_projection",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="statement() rejects PlaceMention with place projections",
        anchor=(
            "        mir::StatementKind::PlaceMention(place) => {\n"
            "            if !place.projection.is_empty() {\n"
            "                return Err(format!(\n"
            '                    "PlaceMention with projections is unsupported: {place:?}"\n'
            "                ));\n"
            "            }"
        ),
        replacement="        mir::StatementKind::PlaceMention(place) => {",
        negative_source=(
            "pub unsafe fn selected(p: *const u8) {\n"
            "    unsafe { let _ = *p; }\n"
            "}\n"
        ),
        expected_baseline_diagnostic="PlaceMention with projections is unsupported",
    ),
    ExtractGuard(
        guard_id="extract_ir_reject_place_mention_unsized",
        target_file="trusted/rustc-capture/src/ir.rs",
        mode="unit",
        description="ir::admit_place_mention rejects unsized PlaceMention locals",
        anchor=(
            "fn admit_place_mention(is_sized: bool) -> Result<(), String> {\n"
            "    if !is_sized {\n"
            '        return Err("PlaceMention on unsized locals is unsupported".into());\n'
            "    }\n"
            "    Ok(())\n"
            "}"
        ),
        replacement=(
            "fn admit_place_mention(_is_sized: bool) -> Result<(), String> {\n"
            "    Ok(())\n"
            "}"
        ),
        unit_test_name=(
            "ir::tests::place_mention_guard_checks_local_bounds_and_sizedness"
        ),
    ),
    ExtractGuard(
        guard_id="extract_ir_reject_effective_retag",
        target_file="trusted/rustc-capture/src/ir.rs",
        mode="unit",
        description="ir::admit_retag rejects erasing WithRetag::Yes on non-noop types",
        anchor=(
            "fn admit_retag(retag_noop: bool, with_retag: bool) -> Result<(), String> {\n"
            "    if with_retag && !retag_noop {\n"
            '        return Err("retagging Use rvalues on reference-bearing types '
            'are unsupported".into());\n'
            "    }\n"
            "    Ok(())\n"
            "}"
        ),
        replacement=(
            "fn admit_retag(_retag_noop: bool, _with_retag: bool) -> Result<(), String> {\n"
            "    Ok(())\n"
            "}"
        ),
        unit_test_name=(
            "ir::tests::retag_guard_refuses_erasing_an_effective_retag"
        ),
    ),
    # ------------------------------------------------------------------
    # Rodata indirect-constant allocation guards (extract.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_rodata_reject_big_endian",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="unit",
        description="read_rodata_scalar_from_alloc rejects non-little-endian layouts",
        anchor=(
            "    width: u32,\n"
            ") -> Result<u128> {\n"
            "    if cx.data_layout().endian != Endian::Little {\n"
            '        return Err("non-little-endian global allocation constants '
            'are unsupported".into());\n'
            "    }"
        ),
        replacement=(
            "    width: u32,\n"
            ") -> Result<u128> {\n"
            "    let _ = cx.data_layout().endian;"
        ),
        unit_test_name=(
            "extract::tests::"
            "rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance"
        ),
    ),
    ExtractGuard(
        guard_id="extract_rodata_reject_mutable_alloc",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="unit",
        description="read_rodata_scalar_from_alloc rejects mutable allocations",
        anchor=(
            "    if alloc.mutability != Mutability::Not {\n"
            '        return Err("mutable global allocations are unsupported '
            'in constants".into());\n'
            "    }\n"
            "    let byte_len = u64::from(width / 8);"
        ),
        replacement=(
            "    let _ = alloc.mutability;\n"
            "    let byte_len = u64::from(width / 8);"
        ),
        unit_test_name=(
            "extract::tests::"
            "rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance"
        ),
    ),
    ExtractGuard(
        guard_id="extract_rodata_reject_oob_range",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="unit",
        description="read_rodata_scalar_from_alloc rejects out-of-bounds ranges",
        anchor=(
            "    if end > alloc.size().bytes() {\n"
            "        return Err(format!(\n"
            '            "global allocation constant range [{}..{end}) '
            'exceeds allocation size {}",\n'
            "            offset.bytes(),\n"
            "            alloc.size().bytes()\n"
            "        ));\n"
            "    }"
        ),
        replacement="    let _ = end;",
        unit_test_name=(
            "extract::tests::"
            "rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance"
        ),
    ),
    ExtractGuard(
        guard_id="extract_rodata_reject_provenance",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="unit",
        description="read_rodata_scalar_from_alloc rejects provenance-bearing ranges",
        anchor=(
            "    if !alloc.provenance().range_empty(range, cx) {\n"
            '        return Err("provenance-bearing global allocation constants '
            'are unsupported".into());\n'
            "    }\n"
            "    let scalar = alloc"
        ),
        replacement=(
            "    let _ = alloc.provenance().range_empty(range, cx);\n"
            "    let scalar = alloc"
        ),
        unit_test_name=(
            "extract::tests::"
            "rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance"
        ),
    ),
    # ------------------------------------------------------------------
    # Unwind / cleanup-block guard (extract.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_reject_cleanup_block",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="body_inner cleanup-block refusal (diagnostic-precedence pin)",
        anchor=(
            "    if let Some((id, _)) = body\n"
            "        .basic_blocks\n"
            "        .iter_enumerated()\n"
            "        .find(|(_, block)| block.is_cleanup)\n"
            "    {\n"
            '        return Err(format!("cleanup block {id:?} is unsupported"));\n'
            "    }"
        ),
        replacement="    let _ = &body.basic_blocks;",
        negative_source=(
            "pub struct Guard;\n"
            "impl Drop for Guard {\n"
            "    fn drop(&mut self) {}\n"
            "}\n"
            "pub fn callee() {}\n"
            "pub fn selected() {\n"
            "    let _guard = Guard;\n"
            "    callee();\n"
            "}\n"
        ),
        expected_baseline_diagnostic="cleanup block bb",
        expected_fallback_diagnostic="unsupported type: Guard",
        allow_downstream_fallback=True,
    ),
    # ------------------------------------------------------------------
    # Statement, call-source, terminator, operator & cast guards (extract.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_reject_statement_intrinsic_assume",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="statement() default-deny refuses StatementKind::Intrinsic(Assume)",
        anchor='        other => return Err(format!("unsupported statement: {other:?}")),',
        replacement=(
            "        mir::StatementKind::Intrinsic(_) => ir::Statement::Nop,\n"
            '        other => return Err(format!("unsupported statement: {other:?}")),'
        ),
        negative_source=(
            "#![feature(no_core, lang_items, intrinsics)]\n"
            "#![allow(internal_features)]\n"
            "#![no_core]\n"
            '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
            '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
            '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
            '#[lang = "copy"] pub trait Copy {}\n'
            "impl Copy for bool {}\n"
            "#[rustc_intrinsic]\n"
            "pub unsafe fn assume(b: bool);\n"
            "pub unsafe fn selected(b: bool) -> u8 {\n"
            "    unsafe { assume(b) };\n"
            "    0\n"
            "}\n"
        ),
        stdlib_crate="core",
        expected_baseline_diagnostic="unsupported statement",
    ),
    ExtractGuard(
        guard_id="extract_reject_call_source_use",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="unit",
        description="check_call_source rejects CallSource::Use terminators",
        anchor=(
            "        mir::CallSource::Use => Err(\n"
            '            "CallSource::Use call terminators are unsupported: post-capture \\\n'
            "             optimize_use_clone may rewrite Clone::clone to a bitwise copy \\\n"
            '             for Copy types, diverging from captured MIR"\n'
            "                .into(),\n"
            "        ),"
        ),
        replacement="        mir::CallSource::Use => Ok(()),",
        unit_test_name=(
            "extract::tests::"
            "call_source_use_fails_closed_while_other_call_sources_pass_guard"
        ),
    ),
    ExtractGuard(
        guard_id="extract_reject_returning_call",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description=(
            "terminator() validates returning Call terminators instead of "
            "short-circuiting them to Unsupported"
        ),
        anchor=(
            "            let Some(target_bb) = target else {\n"
            "                if admit_core_panicking_abort(tcx)"
        ),
        replacement=(
            "            let Some(target_bb) = target.as_ref().filter(|_| false) else {\n"
            "                if admit_core_panicking_abort(tcx)"
        ),
        negative_source=(
            "fn helper<T>(x: T) -> T { x }\n"
            "pub fn selected(x: u32) -> u32 { helper(x) }\n"
        ),
        expected_baseline_diagnostic="calls to generic or monomorphized functions",
    ),
    ExtractGuard(
        guard_id="extract_reject_terminator_inline_asm",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="terminator() default-deny refuses TerminatorKind::InlineAsm",
        anchor='        other => return Err(format!("unsupported terminator: {other:?}")),',
        replacement=(
            "        mir::TerminatorKind::InlineAsm { targets, .. } => "
            "RawTerminator::Resolved(ir::Terminator::Goto {\n"
            "            block: targets[0].as_u32(),\n"
            "        }),\n"
            '        other => return Err(format!("unsupported terminator: {other:?}")),'
        ),
        negative_source=(
            "pub unsafe fn selected() {\n"
            '    unsafe { core::arch::asm!("nop", options(nomem, nostack)) };\n'
            "}\n"
        ),
        expected_baseline_diagnostic="unsupported terminator",
    ),
    ExtractGuard(
        guard_id="extract_reject_unchecked_binop",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="bin_op() rejects unchecked shift operators (ShlUnchecked)",
        anchor='        other => return Err(format!("unsupported binary operator: {other:?}")),',
        replacement=(
            "        mir::BinOp::ShlUnchecked => ir::BinOp::Shl,\n"
            '        other => return Err(format!("unsupported binary operator: {other:?}")),'
        ),
        negative_source=(
            "#![feature(no_core, lang_items, intrinsics)]\n"
            "#![allow(internal_features)]\n"
            "#![no_core]\n"
            '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
            '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
            '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
            '#[lang = "copy"] pub trait Copy {}\n'
            "impl Copy for u32 {}\n"
            "#[rustc_intrinsic]\n"
            "pub unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T;\n"
            "pub unsafe fn selected(a: u32, b: u32) -> u32 {\n"
            "    unsafe { unchecked_shl(a, b) }\n"
            "}\n"
        ),
        stdlib_crate="core",
        expected_baseline_diagnostic="unsupported binary operator: ShlUnchecked",
    ),
    ExtractGuard(
        guard_id="extract_reject_transmute_cast",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="cast_kind() rejects CastKind::Transmute",
        anchor=(
            "        | mir::CastKind::Transmute\n"
            '        | mir::CastKind::Subtype => Err(format!("unsupported cast kind: {kind:?}")),'
        ),
        replacement=(
            '        | mir::CastKind::Subtype => Err(format!("unsupported cast kind: {kind:?}")),\n'
            "        mir::CastKind::Transmute => Ok(ir::CastKind::IntToInt),"
        ),
        negative_source=(
            "pub fn selected(x: u32) -> i32 {\n"
            "    unsafe { core::mem::transmute(x) }\n"
            "}\n"
        ),
        expected_baseline_diagnostic="unsupported cast kind: Transmute",
    ),
    ExtractGuard(
        guard_id="extract_reject_expose_provenance_cast",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="unit",
        description="cast_kind() rejects CastKind::PointerExposeProvenance",
        anchor=(
            "        mir::CastKind::PointerExposeProvenance\n"
            "        | mir::CastKind::PointerCoercion(..)"
        ),
        replacement=(
            "        mir::CastKind::PointerExposeProvenance => "
            "Ok(ir::CastKind::IntToInt),\n"
            "        mir::CastKind::PointerCoercion(..)"
        ),
        unit_test_name=(
            "extract::tests::"
            "operator_and_cast_extractors_admit_modeled_variants_and_refuse_others"
        ),
    ),
    # ------------------------------------------------------------------
    # Intrinsic fallback, ABI, generics & required-const guards (extract.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_reject_intrinsic_fallback",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="body_inner rejects #[rustc_intrinsic] fallback bodies",
        anchor=(
            "    if let Some(intrinsic) = tcx.intrinsic(def) {\n"
            "        return Err(format!(\n"
            '            "intrinsic `{}` is unsupported: '
            'calls need not execute its fallback body",\n'
            "            intrinsic.name\n"
            "        ));\n"
            "    }"
        ),
        replacement="    let _ = tcx.intrinsic(def);",
        negative_source=(
            "#![feature(no_core, lang_items, intrinsics)]\n"
            "#![allow(internal_features)]\n"
            "#![no_core]\n"
            '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
            '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
            '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
            "#[rustc_intrinsic]\n"
            "pub unsafe fn unreachable() -> ! {\n"
            "    loop {}\n"
            "}\n"
        ),
        stdlib_crate="core",
        select_root="unreachable",
        expected_baseline_diagnostic="intrinsic `unreachable` is unsupported",
    ),
    ExtractGuard(
        guard_id="extract_reject_uninstantiated_generic_fn",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description=(
            "body_inner type-generic refusal (diagnostic-precedence pin ahead "
            "of predicates_of PointeeSized check)"
        ),
        anchor=(
            "                    if !matches!(param.kind, ty::GenericParamDefKind::Lifetime) {\n"
            "                        return Err(\n"
            '                            "generic functions require quantified instantiation obligations".into(),\n'
            "                        );\n"
            "                    }"
        ),
        replacement="                    let _ = &param.kind;",
        negative_source="pub fn selected<T: ?Sized>(x: u64) -> u64 { x }\n",
        expected_baseline_diagnostic="generic functions require quantified",
        expected_fallback_diagnostic=(
            "functions with generic or lifetime bounds are unsupported"
        ),
        allow_downstream_fallback=True,
    ),
    ExtractGuard(
        guard_id="extract_reject_non_rust_abi",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="body_inner rejects non-Rust ABI functions (extern \"C\")",
        anchor=(
            "    if signature.abi() != ExternAbi::Rust || signature.c_variadic() {\n"
            '        return Err("only non-variadic Rust ABI functions are admitted".into());\n'
            "    }"
        ),
        replacement=(
            "    if signature.c_variadic() {\n"
            '        return Err("only non-variadic Rust ABI functions are admitted".into());\n'
            "    }"
        ),
        negative_source='pub extern "C" fn selected(x: u64) -> u64 { x }\n',
        expected_baseline_diagnostic="only non-variadic Rust ABI functions are admitted",
    ),
    ExtractGuard(
        guard_id="extract_eval_required_consts",
        target_file="trusted/rustc-capture/src/extract.rs",
        mode="capture",
        description="body_inner evaluates required_consts (diagnostic-precedence pin)",
        anchor="    eval_required_consts(tcx, typing_env, body)?;",
        replacement="    let _ = (tcx, typing_env, body);",
        negative_source=(
            "pub fn pme<T>() -> usize {\n"
            "    if false {\n"
            "        let _ = const { assert!(core::mem::size_of::<T>() > 0); 0f32 };\n"
            "    }\n"
            "    2\n"
            "}\n"
        ),
        capture_scope="instantiate",
        instantiate_json='{"path":"pme","args":["()"]}',
        expected_baseline_status="compiler_failed",
        expected_baseline_diagnostic="E0080",
        expected_fallback_diagnostic="unsupported type:",
        allow_downstream_fallback=True,
    ),
    # ------------------------------------------------------------------
    # Monomorphization & crate-level admission guards (mono.rs, capture.rs)
    # ------------------------------------------------------------------
    ExtractGuard(
        guard_id="extract_mono_verify_predicates_and_wf",
        target_file="trusted/rustc-capture/src/mono.rs",
        mode="capture",
        description="mono::instantiate_body enforces trait and WF predicates",
        anchor='    verify_predicates_and_wf(tcx, typing_env, target_def, args, "target")?;',
        replacement=(
            "    let _ = verify_predicates_and_wf("
            'tcx, typing_env, target_def, args, "target");'
        ),
        negative_source=(
            "pub trait Marker {}\n"
            "pub fn f<T: Marker>(x: u64) -> u64 { x }\n"
        ),
        capture_scope="instantiate",
        instantiate_json='{"path":"f","args":["bool"]}',
        expected_baseline_diagnostic="trait or well-formedness predicates unsatisfied",
    ),
    ExtractGuard(
        guard_id="extract_reject_cfg_attr_rustc_private",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="capture",
        description="validate_crate_root_meta recurses into #![cfg_attr] items",
        anchor=(
            "    if last_ident == Some(sym::cfg_attr)\n"
            "        && let Some(items) = meta.meta_item_list()\n"
            "    {\n"
            "        for item in items.iter().skip(1) {\n"
            "            if let MetaItemInner::MetaItem(nested) = item {\n"
            "                validate_crate_root_meta(nested, expected, false)?;\n"
            "            }\n"
            "        }\n"
            "    }"
        ),
        replacement="    let _ = (last_ident, meta);",
        negative_source=(
            "#![cfg_attr(any(), feature(rustc_private))]\n"
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        expected_baseline_diagnostic="#![feature(rustc_private)]",
    ),
    ExtractGuard(
        guard_id="extract_reject_rustc_private_feature",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="capture",
        description=(
            "validate_crate_root_meta rejects feature(rustc_private) even "
            "behind inactive cfg_attr"
        ),
        anchor=(
            "            if item.has_name(sym::rustc_private) {\n"
            '                return Err("#![feature(rustc_private)] is '
            'unsupported during capture".into());\n'
            "            }"
        ),
        replacement="            let _ = item;",
        negative_source=(
            "#![cfg_attr(any(), feature(rustc_private))]\n"
            "pub fn selected(x: u64) -> u64 { x }\n"
        ),
        expected_baseline_diagnostic="#![feature(rustc_private)]",
    ),
    ExtractGuard(
        guard_id="extract_crate_reject_unsafe_trait",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="capture",
        description="admit_safe_trait rejects unsafe trait declarations in crate scope",
        anchor=(
            "    if *safety != hir::Safety::Safe {\n"
            '        return Err("whole-crate obligation is unsupported: '
            'Trait (unsafe trait)".into());\n'
            "    }"
        ),
        replacement="    let _ = safety;",
        negative_source=(
            "pub unsafe trait Bad { fn f(); }\n"
            "pub fn ok() -> u8 { 0 }\n"
        ),
        capture_scope="crate",
        expected_baseline_diagnostic="Trait (unsafe trait)",
    ),
    ExtractGuard(
        guard_id="extract_crate_reject_unsafe_impl",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="capture",
        description="admit_safe_impl rejects user unsafe impl blocks in crate scope",
        anchor=(
            "            if !is_builtin_trivial_clone {\n"
            "                return Err(\n"
            '                    "whole-crate obligation is unsupported: '
            'Impl { of_trait: true } (unsafe impl)"\n'
            "                        .into(),\n"
            "                );\n"
            "            }"
        ),
        replacement="            let _ = is_builtin_trivial_clone;",
        negative_source=(
            "pub enum E { A }\n"
            "unsafe impl Send for E {}\n"
            "pub fn ok() -> u8 { 0 }\n"
        ),
        capture_scope="crate",
        expected_baseline_diagnostic="Impl { of_trait: true } (unsafe impl)",
    ),
    ExtractGuard(
        guard_id="extract_crate_reject_unsafe_const",
        target_file="trusted/rustc-capture/src/capture.rs",
        mode="capture",
        description="admit_const_item rejects unsafe blocks in const items",
        anchor="    check_const_hir_safety(tcx, def, false, &context)?;",
        replacement="    let _ = check_const_hir_safety(tcx, def, false, &context);",
        negative_source=(
            "pub const X: u8 = unsafe { 1 };\n"
            "pub fn ok() -> u8 { X }\n"
        ),
        capture_scope="crate",
        expected_baseline_diagnostic="unsafe blocks are unsupported in constants",
    ),
)


def apply_single_guard_mutation(
    source_text: str,
    anchor: str,
    replacement: str,
    *,
    guard_id: str,
) -> str:
    """Replace `anchor` with `replacement`, requiring exactly one occurrence.

    Requiring a unique match ensures that refactoring a guarded expression in
    the TCB fails loudly rather than silently skipping the mutation or editing
    the wrong branch.
    """
    occurrences = source_text.count(anchor)
    if occurrences != 1:
        raise ValueError(
            f"guard {guard_id!r}: expected anchor to match exactly once, "
            f"found {occurrences} occurrences"
        )
    if anchor == replacement:
        raise ValueError(
            f"guard {guard_id!r}: replacement must differ from anchor"
        )
    return source_text.replace(anchor, replacement, 1)


def find_theorem_line_span(
    fixture_text: str,
    theorem_name: str,
) -> tuple[int, int]:
    """Return the inclusive 1-based `(start, end)` line span of `theorem_name`.

    Used to confirm that a Lean proof failure on a mutated semantics actually
    originated inside the guard's dedicated refutation theorem rather than in
    an unrelated declaration or file header.
    """
    lines = fixture_text.splitlines()
    decl_re = re.compile(
        r"^(?:theorem|lemma|def|noncomputable\s+def|example|instance|"
        r"abbrev|structure|inductive|class|opaque|end)\b|^@\["
    )
    target_re = re.compile(rf"^theorem\s+{re.escape(theorem_name)}\b")
    start: int | None = None
    for idx, line in enumerate(lines, start=1):
        if start is None:
            if target_re.match(line):
                start = idx
        elif decl_re.match(line):
            return (start, idx - 1)
    if start is None:
        raise ValueError(
            f"theorem {theorem_name!r} not found in fixture source"
        )
    return (start, len(lines))


def classify_refutation_failure(
    returncode: int,
    combined_output: str,
    fixture_filename: str,
    theorem_span: tuple[int, int],
) -> tuple[str, str]:
    """Classify Lean output on a mutated refutation fixture.

    Returns `(status, detail)` where `status` is:
    - `SURVIVED`: Lean accepted (`rc == 0`) the negative refutation even after
      the guard was disabled.
    - `KILLED`: Lean rejected (`rc == 1`) with a genuine proof/type failure
      localized inside the target theorem's line span and with no crash/parse
      markers.
    - `ERROR`: Unexpected exit status, crash/parse/timeout marker, or error
      outside the target theorem span (never counted as a kill).
    """
    if returncode == 0:
        return ("SURVIVED", "refutation theorem still compiled on mutant")
    if returncode != 1:
        return (
            "ERROR",
            f"unexpected Lean exit code {returncode} (expected 1 on proof failure)",
        )
    for marker in NON_KILL_ERROR_MARKERS:
        if marker in combined_output:
            return (
                "ERROR",
                f"non-proof failure marker {marker!r} in Lean output",
            )
    if not any(m in combined_output for m in EXPECTED_PROOF_FAILURE_MARKERS):
        return (
            "ERROR",
            "Lean failed without a recognized proof/type mismatch diagnostic",
        )

    # Extract `<path>:<line>:<col>: error:` diagnostics belonging to the
    # fixture file and confirm at least one lies inside `theorem_span`.
    diag_re = re.compile(
        rf"{re.escape(fixture_filename)}:(\d+):\d+:\s*error:",
        re.MULTILINE,
    )
    error_lines = [int(m.group(1)) for m in diag_re.finditer(combined_output)]
    start, end = theorem_span
    matching = [ln for ln in error_lines if start <= ln <= end]
    if not matching:
        return (
            "ERROR",
            f"no error diagnostic in target theorem lines {start}-{end} "
            f"(saw error lines: {error_lines})",
        )
    return (
        "KILLED",
        f"proof failed inside target theorem at line(s) {matching}",
    )


def _lean_subprocess_env(
    lean_path: list[Path] | None = None,
) -> dict[str, str]:
    """Build a cleared allowlisted environment for child `lean` processes."""
    env: dict[str, str] = {}
    for key in ("HOME", "TMPDIR", "LANG", "LC_ALL"):
        if key in os.environ:
            env[key] = os.environ[key]
    env["PATH"] = os.environ.get("PATH", "/usr/bin:/bin")
    if lean_path is not None:
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in lean_path)
    return env


def _run_lean(
    lean_bin: Path,
    args: list[str],
    *,
    lean_path: list[Path],
    timeout_sec: int,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(lean_bin), *args],
        env=_lean_subprocess_env(lean_path),
        capture_output=True,
        text=True,
        timeout=timeout_sec,
    )


def _compile_module(
    lean_bin: Path,
    root_dir: Path,
    module: str,
    out_dir: Path,
    *,
    lean_path: list[Path],
    timeout_sec: int,
) -> subprocess.CompletedProcess[str]:
    src = root_dir / f"{module}.lean"
    olean = out_dir / f"{module}.olean"
    olean.parent.mkdir(parents=True, exist_ok=True)
    return _run_lean(
        lean_bin,
        ["-R", str(root_dir), "-o", str(olean), str(src)],
        lean_path=lean_path,
        timeout_sec=timeout_sec,
    )


def _query_lean_sysroot(lean_bin: Path, timeout_sec: int) -> str:
    res = subprocess.run(
        [str(lean_bin), "--print-prefix"],
        env=_lean_subprocess_env(),
        capture_output=True,
        text=True,
        timeout=timeout_sec,
        check=True,
    )
    return res.stdout.strip()


def _run_tb_request(
    lean_bin: Path,
    tb_olean_dir: Path,
    req_payload: dict[str, object],
    work_dir: Path,
    *,
    tag: str,
    module_name: str = "TrustedBoundary",
    timeout_sec: int,
) -> tuple[int, dict[str, object] | None, str]:
    """Invoke precompiled audit module (`TrustedBoundary` or `SpecPreflight`)."""
    req_path = work_dir / f"req_{tag}.json"
    res_path = work_dir / f"res_{tag}.json"
    runner_path = work_dir / f"run_{module_name}.lean"
    req_path.write_text(json.dumps(req_payload), encoding="utf-8")
    if not runner_path.exists():
        runner_path.write_text(f"import {module_name}\n", encoding="utf-8")
    proc = _run_lean(
        lean_bin,
        ["--run", str(runner_path), str(req_path), str(res_path)],
        lean_path=[tb_olean_dir],
        timeout_sec=timeout_sec,
    )
    parsed: dict[str, object] | None = None
    if res_path.is_file():
        try:
            parsed = json.loads(res_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            parsed = None
    return proc.returncode, parsed, (proc.stdout + "\n" + proc.stderr).strip()


def _run_audit_headers(
    lean_bin: Path,
    tb_olean_dir: Path,
    sysroot: str,
    source_text: str,
    work_dir: Path,
    *,
    module_name: str = "TrustedBoundary",
    timeout_sec: int,
) -> tuple[int, dict[str, object] | None, str]:
    """Invoke precompiled `TrustedBoundary` or `SpecPreflight` in `"headers"` mode."""
    target_src = work_dir / "Target.lean"
    target_src.write_text(source_text, encoding="utf-8")
    return _run_tb_request(
        lean_bin,
        tb_olean_dir,
        {
            "mode": "headers",
            "sysroot": sysroot,
            "sources": [["Target", str(target_src)]],
        },
        work_dir,
        tag="headers",
        module_name=module_name,
        timeout_sec=timeout_sec,
    )


def _load_foundation_artifacts(
    anneal_root: Path,
    sysroot: str,
) -> tuple[list[str], dict[str, list[list[str]]]]:
    """Load foundation module names and sysroot artifact paths from lock."""
    lock = json.loads(
        (anneal_root / "trusted/lean/foundation-lock.json").read_text(
            encoding="utf-8"
        )
    )
    lean_lib = Path(sysroot) / "lib/lean"
    foundation_mods = sorted(lock["modules"].keys())
    artifacts: dict[str, list[list[str]]] = {}
    for mod in foundation_mods:
        parts = lock["modules"][mod]["parts"]
        rel = mod.replace(".", "/")
        olean_parts = [
            str(lean_lib / f"{rel}.{ext}")
            for ext in ("olean", "olean.server", "olean.private")
            if parts.get(ext) is not None
        ]
        artifacts[mod] = [olean_parts, []]
    return foundation_mods, artifacts


def _build_boundary_fixtures(
    *,
    anneal_root: Path,
    lean_bin: Path,
    tb_olean_dir: Path,
    sysroot: str,
    fixtures_root: Path,
    timeout_sec: int,
) -> tuple[dict[str, dict[str, object]], dict[str, dict[str, object]]]:
    """Compile minimal baseline and negative boundary fixtures once."""
    foundation_mods, foundation_arts = _load_foundation_artifacts(
        anneal_root, sysroot
    )
    rc, parsed, out = _run_tb_request(
        lean_bin,
        tb_olean_dir,
        {
            "mode": "resolve-imports",
            "sysroot": sysroot,
            "modules": foundation_mods,
        },
        fixtures_root,
        tag="resolve_found",
        timeout_sec=timeout_sec,
    )
    if rc != 0 or not isinstance(parsed, dict) or parsed.get("ok") is not True:
        raise RuntimeError(
            f"resolve-imports failed for foundation: rc={rc} out={out}"
        )
    found_graph = dict(parsed["result"]["graph"])  # type: ignore[index]

    # Pre-Preflight requests
    spec_srcs: dict[str, str] = {
        "spec_sanity": (
            "prelude\nimport Model\n"
            "def Spec.specs (p : Nat) : Prop := p = p\n"
        ),
        "spec_auto_implicit": (
            "prelude\nimport Model\n"
            "set_option autoImplicit true in\n"
            "def Spec.bad (x : y_auto) : Nat := 0\n"
        ),
        "spec_bang_ident": (
            "prelude\nimport Model\n"
            "def Spec.bad (xs : List Nat) : Nat := xs.head!\n"
        ),
        "spec_dbg_trace": (
            "prelude\nimport Model\n"
            'def Spec.bad : Nat := dbgTrace "leak" fun _ => 1\n'
        ),
        "spec_uv_open": (
            "prelude\nimport Model\ndef Spec.specs (p : Nat) : Prop := p = p\n"
            "open Std.Internal.UV\n"
        ),
    }
    spec_reqs: dict[str, dict[str, object]] = {}
    for name, src in spec_srcs.items():
        p = fixtures_root / f"{name}.lean"
        p.write_text(src, encoding="utf-8")
        spec_reqs[name] = {
            "mode": "spec-preflight",
            "sysroot": sysroot,
            "foundation": foundation_mods,
            "libraries": [],
            "artifacts": list(foundation_arts.items()),
            "graph": found_graph,
            "sources": [["Spec", str(p)]],
        }

    # Build minimal Init.Core-only `.olean` target fixtures for target-audit.
    src_dir = fixtures_root / "src"
    olean_dir = fixtures_root / "olean"
    src_dir.mkdir()
    olean_dir.mkdir()

    def compile_target_mod(
        mod: str,
        code: str,
        bucket: str,
        *,
        deps_olean_dirs: list[Path] | None = None,
    ) -> tuple[Path, Path]:
        mod_src_root = src_dir / bucket
        mod_olean_root = olean_dir / bucket
        s_path = mod_src_root / f"{mod}.lean"
        o_path = mod_olean_root / f"{mod}.olean"
        s_path.parent.mkdir(parents=True, exist_ok=True)
        o_path.parent.mkdir(parents=True, exist_ok=True)
        s_path.write_text(code, encoding="utf-8")
        c_res = _compile_module(
            lean_bin,
            mod_src_root,
            mod,
            mod_olean_root,
            lean_path=[*(deps_olean_dirs or []), mod_olean_root],
            timeout_sec=timeout_sec,
        )
        if c_res.returncode != 0:
            raise RuntimeError(
                f"failed to compile {bucket}/{mod}: "
                f"{c_res.stdout}\n{c_res.stderr}"
            )
        return o_path, mod_olean_root

    model_body = (
        "namespace Trusted.MirSemantics\n"
        "structure Crate where\n"
        "  program : Nat\n"
        "  specs : Nat → Prop\n"
        "def UnitTheorem (c : Crate) : Prop :=\n"
        "  c.program = 7 ∧ c.specs c.program\n"
        "end Trusted.MirSemantics\n"
    )
    model_src = "prelude\nimport Init.Core\n" + model_body
    model_dbg_src = (
        "prelude\nimport Init.Core\nimport Init.Util\n"
        + model_body
        + 'def Model.dbgLeak (n : Nat) : Nat := dbgTrace "leak" fun _ => n\n'
    )
    model_olean, base_odir = compile_target_mod("Model", model_src, "base")
    cap_olean, _ = compile_target_mod(
        "Captured",
        "prelude\nimport Model\ndef Captured.program : Nat := 7\n",
        "base",
    )
    spec_ok_src = (
        "prelude\nimport Model\ndef Spec.specs (p : Nat) : Prop := p = 7\n"
    )
    spec_olean, _ = compile_target_mod("Spec", spec_ok_src, "base")
    exp_ok_src = (
        "prelude\nimport Model\nimport Captured\nimport Spec\n"
        "def Expected.claim : Prop :=\n"
        "  Trusted.MirSemantics.UnitTheorem\n"
        "    (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n"
    )
    exp_olean, _ = compile_target_mod("Expected", exp_ok_src, "base")
    proof_ok_olean, _ = compile_target_mod(
        "Proof",
        "prelude\nimport Expected\n"
        "theorem Proof.verify : Expected.claim := And.intro rfl rfl\n",
        "base",
    )

    core_edge = [{"module": "Init.Core", "isExported": True, "importAll": False, "isMeta": False}]
    model_edge = [{"module": "Model", "isExported": True, "importAll": False, "isMeta": False}]
    cap_edge = [{"module": "Captured", "isExported": True, "importAll": False, "isMeta": False}]
    spec_edge = [{"module": "Spec", "isExported": True, "importAll": False, "isMeta": False}]
    exp_edge = [{"module": "Expected", "isExported": True, "importAll": False, "isMeta": False}]
    base_graph = dict(found_graph)
    base_graph.update(
        {
            "Model": core_edge,
            "Captured": model_edge,
            "Spec": model_edge,
            "Expected": model_edge + cap_edge + spec_edge,
            "Proof": exp_edge,
        }
    )

    def make_ta_case(
        case_id: str,
        *,
        mod_oleans: dict[str, Path],
        proof_o: Path,
        allow_sorry: bool = False,
        graph_override: dict[str, object] | None = None,
        libraries: list[str] | None = None,
    ) -> dict[str, object]:
        case_dir = fixtures_root / f"case_{case_id}"
        case_dir.mkdir()
        arts_all = dict(foundation_arts)
        for m, p in mod_oleans.items():
            arts_all[m] = [[str(p)], []]
        export_arts = dict(arts_all)
        export_arts["Proof"] = [[str(proof_o)], []]
        modules_meta = [
            {"module": "Model", "role": "model", "isModule": False},
            {"module": "Captured", "role": "capture", "isModule": False},
            {"module": "Spec", "role": "specification", "isModule": False},
            {"module": "Expected", "role": "expected", "isModule": False},
            {"module": "Proof", "role": "proof", "isModule": False},
        ]
        target_meta: dict[str, object] = {
            "modules": modules_meta,
            "theoremName": "Proof.verify",
            "theoremModule": "Proof",
            "expectedDeclaration": "Expected.claim",
            "expectedModule": "Expected",
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "subjectDeclaration": "Captured.program",
            "specificationDeclaration": "Spec.specs",
            "allowSorryInProof": allow_sorry,
        }
        use_graph = graph_override if graph_override is not None else base_graph
        use_libs = libraries if libraries is not None else []
        export_req = {
            "mode": "target-export",
            "sysroot": sysroot,
            "foundation": foundation_mods,
            "libraries": use_libs,
            "target": target_meta,
            "artifacts": list(export_arts.items()),
            "graph": use_graph,
        }
        e_rc, e_parsed, e_out = _run_tb_request(
            lean_bin,
            tb_olean_dir,
            export_req,
            case_dir,
            tag="export",
            timeout_sec=timeout_sec,
        )
        if e_rc != 0 or not isinstance(e_parsed, dict) or e_parsed.get("ok") is not True:
            raise RuntimeError(
                f"target-export failed for {case_id}: rc={e_rc} out={e_out}"
            )
        export_path = case_dir / "proof_export.json"
        export_path.write_text(
            json.dumps(e_parsed["result"]), encoding="utf-8"
        )
        return {
            "mode": "target-audit",
            "sysroot": sysroot,
            "foundation": foundation_mods,
            "libraries": use_libs,
            "target": target_meta,
            "artifacts": list(arts_all.items()),
            "graph": use_graph,
            "proofExportPath": str(export_path),
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"],
            ],
        }

    target_reqs: dict[str, dict[str, object]] = {
        "target_sanity": make_ta_case(
            "sanity",
            mod_oleans={
                "Model": model_olean,
                "Captured": cap_olean,
                "Spec": spec_olean,
                "Expected": exp_olean,
            },
            proof_o=proof_ok_olean,
        ),
    }

    # Case: target_expected_true (`Expected.claim := True` while Proof proves
    # canonical claim)
    exp_true_o, exp_true_dir = compile_target_mod(
        "Expected",
        "prelude\nimport Model\nimport Captured\nimport Spec\n"
        "def Expected.claim : Prop := True\n",
        "expected_true",
        deps_olean_dirs=[base_odir],
    )
    proof_true_o, _ = compile_target_mod(
        "Proof",
        "prelude\nimport Expected\n"
        "theorem Proof.verify : Trusted.MirSemantics.UnitTheorem\n"
        "    (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs) :=\n"
        "  And.intro rfl rfl\n",
        "expected_true",
        deps_olean_dirs=[exp_true_dir, base_odir],
    )
    target_reqs["target_expected_true"] = make_ta_case(
        "expected_true",
        mod_oleans={
            "Model": model_olean,
            "Captured": cap_olean,
            "Spec": spec_olean,
            "Expected": exp_true_o,
        },
        proof_o=proof_true_o,
    )

    # Case: target_bad_theorem_type (theorem Proof.verify takes `(h : False)`)
    proof_bad_ty_o, _ = compile_target_mod(
        "Proof",
        "prelude\nimport Expected\n"
        "theorem Proof.verify (h : False) : Expected.claim := False.elim h\n",
        "bad_theorem_type",
        deps_olean_dirs=[base_odir],
    )
    target_reqs["target_bad_theorem_type"] = make_ta_case(
        "bad_theorem_type",
        mod_oleans={
            "Model": model_olean,
            "Captured": cap_olean,
            "Spec": spec_olean,
            "Expected": exp_olean,
        },
        proof_o=proof_bad_ty_o,
    )

    # Case: target_proof_sorry (uses `sorry` with `allowSorryInProof = false`)
    proof_sorry_o, _ = compile_target_mod(
        "Proof",
        "prelude\nimport Expected\n"
        "theorem Proof.verify : Expected.claim := And.intro rfl sorry\n",
        "proof_sorry",
        deps_olean_dirs=[base_odir],
    )
    target_reqs["target_proof_sorry"] = make_ta_case(
        "proof_sorry",
        mod_oleans={
            "Model": model_olean,
            "Captured": cap_olean,
            "Spec": spec_olean,
            "Expected": exp_olean,
        },
        proof_o=proof_sorry_o,
        allow_sorry=False,
    )

    # Case: target_impl_by (`@[implemented_by]` inside Proof on logical helper)
    proof_impl_o, _ = compile_target_mod(
        "Proof",
        "prelude\nimport Expected\n"
        "unsafe def Proof.nativeH : Nat := 1\n"
        "@[implemented_by Proof.nativeH] def Proof.logH : Nat := 0\n"
        "theorem Proof.verify : Expected.claim :=\n"
        "  (fun _ : Proof.logH = 0 => And.intro rfl rfl) rfl\n",
        "impl_by",
        deps_olean_dirs=[base_odir],
    )
    target_reqs["target_impl_by"] = make_ta_case(
        "impl_by",
        mod_oleans={
            "Model": model_olean,
            "Captured": cap_olean,
            "Spec": spec_olean,
            "Expected": exp_olean,
        },
        proof_o=proof_impl_o,
    )

    # Case: target_spec_transitive_dbg (Spec calls `Model.dbgLeak`)
    model_dbg_o, dbg_odir = compile_target_mod(
        "Model", model_dbg_src, "spec_transitive_dbg"
    )
    cap_dbg_o, _ = compile_target_mod(
        "Captured",
        "prelude\nimport Model\ndef Captured.program : Nat := 7\n",
        "spec_transitive_dbg",
        deps_olean_dirs=[dbg_odir],
    )
    spec_dbg_o, _ = compile_target_mod(
        "Spec",
        "prelude\nimport Model\n"
        "def Spec.specs (p : Nat) : Prop := p = 7 ∧ Model.dbgLeak p = p\n",
        "spec_transitive_dbg",
        deps_olean_dirs=[dbg_odir],
    )
    exp_dbg_o, _ = compile_target_mod(
        "Expected",
        exp_ok_src,
        "spec_transitive_dbg",
        deps_olean_dirs=[dbg_odir],
    )
    proof_dbg_o, _ = compile_target_mod(
        "Proof",
        "prelude\nimport Expected\n"
        "theorem Proof.verify : Expected.claim :=\n"
        "  And.intro rfl (And.intro rfl rfl)\n",
        "spec_transitive_dbg",
        deps_olean_dirs=[dbg_odir],
    )
    dbg_graph = dict(base_graph)
    dbg_graph["Model"] = core_edge + [
        {"module": "Init.Util", "isExported": True, "importAll": False, "isMeta": False}
    ]
    target_reqs["target_spec_transitive_dbg"] = make_ta_case(
        "spec_transitive_dbg",
        mod_oleans={
            "Model": model_dbg_o,
            "Captured": cap_dbg_o,
            "Spec": spec_dbg_o,
            "Expected": exp_dbg_o,
        },
        proof_o=proof_dbg_o,
        graph_override=dbg_graph,
    )

    def run_lean_forge(tag: str, script_body: str) -> None:
        script_path = fixtures_root / f"forge_{tag}.lean"
        script_path.write_text(script_body, encoding="utf-8")
        res = subprocess.run(
            [
                str(lean_bin),
                "-j1",
                "-M2048",
                "-s16384",
                "--run",
                str(script_path),
            ],
            env=_lean_subprocess_env([]),
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
        if res.returncode != 0:
            raise RuntimeError(
                f"failed forging fixture {tag}: {res.stdout + res.stderr}"
            )

    # Case: target_dup_library (intra-module duplicate in .library)
    dup_lib_o = fixtures_root / "DupLib.olean"
    run_lean_forge(
        "dup_library",
        "import Lean.Environment\n"
        "open Lean in\n"
        "def main : IO Unit := do\n"
        "  let ci : ConstantInfo := .thmInfo {\n"
        "    name := `DupLib.t, levelParams := [], type := .const `True [],\n"
        "    value := .const `True.intro [], all := [`DupLib.t] }\n"
        "  let md : ModuleData := {\n"
        "    isModule := false, imports := #[{ module := `Init.Core }],\n"
        "    constNames := #[`DupLib.t, `DupLib.t], constants := #[ci, ci],\n"
        "    extraConstNames := #[], entries := #[] }\n"
        f"  saveModuleData (System.FilePath.mk {json.dumps(str(dup_lib_o))}) `DupLib md\n",
    )
    dup_graph = dict(base_graph)
    dup_graph["DupLib"] = core_edge
    target_reqs["target_dup_library"] = make_ta_case(
        "dup_library",
        mod_oleans={
            "Model": model_olean,
            "Captured": cap_olean,
            "Spec": spec_olean,
            "Expected": exp_olean,
            "DupLib": dup_lib_o,
        },
        proof_o=proof_ok_olean,
        graph_override=dup_graph,
        libraries=["DupLib"],
    )

    # Case: target_unsafe_rec_type_mismatch (`Spec.foo._unsafe_rec` : Bool)
    bad_rec_spec_o = fixtures_root / "SpecBadUnsafeRec.olean"
    shutil.copy2(spec_olean, bad_rec_spec_o)
    run_lean_forge(
        "unsafe_rec_type_mismatch",
        "import Lean.Environment\n"
        "open Lean in\n"
        "def main : IO Unit := do\n"
        f"  let p := System.FilePath.mk {json.dumps(str(bad_rec_spec_o))}\n"
        "  let (data, _) ← readModuleData p\n"
        "  let parentCi : ConstantInfo := .defnInfo {\n"
        "    name := `Spec.foo, levelParams := [], type := .const `Nat [],\n"
        "    value := .lit (.natVal 0), hints := .abbrev, safety := .safe,\n"
        "    all := [`Spec.foo] }\n"
        "  let badRecCi : ConstantInfo := .defnInfo {\n"
        "    name := `Spec.foo._unsafe_rec, levelParams := [],\n"
        "    type := .const `Bool [], value := .const `Bool.true [],\n"
        "    hints := .abbrev, safety := .partial,\n"
        "    all := [`Spec.foo._unsafe_rec] }\n"
        "  let newNames := data.constNames ++ #[`Spec.foo, `Spec.foo._unsafe_rec]\n"
        "  let newConsts := data.constants ++ #[parentCi, badRecCi]\n"
        "  saveModuleData p `Spec\n"
        "    { data with constNames := newNames, constants := newConsts }\n",
    )
    target_reqs["target_unsafe_rec_type_mismatch"] = make_ta_case(
        "unsafe_rec_type_mismatch",
        mod_oleans={
            "Model": model_olean,
            "Captured": cap_olean,
            "Spec": bad_rec_spec_o,
            "Expected": exp_olean,
        },
        proof_o=proof_ok_olean,
    )

    # Case: target_foundation_propext_hijack (`Model` subsumes `propext`)
    bad_propext_model_o = fixtures_root / "ModelPropextHijack.olean"
    shutil.copy2(model_olean, bad_propext_model_o)
    run_lean_forge(
        "foundation_propext_hijack",
        "import Lean.Environment\n"
        "open Lean in\n"
        "def main : IO Unit := do\n"
        f"  initSearchPath (System.FilePath.mk {json.dumps(str(sysroot))})\n"
        "  let env ← importModules #[{ module := `Init.Core }] {}\n"
        "    (trustLevel := 0) (plugins := #[]) (loadExts := false)\n"
        "    (level := .private)\n"
        "  let some px := env.checked.get.find? `propext\n"
        '    | throw (IO.userError "missing propext")\n'
        f"  let p := System.FilePath.mk {json.dumps(str(bad_propext_model_o))}\n"
        "  let (data, _) ← readModuleData p\n"
        "  let body := Expr.const `True []\n"
        "  let fakeThm : ConstantInfo := .thmInfo {\n"
        "    name := `propext, levelParams := px.levelParams,\n"
        "    type := px.type, value := body, all := [`propext] }\n"
        "  let newNames := data.constNames.push `propext\n"
        "  let newConsts := data.constants.push fakeThm\n"
        "  saveModuleData p `Model\n"
        "    { data with constNames := newNames, constants := newConsts }\n",
    )
    target_reqs["target_foundation_propext_hijack"] = make_ta_case(
        "foundation_propext_hijack",
        mod_oleans={
            "Model": bad_propext_model_o,
            "Captured": cap_olean,
            "Spec": spec_olean,
            "Expected": exp_olean,
        },
        proof_o=proof_ok_olean,
    )

    built_spec_ids = set(spec_reqs.keys()) - {"spec_sanity"}
    if built_spec_ids != VALID_SPEC_BOUNDARY_FIXTURE_IDS:
        raise RuntimeError(
            "spec boundary fixture keys drifted from static allowlist: "
            f"{sorted(built_spec_ids)} != {sorted(VALID_SPEC_BOUNDARY_FIXTURE_IDS)}"
        )
    built_target_ids = set(target_reqs.keys()) - {"target_sanity"}
    if built_target_ids != VALID_TARGET_BOUNDARY_FIXTURE_IDS:
        raise RuntimeError(
            "target boundary fixture keys drifted from static allowlist: "
            f"{sorted(built_target_ids)} != {sorted(VALID_TARGET_BOUNDARY_FIXTURE_IDS)}"
        )

    return spec_reqs, target_reqs


def _check_one_mir_guard(
    guard: MirSemanticsGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    base_olean_dir: Path,
    fixtures_dir: Path,
    timeout_sec: int,
) -> GuardResult:
    t0 = time.monotonic()
    trusted_lean_dir = anneal_root / "trusted/lean"
    src_path = anneal_root / guard.target_file
    original_text = src_path.read_text(encoding="utf-8")
    try:
        mutated_text = apply_single_guard_mutation(
            original_text,
            guard.anchor,
            guard.replacement,
            guard_id=guard.guard_id,
        )
    except ValueError as exc:
        return GuardResult(
            suite="mir_semantics",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=str(exc),
        )

    fixture_path = fixtures_dir / f"{guard.fixture_module}.lean"
    fixture_text = fixture_path.read_text(encoding="utf-8")
    theorem_span = find_theorem_line_span(fixture_text, guard.theorem_name)

    with tempfile.TemporaryDirectory(
        prefix=f"anneal-gmut-{guard.guard_id}-"
    ) as tmp:
        tmp_path = Path(tmp)
        mut_src_root = tmp_path / "trusted_lean"
        mut_olean_dir = tmp_path / "olean"
        mut_olean_dir.mkdir()

        # Copy only the mutated source file into a minimal `trusted_lean`
        # overlay; unchanged downstream `.lean` sources are compiled directly
        # from `trusted_lean_dir` while reading mutated `.olean`s from
        # `mut_olean_dir` first via `LEAN_PATH`.
        rel_target = Path(f"{guard.target_module}.lean")
        mut_target_path = mut_src_root / rel_target
        mut_target_path.parent.mkdir(parents=True, exist_ok=True)
        mut_target_path.write_text(mutated_text, encoding="utf-8")

        # Seed `mut_olean_dir` with hardlinks (falling back to copies across
        # filesystems) to every unmodified module artifact (`.olean*` and
        # `.ir*`) in `base_olean_dir`. Lean 4 resolves a root namespace
        # (`Trusted.*`) from the first `LEAN_PATH` entry containing that root
        # directory, and non-`module` fixtures importing `module` dependencies
        # also load `.ir` files alongside `.olean*`.
        downstream = SEMANTICS_DOWNSTREAM[guard.target_module]
        rebuilt_mods = set(downstream) | {
            guard.sanity_module,
            guard.fixture_module,
        }
        if guard.sanity_module == "PositiveSanity":
            rebuilt_mods |= set(
                FIXTURE_HELPERS_END_TO_END
                if guard.needs_wf_helper
                else FIXTURE_HELPERS_BOUNDARY
            )
        for src_art in base_olean_dir.rglob("*"):
            if not src_art.is_file():
                continue
            rel = src_art.relative_to(base_olean_dir)
            rel_str = rel.as_posix()
            rel_mod = None
            for ext in (
                ".olean",
                ".olean.server",
                ".olean.private",
                ".ir",
                ".ir.sig",
            ):
                if rel_str.endswith(ext):
                    rel_mod = rel_str[: -len(ext)]
                    break
            if rel_mod is None or rel_mod in rebuilt_mods:
                continue
            dst_art = mut_olean_dir / rel
            dst_art.parent.mkdir(parents=True, exist_ok=True)
            try:
                os.link(src_art, dst_art)
            except OSError:
                shutil.copy2(src_art, dst_art)

        lean_path = [mut_olean_dir]
        for idx, mod in enumerate(downstream):
            root_for_mod = mut_src_root if idx == 0 else trusted_lean_dir
            res = _compile_module(
                lean_bin,
                root_for_mod,
                mod,
                mut_olean_dir,
                lean_path=lean_path,
                timeout_sec=timeout_sec,
            )
            if res.returncode != 0:
                return GuardResult(
                    suite="mir_semantics",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=(
                        f"mutated semantics module {mod} failed to compile "
                        f"(rc={res.returncode}): {(res.stdout + res.stderr).strip()[:300]}"
                    ),
                )

        # Rebuild the fixture helper(s) needed by this guard against the
        # mutated semantics `.olean`s, and confirm positive sanity still passes.
        if guard.sanity_module == "PositiveSanity":
            helpers = (
                FIXTURE_HELPERS_END_TO_END
                if guard.needs_wf_helper
                else FIXTURE_HELPERS_BOUNDARY
            )
            for helper in helpers:
                h_res = _compile_module(
                    lean_bin,
                    fixtures_dir,
                    helper,
                    mut_olean_dir,
                    lean_path=lean_path,
                    timeout_sec=timeout_sec,
                )
                if h_res.returncode != 0:
                    return GuardResult(
                        suite="mir_semantics",
                        guard_id=guard.guard_id,
                        target_file=guard.target_file,
                        status="ERROR",
                        duration_sec=time.monotonic() - t0,
                        detail=(
                            f"fixture helper {helper} failed to compile on mutant: "
                            f"{(h_res.stdout + h_res.stderr).strip()[:300]}"
                        ),
                    )

        sanity_res = _compile_module(
            lean_bin,
            fixtures_dir,
            guard.sanity_module,
            mut_olean_dir,
            lean_path=lean_path,
            timeout_sec=timeout_sec,
        )
        if sanity_res.returncode != 0:
            return GuardResult(
                suite="mir_semantics",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"positive sanity {guard.sanity_module} broke on mutant "
                    f"(rc={sanity_res.returncode}): "
                    f"{(sanity_res.stdout + sanity_res.stderr).strip()[:300]}"
                ),
            )

        # Compile the guard's negative refutation module. It MUST fail with a
        # proof/type error inside `guard.theorem_name`.
        refute_res = _compile_module(
            lean_bin,
            fixtures_dir,
            guard.fixture_module,
            mut_olean_dir,
            lean_path=lean_path,
            timeout_sec=timeout_sec,
        )
        combined = (refute_res.stdout + "\n" + refute_res.stderr).strip()
        status, detail = classify_refutation_failure(
            refute_res.returncode,
            combined,
            f"{guard.fixture_module}.lean",
            theorem_span,
        )
        return GuardResult(
            suite="mir_semantics",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status=status,
            duration_sec=time.monotonic() - t0,
            detail=detail,
        )


def _compile_mutated_tb(
    lean_bin: Path,
    mutated_text: str,
    tmp_path: Path,
    *,
    module_name: str = "TrustedBoundary",
    timeout_sec: int,
) -> tuple[Path | None, str]:
    """Compile mutated `TrustedBoundary.lean` or `SpecPreflight.lean`."""
    mut_src_dir = tmp_path / "src"
    mut_src_dir.mkdir()
    src_name = f"{module_name}.lean"
    (mut_src_dir / src_name).write_text(mutated_text, encoding="utf-8")
    mut_olean_dir = tmp_path / "olean"
    mut_olean_dir.mkdir()
    comp = _compile_module(
        lean_bin,
        mut_src_dir,
        module_name,
        mut_olean_dir,
        lean_path=[],
        timeout_sec=timeout_sec,
    )
    if comp.returncode != 0:
        return None, (
            f"mutated {src_name} failed to compile: "
            f"{(comp.stdout + comp.stderr).strip()[:300]}"
        )
    return mut_olean_dir, ""


def _check_one_audit_guard(
    guard: AuditHeaderGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    sysroot: str,
    timeout_sec: int,
) -> GuardResult:
    t0 = time.monotonic()
    tb_path = anneal_root / guard.target_file
    mod_name = Path(guard.target_file).stem
    original_text = tb_path.read_text(encoding="utf-8")
    try:
        mutated_text = apply_single_guard_mutation(
            original_text,
            guard.anchor,
            guard.replacement,
            guard_id=guard.guard_id,
        )
    except ValueError as exc:
        return GuardResult(
            suite="audit_headers",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=str(exc),
        )

    with tempfile.TemporaryDirectory(
        prefix=f"anneal-gmut-{guard.guard_id}-"
    ) as tmp:
        tmp_path = Path(tmp)
        mut_olean_dir, comp_err = _compile_mutated_tb(
            lean_bin,
            mutated_text,
            tmp_path,
            module_name=mod_name,
            timeout_sec=timeout_sec,
        )
        if mut_olean_dir is None:
            return GuardResult(
                suite="audit_headers",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=comp_err,
            )

        rc, parsed, out = _run_audit_headers(
            lean_bin,
            mut_olean_dir,
            sysroot,
            guard.negative_source,
            tmp_path,
            module_name=mod_name,
            timeout_sec=timeout_sec,
        )
        if rc == 0 and isinstance(parsed, dict) and parsed.get("ok") is True:
            return GuardResult(
                suite="audit_headers",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="KILLED",
                duration_sec=time.monotonic() - t0,
                detail="negative header fixture flipped from policy reject to accept",
            )
        if (
            rc == 1
            and isinstance(parsed, dict)
            and parsed.get("ok") is False
            and parsed.get("category") == "policy"
        ):
            return GuardResult(
                suite="audit_headers",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="SURVIVED",
                duration_sec=time.monotonic() - t0,
                detail=f"mutant still rejected header: {parsed.get('message')!r}",
            )
        return GuardResult(
            suite="audit_headers",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=f"unexpected auditor result rc={rc} parsed={parsed!r} out={out[:200]}",
        )


def _check_one_boundary_guard(
    guard: AuditBoundaryGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    sanity_req: dict[str, object],
    negative_req: dict[str, object],
    timeout_sec: int,
) -> GuardResult:
    t0 = time.monotonic()
    tb_path = anneal_root / guard.target_file
    original_text = tb_path.read_text(encoding="utf-8")
    try:
        mutated_text = apply_single_guard_mutation(
            original_text,
            guard.anchor,
            guard.replacement,
            guard_id=guard.guard_id,
        )
    except ValueError as exc:
        return GuardResult(
            suite="audit_boundary",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=str(exc),
        )

    with tempfile.TemporaryDirectory(
        prefix=f"anneal-gmut-{guard.guard_id}-"
    ) as tmp:
        tmp_path = Path(tmp)
        mut_olean_dir, comp_err = _compile_mutated_tb(
            lean_bin, mutated_text, tmp_path, timeout_sec=timeout_sec
        )
        if mut_olean_dir is None:
            return GuardResult(
                suite="audit_boundary",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=comp_err,
            )

        s_rc, s_parsed, s_out = _run_tb_request(
            lean_bin,
            mut_olean_dir,
            sanity_req,
            tmp_path,
            tag="sanity",
            timeout_sec=timeout_sec,
        )
        if s_rc != 0 or not isinstance(s_parsed, dict) or s_parsed.get("ok") is not True:
            return GuardResult(
                suite="audit_boundary",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"positive {guard.mode} sanity broke on mutant: "
                    f"rc={s_rc} parsed={s_parsed!r} out={s_out[:200]}"
                ),
            )

        rc, parsed, out = _run_tb_request(
            lean_bin,
            mut_olean_dir,
            negative_req,
            tmp_path,
            tag="neg",
            timeout_sec=timeout_sec,
        )
        if rc == 0 and isinstance(parsed, dict) and parsed.get("ok") is True:
            return GuardResult(
                suite="audit_boundary",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="KILLED",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"negative {guard.mode} fixture ({guard.fixture_id}) "
                    "flipped from policy reject to accept"
                ),
            )
        if (
            rc == 1
            and isinstance(parsed, dict)
            and parsed.get("ok") is False
            and parsed.get("category") == "policy"
        ):
            return GuardResult(
                suite="audit_boundary",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="SURVIVED",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"mutant still rejected {guard.mode} fixture: "
                    f"{parsed.get('message')!r}"
                ),
            )
        return GuardResult(
            suite="audit_boundary",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=f"unexpected boundary result rc={rc} parsed={parsed!r} out={out[:200]}",
        )


FORBIDDEN_LOADER_ENV_VARS: tuple[str, ...] = (
    "LD_PRELOAD",
    "LD_AUDIT",
    "LD_DYNAMIC_WEAK",
    "LD_USE_LOAD_BIAS",
    "DYLD_INSERT_LIBRARIES",
    "DYLD_FORCE_FLAT_NAMESPACE",
)


def _read_pinned_compiler_commit(anneal_root: Path) -> str:
    """Read `COMPILER_COMMIT` from `trusted/rustc-capture/src/ir.rs`."""
    ir_path = anneal_root / "trusted/rustc-capture/src/ir.rs"
    text = ir_path.read_text(encoding="utf-8")
    m = re.search(r'pub const COMPILER_COMMIT: &str = "([0-9a-f]+)";', text)
    if m is None:
        raise RuntimeError(f"COMPILER_COMMIT not found in {ir_path}")
    return m.group(1)


def _extract_subprocess_env(
    rustc_bin: Path,
    sysroot: str,
    ice_dir: Path,
    host_triple: str | None = None,
    cargo_cwd: Path | None = None,
) -> dict[str, str]:
    """Build a sanitized environment for `rustc-capture` compile/run steps."""
    env = dict(os.environ)
    for var in FORBIDDEN_LOADER_ENV_VARS:
        env.pop(var, None)
    for key in list(env):
        if (
            key
            in (
                "RUSTFLAGS",
                "CARGO_BUILD_RUSTFLAGS",
                "CARGO_BUILD_RUSTC_WRAPPER",
                "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
            )
            or (
                key.startswith("CARGO_TARGET_")
                and key.endswith(("_RUSTFLAGS", "_LINKER"))
            )
            or (key.startswith("CARGO_PROFILE_") and key.endswith("_PANIC"))
        ):
            env.pop(key, None)
    sysroot_lib = str(Path(sysroot) / "lib")
    # Cargo checks `CARGO_ENCODED_RUSTFLAGS` first with mutual exclusion over
    # `RUSTFLAGS`, `target.*.rustflags`, and `build.rustflags`: pin the
    # toolchain `<sysroot>/lib` native search path and `-Wl,-rpath` so baseline
    # Cargo builds link and execute consistently with mutated direct-`rustc`
    # builds on Linux, Nix/omnibus, and macOS while still blocking caller
    # rustflags and target linker overrides (`CARGO_TARGET_*_LINKER` applies
    # only to Cargo builds, not direct `rustc`). Clear `RUSTC_WRAPPER` and
    # `RUSTC_WORKSPACE_WRAPPER` to empty string too so relative wrappers and
    # Cargo config-level wrappers cannot fail after `cwd` changes or inject
    # extra options missing from direct `rustc` mutant compiles. Force
    # `profile.dev.panic = "unwind"` (the `test` profile inherits `dev` in
    # `CARGO_PROFILE_*_PANIC=abort` overrides cannot produce abort `.rlib`s
    # incompatible with direct `rustc -C panic=unwind` mutants.
    env["CARGO_ENCODED_RUSTFLAGS"] = (
        f"-Lnative={sysroot_lib}\x1f-Clink-arg=-Wl,-rpath,{sysroot_lib}"
    )
    env["CARGO_PROFILE_DEV_PANIC"] = "unwind"
    env["RUSTC_WRAPPER"] = ""
    env["RUSTC_WORKSPACE_WRAPPER"] = ""
    if host_triple is not None and env.get("CARGO_BUILD_TARGET") not in (
        None,
        "",
        host_triple,
    ):
        env.pop("CARGO_BUILD_TARGET", None)
    env["RUSTC"] = str(rustc_bin)
    env["CARGO_PKG_VERSION"] = "0.1.0"
    env["CARGO_NET_OFFLINE"] = "true"
    env["RUSTC_ICE"] = str(ice_dir)
    for lib_var in ("LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
        existing_lib = env.get(lib_var, "")
        env[lib_var] = (
            f"{sysroot_lib}{os.pathsep}{existing_lib}"
            if existing_lib
            else sysroot_lib
        )
    if cargo_cwd is not None:
        resolved_cwd = cargo_cwd.resolve()
        for home_var in ("CARGO_HOME", "HOME"):
            raw_val = env.get(home_var, "")
            if raw_val and not Path(raw_val).is_absolute():
                env[home_var] = str(
                    Path(os.path.normpath(resolved_cwd / raw_val))
                )
    return env


ALLOWED_CARGO_HOME_CONFIG_SECTIONS: frozenset[str] = frozenset({
    "source",
})
ALLOWED_CARGO_SOURCE_KEYS: frozenset[str] = frozenset({
    "replace-with",
    "directory",
})


def _validate_cargo_home_config(parsed: dict[str, object], cand: Path) -> None:
    """Permit only offline directory-vendored `[source]` entries in config."""
    disallowed = sorted(
        k for k in parsed if k not in ALLOWED_CARGO_HOME_CONFIG_SECTIONS
    )
    if disallowed:
        raise RuntimeError(
            "refusing extract_guards execution with ambient Cargo home "
            f"config sections {disallowed} in {cand}"
        )
    sources = parsed.get("source")
    if sources is None:
        return
    if not isinstance(sources, dict):
        raise RuntimeError(
            "refusing extract_guards execution with invalid Cargo home "
            f"config [source] section in {cand}"
        )
    for src_name, entry in sources.items():
        if not isinstance(entry, dict):
            raise RuntimeError(
                "refusing extract_guards execution with invalid Cargo home "
                f"config [source.{src_name}] entry in {cand}"
            )
        bad_keys = sorted(k for k in entry if k not in ALLOWED_CARGO_SOURCE_KEYS)
        if bad_keys:
            raise RuntimeError(
                "refusing extract_guards execution with non-vendoring Cargo "
                f"home config keys {bad_keys} under [source.{src_name}] in "
                f"{cand}"
            )
        has_dir = "directory" in entry
        has_repl = "replace-with" in entry
        if has_dir == has_repl:
            raise RuntimeError(
                "refusing extract_guards execution with invalid Cargo home "
                f"config [source.{src_name}] (must specify exactly one of "
                f"directory or replace-with) in {cand}"
            )
        if has_dir:
            dir_val = entry["directory"]
            if not isinstance(dir_val, str) or not dir_val.strip():
                raise RuntimeError(
                    "refusing extract_guards execution with empty Cargo home "
                    f"config [source.{src_name}].directory in {cand}"
                )
        else:
            repl_val = entry["replace-with"]
            if not isinstance(repl_val, str) or repl_val not in sources:
                raise RuntimeError(
                    "refusing extract_guards execution with unknown Cargo "
                    f"home config [source.{src_name}].replace-with="
                    f"{repl_val!r} in {cand}"
                )
    for src_name in sources:
        seen: set[str] = set()
        cur = src_name
        while "replace-with" in sources[cur]:
            if cur in seen:
                raise RuntimeError(
                    "refusing extract_guards execution with cyclic Cargo "
                    f"home config [source] replace-with in {cand}"
                )
            seen.add(cur)
            cur = sources[cur]["replace-with"]


def _resolve_cargo_home_dir(base_dir: Path | None = None) -> Path | None:
    """Resolve Cargo's `CARGO_HOME` relative to `base_dir` if non-absolute."""
    anchor = (
        Path(os.path.abspath(base_dir)) if base_dir is not None else Path.cwd()
    )
    cargo_home_env = os.environ.get("CARGO_HOME", "")
    if cargo_home_env:
        raw_ch = Path(cargo_home_env)
        return (
            raw_ch
            if raw_ch.is_absolute()
            else Path(os.path.normpath(anchor / raw_ch))
        )
    home_env = os.environ.get("HOME", "")
    if home_env:
        raw_home = Path(home_env)
        base_home = (
            raw_home
            if raw_home.is_absolute()
            else Path(os.path.normpath(anchor / raw_home))
        )
        return base_home / ".cargo"
    return Path.home() / ".cargo"


def _collect_cargo_home_roots(bases: list[Path]) -> list[Path]:
    """Collect logical and resolved `CARGO_HOME` candidates for `bases`."""
    ch_roots: list[Path] = []
    for base in bases:
        cargo_home = _resolve_cargo_home_dir(base)
        if cargo_home is None:
            continue
        cand_root = Path(os.path.normpath(cargo_home))
        if cand_root not in ch_roots:
            ch_roots.append(cand_root)
        if cand_root.exists() or cand_root.is_symlink():
            try:
                resolved_ch = cand_root.resolve()
            except OSError:
                resolved_ch = None
            if resolved_ch is not None and resolved_ch not in ch_roots:
                ch_roots.append(resolved_ch)
    return ch_roots


def _assert_no_ambient_toolchain_configs(
    directory: Path,
    *,
    check_root_dot_cargo: bool = False,
    check_cargo_home: bool = False,
) -> None:
    """Fail closed if ancestors or `CARGO_HOME` hold Cargo/rustup overrides."""
    bases: list[Path] = []
    for base in (Path(os.path.abspath(directory)), directory.resolve()):
        if base not in bases:
            bases.append(base)
    roots: list[Path] = []
    for base in bases:
        for ancestor in (base, *base.parents):
            if ancestor not in roots:
                roots.append(ancestor)
    local_forbidden: set[Path] = set()
    if check_root_dot_cargo:
        for base in bases:
            for local in (base, base.parent):
                local_forbidden.add(local)
                dot_cargo = local / ".cargo"
                if dot_cargo.exists() or dot_cargo.is_symlink():
                    raise RuntimeError(
                        "refusing extract_guards execution with forbidden root "
                        f"Cargo config directory: {dot_cargo}"
                    )
    ch_roots = _collect_cargo_home_roots(bases) if check_cargo_home else []
    ch_root_set = set(ch_roots)
    for ancestor in roots:
        dot_cargo = ancestor / ".cargo"
        defer_dot_cargo = False
        if check_cargo_home and ancestor not in local_forbidden:
            dot_cargo_norm = Path(os.path.normpath(dot_cargo))
            if dot_cargo_norm in ch_root_set:
                defer_dot_cargo = True
            elif dot_cargo.exists() or dot_cargo.is_symlink():
                try:
                    if dot_cargo.resolve() in ch_root_set:
                        defer_dot_cargo = True
                except OSError:
                    pass
        if not defer_dot_cargo and dot_cargo.is_symlink():
            raise RuntimeError(
                "refusing extract_guards execution with symlinked ambient "
                f".cargo override: {dot_cargo}"
            )
        cargo_rels: tuple[tuple[str, ...], ...] = (
            ()
            if defer_dot_cargo
            else ((".cargo", "config"), (".cargo", "config.toml"))
        )
        for rel in (*cargo_rels, ("rust-toolchain",), ("rust-toolchain.toml",)):
            cand = ancestor.joinpath(*rel)
            if cand.exists() or cand.is_symlink():
                raise RuntimeError(
                    "refusing extract_guards execution with ambient toolchain "
                    f"or Cargo config override: {cand}"
                )
    if not check_cargo_home:
        return
    for ch_dir in ch_roots:
        for cfg_name in ("config", "config.toml"):
            cand = ch_dir / cfg_name
            if not cand.exists() and not cand.is_symlink():
                continue
            if cand.is_symlink() or not cand.is_file():
                raise RuntimeError(
                    "refusing extract_guards execution with non-regular or "
                    f"symlinked Cargo home config: {cand}"
                )
            try:
                parsed = tomllib.loads(cand.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
                raise RuntimeError(
                    "refusing extract_guards execution with unreadable or "
                    f"invalid Cargo home config {cand}: {exc}"
                ) from exc
            _validate_cargo_home_config(parsed, cand)


def _resolve_executable_token(raw: str | Path) -> Path | None:
    """Resolve an explicit path or a bare command name strictly via `PATH`."""
    raw_str = str(raw)
    if not raw_str:
        return None
    if os.sep in raw_str or (os.altsep and os.altsep in raw_str):
        cand = Path(raw_str)
        if cand.is_file() and os.access(cand, os.X_OK):
            return Path(os.path.abspath(cand))
        return None
    found = shutil.which(raw_str)
    if found:
        cand = Path(found)
        if cand.is_file() and os.access(cand, os.X_OK):
            return Path(os.path.abspath(cand))
    return None


def _is_rustup_proxy(exe: Path) -> bool:
    """Return True when `exe` resolves to a `rustup` proxy shim."""
    try:
        real_stem = Path(os.path.realpath(exe)).stem.lower()
    except OSError:
        return False
    return real_stem == "rustup"


def _sanitized_probe_env() -> dict[str, str]:
    """Return `os.environ` stripped of dynamic-loader injection variables."""
    return {
        k: v
        for k, v in os.environ.items()
        if k not in FORBIDDEN_LOADER_ENV_VARS
    }


def _query_rustc_info(
    rustc_bin: Path,
    timeout_sec: int,
    cwd: Path | None = None,
) -> tuple[str, str, str] | None:
    """Run `rustc -vV` and `--print sysroot`, returning `(commit, host, abs_sr)`."""
    run_cwd = str(cwd) if cwd is not None else None
    probe_env = _sanitized_probe_env()
    try:
        ver = subprocess.run(
            [str(rustc_bin), "--version", "--verbose"],
            capture_output=True,
            text=True,
            env=probe_env,
            cwd=run_cwd,
            timeout=timeout_sec,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if ver.returncode != 0:
        return None
    commit_hash = ""
    host_triple = ""
    for line in ver.stdout.splitlines():
        if line.startswith("commit-hash:"):
            commit_hash = line.split(":", 1)[1].strip()
        elif line.startswith("host:"):
            host_triple = line.split(":", 1)[1].strip()
    if not commit_hash or not host_triple:
        return None

    try:
        sr = subprocess.run(
            [str(rustc_bin), "--print", "sysroot"],
            capture_output=True,
            text=True,
            env=probe_env,
            cwd=run_cwd,
            timeout=timeout_sec,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if sr.returncode != 0:
        return None
    raw_sysroot = sr.stdout.strip()
    if not raw_sysroot:
        return None
    base_cwd = run_cwd if run_cwd is not None else os.getcwd()
    resolved_sysroot = os.path.abspath(os.path.join(base_cwd, raw_sysroot))
    return commit_hash, host_triple, resolved_sysroot


def _run_cargo_version(
    cargo_bin: Path,
    timeout_sec: int,
    *,
    cwd: Path | None = None,
) -> str | None:
    """Return `cargo_bin --version` stdout when runnable, else `None`."""
    try:
        proc = subprocess.run(
            [str(cargo_bin), "--version"],
            capture_output=True,
            text=True,
            env=_sanitized_probe_env(),
            cwd=str(cwd) if cwd is not None else None,
            timeout=timeout_sec,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def _cargo_usable_in_cwd(
    cargo_bin: Path,
    probe_cwd: Path,
    timeout_sec: int,
    *,
    build_cwd: Path | None = None,
) -> bool:
    """Check that `cargo_bin` is not a cwd-sensitive `rustup` or shim proxy."""
    if _is_rustup_proxy(cargo_bin):
        return False
    ver_caller = _run_cargo_version(cargo_bin, timeout_sec)
    ver_tmp = _run_cargo_version(cargo_bin, timeout_sec, cwd=probe_cwd)
    if ver_caller is None or ver_tmp is None or ver_caller != ver_tmp:
        return False
    if build_cwd is not None:
        ver_build = _run_cargo_version(cargo_bin, timeout_sec, cwd=build_cwd)
        if ver_build is None or ver_build != ver_caller:
            return False
    return True


def _validate_explicit_cargo_env() -> Path | None:
    """Resolve an explicit `CARGO` override or fail closed on invalid paths."""
    env_cargo = os.environ.get("CARGO")
    if env_cargo is None:
        return None
    if not env_cargo:
        raise RuntimeError(
            "CARGO is empty; set CARGO to a runnable cargo binary or unset CARGO"
        )
    explicit_cargo = _resolve_executable_token(env_cargo)
    if explicit_cargo is None or not os.access(explicit_cargo, os.X_OK):
        raise RuntimeError(
            f"CARGO={env_cargo!r} does not point to a runnable cargo binary; "
            "pass a valid cargo or unset CARGO"
        )
    return explicit_cargo


def _is_runnable_cargo(cargo_bin: Path, timeout_sec: int) -> bool:
    """Return True when `cargo_bin` is executable and runs `--version`."""
    return (
        cargo_bin.is_file()
        and os.access(cargo_bin, os.X_OK)
        and not _is_rustup_proxy(cargo_bin)
        and _run_cargo_version(cargo_bin, timeout_sec) is not None
    )


def _resolve_cargo_for_rustc(
    rustc_bin: Path,
    sysroot: Path,
    probe_cwd: Path,
    timeout_sec: int,
    *,
    build_cwd: Path | None = None,
) -> Path | None:
    """Select a concrete `cargo` binary paired with `rustc_bin` / `sysroot`."""
    exe_name = "cargo.exe" if os.name == "nt" else "cargo"
    sysroot_cargo = sysroot / "bin" / exe_name
    sibling_cargo = rustc_bin.parent / exe_name
    has_sysroot_cargo = _is_runnable_cargo(
        sysroot_cargo, timeout_sec
    ) and _cargo_usable_in_cwd(
        sysroot_cargo, probe_cwd, timeout_sec, build_cwd=build_cwd
    )

    explicit_cargo = _validate_explicit_cargo_env()
    if explicit_cargo is not None:
        env_cargo = os.environ["CARGO"]
        if _is_rustup_proxy(explicit_cargo):
            if has_sysroot_cargo:
                return Path(os.path.abspath(sysroot_cargo))
            raise RuntimeError(
                f"CARGO={env_cargo!r} is a rustup proxy without a usable "
                f"sysroot cargo at {sysroot_cargo}"
            )
        if _cargo_usable_in_cwd(
            explicit_cargo, probe_cwd, timeout_sec, build_cwd=build_cwd
        ):
            return explicit_cargo
        # A cwd-sensitive wrapper (e.g. a directory-override `cargo` shim) may
        # run in the caller cwd while delegating to the toolchain sysroot.
        if (
            has_sysroot_cargo
            and _run_cargo_version(explicit_cargo, timeout_sec) is not None
        ):
            return Path(os.path.abspath(sysroot_cargo))
        raise RuntimeError(
            f"CARGO={env_cargo!r} does not point to a runnable cargo binary "
            "usable across working directories; pass a valid cargo or unset "
            "CARGO"
        )

    if has_sysroot_cargo:
        return Path(os.path.abspath(sysroot_cargo))
    if (
        sibling_cargo != sysroot_cargo
        and _is_runnable_cargo(sibling_cargo, timeout_sec)
        and _cargo_usable_in_cwd(
            sibling_cargo, probe_cwd, timeout_sec, build_cwd=build_cwd
        )
    ):
        return Path(os.path.abspath(sibling_cargo))

    which_cargo = shutil.which("cargo")
    if which_cargo:
        found = Path(os.path.abspath(which_cargo))
        if _is_runnable_cargo(found, timeout_sec) and _cargo_usable_in_cwd(
            found, probe_cwd, timeout_sec, build_cwd=build_cwd
        ):
            return found
    return None


def _is_runnable_rustc(rustc_bin: Path, timeout_sec: int) -> bool:
    """Return True when `rustc_bin -vV` executes and prints host metadata."""
    try:
        ver = subprocess.run(
            [str(rustc_bin), "--version", "--verbose"],
            capture_output=True,
            text=True,
            env=_sanitized_probe_env(),
            timeout=timeout_sec,
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    return (
        ver.returncode == 0
        and "commit-hash:" in ver.stdout
        and "host:" in ver.stdout
    )


SUPPORTED_EXTRACT_HOST_TRIPLE = "x86_64-unknown-linux-gnu"
REQUIRED_EXTRACT_HOST_CFGS = frozenset(
    {
        'target_arch="x86_64"',
        'target_os="linux"',
        'target_pointer_width="64"',
        'target_endian="little"',
    }
)


def _is_supported_extract_host(
    rustc_bin: Path,
    host_triple: str,
    timeout_sec: int,
    cwd: Path | None = None,
) -> bool:
    """Return True iff `rustc_bin` targets `x86_64-unknown-linux-gnu`."""
    if host_triple != SUPPORTED_EXTRACT_HOST_TRIPLE:
        return False
    try:
        cfg = subprocess.run(
            [str(rustc_bin), "--print", "cfg"],
            capture_output=True,
            text=True,
            env=_sanitized_probe_env(),
            cwd=str(cwd) if cwd is not None else None,
            timeout=timeout_sec,
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    if cfg.returncode != 0:
        return False
    cfg_lines = {line.strip() for line in cfg.stdout.splitlines()}
    return REQUIRED_EXTRACT_HOST_CFGS.issubset(cfg_lines)


def _probe_rustc_candidate(
    rustc_bin: Path,
    pinned_commit: str,
    timeout_sec: int,
    *,
    build_cwd: Path | None = None,
) -> tuple[Path, Path, str, str] | None:
    """Verify `rustc_bin` matches `pinned_commit` on x86_64-unknown-linux-gnu."""
    _assert_no_ambient_toolchain_configs(Path.cwd(), check_cargo_home=True)
    check_build_cwd = (
        build_cwd if (build_cwd is not None and build_cwd.is_dir()) else None
    )
    if check_build_cwd is not None:
        _assert_no_ambient_toolchain_configs(
            check_build_cwd, check_root_dot_cargo=True, check_cargo_home=True
        )
    resolved_rustc = Path(os.path.abspath(rustc_bin))
    if not resolved_rustc.is_file():
        return None
    caller_info = _query_rustc_info(resolved_rustc, timeout_sec)
    if caller_info is None:
        return None
    commit_hash, host_triple, sysroot = caller_info
    if commit_hash != pinned_commit or not _is_supported_extract_host(
        resolved_rustc, host_triple, timeout_sec
    ):
        return None

    sysroot_path = Path(sysroot)
    lib_dir = sysroot_path / "lib"
    rustlib_dir = sysroot_path / "lib" / "rustlib" / host_triple / "lib"
    if not lib_dir.is_dir() or not rustlib_dir.is_dir():
        return None
    has_sysroot_driver = any(
        p.name.startswith("librustc_driver") and p.is_file()
        for p in lib_dir.iterdir()
    )
    # Base `rustc` ships `<sysroot>/lib/librustc_driver*` even without the
    # `rustc-dev` (`rustc_private`) component. Check target `rustlib` for both
    # `librustc_driver*` and `librustc_middle*` metadata/libs.
    has_rustlib_driver = any(
        p.name.startswith("librustc_driver") and p.is_file()
        for p in rustlib_dir.iterdir()
    )
    has_rustlib_middle = any(
        p.name.startswith("librustc_middle") and p.is_file()
        for p in rustlib_dir.iterdir()
    )
    if not (has_sysroot_driver and has_rustlib_driver and has_rustlib_middle):
        return None

    with tempfile.TemporaryDirectory(prefix="anneal-rustc-probe-") as probe_tmp:
        probe_cwd = Path(probe_tmp)
        _assert_no_ambient_toolchain_configs(probe_cwd, check_cargo_home=True)
        probe_dirs = [probe_cwd]
        if check_build_cwd is not None:
            probe_dirs.append(check_build_cwd)
        if _is_rustup_proxy(resolved_rustc):
            needs_sysroot_rustc = True
        else:
            needs_sysroot_rustc = False
            for d in probe_dirs:
                dir_info = _query_rustc_info(resolved_rustc, timeout_sec, cwd=d)
                if (
                    dir_info is None
                    or dir_info[0] != commit_hash
                    or dir_info[1] != host_triple
                    or dir_info[2] != sysroot
                    or not _is_supported_extract_host(
                        resolved_rustc, host_triple, timeout_sec, cwd=d
                    )
                ):
                    needs_sysroot_rustc = True
                    break
        if needs_sysroot_rustc:
            rustc_exe = "rustc.exe" if os.name == "nt" else "rustc"
            sysroot_rustc = sysroot_path / "bin" / rustc_exe
            if not sysroot_rustc.is_file():
                return None
            for d in probe_dirs:
                sr_info = _query_rustc_info(sysroot_rustc, timeout_sec, cwd=d)
                if (
                    sr_info is None
                    or sr_info[0] != pinned_commit
                    or sr_info[1] != host_triple
                    or sr_info[2] != sysroot
                    or not _is_supported_extract_host(
                        sysroot_rustc, host_triple, timeout_sec, cwd=d
                    )
                ):
                    return None
            resolved_rustc = Path(os.path.abspath(sysroot_rustc))

        cargo_bin = _resolve_cargo_for_rustc(
            resolved_rustc,
            sysroot_path,
            probe_cwd,
            timeout_sec,
            build_cwd=check_build_cwd,
        )
        if cargo_bin is None:
            return None
        return resolved_rustc, cargo_bin, sysroot, host_triple


def _resolve_extract_toolchain(
    anneal_root: Path,
    explicit_rustc: str | Path | None,
    timeout_sec: int,
) -> tuple[Path, Path, str, str] | None:
    """Resolve the pinned nightly `rustc` with `rustc-dev` and `cargo`."""
    _assert_no_ambient_toolchain_configs(
        anneal_root, check_root_dot_cargo=True, check_cargo_home=True
    )
    _assert_no_ambient_toolchain_configs(Path.cwd(), check_cargo_home=True)
    _validate_explicit_cargo_env()
    pinned_commit = _read_pinned_compiler_commit(anneal_root)
    if explicit_rustc is not None:
        explicit_cand = _resolve_executable_token(explicit_rustc)
        if explicit_cand is None:
            return None
        return _probe_rustc_candidate(
            explicit_cand, pinned_commit, timeout_sec, build_cwd=anneal_root
        )

    env_rustc = os.environ.get("RUSTC")
    if env_rustc is not None:
        if not env_rustc:
            raise RuntimeError(
                "RUSTC is empty; set RUSTC to a runnable pinned nightly "
                "rustc or unset RUSTC"
            )
        env_cand = _resolve_executable_token(env_rustc)
        if env_cand is None or not _is_runnable_rustc(env_cand, timeout_sec):
            raise RuntimeError(
                f"RUSTC={env_rustc!r} does not point to a runnable rustc "
                "binary; pass a valid rustc or unset RUSTC"
            )
        resolved = _probe_rustc_candidate(
            env_cand, pinned_commit, timeout_sec, build_cwd=anneal_root
        )
        if resolved is None:
            raise RuntimeError(
                f"RUSTC={env_rustc!r} is not the pinned nightly rustc "
                f"({pinned_commit}) on an x86_64-unknown-linux-gnu host with "
                "rustc-dev artifacts and cargo; pass a valid rustc or unset RUSTC"
            )
        return resolved

    which_rustc = shutil.which("rustc")
    if which_rustc:
        cand = Path(os.path.abspath(which_rustc))
        resolved = _probe_rustc_candidate(
            cand, pinned_commit, timeout_sec, build_cwd=anneal_root
        )
        if resolved is not None:
            return resolved
    return None


def _add_unique_path(paths: list[Path], cand: Path) -> None:
    resolved = Path(os.path.abspath(cand))
    if resolved not in paths:
        paths.append(resolved)


def _parse_cargo_json_artifacts(
    stdout: str,
    extern_rlibs: dict[str, Path],
    deps_dirs: list[Path] | None = None,
) -> tuple[Path | None, Path | None]:
    """Extract direct-dep `.rlib` paths, `deps` dirs, and executables."""
    capture_bin: Path | None = None
    unit_bin: Path | None = None
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("reason") != "compiler-artifact":
            continue
        target = msg.get("target", {})
        name = target.get("name")
        kinds = target.get("kind", [])
        is_test = bool(msg.get("profile", {}).get("test"))
        filenames = msg.get("filenames")
        if isinstance(filenames, list) and deps_dirs is not None:
            for fname in filenames:
                if not isinstance(fname, str) or not fname:
                    continue
                fpath = Path(os.path.abspath(fname))
                if fpath.parent.name == "deps":
                    _add_unique_path(deps_dirs, fpath.parent)
        if name in EXTRACT_DIRECT_DEPS and not is_test:
            for fname in filenames if isinstance(filenames, list) else []:
                if isinstance(fname, str) and fname.endswith(".rlib"):
                    rpath = Path(os.path.abspath(fname))
                    extern_rlibs[name] = rpath
                    if deps_dirs is not None:
                        _add_unique_path(deps_dirs, rpath.parent)
                    break
        elif name in ("anneal-rustc-capture", "anneal_rustc_capture"):
            exe = msg.get("executable")
            if exe:
                exe_path = Path(os.path.abspath(exe))
                if deps_dirs is not None:
                    if exe_path.parent.name == "deps":
                        _add_unique_path(deps_dirs, exe_path.parent)
                    elif (exe_path.parent / "deps").is_dir():
                        _add_unique_path(deps_dirs, exe_path.parent / "deps")
                if "lib" in kinds and is_test:
                    unit_bin = exe_path
                elif "bin" in kinds and not is_test:
                    capture_bin = exe_path
    return capture_bin, unit_bin


def _build_extract_baseline(
    *,
    anneal_root: Path,
    rustc_bin: Path,
    cargo_bin: Path,
    sysroot: str,
    host_triple: str,
    base_target_dir: Path,
    need_capture: bool,
    need_unit: bool,
    timeout_sec: int,
) -> tuple[Path | None, Path | None, tuple[Path, ...], dict[str, Path]]:
    """Build unmodified `anneal-rustc-capture` bin/lib-tests and dep rlibs."""
    _assert_no_ambient_toolchain_configs(
        anneal_root, check_root_dot_cargo=True, check_cargo_home=True
    )
    base_target_dir.mkdir(parents=True, exist_ok=True)
    env = _extract_subprocess_env(
        rustc_bin, sysroot, base_target_dir, host_triple, cargo_cwd=anneal_root
    )
    manifest_path = anneal_root / "Cargo.toml"
    build_timeout = max(timeout_sec, 180)
    extern_rlibs: dict[str, Path] = {}
    deps_dirs: list[Path] = []
    capture_bin: Path | None = None
    unit_bin: Path | None = None

    if need_unit:
        try:
            proc = subprocess.run(
                [
                    str(cargo_bin),
                    "test",
                    "--locked",
                    "--offline",
                    "--no-run",
                    "--manifest-path",
                    str(manifest_path),
                    "-p",
                    "anneal-rustc-capture",
                    "--lib",
                    "--target",
                    host_triple,
                    "--config",
                    'profile.dev.panic="unwind"',
                    "--target-dir",
                    str(base_target_dir),
                    "--message-format=json",
                ],
                capture_output=True,
                text=True,
                env=env,
                cwd=str(anneal_root),
                timeout=build_timeout,
            )
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(
                "baseline anneal-rustc-capture lib-test build timed out after "
                f"{build_timeout}s"
            ) from exc
        except OSError as exc:
            raise RuntimeError(
                "failed to execute cargo for baseline anneal-rustc-capture "
                f"lib-test build: {exc}"
            ) from exc
        if proc.returncode != 0:
            raise RuntimeError(
                "baseline anneal-rustc-capture lib-test build failed:\n"
                f"{proc.stderr[-1000:]}"
            )
        _, parsed_unit = _parse_cargo_json_artifacts(
            proc.stdout, extern_rlibs, deps_dirs
        )
        unit_bin = parsed_unit
        if unit_bin is None or not unit_bin.is_file():
            raise RuntimeError(
                "baseline cargo test --lib produced no test executable"
            )

    if need_capture:
        try:
            proc = subprocess.run(
                [
                    str(cargo_bin),
                    "build",
                    "--locked",
                    "--offline",
                    "--manifest-path",
                    str(manifest_path),
                    "-p",
                    "anneal-rustc-capture",
                    "--bin",
                    "anneal-rustc-capture",
                    "--target",
                    host_triple,
                    "--config",
                    'profile.dev.panic="unwind"',
                    "--target-dir",
                    str(base_target_dir),
                    "--message-format=json",
                ],
                capture_output=True,
                text=True,
                env=env,
                cwd=str(anneal_root),
                timeout=build_timeout,
            )
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(
                "baseline anneal-rustc-capture binary build timed out after "
                f"{build_timeout}s"
            ) from exc
        except OSError as exc:
            raise RuntimeError(
                "failed to execute cargo for baseline anneal-rustc-capture "
                f"binary build: {exc}"
            ) from exc
        if proc.returncode != 0:
            raise RuntimeError(
                "baseline anneal-rustc-capture binary build failed:\n"
                f"{proc.stderr[-1000:]}"
            )
        parsed_cap, _ = _parse_cargo_json_artifacts(
            proc.stdout, extern_rlibs, deps_dirs
        )
        capture_bin = parsed_cap
        if capture_bin is None or not capture_bin.is_file():
            raise RuntimeError(
                "baseline cargo build --bin produced no capture executable"
            )

    missing_deps = [d for d in EXTRACT_DIRECT_DEPS if d not in extern_rlibs]
    if missing_deps:
        raise RuntimeError(
            f"baseline cargo build missing direct dep rlibs: {missing_deps}"
        )
    host_deps_dir = Path(os.path.abspath(base_target_dir / "debug" / "deps"))
    if host_deps_dir.is_dir():
        _add_unique_path(deps_dirs, host_deps_dir)
    if not deps_dirs:
        _add_unique_path(deps_dirs, host_deps_dir)
    return capture_bin, unit_bin, tuple(deps_dirs), extern_rlibs


def _extract_diag_text(parsed: dict[str, object] | None) -> str:
    """Flatten top-level diagnostics and per-item unsupported reasons."""
    if not isinstance(parsed, dict):
        return ""
    parts: list[str] = []
    diags = parsed.get("diagnostics")
    if isinstance(diags, list):
        parts.extend(str(d) for d in diags)
    unsup = parsed.get("unsupported")
    if isinstance(unsup, list):
        for item in unsup:
            if isinstance(item, dict) and "reason" in item:
                parts.append(str(item["reason"]))
    return "\n".join(parts)


def _run_extract_capture(
    capture_bin: Path,
    source_text: str,
    *,
    capture_scope: str,
    select_root: str,
    instantiate_json: str,
    allow_unstable_features: tuple[str, ...] = (),
    stdlib_crate: str = "",
    work_dir: Path,
    tag: str,
    sysroot: str,
    host_triple: str,
    env: dict[str, str],
    timeout_sec: int,
) -> tuple[int, dict[str, object] | None, str]:
    """Run `anneal-rustc-capture capture` on an isolated temporary crate."""
    src_file = work_dir / f"{tag}_lib.rs"
    src_file.write_text(source_text, encoding="utf-8")
    out_dir = work_dir / f"{tag}_out"
    crate_name = stdlib_crate or "demo"
    cmd = [
        str(capture_bin),
        "capture",
        "--crate-root",
        str(src_file),
        "--crate-name",
        crate_name,
        "--edition",
        "2024",
        "--target",
        host_triple,
        "--out-dir",
        str(out_dir),
        "--sysroot",
        sysroot,
        "--source-file",
        str(src_file),
    ]
    if stdlib_crate:
        cmd.extend(["--stdlib-crate", stdlib_crate])
    for feat in allow_unstable_features:
        cmd.extend(["--allow-unstable-feature", feat])
    if capture_scope == "crate":
        cmd.extend(["--scope", "crate"])
    elif capture_scope == "instantiate":
        cmd.extend(["--instantiate", instantiate_json])
    else:
        cmd.extend(["--select", select_root])

    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            env=env,
            cwd=str(work_dir),
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return -1, None, f"capture timed out after {timeout_sec}s"
    except OSError as exc:
        return -1, None, f"capture launch failed: {exc}"

    parsed: dict[str, object] | None = None
    for line in reversed(proc.stdout.splitlines()):
        stripped = line.strip()
        if stripped.startswith("{"):
            try:
                obj = json.loads(stripped)
                if isinstance(obj, dict):
                    parsed = obj
                    break
            except json.JSONDecodeError:
                continue
    combined = (proc.stdout + "\n" + proc.stderr).strip()
    return proc.returncode, parsed, combined


def _run_extract_unit_test(
    unit_bin: Path,
    test_name: str,
    *,
    work_dir: Path,
    env: dict[str, str],
    timeout_sec: int,
) -> tuple[int, str]:
    """Execute one exact Rust unit test from `anneal-rustc-capture`."""
    try:
        proc = subprocess.run(
            [str(unit_bin), "--exact", test_name, "--nocapture"],
            capture_output=True,
            text=True,
            env=env,
            cwd=str(work_dir),
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return -1, f"unit test timed out after {timeout_sec}s"
    except OSError as exc:
        return -1, f"unit test launch failed: {exc}"
    return proc.returncode, (proc.stdout + "\n" + proc.stderr).strip()


def _copy_mutated_extract_src(
    anneal_root: Path,
    guard: ExtractGuard,
    mut_src_dir: Path,
) -> str | None:
    """Copy `trusted/rustc-capture/src/*.rs` and apply one guard mutation."""
    src_root = anneal_root / "trusted/rustc-capture/src"
    mut_src_dir.mkdir(parents=True, exist_ok=True)
    target_name = Path(guard.target_file).name
    found_target = False
    for rs_file in src_root.glob("*.rs"):
        text = rs_file.read_text(encoding="utf-8")
        if rs_file.name == target_name:
            found_target = True
            try:
                text = apply_single_guard_mutation(
                    text,
                    guard.anchor,
                    guard.replacement,
                    guard_id=guard.guard_id,
                )
            except ValueError as exc:
                return str(exc)
        (mut_src_dir / rs_file.name).write_text(text, encoding="utf-8")
    if not found_target:
        return f"target file {guard.target_file} not found under {src_root}"
    return None


def _compile_mutated_extract_unit(
    rustc_bin: Path,
    mut_src_dir: Path,
    out_bin: Path,
    *,
    host_triple: str,
    deps_dirs: tuple[Path, ...],
    extern_rlibs: dict[str, Path],
    sysroot: str,
    env: dict[str, str],
    timeout_sec: int,
) -> tuple[bool, str]:
    """Compile mutated `anneal-rustc-capture` lib unit tests directly."""
    cmd = [
        str(rustc_bin),
        "--crate-name",
        "anneal_rustc_capture",
        "--edition=2024",
        "--target",
        host_triple,
        "--test",
        "-C",
        "panic=unwind",
        "-C",
        "debuginfo=0",
    ]
    for d_dir in deps_dirs:
        cmd.extend(["-L", f"dependency={d_dir}"])
    for dep_name in EXTRACT_DIRECT_DEPS:
        cmd.extend(["--extern", f"{dep_name}={extern_rlibs[dep_name]}"])
    cmd.extend([
        "-L",
        f"native={Path(sysroot) / 'lib'}",
        "-C",
        f"link-arg=-Wl,-rpath,{Path(sysroot) / 'lib'}",
        str(mut_src_dir / "lib.rs"),
        "-o",
        str(out_bin),
    ])
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            env=env,
            cwd=str(out_bin.parent),
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return False, f"mutated unit-test rustc timed out after {timeout_sec}s"
    if proc.returncode != 0:
        return False, (
            f"mutated unit-test build failed (rc={proc.returncode}): "
            f"{(proc.stdout + proc.stderr).strip()[:300]}"
        )
    return True, ""


def _compile_mutated_extract_capture(
    rustc_bin: Path,
    mut_src_dir: Path,
    tmp_path: Path,
    out_bin: Path,
    *,
    host_triple: str,
    deps_dirs: tuple[Path, ...],
    extern_rlibs: dict[str, Path],
    sysroot: str,
    env: dict[str, str],
    timeout_sec: int,
) -> tuple[bool, str]:
    """Compile mutated `anneal-rustc-capture` library + binary directly."""
    mut_rlib = tmp_path / "libanneal_rustc_capture.rlib"
    lib_cmd = [
        str(rustc_bin),
        "--crate-name",
        "anneal_rustc_capture",
        "--edition=2024",
        "--target",
        host_triple,
        "--crate-type",
        "lib",
        "-C",
        "panic=unwind",
        "-C",
        "debuginfo=0",
    ]
    for d_dir in deps_dirs:
        lib_cmd.extend(["-L", f"dependency={d_dir}"])
    for dep_name in EXTRACT_DIRECT_DEPS:
        lib_cmd.extend(["--extern", f"{dep_name}={extern_rlibs[dep_name]}"])
    lib_cmd.extend([str(mut_src_dir / "lib.rs"), "-o", str(mut_rlib)])

    try:
        lib_proc = subprocess.run(
            lib_cmd,
            capture_output=True,
            text=True,
            env=env,
            cwd=str(tmp_path),
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return False, f"mutated lib rustc timed out after {timeout_sec}s"
    if lib_proc.returncode != 0:
        return False, (
            f"mutated lib build failed (rc={lib_proc.returncode}): "
            f"{(lib_proc.stdout + lib_proc.stderr).strip()[:300]}"
        )

    bin_cmd = [
        str(rustc_bin),
        "--crate-name",
        "anneal_rustc_capture",
        "--edition=2024",
        "--target",
        host_triple,
        "--crate-type",
        "bin",
        "-C",
        "panic=unwind",
        "-C",
        "debuginfo=0",
    ]
    for d_dir in deps_dirs:
        bin_cmd.extend(["-L", f"dependency={d_dir}"])
    bin_cmd.extend([
        "--extern",
        f"anneal_rustc_capture={mut_rlib}",
        "-L",
        f"native={Path(sysroot) / 'lib'}",
        "-C",
        f"link-arg=-Wl,-rpath,{Path(sysroot) / 'lib'}",
        str(mut_src_dir / "main.rs"),
        "-o",
        str(out_bin),
    ])
    try:
        bin_proc = subprocess.run(
            bin_cmd,
            capture_output=True,
            text=True,
            env=env,
            cwd=str(tmp_path),
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return False, f"mutated bin rustc timed out after {timeout_sec}s"
    if bin_proc.returncode != 0:
        return False, (
            f"mutated bin build failed (rc={bin_proc.returncode}): "
            f"{(bin_proc.stdout + bin_proc.stderr).strip()[:300]}"
        )
    return True, ""


def _check_one_extract_guard(
    guard: ExtractGuard,
    *,
    anneal_root: Path,
    rustc_bin: Path,
    sysroot: str,
    host_triple: str,
    deps_dirs: tuple[Path, ...],
    extern_rlibs: dict[str, Path],
    timeout_sec: int,
) -> GuardResult:
    t0 = time.monotonic()
    with tempfile.TemporaryDirectory(
        prefix=f"anneal-gmut-{guard.guard_id}-"
    ) as tmp:
        tmp_path = Path(tmp)
        env = _extract_subprocess_env(
            rustc_bin, sysroot, tmp_path, host_triple
        )
        mut_src_dir = tmp_path / "src"
        mut_err = _copy_mutated_extract_src(anneal_root, guard, mut_src_dir)
        if mut_err is not None:
            return GuardResult(
                suite="extract_guards",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=mut_err,
            )

        if guard.mode == "unit":
            mut_unit_bin = tmp_path / "mut_unit"
            ok, err = _compile_mutated_extract_unit(
                rustc_bin,
                mut_src_dir,
                mut_unit_bin,
                host_triple=host_triple,
                deps_dirs=deps_dirs,
                extern_rlibs=extern_rlibs,
                sysroot=sysroot,
                env=env,
                timeout_sec=timeout_sec,
            )
            if not ok:
                return GuardResult(
                    suite="extract_guards",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=err,
                )

            s_rc, s_out = _run_extract_unit_test(
                mut_unit_bin,
                guard.sanity_unit_test,
                work_dir=tmp_path,
                env=env,
                timeout_sec=timeout_sec,
            )
            if s_rc != 0 or "1 passed; 0 failed" not in s_out:
                return GuardResult(
                    suite="extract_guards",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=(
                        f"positive unit sanity {guard.sanity_unit_test} broke "
                        f"(rc={s_rc}): {s_out[:220]}"
                    ),
                )

            rc, out = _run_extract_unit_test(
                mut_unit_bin,
                guard.unit_test_name,
                work_dir=tmp_path,
                env=env,
                timeout_sec=timeout_sec,
            )
            if rc == 0 and "1 passed; 0 failed" in out:
                return GuardResult(
                    suite="extract_guards",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="SURVIVED",
                    duration_sec=time.monotonic() - t0,
                    detail=f"unit test {guard.unit_test_name} still passed on mutant",
                )
            if (
                rc == 101
                and f"test {guard.unit_test_name} ... FAILED" in out
                and "0 passed; 1 failed" in out
            ):
                return GuardResult(
                    suite="extract_guards",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="KILLED",
                    duration_sec=time.monotonic() - t0,
                    detail=f"unit test {guard.unit_test_name} failed as expected",
                )
            return GuardResult(
                suite="extract_guards",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=f"unexpected unit-test outcome rc={rc}: {out[:240]}",
            )

        # mode == "capture"
        mut_cap_bin = tmp_path / "mut_capture"
        ok, err = _compile_mutated_extract_capture(
            rustc_bin,
            mut_src_dir,
            tmp_path,
            mut_cap_bin,
            host_triple=host_triple,
            deps_dirs=deps_dirs,
            extern_rlibs=extern_rlibs,
            sysroot=sysroot,
            env=env,
            timeout_sec=timeout_sec,
        )
        if not ok:
            return GuardResult(
                suite="extract_guards",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=err,
            )

        sanity_scope = "crate" if guard.capture_scope == "crate" else "select"
        s_rc, s_parsed, s_out = _run_extract_capture(
            mut_cap_bin,
            EXTRACT_POSITIVE_SANITY_SOURCE,
            capture_scope=sanity_scope,
            select_root="selected",
            instantiate_json="",
            work_dir=tmp_path,
            tag="sanity",
            sysroot=sysroot,
            host_triple=host_triple,
            env=env,
            timeout_sec=timeout_sec,
        )
        if (
            s_rc != 0
            or not isinstance(s_parsed, dict)
            or s_parsed.get("status") != "captured"
        ):
            return GuardResult(
                suite="extract_guards",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"positive capture sanity broke on mutant "
                    f"(rc={s_rc}, parsed={s_parsed!r}): {s_out[:200]}"
                ),
            )

        rc, parsed, out = _run_extract_capture(
            mut_cap_bin,
            guard.negative_source,
            capture_scope=guard.capture_scope,
            select_root=guard.select_root,
            instantiate_json=guard.instantiate_json,
            allow_unstable_features=guard.allow_unstable_features,
            stdlib_crate=guard.stdlib_crate,
            work_dir=tmp_path,
            tag="neg",
            sysroot=sysroot,
            host_triple=host_triple,
            env=env,
            timeout_sec=timeout_sec,
        )
        status_field = parsed.get("status") if isinstance(parsed, dict) else None
        if rc == 0 and status_field == "captured":
            return GuardResult(
                suite="extract_guards",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="KILLED",
                duration_sec=time.monotonic() - t0,
                detail="negative capture witness flipped from unsupported to captured",
            )
        if rc == 1 and status_field == guard.expected_baseline_status:
            diag_text = (
                out
                if status_field == "compiler_failed"
                else _extract_diag_text(parsed)
            )
            if (
                not guard.expected_baseline_diagnostic
                or guard.expected_baseline_diagnostic in diag_text
            ):
                return GuardResult(
                    suite="extract_guards",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="SURVIVED",
                    duration_sec=time.monotonic() - t0,
                    detail=(
                        "mutant still rejected witness: "
                        f"{diag_text[:200]!r}"
                    ),
                )
        if (
            guard.allow_downstream_fallback
            and rc == 1
            and status_field == "unsupported"
        ):
            fallback_diag = _extract_diag_text(parsed)
            if (
                (
                    not guard.expected_baseline_diagnostic
                    or guard.expected_baseline_diagnostic not in fallback_diag
                )
                and guard.expected_fallback_diagnostic
                and guard.expected_fallback_diagnostic in fallback_diag
            ):
                return GuardResult(
                    suite="extract_guards",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="KILLED",
                    duration_sec=time.monotonic() - t0,
                    detail=(
                        "precedence guard bypassed; fell through to downstream "
                        f"refusal: {fallback_diag[:160]!r}"
                    ),
                )
        return GuardResult(
            suite="extract_guards",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=(
                f"unexpected capture result rc={rc} status={status_field!r} "
                f"out={out[:220]}"
            ),
        )


FORBIDDEN_FIXTURE_TOKENS_RE = re.compile(
    r"\b(?:sorry|admit|native_decide|ofReduceBool|axiom|unsafe)\b"
)
LEAN_CHAR_LIT_RE = re.compile(
    r"'(?:[^'\\\r\n]|\\(?:[\\\"'ntr0]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'"
)
LEAN_IMPORT_HEADER_RE = re.compile(
    r"(?:^|(?<=[\s;]))(?:(?:public|meta)\s+)*"
    r"import(?![A-Za-z0-9_'!?»])(?:\s+all(?![A-Za-z0-9_'!?»]))?"
)
_LEAN_MOD_SEGMENT_PATTERN = r"(?:«[^»\r\n]+»|[A-Za-z_][A-Za-z0-9_'!?]*)"
LEAN_IDENT_RE = re.compile(
    rf"{_LEAN_MOD_SEGMENT_PATTERN}(?:\.{_LEAN_MOD_SEGMENT_PATTERN})*"
)
_LEAN_QUOTED_SEG_RE = re.compile(r"«([^»\r\n]+)»")
LEAN_IMPORT_STOP_KEYWORDS = frozenset({
    "prelude",
    "module",
    "public",
    "meta",
    "import",
    "all",
    "theorem",
    "def",
    "lemma",
    "abbrev",
    "opaque",
    "axiom",
    "inductive",
    "structure",
    "class",
    "instance",
    "example",
    "namespace",
    "section",
    "end",
    "open",
    "export",
    "variable",
    "universe",
    "set_option",
    "attribute",
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "deriving",
    "initialize",
    "builtin_initialize",
    "macro",
    "macro_rules",
    "syntax",
    "elab",
    "elab_rules",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "mutual",
    "reducible",
    "scoped",
    "local",
    "sorry",
    "admit",
    "native_decide",
    "ofReduceBool",
    "run_cmd",
    "eval",
    "check",
    "print",
    "reduce",
    "guard_msgs",
    "unseal",
    "seal",
    "irreducible_def",
})


def _strip_lean_comments_and_strings(text: str) -> str:
    """Strip Lean comments, string literals, and char literals for linting."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_str = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                if block_depth == 0:
                    out.append(" ")
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if in_str:
            if ch == "\\" and i + 1 < n:
                if text[i + 1] == "\n":
                    out.append("\n")
                i += 2
                continue
            if ch == '"':
                in_str = False
                out.append(" ")
            elif ch == "\n":
                out.append("\n")
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch == "r" and (
            i == 0
            or not (text[i - 1].isalnum() or text[i - 1] in ("_", "'", "»"))
        ):
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            if j < n and text[j] == '"':
                close_seq = '"' + ("#" * (j - (i + 1)))
                k = j + 1
                while k < n:
                    if text.startswith(close_seq, k):
                        out.append(" ")
                        i = k + len(close_seq)
                        break
                    if text[k] == "\n":
                        out.append("\n")
                    k += 1
                else:
                    i = n
                continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch == "'" and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in ("_", "'"))
        ):
            m_char = LEAN_CHAR_LIT_RE.match(text, i)
            if m_char is not None:
                out.append(" ")
                i = m_char.end()
                continue
        out.append(ch)
        i += 1
    return "".join(out)


def _find_forbidden_fixture_tokens(text: str) -> list[str]:
    cleaned = _strip_lean_comments_and_strings(text)
    return sorted(set(FORBIDDEN_FIXTURE_TOKENS_RE.findall(cleaned)))


def _normalize_lean_module_token(raw_tok: str) -> str:
    """Strip Lean guillemet quotes (`«...»`) from module name segments."""
    return _LEAN_QUOTED_SEG_RE.sub(r"\1", raw_tok)


def _extract_lean_imports(text: str) -> list[str]:
    """Extract imported Lean modules across multiline/`public`/`meta`/`all`.

    Parses both plain identifiers and guillemet-quoted (`«...»`) hierarchical
    segments and raises `ValueError` fail-closed if an `import` clause contains
    an unrecognized or unclosed token.
    """
    cleaned = _strip_lean_comments_and_strings(text)
    cleaned = cleaned.replace("\r\n", "\n").replace("\r", "\n")
    imports: list[str] = []
    n = len(cleaned)
    pos = 0
    while pos < n:
        m = LEAN_IMPORT_HEADER_RE.search(cleaned, pos)
        if m is None:
            break
        cur = m.end()
        pos = cur
        if cur >= n or not cleaned[cur].isspace():
            raise ValueError(
                f"unrecognized Lean import syntax near "
                f"{cleaned[m.start():m.end() + 24]!r}"
            )
        parsed_any = False
        while True:
            while cur < n and cleaned[cur].isspace():
                cur += 1
            if cur >= n or cleaned[cur] == ";":
                break
            if parsed_any and cleaned[cur] in ("#", "@"):
                break
            tok = LEAN_IDENT_RE.match(cleaned, cur)
            if tok is None:
                raise ValueError(
                    f"unrecognized Lean import token near {cleaned[cur:cur + 40]!r}"
                )
            raw_mod = tok.group(0)
            end = tok.end()
            if end < n and not (
                cleaned[end].isspace() or cleaned[end] == ";"
            ):
                raise ValueError(
                    f"unrecognized Lean import token near {cleaned[cur:end + 24]!r}"
                )
            if (
                "." not in raw_mod
                and "«" not in raw_mod
                and raw_mod in LEAN_IMPORT_STOP_KEYWORDS
            ):
                break
            imports.append(_normalize_lean_module_token(raw_mod))
            parsed_any = True
            pos = end
            cur = end
        if not parsed_any:
            raise ValueError(
                f"import clause yielded no module name near "
                f"{cleaned[m.start():m.start() + 40]!r}"
            )
    return imports


def _compute_true_semantics_downstream(
    trusted_lean_dir: Path,
) -> dict[str, set[str]]:
    """Compute true transitive downstream closure across `SEMANTICS_MODULES`."""
    sem_set = set(SEMANTICS_MODULES)
    direct_importers: dict[str, set[str]] = {m: set() for m in SEMANTICS_MODULES}
    for mod in SEMANTICS_MODULES:
        mod_path = trusted_lean_dir / f"{mod}.lean"
        if not mod_path.is_file():
            continue
        for mod_tok in _extract_lean_imports(
            mod_path.read_text(encoding="utf-8")
        ):
            imp = mod_tok.replace(".", "/")
            if imp in sem_set:
                direct_importers[imp].add(mod)
    closure: dict[str, set[str]] = {}
    for mod in SEMANTICS_MODULES:
        visited = {mod}
        stack = [mod]
        while stack:
            cur = stack.pop()
            for nxt in direct_importers.get(cur, ()):
                if nxt not in visited:
                    visited.add(nxt)
                    stack.append(nxt)
        closure[mod] = visited
    return closure


def _collect_fixture_semantics_imports(
    fixtures_dir: Path,
    mod: str,
    cache: dict[str, set[str]],
) -> set[str]:
    """Return all `Trusted/MirSemantics/*` modules transitively imported."""
    if mod in cache:
        return cache[mod]
    sem_set = set(SEMANTICS_MODULES)
    found: set[str] = set()
    cache[mod] = found
    path = fixtures_dir / f"{mod}.lean"
    if not path.is_file():
        return found
    for mod_tok in _extract_lean_imports(path.read_text(encoding="utf-8")):
        imp_slash = mod_tok.replace(".", "/")
        if imp_slash in sem_set:
            found.add(imp_slash)
        elif (fixtures_dir / f"{imp_slash}.lean").is_file():
            found.update(
                _collect_fixture_semantics_imports(
                    fixtures_dir, imp_slash, cache
                )
            )
    cache[mod] = found
    return found


def validate_catalog_invariants(
    anneal_root: Path,
    *,
    lean_only: bool = False,
) -> list[str]:
    """Check static catalog invariants without invoking Lean or rustc.

    When `lean_only` is True (used by `ci-core` Lean-only sandboxes that omit
    `trusted/rustc-capture/src/`), metadata invariants across all four suites
    and source anchors across the three Lean suites are checked without reading
    `trusted/rustc-capture/src/*.rs`.

    Returns a list of error strings (empty when all invariants hold).
    """
    errors: list[str] = []
    seen_ids: set[str] = set()
    fixtures_dir = anneal_root / "ci/fixtures/guard_mutation"
    trusted_lean_dir = anneal_root / "trusted/lean"
    semantics_dir = trusted_lean_dir / "Trusted/MirSemantics"
    if semantics_dir.is_dir():
        discovered_sem = {
            f"Trusted/MirSemantics/{p.stem}"
            for p in semantics_dir.glob("*.lean")
        }
        overlap = set(SEMANTICS_MODULES) & set(NON_GUARD_SEMANTICS_MODULES)
        if overlap:
            errors.append(
                "SEMANTICS_MODULES and NON_GUARD_SEMANTICS_MODULES overlap: "
                f"{sorted(overlap)}"
            )
        missing_exclusions = (
            set(NON_GUARD_SEMANTICS_MODULES) - discovered_sem
        )
        if missing_exclusions:
            errors.append(
                "NON_GUARD_SEMANTICS_MODULES references missing file(s): "
                f"{sorted(missing_exclusions)}"
            )
        uncovered_dir_mods = (
            discovered_sem
            - set(SEMANTICS_MODULES)
            - set(NON_GUARD_SEMANTICS_MODULES)
        )
        if uncovered_dir_mods:
            errors.append(
                "Trusted/MirSemantics/ has modules outside SEMANTICS_MODULES "
                f"and NON_GUARD_SEMANTICS_MODULES: {sorted(uncovered_dir_mods)}"
            )
    try:
        true_downstream = _compute_true_semantics_downstream(trusted_lean_dir)
    except ValueError as exc:
        errors.append(str(exc))
        true_downstream = {}
    fixture_import_cache: dict[str, set[str]] = {}
    checked_fixture_files: set[Path] = set()
    for helper in FIXTURE_HELPERS_END_TO_END:
        hp = fixtures_dir / f"{helper}.lean"
        if hp.is_file():
            checked_fixture_files.add(hp)
            bad_toks = _find_forbidden_fixture_tokens(
                hp.read_text(encoding="utf-8")
            )
            if bad_toks:
                errors.append(
                    f"{helper}.lean: forbidden fixture tokens {bad_toks}"
                )

    for guard in MIR_SEMANTICS_GUARDS:
        if guard.guard_id in seen_ids:
            errors.append(f"duplicate guard_id: {guard.guard_id}")
        seen_ids.add(guard.guard_id)
        if guard.target_module not in SEMANTICS_DOWNSTREAM:
            errors.append(
                f"{guard.guard_id}: unknown target_module {guard.target_module}"
            )
        target_path = anneal_root / guard.target_file
        if not target_path.is_file():
            errors.append(f"{guard.guard_id}: missing target_file {target_path}")
        else:
            text = target_path.read_text(encoding="utf-8")
            try:
                apply_single_guard_mutation(
                    text, guard.anchor, guard.replacement, guard_id=guard.guard_id
                )
            except ValueError as exc:
                errors.append(str(exc))
        fixture_path = fixtures_dir / f"{guard.fixture_module}.lean"
        if not fixture_path.is_file():
            errors.append(
                f"{guard.guard_id}: missing fixture_module {fixture_path}"
            )
        else:
            ftext = fixture_path.read_text(encoding="utf-8")
            if fixture_path not in checked_fixture_files:
                checked_fixture_files.add(fixture_path)
                bad_toks = _find_forbidden_fixture_tokens(ftext)
                if bad_toks:
                    errors.append(
                        f"{guard.fixture_module}.lean: forbidden fixture "
                        f"tokens {bad_toks}"
                    )
            try:
                find_theorem_line_span(ftext, guard.theorem_name)
            except ValueError as exc:
                errors.append(f"{guard.guard_id}: {exc}")

        sanity_path = fixtures_dir / f"{guard.sanity_module}.lean"
        if not sanity_path.is_file():
            errors.append(
                f"{guard.guard_id}: missing sanity_module {sanity_path}"
            )
        elif sanity_path not in checked_fixture_files:
            checked_fixture_files.add(sanity_path)
            bad_toks = _find_forbidden_fixture_tokens(
                sanity_path.read_text(encoding="utf-8")
            )
            if bad_toks:
                errors.append(
                    f"{guard.sanity_module}.lean: forbidden fixture "
                    f"tokens {bad_toks}"
                )

        if guard.target_module in SEMANTICS_DOWNSTREAM:
            rebuilt = set(SEMANTICS_DOWNSTREAM[guard.target_module])
            omitted_downstream = (
                true_downstream.get(guard.target_module, set()) - rebuilt
            )
            for mod_label, mod_name in (
                ("fixture_module", guard.fixture_module),
                ("sanity_module", guard.sanity_module),
            ):
                try:
                    trans_imps = _collect_fixture_semantics_imports(
                        fixtures_dir, mod_name, fixture_import_cache
                    )
                except ValueError as exc:
                    errors.append(
                        f"{guard.guard_id}: {mod_label} {mod_name}: {exc}"
                    )
                    continue
                stale_imps = sorted(trans_imps & omitted_downstream)
                if stale_imps:
                    errors.append(
                        f"{guard.guard_id}: {mod_label} {mod_name} "
                        f"transitively imports {stale_imps} outside "
                        f"SEMANTICS_DOWNSTREAM[{guard.target_module!r}]"
                    )

    for guard in (*AUDIT_HEADER_GUARDS, *AUDIT_BOUNDARY_GUARDS):
        if guard.guard_id in seen_ids:
            errors.append(f"duplicate guard_id: {guard.guard_id}")
        seen_ids.add(guard.guard_id)
        if isinstance(guard, AuditBoundaryGuard):
            if guard.mode == "spec-preflight":
                if guard.fixture_id not in VALID_SPEC_BOUNDARY_FIXTURE_IDS:
                    errors.append(
                        f"{guard.guard_id}: unknown spec-preflight fixture_id "
                        f"{guard.fixture_id!r}"
                    )
            elif guard.mode == "target-audit":
                if guard.fixture_id not in VALID_TARGET_BOUNDARY_FIXTURE_IDS:
                    errors.append(
                        f"{guard.guard_id}: unknown target-audit fixture_id "
                        f"{guard.fixture_id!r}"
                    )
            else:
                errors.append(f"{guard.guard_id}: invalid mode {guard.mode!r}")
        target_path = anneal_root / guard.target_file
        if not target_path.is_file():
            errors.append(f"{guard.guard_id}: missing target_file {target_path}")
        else:
            text = target_path.read_text(encoding="utf-8")
            try:
                apply_single_guard_mutation(
                    text, guard.anchor, guard.replacement, guard_id=guard.guard_id
                )
            except ValueError as exc:
                errors.append(str(exc))

    for guard in EXTRACT_GUARDS:
        if guard.guard_id in seen_ids:
            errors.append(f"duplicate guard_id: {guard.guard_id}")
        seen_ids.add(guard.guard_id)
        if guard.mode not in ("capture", "unit"):
            errors.append(f"{guard.guard_id}: invalid mode {guard.mode!r}")
        elif guard.mode == "unit":
            if not guard.unit_test_name:
                errors.append(f"{guard.guard_id}: missing unit_test_name")
        else:
            if not guard.negative_source.strip():
                errors.append(f"{guard.guard_id}: missing negative_source")
            if guard.capture_scope not in ("select", "crate", "instantiate"):
                errors.append(
                    f"{guard.guard_id}: invalid capture_scope {guard.capture_scope!r}"
                )
            if guard.expected_baseline_status not in (
                "unsupported",
                "compiler_failed",
            ):
                errors.append(
                    f"{guard.guard_id}: invalid expected_baseline_status "
                    f"{guard.expected_baseline_status!r}"
                )
            if guard.capture_scope == "instantiate" and not guard.instantiate_json:
                errors.append(f"{guard.guard_id}: missing instantiate_json")
            if guard.stdlib_crate not in ("", "core"):
                errors.append(
                    f"{guard.guard_id}: invalid stdlib_crate {guard.stdlib_crate!r}"
                )
            if guard.stdlib_crate and guard.allow_unstable_features:
                errors.append(
                    f"{guard.guard_id}: stdlib_crate and allow_unstable_features "
                    "are mutually exclusive"
                )
            if guard.allow_unstable_features and (
                guard.allow_unstable_features
                != tuple(sorted(set(guard.allow_unstable_features)))
                or any(
                    not re.fullmatch(r"[a-z][a-z0-9_]*", f)
                    for f in guard.allow_unstable_features
                )
            ):
                errors.append(
                    f"{guard.guard_id}: invalid or unsorted "
                    f"allow_unstable_features {guard.allow_unstable_features!r}"
                )
            if guard.allow_downstream_fallback and (
                not guard.expected_baseline_diagnostic
                or not guard.expected_fallback_diagnostic
            ):
                errors.append(
                    f"{guard.guard_id}: allow_downstream_fallback requires "
                    "expected_baseline_diagnostic and "
                    "expected_fallback_diagnostic"
                )
        if not lean_only:
            target_path = anneal_root / guard.target_file
            if not target_path.is_file():
                errors.append(
                    f"{guard.guard_id}: missing target_file {target_path}"
                )
            else:
                text = target_path.read_text(encoding="utf-8")
                try:
                    apply_single_guard_mutation(
                        text,
                        guard.anchor,
                        guard.replacement,
                        guard_id=guard.guard_id,
                    )
                except ValueError as exc:
                    errors.append(str(exc))

    return errors


def _select_guards(
    suite: str,
    name_filter: str | None,
) -> tuple[
    list[MirSemanticsGuard],
    list[AuditHeaderGuard],
    list[AuditBoundaryGuard],
    list[ExtractGuard],
]:
    mir_guards = (
        list(MIR_SEMANTICS_GUARDS)
        if suite in ("all", "mir_semantics")
        else []
    )
    audit_guards = (
        list(AUDIT_HEADER_GUARDS)
        if suite in ("all", "audit_headers")
        else []
    )
    boundary_guards = (
        list(AUDIT_BOUNDARY_GUARDS)
        if suite in ("all", "audit_boundary")
        else []
    )
    extract_guards = (
        list(EXTRACT_GUARDS)
        if suite in ("all", "extract_guards")
        else []
    )
    if name_filter:
        mir_guards = [g for g in mir_guards if name_filter in g.guard_id]
        audit_guards = [g for g in audit_guards if name_filter in g.guard_id]
        boundary_guards = [
            g for g in boundary_guards if name_filter in g.guard_id
        ]
        extract_guards = [
            g for g in extract_guards if name_filter in g.guard_id
        ]
    return mir_guards, audit_guards, boundary_guards, extract_guards


def run_guard_mutation_suite(
    *,
    anneal_root: Path,
    lean_bin: Path | None,
    rustc_bin: str | Path | None = None,
    suite: str = "all",
    lean_only: bool = False,
    name_filter: str | None = None,
    jobs: int = 4,
    timeout_sec: int = 60,
) -> dict[str, object]:
    """Run baseline verification and all selected single-guard mutations."""
    t_start = time.monotonic()
    if lean_only and suite == "extract_guards":
        raise RuntimeError(
            "--lean-only cannot be combined with --suite extract_guards"
        )
    anneal_root = Path(os.path.abspath(anneal_root))
    if lean_bin is not None:
        lean_bin = Path(os.path.abspath(lean_bin))
    catalog_errors = validate_catalog_invariants(
        anneal_root, lean_only=lean_only
    )
    if catalog_errors:
        raise RuntimeError(
            "guard catalog validation failed:\n  - "
            + "\n  - ".join(catalog_errors)
        )

    mir_guards, audit_guards, boundary_guards, extract_guards = _select_guards(
        suite, name_filter
    )
    need_lean = bool(mir_guards or audit_guards or boundary_guards)
    if lean_only and not need_lean:
        raise RuntimeError(
            f"no Lean guards matched suite={suite!r} filter={name_filter!r} "
            "under --lean-only"
        )
    if not need_lean and not extract_guards:
        raise RuntimeError(
            f"no guards matched suite={suite!r} filter={name_filter!r}"
        )

    if need_lean and lean_bin is None:
        raise RuntimeError(
            "Lean binary is required for mir_semantics / audit_* suites"
        )

    trusted_lean_dir = anneal_root / "trusted/lean"
    fixtures_dir = anneal_root / "ci/fixtures/guard_mutation"
    results: list[GuardResult] = []
    skipped_suites: list[str] = []
    baseline_sec = 0.0

    with tempfile.TemporaryDirectory(prefix="anneal-gmut-base-") as base_tmp:
        base_path = Path(base_tmp)
        base_olean_dir = base_path / "olean"
        base_olean_dir.mkdir()

        # --------------------------------------------------------------
        # Suite 1: Trusted/MirSemantics/ baseline + mutants
        # --------------------------------------------------------------
        if mir_guards:
            assert lean_bin is not None
            t_base = time.monotonic()
            for mod in (*BASE_TRUSTED_MODULES, *SEMANTICS_MODULES):
                res = _compile_module(
                    lean_bin,
                    trusted_lean_dir,
                    mod,
                    base_olean_dir,
                    lean_path=[base_olean_dir],
                    timeout_sec=timeout_sec,
                )
                if res.returncode != 0:
                    raise RuntimeError(
                        f"baseline trusted module {mod} failed to compile:\n"
                        f"{res.stdout}\n{res.stderr}"
                    )

            # Verify baseline helpers, positive sanity checks, and every
            # negative refutation module pass cleanly on unmodified TCB.
            needed_fixtures = sorted({g.fixture_module for g in mir_guards})
            needed_sanity = sorted({g.sanity_module for g in mir_guards})
            baseline_fixture_mods: list[str] = [
                *FIXTURE_HELPERS_END_TO_END,
                *needed_sanity,
                *needed_fixtures,
            ]
            for mod in baseline_fixture_mods:
                f_src = (fixtures_dir / f"{mod}.lean").read_text(
                    encoding="utf-8"
                )
                bad_toks = _find_forbidden_fixture_tokens(f_src)
                if bad_toks:
                    raise RuntimeError(
                        f"baseline fixture {mod}.lean contains forbidden "
                        f"tokens: {bad_toks}"
                    )
                res = _compile_module(
                    lean_bin,
                    fixtures_dir,
                    mod,
                    base_olean_dir,
                    lean_path=[base_olean_dir],
                    timeout_sec=timeout_sec,
                )
                combined = res.stdout + "\n" + res.stderr
                if res.returncode != 0 or "uses 'sorry'" in combined:
                    raise RuntimeError(
                        f"baseline fixture {mod} failed on unmodified TCB "
                        f"(rc={res.returncode}):\n{combined}"
                    )
            baseline_sec += time.monotonic() - t_base

            worker_count = max(1, min(jobs, len(mir_guards)))
            with ThreadPoolExecutor(max_workers=worker_count) as pool:
                future_map = {
                    pool.submit(
                        _check_one_mir_guard,
                        guard,
                        anneal_root=anneal_root,
                        lean_bin=lean_bin,
                        base_olean_dir=base_olean_dir,
                        fixtures_dir=fixtures_dir,
                        timeout_sec=timeout_sec,
                    ): guard
                    for guard in mir_guards
                }
                mir_by_id: dict[str, GuardResult] = {}
                for fut in as_completed(future_map):
                    res = fut.result()
                    mir_by_id[res.guard_id] = res
            results.extend(mir_by_id[g.guard_id] for g in mir_guards)

        # --------------------------------------------------------------
        # Suite 2 & 3: Audit header and boundary guards
        # --------------------------------------------------------------
        if audit_guards or boundary_guards:
            assert lean_bin is not None
            t_audit_base = time.monotonic()
            sysroot = _query_lean_sysroot(lean_bin, timeout_sec)
            tb_olean_dir = base_path / "tb_olean"
            tb_olean_dir.mkdir()
            tb_src_dir = anneal_root / "trusted/audit"
            compiled_mods: set[str] = set()
            for guard in audit_guards:
                mod_name = Path(guard.target_file).stem
                if mod_name not in compiled_mods:
                    comp = _compile_module(
                        lean_bin,
                        tb_src_dir,
                        mod_name,
                        tb_olean_dir,
                        lean_path=[],
                        timeout_sec=timeout_sec,
                    )
                    if comp.returncode != 0:
                        raise RuntimeError(
                            f"baseline {Path(guard.target_file).name} failed to compile:\n"
                            f"{comp.stdout}\n{comp.stderr}"
                        )
                    compiled_mods.add(mod_name)
                check_dir = base_path / f"base_{guard.guard_id}"
                check_dir.mkdir()
                rc, parsed, out = _run_audit_headers(
                    lean_bin,
                    tb_olean_dir,
                    sysroot,
                    guard.negative_source,
                    check_dir,
                    module_name=mod_name,
                    timeout_sec=timeout_sec,
                )
                if not (
                    rc == 1
                    and isinstance(parsed, dict)
                    and parsed.get("ok") is False
                    and parsed.get("category") == "policy"
                ):
                    raise RuntimeError(
                        f"baseline {mod_name} did not policy-reject "
                        f"{guard.guard_id}: rc={rc} parsed={parsed!r} out={out}"
                    )

            spec_reqs: dict[str, dict[str, object]] = {}
            target_reqs: dict[str, dict[str, object]] = {}
            if boundary_guards:
                if "TrustedBoundary" not in compiled_mods:
                    comp = _compile_module(
                        lean_bin,
                        tb_src_dir,
                        "TrustedBoundary",
                        tb_olean_dir,
                        lean_path=[],
                        timeout_sec=timeout_sec,
                    )
                    if comp.returncode != 0:
                        raise RuntimeError(
                            "baseline TrustedBoundary.lean failed to compile:\n"
                            f"{comp.stdout}\n{comp.stderr}"
                        )
                    compiled_mods.add("TrustedBoundary")
                fixtures_root = base_path / "boundary_fixtures"
                fixtures_root.mkdir()
                spec_reqs, target_reqs = _build_boundary_fixtures(
                    anneal_root=anneal_root,
                    lean_bin=lean_bin,
                    tb_olean_dir=tb_olean_dir,
                    sysroot=sysroot,
                    fixtures_root=fixtures_root,
                    timeout_sec=timeout_sec,
                )
                for sanity_name, sanity_req in (
                    ("spec_sanity", spec_reqs["spec_sanity"]),
                    ("target_sanity", target_reqs["target_sanity"]),
                ):
                    s_dir = base_path / f"base_{sanity_name}"
                    s_dir.mkdir()
                    s_rc, s_parsed, s_out = _run_tb_request(
                        lean_bin,
                        tb_olean_dir,
                        sanity_req,
                        s_dir,
                        tag=sanity_name,
                        timeout_sec=timeout_sec,
                    )
                    if (
                        s_rc != 0
                        or not isinstance(s_parsed, dict)
                        or s_parsed.get("ok") is not True
                    ):
                        raise RuntimeError(
                            f"baseline boundary sanity {sanity_name} failed: "
                            f"rc={s_rc} parsed={s_parsed!r} out={s_out}"
                        )
                for guard in boundary_guards:
                    req_map = (
                        spec_reqs
                        if guard.mode == "spec-preflight"
                        else target_reqs
                    )
                    neg_req = req_map[guard.fixture_id]
                    b_dir = base_path / f"base_{guard.guard_id}"
                    b_dir.mkdir()
                    rc, parsed, out = _run_tb_request(
                        lean_bin,
                        tb_olean_dir,
                        neg_req,
                        b_dir,
                        tag="base_neg",
                        timeout_sec=timeout_sec,
                    )
                    if not (
                        rc == 1
                        and isinstance(parsed, dict)
                        and parsed.get("ok") is False
                        and parsed.get("category") == "policy"
                    ):
                        raise RuntimeError(
                            f"baseline TrustedBoundary did not policy-reject "
                            f"{guard.guard_id}: rc={rc} parsed={parsed!r} "
                            f"out={out}"
                        )
            baseline_sec += time.monotonic() - t_audit_base

            # Cap concurrent `TrustedBoundary.lean` compilations to 2 workers
            # to keep peak memory bounded on 4-vCPU CI runners.
            total_tb = len(audit_guards) + len(boundary_guards)
            audit_workers = max(1, min(jobs, 2, total_tb))
            with ThreadPoolExecutor(max_workers=audit_workers) as pool:
                if audit_guards:
                    future_map = {
                        pool.submit(
                            _check_one_audit_guard,
                            guard,
                            anneal_root=anneal_root,
                            lean_bin=lean_bin,
                            sysroot=sysroot,
                            timeout_sec=timeout_sec,
                        ): guard
                        for guard in audit_guards
                    }
                    audit_by_id: dict[str, GuardResult] = {}
                    for fut in as_completed(future_map):
                        res = fut.result()
                        audit_by_id[res.guard_id] = res
                    results.extend(audit_by_id[g.guard_id] for g in audit_guards)
                if boundary_guards:
                    b_future_map = {
                        pool.submit(
                            _check_one_boundary_guard,
                            guard,
                            anneal_root=anneal_root,
                            lean_bin=lean_bin,
                            sanity_req=(
                                spec_reqs["spec_sanity"]
                                if guard.mode == "spec-preflight"
                                else target_reqs["target_sanity"]
                            ),
                            negative_req=(
                                spec_reqs[guard.fixture_id]
                                if guard.mode == "spec-preflight"
                                else target_reqs[guard.fixture_id]
                            ),
                            timeout_sec=timeout_sec,
                        ): guard
                        for guard in boundary_guards
                    }
                    boundary_by_id: dict[str, GuardResult] = {}
                    for fut in as_completed(b_future_map):
                        res = fut.result()
                        boundary_by_id[res.guard_id] = res
                    results.extend(
                        boundary_by_id[g.guard_id] for g in boundary_guards
                    )

        # --------------------------------------------------------------
        # Suite 4: trusted/rustc-capture/src/ extraction & profile guards
        # --------------------------------------------------------------
        if extract_guards:
            if lean_only:
                print(
                    "NOTE: skipping extract_guards suite (--lean-only "
                    "requested)",
                    file=sys.stderr,
                )
                skipped_suites.append("extract_guards")
                toolchain = None
            else:
                toolchain = _resolve_extract_toolchain(
                    anneal_root, rustc_bin, timeout_sec
                )
                if toolchain is None:
                    if (
                        suite == "extract_guards"
                        or rustc_bin is not None
                        or not need_lean
                    ):
                        raise RuntimeError(
                            "pinned nightly rustc with rustc-dev (matching "
                            "trusted/rustc-capture/src/ir.rs COMPILER_COMMIT) "
                            "and cargo on an x86_64-unknown-linux-gnu host "
                            "are required for extract_guards; pass --rustc "
                            "<path> or set RUSTC"
                        )
                    print(
                        "NOTE: skipping extract_guards suite (pinned "
                        "x86_64-unknown-linux-gnu nightly rustc with "
                        "rustc-dev not available in environment)",
                        file=sys.stderr,
                    )
                    skipped_suites.append("extract_guards")
            if toolchain is not None:
                r_bin, c_bin, r_sysroot, host_triple = toolchain
                t_ext_base = time.monotonic()
                need_capture = any(g.mode == "capture" for g in extract_guards)
                need_unit = any(g.mode == "unit" for g in extract_guards)
                base_target_dir = base_path / "extract_target"
                cap_bin, unit_bin, deps_dirs, extern_rlibs = (
                    _build_extract_baseline(
                        anneal_root=anneal_root,
                        rustc_bin=r_bin,
                        cargo_bin=c_bin,
                        sysroot=r_sysroot,
                        host_triple=host_triple,
                        base_target_dir=base_target_dir,
                        need_capture=need_capture,
                        need_unit=need_unit,
                        timeout_sec=timeout_sec,
                    )
                )
                ext_env = _extract_subprocess_env(
                    r_bin, r_sysroot, base_target_dir, host_triple
                )

                if need_unit:
                    assert unit_bin is not None
                    needed_tests = sorted(
                        {
                            t
                            for g in extract_guards
                            if g.mode == "unit"
                            for t in (g.sanity_unit_test, g.unit_test_name)
                        }
                    )
                    for test_name in needed_tests:
                        u_rc, u_out = _run_extract_unit_test(
                            unit_bin,
                            test_name,
                            work_dir=base_target_dir,
                            env=ext_env,
                            timeout_sec=timeout_sec,
                        )
                        if u_rc != 0 or "1 passed; 0 failed" not in u_out:
                            raise RuntimeError(
                                f"baseline rustc-capture unit test {test_name} "
                                f"failed (rc={u_rc}):\n{u_out[-500:]}"
                            )

                if need_capture:
                    assert cap_bin is not None
                    ext_base_work = base_path / "extract_base_work"
                    ext_base_work.mkdir()
                    for s_scope in sorted(
                        {
                            "crate" if g.capture_scope == "crate" else "select"
                            for g in extract_guards
                            if g.mode == "capture"
                        }
                    ):
                        s_rc, s_parsed, s_out = _run_extract_capture(
                            cap_bin,
                            EXTRACT_POSITIVE_SANITY_SOURCE,
                            capture_scope=s_scope,
                            select_root="selected",
                            instantiate_json="",
                            work_dir=ext_base_work,
                            tag=f"sanity_{s_scope}",
                            sysroot=r_sysroot,
                            host_triple=host_triple,
                            env=ext_env,
                            timeout_sec=timeout_sec,
                        )
                        if (
                            s_rc != 0
                            or not isinstance(s_parsed, dict)
                            or s_parsed.get("status") != "captured"
                        ):
                            raise RuntimeError(
                                f"baseline capture sanity ({s_scope}) failed "
                                f"(rc={s_rc}, parsed={s_parsed!r}):\n"
                                f"{s_out[-400:]}"
                            )
                    capture_guards = [
                        g for g in extract_guards if g.mode == "capture"
                    ]
                    base_workers = max(1, min(jobs, len(capture_guards)))

                    def _verify_base_capture(guard: ExtractGuard) -> None:
                        b_rc, b_parsed, b_out = _run_extract_capture(
                            cap_bin,
                            guard.negative_source,
                            capture_scope=guard.capture_scope,
                            select_root=guard.select_root,
                            instantiate_json=guard.instantiate_json,
                            allow_unstable_features=guard.allow_unstable_features,
                            stdlib_crate=guard.stdlib_crate,
                            work_dir=ext_base_work,
                            tag=f"neg_{guard.guard_id}",
                            sysroot=r_sysroot,
                            host_triple=host_triple,
                            env=ext_env,
                            timeout_sec=timeout_sec,
                        )
                        b_status = (
                            b_parsed.get("status")
                            if isinstance(b_parsed, dict)
                            else None
                        )
                        b_diag = _extract_diag_text(b_parsed)
                        if b_rc != 1 or b_status != guard.expected_baseline_status:
                            raise RuntimeError(
                                f"baseline anneal-rustc-capture did not "
                                f"reject {guard.guard_id} with exit code 1 "
                                f"and status "
                                f"{guard.expected_baseline_status!r} "
                                f"(rc={b_rc}, status={b_status!r}):\n"
                                f"{b_out[-400:]}"
                            )
                        diag_haystack = (
                            b_out
                            if guard.expected_baseline_status == "compiler_failed"
                            else b_diag
                        )
                        if (
                            guard.expected_baseline_diagnostic
                            and guard.expected_baseline_diagnostic
                            not in diag_haystack
                        ):
                            raise RuntimeError(
                                f"baseline rejection for {guard.guard_id} "
                                f"lacked expected diagnostic "
                                f"{guard.expected_baseline_diagnostic!r}; "
                                f"got: {diag_haystack[:300]!r}"
                            )

                    with ThreadPoolExecutor(max_workers=base_workers) as pool:
                        futs = [
                            pool.submit(_verify_base_capture, g)
                            for g in capture_guards
                        ]
                        for fut in as_completed(futs):
                            fut.result()
                baseline_sec += time.monotonic() - t_ext_base

                ext_workers = max(1, min(jobs, len(extract_guards)))
                with ThreadPoolExecutor(max_workers=ext_workers) as pool:
                    e_future_map = {
                        pool.submit(
                            _check_one_extract_guard,
                            guard,
                            anneal_root=anneal_root,
                            rustc_bin=r_bin,
                            sysroot=r_sysroot,
                            host_triple=host_triple,
                            deps_dirs=deps_dirs,
                            extern_rlibs=extern_rlibs,
                            timeout_sec=timeout_sec,
                        ): guard
                        for guard in extract_guards
                    }
                    ext_by_id: dict[str, GuardResult] = {}
                    for fut in as_completed(e_future_map):
                        res = fut.result()
                        ext_by_id[res.guard_id] = res
                results.extend(ext_by_id[g.guard_id] for g in extract_guards)

    total = len(results)
    killed = sum(1 for r in results if r.status == "KILLED")
    survived = sum(1 for r in results if r.status == "SURVIVED")
    errors = sum(1 for r in results if r.status == "ERROR")
    return {
        "total": total,
        "killed": killed,
        "survived": survived,
        "errors": errors,
        "kill_rate_pct": (100.0 * killed / total) if total else 0.0,
        "baseline_sec": round(baseline_sec, 3),
        "total_sec": round(time.monotonic() - t_start, 3),
        "skipped_suites": skipped_suites,
        "skipped_reason": (
            "--lean-only requested"
            if lean_only and skipped_suites
            else ("toolchain unavailable" if skipped_suites else None)
        ),
        "results": [asdict(r) for r in results],
    }


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _resolve_lean_binary(explicit: str | Path | None) -> Path:
    if explicit is not None:
        cand = _resolve_executable_token(explicit)
        if cand is None:
            raise SystemExit(f"Lean binary not found: {explicit}")
        return cand
    env_lean = os.environ.get("ANNEAL_LEAN")
    if env_lean:
        cand = _resolve_executable_token(env_lean)
        if cand is not None:
            return cand
    found = shutil.which("lean")
    if found:
        return Path(os.path.abspath(found))
    raise SystemExit(
        "Lean binary not specified; pass --lean <path> or set ANNEAL_LEAN"
    )


def _format_summary(report: dict[str, object]) -> str:
    lines: list[str] = []
    for entry in report["results"]:  # type: ignore[index]
        lines.append(
            f"[{entry['status']:8s}] ({entry['suite']:14s}) "
            f"{entry['guard_id']:42s} {entry['duration_sec']:5.2f}s  "
            f"{entry['detail']}"
        )
    skipped = report.get("skipped_suites")
    if isinstance(skipped, list) and skipped:
        reason = report.get("skipped_reason") or "toolchain unavailable"
        lines.append(f"Skipped suites ({reason}): {', '.join(skipped)}")
    lines.append(
        f"Guard-mutation summary: {report['killed']}/{report['total']} killed "
        f"({report['kill_rate_pct']:.1f}%), {report['survived']} survived, "
        f"{report['errors']} errors "
        f"(baseline {report['baseline_sec']:.2f}s, total {report['total_sec']:.2f}s)"
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run single-guard mutation checks against Trusted/MirSemantics/, "
            "TrustedBoundary.lean, and trusted/rustc-capture/src/."
        )
    )
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=_default_anneal_root(),
        help="Path to the `anneal/` directory (defaults to script parent).",
    )
    parser.add_argument(
        "--lean",
        type=str,
        default=None,
        help="Path to the pinned `lean` executable (falls back to ANNEAL_LEAN / PATH).",
    )
    parser.add_argument(
        "--rustc",
        type=str,
        default=None,
        help=(
            "Path to the pinned nightly `rustc` with `rustc-dev` for "
            "extract_guards (falls back to RUSTC / PATH)."
        ),
    )
    parser.add_argument(
        "--suite",
        choices=(
            "all",
            "mir_semantics",
            "audit_headers",
            "audit_boundary",
            "extract_guards",
        ),
        default="all",
        help="Which guard-mutation suite(s) to execute.",
    )
    parser.add_argument(
        "--filter",
        dest="name_filter",
        default=None,
        help="Optional substring filter on guard_id.",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="Maximum parallel worker threads (default: min(4, CPU count)).",
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=60,
        help="Per-invocation timeout in seconds (default: 60).",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Optional file path to write the structured JSON report.",
    )
    parser.add_argument(
        "--lean-only",
        action="store_true",
        help=(
            "Execute only the Lean suites (mir_semantics, audit_headers, "
            "audit_boundary) without probing rustc or reading "
            "trusted/rustc-capture/src/."
        ),
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="Validate static catalog invariants, list all guards, and exit.",
    )
    args = parser.parse_args(argv)
    anneal_root = Path(os.path.abspath(args.anneal_root))
    json_out = (
        Path(os.path.abspath(args.json_out))
        if args.json_out is not None
        else None
    )

    if args.list:
        if args.lean_only and args.suite == "extract_guards":
            print(
                "ERROR: --lean-only cannot be combined with "
                "--suite extract_guards",
                file=sys.stderr,
            )
            return 1
        errors = validate_catalog_invariants(
            anneal_root, lean_only=args.lean_only
        )
        if errors:
            for err in errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        mir_guards, audit_guards, boundary_guards, extract_guards = (
            _select_guards(args.suite, args.name_filter)
        )
        if args.lean_only:
            extract_guards = []
        total = (
            len(mir_guards)
            + len(audit_guards)
            + len(boundary_guards)
            + len(extract_guards)
        )
        if total == 0:
            print(
                f"ERROR: no guards matched suite={args.suite!r} "
                f"filter={args.name_filter!r}",
                file=sys.stderr,
            )
            return 1
        for g in mir_guards:
            print(f"mir_semantics  {g.guard_id:42s} {g.target_file}")
        for g in audit_guards:
            print(f"audit_headers  {g.guard_id:42s} {g.target_file}")
        for g in boundary_guards:
            print(f"audit_boundary {g.guard_id:42s} {g.target_file}")
        for g in extract_guards:
            print(f"extract_guards {g.guard_id:42s} {g.target_file}")
        print(f"Total cataloged guards: {total}")
        return 0

    mir_g, audit_g, boundary_g, _ = _select_guards(args.suite, args.name_filter)
    need_lean = bool(mir_g or audit_g or boundary_g)
    lean_bin = _resolve_lean_binary(args.lean) if need_lean else None
    try:
        report = run_guard_mutation_suite(
            anneal_root=anneal_root,
            lean_bin=lean_bin,
            rustc_bin=args.rustc,
            suite=args.suite,
            lean_only=args.lean_only,
            name_filter=args.name_filter,
            jobs=args.jobs,
            timeout_sec=args.timeout_sec,
        )
    except (RuntimeError, subprocess.SubprocessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    print(_format_summary(report))
    if json_out is not None:
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )

    if report["killed"] != report["total"] or report["errors"] != 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
