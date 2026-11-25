# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Guard-mutation CI check for Anneal's MIR semantics and boundary auditor.

Why this check exists
---------------------

Positive verification proofs and positive canary suites cannot catch an
accidental deletion or weakening of an undefined-behavior (UB) guard or policy
rejection branch. If a refactor drops division-by-zero checking, removes an
alignment check, or disables an import restriction, every positive proof still
succeeds while unsound programs silently become provable.

This script closes that blind spot by performing single-guard mutation testing
in temporary directories (never modifying the repository working tree):

1. Against the unmodified TCB sources, every negative refutation theorem in
   `ci/fixtures/guard_mutation/` must compile with zero errors, and every
   negative header fixture must be rejected by `TrustedBoundary.lean` with a
   policy error (`exit 1`, `"category": "policy"`).
2. For each cataloged guard, the runner disables only that guard inside a fresh
   `tempfile.TemporaryDirectory()` copy, confirms that the mutated TCB module
   and positive sanity checks still compile cleanly (preventing syntax or type
   errors from masquerading as mutant kills), and verifies that the guard's
   targeted negative refutation fails with a proof/type error on the target
   theorem (or flips from policy reject to accept in `TrustedBoundary.lean`).
3. The check exits `0` only if 100% of cataloged guards are killed.

What this check guarantees — and what it does NOT guarantee
-----------------------------------------------------------

- **Guarantees:** Every guard explicitly listed in `MIR_SEMANTICS_GUARDS` and
  `AUDIT_HEADER_GUARDS` is active, non-redundant, and genuinely exercised by a
  negative refutation or negative auditor fixture. When `--changed-file` is
  supplied, every path is validated upfront and selection partitions into
  full-sweep (`109`), audit-only (`17`), MIR-semantics (`92`), union (`109`), or
  `0`-guard skip after `validate_catalog_invariants`.
- **Does NOT guarantee:** Coverage of unmodeled Rust semantics, UB guards added
  to `Trusted/MirSemantics/` or `TrustedBoundary.lean` without a catalog entry,
  or Rust compiler-capture (`anneal-rustc-capture`) checks outside the Lean TCB
  files cataloged here.

How to add a new guard
----------------------

Whenever a new UB check lands in `trusted/lean/Trusted/MirSemantics/` (or a new
header/import policy guard lands in `trusted/audit/TrustedBoundary.lean`):

1. Add a minimal negative refutation theorem `refute_<guard_id>` in the
   corresponding `ci/fixtures/guard_mutation/*Refutations.lean` file (or a
   negative header input for `AUDIT_HEADER_GUARDS`).
2. Add a matching `MirSemanticsGuard` (or `AuditHeaderGuard`) entry below whose
   `anchor` matches the guard expression uniquely and whose `replacement`
   weakens only that guard while keeping the mutated Lean file well-typed.
3. Run `python3 -I -B ci/check_guard_mutation.py --lean <path-to-lean>` and
   confirm a 100% kill rate.
"""

from __future__ import annotations

import argparse
from collections.abc import Sequence
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

# Operational semantics modules in strict topological import order. When a guard
# mutates one of these modules, only that module and the modules reachable from
# it in `SEMANTICS_DOWNSTREAM` need to be recompiled for that mutant.
SEMANTICS_MODULES: tuple[str, ...] = (
    "Trusted/MirSemantics/Ops",
    "Trusted/MirSemantics/Enum",
    "Trusted/MirSemantics/Layout",
    "Trusted/MirSemantics/Memory",
    "Trusted/MirSemantics/Bytes",
    "Trusted/MirSemantics/State",
    "Trusted/MirSemantics/Step",
    "Trusted/MirSemantics/Boundary",
)

# Exact transitive downstream closure (inclusive, in topological order) up to
# `Trusted/MirSemantics/Boundary` for each mutable semantics module.
SEMANTICS_DOWNSTREAM: dict[str, tuple[str, ...]] = {
    "Trusted/MirSemantics/Ops": (
        "Trusted/MirSemantics/Ops",
        "Trusted/MirSemantics/Enum",
        "Trusted/MirSemantics/Layout",
        "Trusted/MirSemantics/Memory",
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Enum": (
        "Trusted/MirSemantics/Enum",
        "Trusted/MirSemantics/Layout",
        "Trusted/MirSemantics/Memory",
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Layout": (
        "Trusted/MirSemantics/Layout",
        "Trusted/MirSemantics/Memory",
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Memory": (
        "Trusted/MirSemantics/Memory",
    ),
    "Trusted/MirSemantics/Bytes": (
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Step": (
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/Boundary": (
        "Trusted/MirSemantics/Boundary",
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
    """Single-guard mutation entry targeting `TrustedBoundary.lean`.

    Supports `"headers"`, `"spec-preflight"`, `"preflight"`, and `"audit"`
    auditor modes. Every entry carries a negative fixture that the baseline
    auditor must policy-reject (`category == "policy"`) and that a broken
    mutant accepts (`ok == True`). Optional `positive_source` verifies that the
    mutated auditor continues accepting valid inputs (anti-crash-masquerading).
    """

    guard_id: str
    target_file: str
    description: str
    anchor: str
    replacement: str
    negative_source: str
    mode: str = "headers"
    module_name: str = "Target"
    trust_tier: str | None = None
    positive_source: str | None = None
    positive_module: str | None = None
    use_full_foundation: bool = False
    extra_modules: tuple[tuple[str, str, str | None], ...] = ()


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
    # Trusted/MirSemantics/Ops.lean (4 UB guards)
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
        guard_id="ops_binop_width_sign_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="Non-shift BinOp rejects mismatched operand width or signedness",
        anchor=(
            "    else if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then\n"
            "      .error .unsupported"
        ),
        replacement=(
            "    else if false then\n"
            "      .error .unsupported"
        ),
        fixture_module="OpsRefutations",
        theorem_name="refute_ops_binop_width_sign_mismatch",
    ),
    MirSemanticsGuard(
        guard_id="ops_int_to_char_above_u8_max",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="CastKind::IntToInt targeting char rejects integers > 255",
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
        theorem_name="refute_ops_int_to_char_above_u8_max",
    ),
    MirSemanticsGuard(
        guard_id="ops_unsigned_neg_unsupported",
        target_file="trusted/lean/Trusted/MirSemantics/Ops.lean",
        target_module="Trusted/MirSemantics/Ops",
        description="UnOp::Neg rejects unsigned integer operands as unsupported",
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
        theorem_name="refute_ops_unsigned_neg_unsupported",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Enum.lean (5 range, admission, and Val.ty? guards)
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
        guard_id="enum_admitted_nonempty_discrs",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted rejects fieldless enums with zero variants",
        anchor=(
            "noncomputable def enumAdmitted (ety : EnumTy) : Bool :=\n"
            "  !ety.discriminants.isEmpty &&\n"
            "    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&"
        ),
        replacement=(
            "noncomputable def enumAdmitted (ety : EnumTy) : Bool :=\n"
            "  true &&\n"
            "    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&"
        ),
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_nonempty_discrs",
    ),
    MirSemanticsGuard(
        guard_id="enum_admitted_distinct_discrs",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="enumAdmitted rejects enums with duplicate discriminants",
        anchor="    natListPairwiseNe ety.discriminants &&",
        replacement="    true &&",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_admitted_distinct_discrs",
    ),
    MirSemanticsGuard(
        guard_id="enum_val_ty_oob_variant",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="Val.ty? rejects enumVal with out-of-bounds variant index",
        anchor="    if enumAdmitted ety && Nat.blt v ety.discriminants.length then",
        replacement="    if enumAdmitted ety && true then",
        fixture_module="EnumRefutations",
        theorem_name="refute_enum_val_ty_oob_variant",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Layout.lean (4 layout admission, size, align guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="layout_reject_unadmitted_enum",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="layoutOfTy returns none for unadmitted enums",
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
        theorem_name="refute_layout_reject_unadmitted_enum",
    ),
    MirSemanticsGuard(
        guard_id="layout_reject_non_overflow_tuple",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="layoutOfTy rejects tuple types outside overflow pairs",
        anchor=(
            "  | .tuple [.int w _, .bool] => some (overflowPairLayout w)\n"
            "  | _ => none"
        ),
        replacement=(
            "  | .tuple [.int w _, .bool] => some (overflowPairLayout w)\n"
            "  | .tuple _ => some ⟨1, 0⟩\n"
            "  | _ => none"
        ),
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_reject_non_overflow_tuple",
    ),
    MirSemanticsGuard(
        guard_id="layout_isize_64bit_align",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="intLayout gives 64-bit isize size 8 and alignLog2 3",
        anchor="  | .i64 | .isize => ⟨8, 3⟩",
        replacement="  | .i64 => ⟨8, 3⟩\n  | .isize => ⟨4, 2⟩",
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_isize_64bit_align",
    ),
    MirSemanticsGuard(
        guard_id="layout_overflow_pair_size",
        target_file="trusted/lean/Trusted/MirSemantics/Layout.lean",
        target_module="Trusted/MirSemantics/Layout",
        description="overflowPairLayout accounts for bool field and padding size",
        anchor=(
            "noncomputable def overflowPairLayout (w : IntWidth) : LayoutData :=\n"
            "  ⟨2 * (intLayout w).size, (intLayout w).alignLog2⟩"
        ),
        replacement=(
            "noncomputable def overflowPairLayout (w : IntWidth) : LayoutData :=\n"
            "  ⟨(intLayout w).size, (intLayout w).alignLog2⟩"
        ),
        fixture_module="LayoutRefutations",
        theorem_name="refute_layout_overflow_pair_size",
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Bytes.lean (10 validity, width, and uninit guards)
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
        guard_id="bytes_int_scalar_width_check",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit rejects integer scalar bits exceeding target width",
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
        theorem_name="refute_bytes_int_scalar_width_check",
    ),
    MirSemanticsGuard(
        guard_id="bytes_bool_scalar_width_check",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit rejects bool scalar bits exceeding 1 byte",
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
        theorem_name="refute_bytes_bool_scalar_width_check",
    ),
    MirSemanticsGuard(
        guard_id="bytes_char_scalar_width_check",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit rejects char scalar bits exceeding 32 bits as unsupported",
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
        theorem_name="refute_bytes_char_scalar_width_check",
    ),
    MirSemanticsGuard(
        guard_id="bytes_enum_tag_width_check",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="evalConstLit rejects enum tag bits exceeding tagW width",
        anchor=(
            "      if !enumAdmitted ety || truncateBits tagW bits != bits then\n"
            "        .error .unsupported"
        ),
        replacement=(
            "      if !enumAdmitted ety then\n"
            "        .error .unsupported"
        ),
        fixture_module="BytesRefutations",
        theorem_name="refute_bytes_enum_tag_width_check",
    ),
    MirSemanticsGuard(
        guard_id="bytes_decode_length_mismatch",
        target_file="trusted/lean/Trusted/MirSemantics/Bytes.lean",
        target_module="Trusted/MirSemantics/Bytes",
        description="decodeVal rejects byte slices whose length != layout.size",
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
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Memory.lean (24 allocation/bounds/align/mut guards)
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
        guard_id="mem_alloc_starts_uninit",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="allocateStack initializes allocation bytes to .uninit",
        anchor="    bytes := List.replicate layout.size .uninit",
        replacement="    bytes := List.replicate layout.size (.init 0 none)",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_alloc_starts_uninit",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_dealloc_clears_live",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="deallocateStack sets live := false so reads fault use-after-free",
        anchor="              replaceAllocation { a with live := false } m.allocations }",
        replacement="              m.allocations }",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_dealloc_clears_live",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_alloc_id_fresh",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="reserveAllocId increments nextAllocId so allocations stay distinct",
        anchor="  ({ m with nextAllocId := m.nextAllocId + 1 }, m.nextAllocId)",
        replacement="  (m, m.nextAllocId)",
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_alloc_id_fresh",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Step.lean (15 UB and move-deinit guards)
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
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Boundary.lean (8 judgment soundness guards)
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
    # Profile v2 memory, step, type-admission, and boundary guards (19 guards)
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
        description="sliceFromRawPartsCheck rejects null pointer even for zero-length slices as UB",
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
        description="sliceFromRawPartsCheck rejects mutable slice over .shared allocation as UB",
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
            "        else if !isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take totalBytes) then\n"
            "          .error .undefined\n"
            "        else\n"
            "          .ok (.slicePtr p len)"
        ),
        replacement=(
            "        else if false then\n"
            "          .error .undefined\n"
            "        else\n"
            "          .ok (.slicePtr p len)"
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
            "    (len startOff endOff : Nat) : Except FaultKind Val :=\n"
            "  if !Nat.ble startOff endOff || !Nat.ble endOff len then\n"
            "    .error .undefined"
        ),
        replacement=(
            "    (len startOff endOff : Nat) : Except FaultKind Val :=\n"
            "  if !Nat.ble startOff endOff || false then\n"
            "    .error .undefined"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_v2_slice_get_unchecked_oob",
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
            "          if !refsStayInCallerMem callerMem retTy retVal ||\n"
            "              !refsValidInMem mem retTy retVal ||\n"
            "              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then\n"
            "            .fault .undefined"
        ),
        replacement=(
            "          if false ||\n"
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
            "        match refValidInMem m inMut (.slice (.int .i8 false)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () => sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat"
        ),
        replacement=(
            "        match refValidInMem m outMut (.slice (.int .i8 false)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () => sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat"
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
            "        match refValidInMem m inMut (.slice (.int .i8 false)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () => sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat"
        ),
        replacement=(
            "        match refValidInMem m outMut (.slice (.int .i8 false)) (.slicePtr p len) with\n"
            "        | .error k => .error k\n"
            "        | .ok () => sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat"
        ),
        fixture_module="StepRefutations",
        theorem_name="refute_step_v2_get_unchecked_range_from_in_mut",
    ),
    MirSemanticsGuard(
        guard_id="enum_v2_overflow_pair_pointee",
        target_file="trusted/lean/Trusted/MirSemantics/Enum.lean",
        target_module="Trusted/MirSemantics/Enum",
        description="isSupportedV2LocalTy rejects pointers to overflow pairs",
        anchor=(
            "    | .ref _ pt | .rawPtr _ pt =>\n"
            "      !isOverflowPairTy pt && isSupportedScalarOrUnitTy pt"
        ),
        replacement=(
            "    | .ref _ pt | .rawPtr _ pt =>\n"
            "      true && isSupportedScalarOrUnitTy pt"
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
        anchor="  BodyStaticAdmittedV2 p body = true ∧",
        replacement="  True ∧",
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
        guard_id="boundary_body_verified_binds_def_id",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyVerified binds body to p.bodies[defId]",
        anchor=(
            "    (safetyPre : List Val → Prop) : Prop :=\n"
            "  getElem? p.bodies defId = some body ∧\n"
            "  BodyStaticAdmitted p body = true ∧"
        ),
        replacement=(
            "    (safetyPre : List Val → Prop) : Prop :=\n"
            "  True ∧\n"
            "  BodyStaticAdmitted p body = true ∧"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_body_verified_binds_def_id",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_admitted_nonempty_identity",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="BodyStaticAdmitted requires non-empty body.identity",
        anchor=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    !stringIsEmpty body.identity &&\n"
            "    !body.basicBlocks.isEmpty &&"
        ),
        replacement=(
            "    Nat.beq p.mirProfileVersion 1 &&\n"
            "    true &&\n"
            "    !body.basicBlocks.isEmpty &&"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_admitted_nonempty_identity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_program_entry_def_in_bounds",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="ProgramVerified requires entryDefId < p.bodies.length",
        anchor=(
            "  !p.bodies.isEmpty = true ∧\n"
            "  Nat.blt p.entryDefId p.bodies.length = true ∧\n"
            "  bodiesHaveUniqueIdentities p.bodies = true ∧\n"
            "  (∀ (defId : DefId) (body : Body),\n"
            "    getElem? p.bodies defId = some body →\n"
            "    BodyVerified p defId body"
        ),
        replacement=(
            "  !p.bodies.isEmpty = true ∧\n"
            "  True ∧\n"
            "  bodiesHaveUniqueIdentities p.bodies = true ∧\n"
            "  (∀ (defId : DefId) (body : Body),\n"
            "    getElem? p.bodies defId = some body →\n"
            "    BodyVerified p defId body"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_program_entry_def_in_bounds",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_unique_body_identities",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="ProgramVerified requires pairwise-distinct body identities",
        anchor=(
            "  bodiesHaveUniqueIdentities p.bodies = true ∧\n"
            "  (∀ (defId : DefId) (body : Body),\n"
            "    getElem? p.bodies defId = some body →\n"
            "    BodyVerified p defId body"
        ),
        replacement=(
            "  True ∧\n"
            "  (∀ (defId : DefId) (body : Body),\n"
            "    getElem? p.bodies defId = some body →\n"
            "    BodyVerified p defId body"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_unique_body_identities",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="boundary_crate_theorem_scope",
        target_file="trusted/lean/Trusted/MirSemantics/Boundary.lean",
        target_module="Trusted/MirSemantics/Boundary",
        description="CrateTheorem requires verification scope .crate",
        anchor=(
            "noncomputable def CrateTheorem (c : Crate) : Prop :=\n"
            "  c.program.scope = .crate ∧ ProgramVerified c.program c.specs"
        ),
        replacement=(
            "noncomputable def CrateTheorem (c : Crate) : Prop :=\n"
            "  True ∧ ProgramVerified c.program c.specs"
        ),
        fixture_module="BoundaryRefutations",
        theorem_name="refute_boundary_crate_theorem_scope",
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
        guard_id="audit_spec_reject_axiom_decl",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="spec-preflight rejects `axiom` declarations in target specs",
        anchor=(
            "      unless allowedSpecDeclarationKinds.contains declKind do\n"
            '        fail s!"unsupported declaration kind {declKind} in specification"'
        ),
        replacement=(
            "      unless true do\n"
            '        fail s!"unsupported declaration kind {declKind} in specification"'
        ),
        mode="spec-preflight",
        module_name="Spec",
        negative_source="prelude\nimport Init.Prelude\naxiom badAx : True\n",
        positive_source="prelude\nimport Init.Prelude\ndef Spec.ok : Prop := True\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_spec_reject_eval_cmd",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="spec-preflight rejects `#eval` commands in target specs",
        anchor=(
            "  ``Parser.Command.attribute, ``Parser.Command.deriving,\n"
            "  ``Parser.Command.set_option, ``Parser.Command.moduleDoc]"
        ),
        replacement=(
            "  ``Parser.Command.attribute, ``Parser.Command.deriving,\n"
            "  ``Parser.Command.set_option, ``Parser.Command.moduleDoc,\n"
            "  `Lean.Parser.Command.eval]"
        ),
        mode="spec-preflight",
        module_name="Spec",
        negative_source="prelude\nimport Init.Prelude\n#eval 1\n",
        positive_source="prelude\nimport Init.Prelude\ndef Spec.ok : Prop := True\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_spec_reject_sorry_tactic",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="spec-preflight rejects `by sorry` tactic in target specs",
        anchor=(
            "      if tacticLikeKinds.contains k || (`Lean.Parser.Tactic).isPrefixOf k then\n"
            "        unless allowedSpecTacticKinds.contains k do\n"
            '          fail s!"unsupported tactic {k} in specification"'
        ),
        replacement=(
            "      if false then\n"
            "        unless allowedSpecTacticKinds.contains k do\n"
            '          fail s!"unsupported tactic {k} in specification"'
        ),
        mode="spec-preflight",
        module_name="Spec",
        use_full_foundation=True,
        negative_source="prelude\nimport Init.Tactics\ntheorem bad : True := by sorry\n",
        positive_source=(
            "prelude\nimport Init.Tactics\n"
            "theorem ok : True := by exact True.intro\n"
        ),
    ),
    AuditHeaderGuard(
        guard_id="audit_spec_reject_forbidden_ns_lean",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="spec-preflight rejects opening `Lean` namespace in target specs",
        anchor=(
            "def isForbiddenPureNamespace (n : Name) (banLeanRoot : Bool := false) : Bool :=\n"
            "  let u := n.replacePrefix rootNamespace .anonymous\n"
            "  let r := u.getRoot\n"
            "  forbiddenPureRootNamespaces.contains r ||\n"
            "    (banLeanRoot && r == `Lean) ||"
        ),
        replacement=(
            "def isForbiddenPureNamespace (n : Name) (banLeanRoot : Bool := false) : Bool :=\n"
            "  let u := n.replacePrefix rootNamespace .anonymous\n"
            "  let r := u.getRoot\n"
            "  forbiddenPureRootNamespaces.contains r ||\n"
            "    (banLeanRoot && false) ||"
        ),
        mode="spec-preflight",
        module_name="Spec",
        negative_source="prelude\nimport Init.Prelude\nopen Lean\n",
        positive_source="prelude\nimport Init.Prelude\ndef Spec.ok : Prop := True\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_spec_reject_auto_param",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="spec-preflight rejects forbidden identifier `autoParam`",
        anchor=(
            "def forbiddenSpecIdentifierComponents : List String := [\n"
            '  "autoParam", "panic", "panicCore", "panicWithPos", "panicWithPosWithDecl",'
        ),
        replacement=(
            "def forbiddenSpecIdentifierComponents : List String := [\n"
            '  "panic", "panicCore", "panicWithPos", "panicWithPosWithDecl",'
        ),
        mode="spec-preflight",
        module_name="Spec",
        negative_source="prelude\nimport Init.Prelude\ndef bad := Nat.autoParam\n",
        positive_source="prelude\nimport Init.Prelude\ndef Spec.ok : Prop := True\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_preflight_reject_noncomputable_section",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="preflight rejects `noncomputable section` modifiers",
        anchor=(
            "  else if k == ``Parser.Command.sectionHeader then\n"
            "    validateSectionHeader args"
        ),
        replacement=(
            "  else if k == ``Parser.Command.sectionHeader then\n"
            "    pure ()"
        ),
        mode="preflight",
        module_name="Theory.Bad",
        negative_source="prelude\nimport Init.Prelude\nnoncomputable section\nend\n",
        positive_source="prelude\nimport Init.Prelude\nsection\nend\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_preflight_reject_theory_trust_tier",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="preflight rejects `-- anneal-trust-tier:` outside `Trusted`",
        anchor=(
            "  | false, _ :: _ =>\n"
            '    fail (s!"trust tier directive is only allowed in Trusted modules " ++\n'
            '      s!"({moduleName})")'
        ),
        replacement=(
            "  | false, _ :: _ =>\n"
            "    pure .theory"
        ),
        mode="preflight",
        module_name="Theory.Bad",
        negative_source="-- anneal-trust-tier: vetted\nprelude\nimport Init.Prelude\n",
        positive_source="prelude\nimport Init.Prelude\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_preflight_reject_trusted_missing_tier",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="preflight requires `-- anneal-trust-tier:` on `Trusted` modules",
        anchor=(
            "  | true, [] =>\n"
            '    fail ("missing `-- anneal-trust-tier: vetted` or " ++\n'
            '      s!"`-- anneal-trust-tier: candidate:<feature>` in {moduleName}")'
        ),
        replacement=(
            "  | true, [] =>\n"
            "    pure (.trusted .vetted)"
        ),
        mode="preflight",
        module_name="Trusted.Bad",
        negative_source="prelude\nimport Init.Prelude\n",
        positive_module="Trusted.Ok",
        positive_source="-- anneal-trust-tier: vetted\nprelude\nimport Init.Prelude\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_reject_unapproved_axiom_sorry",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="audit closure rejects unapproved `sorryAx` axiom dependency",
        anchor=(
            "      let reachedAxioms ← if ci.isAxiom then do\n"
            "        unless axioms.contains (n.toString, m.toString) do\n"
            '          fail s!"unapproved axiom {n} from {m}"\n'
            "        pure (reachedAxioms.insert n)"
        ),
        replacement=(
            "      let reachedAxioms ← if ci.isAxiom then do\n"
            "        if false then\n"
            '          fail s!"unapproved axiom {n} from {m}"\n'
            "        pure (reachedAxioms.insert n)"
        ),
        mode="audit",
        module_name="Theory.BadSorry",
        negative_source="prelude\nimport Init.Prelude\ntheorem badSorry : False := sorryAx False false\n",
        positive_module="Theory.Ok",
        positive_source="prelude\nimport Init.Prelude\ntheorem okThm : True := True.intro\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_reject_theory_in_trusted_ns",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="audit rejects non-Trusted modules declaring in `Trusted.*`",
        anchor=(
            "  if !isTrusted && userRoot == `Trusted &&\n"
            "      !isRealizedOrCompilerHelper env allMatchers isTrustedConst ci then\n"
            '    fail (s!"non-Trusted module {m} cannot declare constant {ci.name} " ++\n'
            '      "in Trusted namespace")'
        ),
        replacement=(
            "  if false &&\n"
            "      !isRealizedOrCompilerHelper env allMatchers isTrustedConst ci then\n"
            '    fail (s!"non-Trusted module {m} cannot declare constant {ci.name} " ++\n'
            '      "in Trusted namespace")'
        ),
        mode="audit",
        module_name="Theory.BadTrustedNs",
        negative_source="prelude\nimport Init.Prelude\ndef Trusted.spoof : Nat := 0\n",
        positive_module="Theory.Ok",
        positive_source="prelude\nimport Init.Prelude\ntheorem okThm : True := True.intro\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_reject_reserved_kernel_ns",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="audit rejects constants declared in reserved kernel namespaces",
        anchor=(
            "  if kernelAcceleratedNames.contains userName ||\n"
            "      (reservedKernelRoots.contains userRoot &&\n"
            "        !isRealizedOrCompilerHelper env allMatchers isFoundationConst ci) then\n"
            '    fail (s!"repository module {m} cannot declare constant {ci.name} " ++\n'
            '      s!"in reserved kernel namespace {userRoot}")'
        ),
        replacement=(
            "  if false then\n"
            '    fail (s!"repository module {m} cannot declare constant {ci.name} " ++\n'
            '      s!"in reserved kernel namespace {userRoot}")'
        ),
        mode="audit",
        module_name="Theory.BadKernelNs",
        negative_source="prelude\nimport Init.Prelude\ndef Nat.spoof : Nat := 0\n",
        positive_module="Theory.Ok",
        positive_source="prelude\nimport Init.Prelude\ntheorem okThm : True := True.intro\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_reject_opaque_decl",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="audit rejects opaque declarations outside Trusted modules",
        anchor=(
            "  if !isTrusted && (ci matches .opaqueInfo _) then\n"
            '    fail s!"opaque declaration {ci.name} in {m} is not allowed outside Trusted"'
        ),
        replacement=(
            "  if false then\n"
            '    fail s!"opaque declaration {ci.name} in {m} is not allowed outside Trusted"'
        ),
        mode="audit",
        module_name="Theory.BadOpaque",
        negative_source="prelude\nimport Init.Prelude\nopaque badOpaque : Nat := 0\n",
        positive_module="Theory.Ok",
        positive_source="prelude\nimport Init.Prelude\ntheorem okThm : True := True.intro\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_reject_vetted_imports_candidate",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="audit rejects vetted Trusted modules importing candidate modules",
        anchor=(
            "  | .foundation, .repo _ =>\n"
            '    some s!"foundation module {m} cannot import {imp}"\n'
            "  | .repo (.trusted .vetted), .foundation\n"
            "  | .repo (.trusted .vetted), .repo (.trusted .vetted) => none\n"
            "  | .repo (.trusted .vetted), .repo (.trusted depTier) =>\n"
            '    some s!"vetted module {m} cannot import {depTier.render} module {imp}"'
        ),
        replacement=(
            "  | .foundation, .repo _ =>\n"
            '    some s!"foundation module {m} cannot import {imp}"\n'
            "  | .repo (.trusted .vetted), .foundation\n"
            "  | .repo (.trusted .vetted), .repo (.trusted .vetted) => none\n"
            "  | .repo (.trusted .vetted), .repo (.trusted _) => none"
        ),
        mode="audit",
        module_name="Trusted.Vet",
        trust_tier="vetted",
        negative_source=(
            "-- anneal-trust-tier: vetted\n"
            "prelude\nimport Init.Prelude\nimport Trusted.Cand\n"
            "def vetVal : Nat := 0\n"
        ),
        extra_modules=(
            (
                "Trusted.Cand",
                "-- anneal-trust-tier: candidate:mir_semantics\n"
                "prelude\nimport Init.Prelude\n"
                "def candVal : Nat := 0\n",
                "candidate:mir_semantics",
            ),
        ),
        positive_module="Trusted.VetOk",
        positive_source=(
            "-- anneal-trust-tier: vetted\n"
            "prelude\nimport Init.Prelude\n"
            "def vetOk : Nat := 0\n"
        ),
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
        r"^(?:theorem|lemma|def|noncomputable\s+def|end)\b"
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


def _run_lean(
    lean_bin: Path,
    args: list[str],
    *,
    lean_path: list[Path],
    timeout_sec: int,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in lean_path)
    return subprocess.run(
        [str(lean_bin), *args],
        env=env,
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
        capture_output=True,
        text=True,
        timeout=timeout_sec,
        check=True,
    )
    return res.stdout.strip()


def _foundation_sysroot_artifacts(
    sysroot: str,
    modules: list[str],
) -> list[list[object]]:
    """Collect `[olean_parts, ir_parts]` entries for foundation modules."""
    lib_lean = Path(sysroot) / "lib/lean"
    result: list[list[object]] = []
    for mod in modules:
        rel = Path(*mod.split("."))
        base = lib_lean / rel
        olean_parts = [
            str(base.with_name(base.name + ext))
            for ext in (".olean", ".olean.server", ".olean.private")
            if base.with_name(base.name + ext).exists()
        ]
        ir_parts = [
            str(base.with_name(base.name + ext))
            for ext in (".ir.sig", ".ir")
            if base.with_name(base.name + ext).exists()
        ]
        result.append([mod, [olean_parts, ir_parts]])
    return result


def _compiled_module_artifacts(
    olean_dir: Path,
    mod: str,
) -> list[list[str]]:
    """Collect `[olean_parts, ir_parts]` wire entries for a compiled fixture."""
    rel = Path(*mod.split("."))
    base = olean_dir / rel
    olean_parts = [
        str(base.with_name(base.name + ext))
        for ext in (".olean", ".olean.server", ".olean.private")
        if base.with_name(base.name + ext).exists()
    ]
    ir_parts = [
        str(base.with_name(base.name + ext))
        for ext in (".ir.sig", ".ir")
        if base.with_name(base.name + ext).exists()
    ]
    return [olean_parts, ir_parts]


def _import_edges_for_source(source_text: str) -> list[dict[str, object]]:
    """Extract simple `import Mod` header edges for synthetic audit fixtures."""
    edges: list[dict[str, object]] = []
    for raw_line in source_text.splitlines():
        line = raw_line.strip()
        if line.startswith("import "):
            mod_name = line[len("import ") :].strip()
            edges.append(
                {
                    "module": mod_name,
                    "importAll": False,
                    "isExported": True,
                    "isMeta": False,
                }
            )
    return edges


def _prepare_audit_payloads(
    guard: AuditHeaderGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    sysroot: str,
    prep_dir: Path,
    foundation_lock: dict[str, object] | None,
    timeout_sec: int,
) -> tuple[dict[str, object], dict[str, object] | None]:
    """Build baseline JSON request payloads `(neg_req, pos_req)` for `guard`."""
    if guard.mode == "headers":
        target_src = prep_dir / f"{guard.module_name}.lean"
        target_src.write_text(guard.negative_source, encoding="utf-8")
        neg_req: dict[str, object] = {
            "mode": "headers",
            "sysroot": sysroot,
            "sources": [[guard.module_name, str(target_src)]],
        }
        pos_req: dict[str, object] | None = None
        if guard.positive_source is not None:
            pos_src = prep_dir / f"{guard.positive_module or guard.module_name}.ok.lean"
            pos_src.write_text(guard.positive_source, encoding="utf-8")
            pos_req = {
                "mode": "headers",
                "sysroot": sysroot,
                "sources": [
                    [guard.positive_module or guard.module_name, str(pos_src)]
                ],
            }
        return neg_req, pos_req

    assert foundation_lock is not None
    full_graph = foundation_lock["graph"]
    assert isinstance(full_graph, dict)
    axioms = foundation_lock["axioms"]
    assert isinstance(axioms, list)

    if guard.use_full_foundation:
        found_mods = sorted(str(k) for k in full_graph)
        found_graph = dict(full_graph)
    else:
        found_mods = ["Init.Prelude"]
        found_graph = {"Init.Prelude": []}
    found_arts = _foundation_sysroot_artifacts(sysroot, found_mods)

    if guard.mode in ("spec-preflight", "preflight"):
        neg_src = prep_dir / "neg.lean"
        neg_src.write_text(guard.negative_source, encoding="utf-8")
        neg_req = {
            "mode": guard.mode,
            "sysroot": sysroot,
            "artifacts": found_arts,
            "foundation": found_mods,
            "graph": found_graph,
            "sources": [[guard.module_name, str(neg_src)]],
        }
        if guard.mode == "spec-preflight":
            neg_req["libraries"] = []
        pos_req = None
        if guard.positive_source is not None:
            pos_mod = guard.positive_module or guard.module_name
            pos_src = prep_dir / "pos.lean"
            pos_src.write_text(guard.positive_source, encoding="utf-8")
            pos_req = {
                **neg_req,
                "sources": [[pos_mod, str(pos_src)]],
            }
        return neg_req, pos_req

    if guard.mode == "audit":
        src_root = prep_dir / "src"
        olean_root = prep_dir / "olean"
        src_root.mkdir(parents=True, exist_ok=True)
        olean_root.mkdir(parents=True, exist_ok=True)

        def _compile_fixture_bundle(
            modules: list[tuple[str, str, str | None]],
            bundle_tag: str,
        ) -> dict[str, object]:
            arts: list[list[object]] = list(found_arts)
            graph = dict(found_graph)
            trusted_list: list[str] = []
            theory_list: list[str] = []
            tiers: list[list[str]] = []
            for mod_name, src_text, tier in modules:
                rel_mod = "/".join(mod_name.split("."))
                src_path = src_root / f"{rel_mod}.lean"
                src_path.parent.mkdir(parents=True, exist_ok=True)
                src_path.write_text(src_text, encoding="utf-8")
                comp = _compile_module(
                    lean_bin,
                    src_root,
                    rel_mod,
                    olean_root,
                    lean_path=[olean_root],
                    timeout_sec=timeout_sec,
                )
                if comp.returncode != 0:
                    raise RuntimeError(
                        f"failed to compile {bundle_tag} audit fixture {mod_name}:\n"
                        f"{comp.stdout}\n{comp.stderr}"
                    )
                arts.append([mod_name, _compiled_module_artifacts(olean_root, mod_name)])
                graph[mod_name] = _import_edges_for_source(src_text)
                if tier is not None:
                    trusted_list.append(mod_name)
                    tiers.append([mod_name, tier])
                else:
                    theory_list.append(mod_name)
            return {
                "mode": "audit",
                "sysroot": sysroot,
                "artifacts": arts,
                "foundation": found_mods,
                "graph": graph,
                "axioms": axioms,
                "trusted": trusted_list,
                "theory": theory_list,
                "moduleTiers": tiers,
                "requireMirWp": False,
            }

        neg_bundle = [
            *guard.extra_modules,
            (guard.module_name, guard.negative_source, guard.trust_tier),
        ]
        neg_req = _compile_fixture_bundle(neg_bundle, f"{guard.guard_id}:neg")
        pos_req = None
        if guard.positive_source is not None:
            pos_mod = guard.positive_module or guard.module_name
            pos_tier = guard.trust_tier
            pos_bundle = [(pos_mod, guard.positive_source, pos_tier)]
            pos_req = _compile_fixture_bundle(pos_bundle, f"{guard.guard_id}:pos")
        return neg_req, pos_req

    raise ValueError(f"{guard.guard_id}: unsupported audit mode {guard.mode!r}")


def _run_audit_request(
    lean_bin: Path,
    tb_olean_dir: Path,
    req_payload: dict[str, object],
    work_dir: Path,
    *,
    tag: str,
    timeout_sec: int,
) -> tuple[int, dict[str, object] | None, str]:
    """Invoke precompiled `TrustedBoundary` with a JSON request dictionary."""
    req_path = work_dir / f"{tag}_req.json"
    res_path = work_dir / f"{tag}_res.json"
    runner_path = work_dir / "run_tb.lean"
    req_path.write_text(json.dumps(req_payload), encoding="utf-8")
    if not runner_path.exists():
        runner_path.write_text("import TrustedBoundary\n", encoding="utf-8")
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
    timeout_sec: int,
) -> tuple[int, dict[str, object] | None, str]:
    """Invoke precompiled `TrustedBoundary` in `"headers"` mode."""
    target_src = work_dir / "Target.lean"
    target_src.write_text(source_text, encoding="utf-8")
    return _run_audit_request(
        lean_bin,
        tb_olean_dir,
        {
            "mode": "headers",
            "sysroot": sysroot,
            "sources": [["Target", str(target_src)]],
        },
        work_dir,
        tag="headers",
        timeout_sec=timeout_sec,
    )


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
        # filesystems) to every unmodified `.olean*` artifact (`.olean`,
        # `.olean.server`, `.olean.private`) in `base_olean_dir`. Lean 4
        # resolves a root namespace (`Trusted.*`) from the first `LEAN_PATH`
        # entry containing that root directory, so giving each mutant one
        # complete `.olean*` directory avoids partial-namespace lookup failures.
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
        for src_art in base_olean_dir.rglob("*.olean*"):
            rel = src_art.relative_to(base_olean_dir)
            rel_str = rel.as_posix()
            rel_mod = None
            for ext in (".olean", ".olean.server", ".olean.private"):
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


def _check_one_audit_guard(
    guard: AuditHeaderGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    sysroot: str,
    timeout_sec: int,
    neg_req: dict[str, object] | None = None,
    pos_req: dict[str, object] | None = None,
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
        mut_src_dir = tmp_path / "src"
        mut_src_dir.mkdir()
        mut_tb = mut_src_dir / "TrustedBoundary.lean"
        mut_tb.write_text(mutated_text, encoding="utf-8")
        mut_olean_dir = tmp_path / "olean"
        mut_olean_dir.mkdir()

        comp = _compile_module(
            lean_bin,
            mut_src_dir,
            "TrustedBoundary",
            mut_olean_dir,
            lean_path=[],
            timeout_sec=timeout_sec,
        )
        if comp.returncode != 0:
            return GuardResult(
                suite="audit_headers",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"mutated TrustedBoundary.lean failed to compile: "
                    f"{(comp.stdout + comp.stderr).strip()[:300]}"
                ),
            )

        if pos_req is not None:
            pos_rc, pos_parsed, pos_out = _run_audit_request(
                lean_bin,
                mut_olean_dir,
                pos_req,
                tmp_path,
                tag="pos",
                timeout_sec=timeout_sec,
            )
            if not (
                pos_rc == 0
                and isinstance(pos_parsed, dict)
                and pos_parsed.get("ok") is True
            ):
                return GuardResult(
                    suite="audit_headers",
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=(
                        f"positive audit sanity broke on mutant "
                        f"rc={pos_rc} parsed={pos_parsed!r} out={pos_out[:200]}"
                    ),
                )

        if neg_req is not None:
            rc, parsed, out = _run_audit_request(
                lean_bin,
                mut_olean_dir,
                neg_req,
                tmp_path,
                tag="neg",
                timeout_sec=timeout_sec,
            )
        else:
            rc, parsed, out = _run_audit_headers(
                lean_bin,
                mut_olean_dir,
                sysroot,
                guard.negative_source,
                tmp_path,
                timeout_sec=timeout_sec,
            )
        if rc == 0 and isinstance(parsed, dict) and parsed.get("ok") is True:
            return GuardResult(
                suite="audit_headers",
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="KILLED",
                duration_sec=time.monotonic() - t0,
                detail=(
                    f"negative {guard.mode} fixture flipped from policy reject "
                    "to accept"
                ),
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
                detail=f"mutant still rejected fixture: {parsed.get('message')!r}",
            )
        return GuardResult(
            suite="audit_headers",
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            status="ERROR",
            duration_sec=time.monotonic() - t0,
            detail=f"unexpected auditor result rc={rc} parsed={parsed!r} out={out[:200]}",
        )


def validate_catalog_invariants(anneal_root: Path) -> list[str]:
    """Check static catalog invariants without invoking Lean.

    Returns a list of error strings (empty when all invariants hold).
    """
    errors: list[str] = []
    seen_ids: set[str] = set()
    fixtures_dir = anneal_root / "ci/fixtures/guard_mutation"

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
            try:
                find_theorem_line_span(
                    fixture_path.read_text(encoding="utf-8"), guard.theorem_name
                )
            except ValueError as exc:
                errors.append(f"{guard.guard_id}: {exc}")

    for guard in AUDIT_HEADER_GUARDS:
        if guard.guard_id in seen_ids:
            errors.append(f"duplicate guard_id: {guard.guard_id}")
        seen_ids.add(guard.guard_id)
        if guard.mode not in ("headers", "spec-preflight", "preflight", "audit"):
            errors.append(f"{guard.guard_id}: invalid audit mode {guard.mode!r}")
        if guard.positive_source is not None and not guard.positive_source.strip():
            errors.append(f"{guard.guard_id}: positive_source cannot be empty")
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

    return errors


_FULL_SWEEP_EXACT_PATHS: frozenset[str] = frozenset(
    {
        "ci/check_guard_mutation.py",
        "ci/fixtures/guard_mutation",
        "trusted/lean/lean-toolchain",
    }
)

_FULL_SWEEP_PREFIXES: tuple[str, ...] = ("ci/fixtures/guard_mutation/",)

_AUDIT_TRIGGER_PATHS: frozenset[str] = frozenset(
    {
        "trusted/audit/TrustedBoundary.lean",
        "trusted/lean/foundation-lock.json",
    }
)

_MIR_EXCLUDED_PATHS: frozenset[str] = frozenset(
    {
        "trusted/lean/foundation-lock.json",
        "trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean",
    }
)


def _normalize_changed_file(raw: str) -> str:
    """Normalize a `--changed-file` path relative to `anneal/`.

    Fails closed on empty, control-byte, backslash, absolute, or traversal
    segments.
    """
    if not raw or not raw.strip():
        raise ValueError("changed file path must be non-empty")
    if "\x00" in raw or "\n" in raw or "\r" in raw:
        raise ValueError(
            f"changed file path contains invalid control byte: {raw!r}"
        )
    if "\\" in raw:
        raise ValueError(
            f"changed file path must use POSIX '/' separators: {raw!r}"
        )
    if raw.startswith("/"):
        raise ValueError(
            f"changed file path must be relative, got: {raw!r}"
        )
    parts = raw.split("/")
    if any(p in ("", ".", "..") for p in parts):
        raise ValueError(
            "changed file path must not contain empty, '.', or '..' "
            f"segments: {raw!r}"
        )
    if parts[0] == "anneal":
        if len(parts) < 2:
            raise ValueError(
                f"changed file path must name a file under 'anneal/': {raw!r}"
            )
        parts = parts[1:]
    return "/".join(parts)


def select_guards_for_changed_files(
    changed_files: Sequence[str],
    *,
    suite: str = "all",
    name_filter: str | None = None,
) -> tuple[list[MirSemanticsGuard], list[AuditHeaderGuard]]:
    """Select the minimal TCB guard closure covering `changed_files`."""
    # Validate and normalize every path upfront before any early trigger check.
    normalized = [_normalize_changed_file(raw) for raw in changed_files]

    full_sweep = False
    include_all_mir = False
    include_audit = False

    for norm in normalized:
        if norm in _FULL_SWEEP_EXACT_PATHS or any(
            norm.startswith(prefix) for prefix in _FULL_SWEEP_PREFIXES
        ):
            full_sweep = True
            break
        if norm in _AUDIT_TRIGGER_PATHS:
            include_audit = True
        elif (
            norm.startswith("trusted/lean/")
            and norm not in _MIR_EXCLUDED_PATHS
        ):
            include_all_mir = True

    if full_sweep:
        include_all_mir = True
        include_audit = True

    mir_guards = (
        list(MIR_SEMANTICS_GUARDS)
        if suite in ("all", "mir_semantics") and include_all_mir
        else []
    )
    audit_guards = (
        list(AUDIT_HEADER_GUARDS)
        if suite in ("all", "audit_headers") and include_audit
        else []
    )

    if name_filter:
        mir_guards = [g for g in mir_guards if name_filter in g.guard_id]
        audit_guards = [g for g in audit_guards if name_filter in g.guard_id]
    return mir_guards, audit_guards


def _select_guards(
    suite: str,
    name_filter: str | None,
    changed_files: Sequence[str] | None = None,
) -> tuple[list[MirSemanticsGuard], list[AuditHeaderGuard]]:
    if changed_files is not None:
        return select_guards_for_changed_files(
            changed_files,
            suite=suite,
            name_filter=name_filter,
        )
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
    if name_filter:
        mir_guards = [g for g in mir_guards if name_filter in g.guard_id]
        audit_guards = [g for g in audit_guards if name_filter in g.guard_id]
    return mir_guards, audit_guards


def run_guard_mutation_suite(
    *,
    anneal_root: Path,
    lean_bin: Path | None = None,
    suite: str = "all",
    name_filter: str | None = None,
    changed_files: Sequence[str] | None = None,
    jobs: int = 4,
    timeout_sec: int = 60,
) -> dict[str, object]:
    """Run baseline verification and all selected single-guard mutations."""
    t_start = time.monotonic()
    catalog_errors = validate_catalog_invariants(anneal_root)
    if catalog_errors:
        raise RuntimeError(
            "guard catalog validation failed:\n  - "
            + "\n  - ".join(catalog_errors)
        )

    mir_guards, audit_guards = _select_guards(
        suite,
        name_filter,
        changed_files=changed_files,
    )
    if not mir_guards and not audit_guards:
        if changed_files is not None:
            return {
                "total": 0,
                "killed": 0,
                "survived": 0,
                "errors": 0,
                "kill_rate_pct": 100.0,
                "baseline_sec": 0.0,
                "total_sec": round(time.monotonic() - t_start, 3),
                "results": [],
            }
        raise RuntimeError(
            f"no guards matched suite={suite!r} filter={name_filter!r}"
        )

    if lean_bin is None:
        lean_bin = _resolve_lean_binary(None)

    trusted_lean_dir = anneal_root / "trusted/lean"
    fixtures_dir = anneal_root / "ci/fixtures/guard_mutation"
    results: list[GuardResult] = []
    baseline_sec = 0.0

    with tempfile.TemporaryDirectory(prefix="anneal-gmut-base-") as base_tmp:
        base_path = Path(base_tmp)
        base_olean_dir = base_path / "olean"
        base_olean_dir.mkdir()

        # --------------------------------------------------------------
        # Suite 1: Trusted/MirSemantics/ baseline + mutants
        # --------------------------------------------------------------
        if mir_guards:
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
        # Suite 2: TrustedBoundary.lean guards baseline + mutants
        # --------------------------------------------------------------
        if audit_guards:
            t_audit_base = time.monotonic()
            sysroot = _query_lean_sysroot(lean_bin, timeout_sec)
            tb_olean_dir = base_path / "tb_olean"
            tb_olean_dir.mkdir()
            tb_src_dir = anneal_root / "trusted/audit"
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
            foundation_lock: dict[str, object] | None = None
            if any(g.mode != "headers" for g in audit_guards):
                lock_path = anneal_root / "trusted/lean/foundation-lock.json"
                foundation_lock = json.loads(lock_path.read_text(encoding="utf-8"))

            prepared_reqs: dict[
                str, tuple[dict[str, object], dict[str, object] | None]
            ] = {}
            for guard in audit_guards:
                check_dir = base_path / f"base_{guard.guard_id}"
                check_dir.mkdir()
                prep_dir = check_dir / "prep"
                prep_dir.mkdir()
                neg_req, pos_req = _prepare_audit_payloads(
                    guard,
                    anneal_root=anneal_root,
                    lean_bin=lean_bin,
                    sysroot=sysroot,
                    prep_dir=prep_dir,
                    foundation_lock=foundation_lock,
                    timeout_sec=timeout_sec,
                )
                prepared_reqs[guard.guard_id] = (neg_req, pos_req)

                if guard.mode == "headers" and guard.positive_source is None:
                    rc, parsed, out = _run_audit_headers(
                        lean_bin,
                        tb_olean_dir,
                        sysroot,
                        guard.negative_source,
                        check_dir,
                        timeout_sec=timeout_sec,
                    )
                else:
                    rc, parsed, out = _run_audit_request(
                        lean_bin,
                        tb_olean_dir,
                        neg_req,
                        check_dir,
                        tag="neg",
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
                        f"{guard.guard_id}: rc={rc} parsed={parsed!r} out={out}"
                    )

                if pos_req is not None:
                    p_rc, p_parsed, p_out = _run_audit_request(
                        lean_bin,
                        tb_olean_dir,
                        pos_req,
                        check_dir,
                        tag="pos",
                        timeout_sec=timeout_sec,
                    )
                    if not (
                        p_rc == 0
                        and isinstance(p_parsed, dict)
                        and p_parsed.get("ok") is True
                    ):
                        raise RuntimeError(
                            f"baseline TrustedBoundary rejected positive sanity "
                            f"for {guard.guard_id}: rc={p_rc} parsed={p_parsed!r} "
                            f"out={p_out}"
                        )
            baseline_sec += time.monotonic() - t_audit_base

            # Cap concurrent `TrustedBoundary.lean` compilations to 2 workers
            # to keep peak memory bounded on 4-vCPU CI runners.
            audit_workers = max(1, min(jobs, 2, len(audit_guards)))
            with ThreadPoolExecutor(max_workers=audit_workers) as pool:
                future_map = {
                    pool.submit(
                        _check_one_audit_guard,
                        guard,
                        anneal_root=anneal_root,
                        lean_bin=lean_bin,
                        sysroot=sysroot,
                        timeout_sec=timeout_sec,
                        neg_req=prepared_reqs[guard.guard_id][0],
                        pos_req=prepared_reqs[guard.guard_id][1],
                    ): guard
                    for guard in audit_guards
                }
                audit_by_id: dict[str, GuardResult] = {}
                for fut in as_completed(future_map):
                    res = fut.result()
                    audit_by_id[res.guard_id] = res
            results.extend(audit_by_id[g.guard_id] for g in audit_guards)

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
        "results": [asdict(r) for r in results],
    }


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _resolve_lean_binary(explicit: Path | None) -> Path:
    if explicit is not None:
        if not explicit.is_file():
            raise SystemExit(f"Lean binary not found: {explicit}")
        return explicit
    env_lean = os.environ.get("ANNEAL_LEAN")
    if env_lean:
        cand = Path(env_lean)
        if cand.is_file():
            return cand
    found = shutil.which("lean")
    if found:
        return Path(found)
    raise SystemExit(
        "Lean binary not specified; pass --lean <path> or set ANNEAL_LEAN"
    )


def _format_summary(report: dict[str, object]) -> str:
    if report["total"] == 0:
        return (
            "0 guards selected (skipping Lean baseline)\n"
            f"Guard-mutation summary: 0/0 killed (100.0%), 0 survived, "
            f"0 errors (baseline {report['baseline_sec']:.2f}s, "
            f"total {report['total_sec']:.2f}s)"
        )
    lines: list[str] = []
    for entry in report["results"]:  # type: ignore[index]
        lines.append(
            f"[{entry['status']:8s}] ({entry['suite']:13s}) "
            f"{entry['guard_id']:36s} {entry['duration_sec']:5.2f}s  "
            f"{entry['detail']}"
        )
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
            "Run single-guard mutation checks against Trusted/MirSemantics/ "
            "and TrustedBoundary.lean."
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
        type=Path,
        default=None,
        help="Path to the pinned `lean` executable (falls back to ANNEAL_LEAN / PATH).",
    )
    parser.add_argument(
        "--suite",
        choices=("all", "mir_semantics", "audit_headers"),
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
        "--changed-file",
        dest="changed_files",
        action="append",
        default=None,
        help=(
            "Repeatable changed file path (relative to repo root or `anneal/`) "
            "to restrict execution to the affected TCB guard closure."
        ),
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
        help="Per-Lean-invocation timeout in seconds (default: 60).",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Optional file path to write the structured JSON report.",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="Validate static catalog invariants, list all guards, and exit.",
    )
    args = parser.parse_args(argv)

    if args.list:
        errors = validate_catalog_invariants(args.anneal_root)
        if errors:
            for err in errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        try:
            mir_guards, audit_guards = _select_guards(
                args.suite,
                args.name_filter,
                changed_files=args.changed_files,
            )
        except ValueError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 1
        for g in mir_guards:
            print(f"mir_semantics  {g.guard_id:36s} {g.target_file}")
        for g in audit_guards:
            print(f"audit_headers  {g.guard_id:36s} {g.target_file}")
        print(f"Total cataloged guards: {len(mir_guards) + len(audit_guards)}")
        return 0

    try:
        need_lean = True
        if args.changed_files is not None:
            mir_sel, audit_sel = _select_guards(
                args.suite,
                args.name_filter,
                changed_files=args.changed_files,
            )
            need_lean = bool(mir_sel or audit_sel)
        lean_bin = _resolve_lean_binary(args.lean) if need_lean else None
        report = run_guard_mutation_suite(
            anneal_root=args.anneal_root,
            lean_bin=lean_bin,
            suite=args.suite,
            name_filter=args.name_filter,
            changed_files=args.changed_files,
            jobs=args.jobs,
            timeout_sec=args.timeout_sec,
        )
    except (RuntimeError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    print(_format_summary(report))
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )

    if report["killed"] != report["total"] or report["errors"] != 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
