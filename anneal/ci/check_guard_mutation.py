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
   negative header or boundary fixture must be rejected by
   `TrustedBoundary.lean` with a policy error (`exit 1`,
   `"category": "policy"`).
2. For each cataloged guard, the runner disables only that guard inside a fresh
   `tempfile.TemporaryDirectory()` copy, confirms that the mutated TCB module
   and positive sanity checks still compile cleanly (preventing syntax or type
   errors from masquerading as mutant kills), and verifies that the guard's
   targeted negative refutation fails with a proof/type error on the target
   theorem (or flips from policy reject to accept in `TrustedBoundary.lean`).
3. The check exits `0` only if 100% of cataloged guards are killed.

What this check guarantees — and what it does NOT guarantee
-----------------------------------------------------------

- **Guarantees:** Every guard explicitly listed in `MIR_SEMANTICS_GUARDS`,
  `AUDIT_HEADER_GUARDS`, and `AUDIT_BOUNDARY_GUARDS` is active, non-redundant,
  and genuinely exercised by a negative refutation or negative auditor fixture.
- **Does NOT guarantee:** Coverage of unmodeled Rust semantics, UB guards added
  to `Trusted/MirSemantics/` or `TrustedBoundary.lean` without a catalog entry,
  or Rust compiler-capture (`anneal-rustc-capture`) checks outside the Lean TCB
  files cataloged here.

How to add a new guard
----------------------

Whenever a new UB check lands in `trusted/lean/Trusted/MirSemantics/` (or a new
header/import/boundary policy guard lands in
`trusted/audit/TrustedBoundary.lean`):

1. Add a minimal negative refutation theorem `refute_<guard_id>` in the
   corresponding `ci/fixtures/guard_mutation/*Refutations.lean` file (or a
   negative header/boundary fixture for `AUDIT_HEADER_GUARDS` /
   `AUDIT_BOUNDARY_GUARDS`).
2. Add a matching `MirSemanticsGuard`, `AuditHeaderGuard`, or
   `AuditBoundaryGuard` entry below whose `anchor` matches the guard expression
   uniquely and whose `replacement` weakens only that guard while keeping the
   mutated Lean file well-typed.
3. Run `python3 -I -B ci/check_guard_mutation.py --lean <path-to-lean>` and
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
    "Trusted/MirSemantics/CoreContracts",
    "Trusted/MirSemantics/AllocContracts",
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
# Baseline-only exact-value fixtures compiled solely against the unmodified
# semantics (never copied into or rebuilt against mutants).
BASELINE_ONLY_MEMORY_FIXTURES: tuple[str, ...] = (
    "MemoryBaselineExact",
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
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Enum.lean (2 Unicode scalar range clauses)
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
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Bytes.lean (14 validity, uninit, and UTF-8 guards)
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
    # Trusted/MirSemantics/Memory.lean (21 allocation/bounds/align/mut guards)
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
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Step.lean (18 UB, move-deinit, and frame guards)
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
    # Trusted/MirSemantics/State.lean (3 sysroot UB + 1 call admission guard)
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
    ),
    # ------------------------------------------------------------------
    # Trusted/MirSemantics/Boundary.lean (3 judgment soundness guards)
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
    # Profile v2 memory, step, type-admission, and boundary guards (83 guards)
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
            "execSliceSplitAt validates the input slice reference at its own "
            "mutability"
        ),
        anchor=(
            "    match refValidInMem m inMut (.slice elem) (.slicePtr p len) with\n"
            "    | .error k => .error k\n"
            "    | .ok () =>\n"
            "      if !Nat.ble mid len.toNat then"
        ),
        replacement=(
            "    match refValidInMem m reqMut (.slice elem) (.slicePtr p len) with\n"
            "    | .error k => .error k\n"
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
    # slice/thin-ref validity, and provenance-free deref guards (24 guards)
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


_LEAN_DECL_MODIFIER_PREFIX = (
    r"(?:(?:private|protected|public|noncomputable|partial|unsafe)\s+)*"
)
_LEAN_DECL_KINDS = (
    r"(?:theorem|lemma|example|def|abbrev|structure|"
    r"inductive|instance|class|axiom|opaque|end)"
)
LEAN_DECL_TOKEN_RE = re.compile(
    r"(?<![.\w'])\b"
    + _LEAN_DECL_MODIFIER_PREFIX
    + r"(theorem|lemma|example|def|abbrev|structure|inductive|instance|"
    r"class|axiom|opaque|end)\b"
    r"(?:\s+(?:(?:[\w']+|«[^»]+»)\.)*([\w']+|«[^»]+»))?"
)


def _strip_lean_segment(
    text: str, start: int, *, stop_at_rbrace: bool
) -> tuple[str, int]:
    """Strip comments and mask literal string payloads in a Lean segment.

    Preserves 1-based line numbers by keeping newlines inside stripped spans,
    and preserves expressions inside Lean interpolated strings (`s!"{...}"`,
    `m!"{...}"`, etc.) by recursively stripping each `{...}` interpolation.
    """
    out: list[str] = []
    i = start
    n = len(text)
    block_depth = 0
    brace_depth = 0
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
            continue
        if stop_at_rbrace:
            if ch == "{":
                brace_depth += 1
            elif ch == "}":
                if brace_depth == 0:
                    return "".join(out), i + 1
                brace_depth -= 1
        if ch == "«":
            i += 1
            inner_chars: list[str] = []
            while i < n:
                c = text[i]
                i += 1
                if c == "»":
                    break
                inner_chars.append(c)
            inner = "".join(inner_chars)
            newlines = "\n" * inner.count("\n")
            if inner and all(c.isalnum() or c in "_'" for c in inner):
                out.append(inner)
            else:
                out.append("«»" + newlines)
            continue
        if (
            ch == "r"
            and (
                i == 0
                or not (text[i - 1].isalnum() or text[i - 1] in "_'")
            )
            and i + 1 < n
            and text[i + 1] in '#"'
        ):
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            hashes = j - (i + 1)
            if j < n and text[j] == '"':
                out.append('""')
                i = j + 1
                closing = '"' + "#" * hashes
                while i < n:
                    if text.startswith(closing, i):
                        i += len(closing)
                        break
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
                continue
        if ch == "/" and nxt == "-":
            out.append(" ")
            block_depth = 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch == '"':
            is_interp = (
                i >= 2
                and text[i - 1] == "!"
                and (text[i - 2].isalnum() or text[i - 2] in "_'")
            )
            out.append('""')
            i += 1
            while i < n:
                c = text[i]
                if c == "\\":
                    if i + 1 < n and text[i + 1] == "\n":
                        out.append("\n")
                    i += 2
                    continue
                if is_interp and c == "{":
                    if i + 1 < n and text[i + 1] == "{":
                        i += 2
                        continue
                    out.append(" (")
                    inner_expr, i = _strip_lean_segment(
                        text, i + 1, stop_at_rbrace=True
                    )
                    out.append(inner_expr)
                    out.append(") ")
                    continue
                if c == "\n":
                    out.append("\n")
                i += 1
                if c == '"':
                    break
            continue
        if ch == "'" and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")
        ):
            j = i + 1
            if j < n and text[j] == "\\":
                j += 2
            elif j < n and text[j] != "\n":
                j += 1
            if j < n and text[j] == "'":
                out.append("''")
                i = j + 1
                continue
        out.append(ch)
        i += 1
    return "".join(out), i


def strip_lean_comments_and_strings(text: str) -> str:
    """Strip Lean `--` and nested `/- ... -/` comments while masking strings.

    Preserves 1-based line numbers by keeping newlines inside stripped spans,
    replaces literal string/char payloads with empty literals so `"/-"` cannot
    start a comment, and preserves `{...}` expressions inside interpolated
    strings (`s!"..."`, `m!"..."`, etc.) so hidden proofs cannot evade audits.
    """
    return _strip_lean_segment(text, 0, stop_at_rbrace=False)[0]


def _declaration_is_mid_line(cleaned: str, offset: int) -> bool:
    """Return True if non-whitespace code precedes `offset` on its line."""
    line_start = cleaned.rfind("\n", 0, offset) + 1
    return bool(cleaned[line_start:offset].strip())


def _find_theorem_line_span_in_cleaned(
    cleaned: str,
    matches: list[re.Match[str]],
    theorem_name: str,
) -> tuple[int, int]:
    start_idx: int | None = None
    start_line: int | None = None
    for i, m in enumerate(matches):
        kind = m.group(1)
        name = (m.group(2) or "").strip("«»")
        if kind in ("theorem", "lemma") and name == theorem_name:
            start_idx = i
            start_line = cleaned.count("\n", 0, m.start()) + 1
            break
    if start_idx is None or start_line is None:
        raise ValueError(
            f"theorem {theorem_name!r} not found in fixture source"
        )
    if _declaration_is_mid_line(cleaned, matches[start_idx].start()):
        raise ValueError(
            f"same-line declaration precedes {theorem_name!r} on line "
            f"{start_line}"
        )
    if start_idx + 1 < len(matches):
        next_match = matches[start_idx + 1]
        next_line = cleaned.count("\n", 0, next_match.start()) + 1
        if next_line == start_line or _declaration_is_mid_line(
            cleaned, next_match.start()
        ):
            raise ValueError(
                f"same-line declaration follows {theorem_name!r} on line "
                f"{next_line}"
            )
        return (start_line, next_line - 1)
    return (start_line, len(cleaned.splitlines()))


def find_theorem_line_span(
    fixture_text: str,
    theorem_name: str,
) -> tuple[int, int]:
    """Return the inclusive 1-based `(start, end)` line span of `theorem_name`.

    Used to confirm that a Lean proof failure on a mutated semantics actually
    originated inside the guard's dedicated refutation theorem rather than in
    an unrelated declaration or file header. Uses the offset-based declaration
    scanner (`LEAN_DECL_TOKEN_RE`) and fails closed if another declaration
    shares any physical line with `theorem_name` (including mid-line
    declarations on a multi-line theorem's final line).
    """
    cleaned = strip_lean_comments_and_strings(fixture_text)
    matches = list(LEAN_DECL_TOKEN_RE.finditer(cleaned))
    return _find_theorem_line_span_in_cleaned(cleaned, matches, theorem_name)


# Exact cataloged refutation assertions whose statement shape is pinned
# verbatim (evaluation-order, allocation-ID freshness, precise span resolution,
# and 128-bit mathematical overflow detection guards whose killed assertion is
# not a `.fault`/`.error` equality). Pinning their normalized declaration text
# prevents unrelated positive conjuncts or secondary canaries from piggybacking
# on an exemption.
PINNED_EXACT_REFUTATIONS: dict[str, str] = {
    "refute_step_v2_assign_resolves_destination_first": (
        "theorem refute_step_v2_assign_resolves_destination_first : "
        "(match evalStatementV2 bodyStoreThroughMovedPtr "
        "{ defId := 0, blockIdx := 0, stmtIdx := 0, "
        "locals := [.immediate (some .unit), "
        ".immediate (some (.ptr ⟨some 1, 0, .isize⟩))] } "
        "{ allocations := [{ allocId := 1 alignLog2 := 0 "
        "mutability := .mut bytes := [] live := true }], "
        "nextAllocId := 2 } {} "
        "(.assign ⟨1, [.deref]⟩ (.unaryOp .ptrMetadata (.move ⟨1, []⟩))) "
        "with | .step _ => True | _ => False) := trivial"
    ),
    "refute_mem_v2_entry_byte_prov_fresh": (
        "theorem refute_mem_v2_entry_byte_prov_fresh : "
        "let cm : CallerMemory := { allocations := [{ "
        "allocId := 2 alignLog2 := 0 mutability := .mut "
        "bytes := [.init 0 (some 5)] live := true }] } "
        "(allocateStack (entryMemoryWithCaller cm) ⟨1, 0⟩).2.allocId "
        "= 6 := rfl"
    ),
    "refute_mem_v2_entry_raw_ptr_arg_fresh": (
        "theorem refute_mem_v2_entry_raw_ptr_arg_fresh : "
        "let emptyCm : CallerMemory := { allocations := [] } "
        "(allocateStack (entryMemoryForArgsV2 emptyCm "
        "[.rawPtr .shared (.int .i8 false)] "
        "[.ptr ⟨some 5, 0, .isize⟩]) ⟨1, 0⟩).2.allocId = 6 := rfl"
    ),
    "refute_mem_v2_entry_option_raw_ptr_ty": (
        "theorem refute_mem_v2_entry_option_raw_ptr_ty : "
        "let emptyCm : CallerMemory := { allocations := [] } "
        "(allocateStack (entryMemoryForArgsV2 emptyCm "
        "[.option (.rawPtr .shared (.int .i8 false))] "
        "[.optionVal (some (.ptr ⟨some 5, 0, .isize⟩))]) "
        "⟨1, 0⟩).2.allocId = 6 ∧ "
        "(allocateStack (entryMemoryForArgsV2 emptyCm "
        "[.tuple [.int .i8 false, "
        ".option (.rawPtr .shared (.int .i8 false))]] "
        "[.tuple [.scalar ⟨.i8, false, 0⟩, "
        ".optionVal (some (.ptr ⟨some 5, 0, .isize⟩))]]) "
        "⟨1, 0⟩).2.allocId = 6 := ⟨rfl, rfl⟩"
    ),
    "refute_mem_v2_entry_option_raw_ptr_val": (
        "theorem refute_mem_v2_entry_option_raw_ptr_val : "
        "maxValPtrAllocId (.optionVal (some (.ptr ⟨some 5, 0, .isize⟩))) "
        "= 5 ∧ maxValPtrAllocId (.tuple [.scalar ⟨.i8, false, 0⟩, "
        ".optionVal (some (.ptr ⟨some 5, 0, .isize⟩))]) = 5 := ⟨rfl, rfl⟩"
    ),
    "refute_step_v2_assign_range_field_span": (
        "theorem refute_step_v2_assign_range_field_span : "
        "checkAssignCopyHazardV2 rangeHazLocals.1 rangeHazLocals.2 "
        "emptyMemory (.local 1) (.range (.int .isize false)) "
        "(.aggregateRange (.int .isize false) "
        "(.copy { localId := 2, projection := [] }) "
        "(.copy { localId := 1, projection := "
        "[.field 1 (.int .isize false)] })) = .ok () := rfl"
    ),
    "refute_step_v2_assign_option_payload_span": (
        "theorem refute_step_v2_assign_option_payload_span : "
        "let u32Ty : MirTy := .int .i32 false "
        "checkAssignCopyHazardV2 optHazLocals.1 optHazLocals.2 "
        "emptyMemory (.local 3) (.tuple [u32Ty, u32Ty, .option u32Ty]) "
        "(.aggregateTuple [ "
        ".copy { localId := 1, projection := [.field 1 u32Ty] }, "
        ".copy { localId := 3, projection := "
        "[.field 2 (.option u32Ty), .downcast 1, .field 0 u32Ty] }, "
        ".copy { localId := 2, projection := [] }]) = .ok () ∧ "
        "checkAssignCopyHazardV2 optHazLocals.1 optHazLocals.2 "
        "emptyMemory (.local 1) (.tuple [.option u32Ty, u32Ty]) "
        "(.aggregateTuple [ "
        ".copy { localId := 2, projection := [] }, "
        ".copy { localId := 1, projection := "
        "[.field 0 (.option u32Ty), .downcast 1, .field 0 u32Ty] }]) "
        "= .error .unsupported := ⟨rfl, rfl⟩"
    ),
    "refute_core_contracts_i128_host_overflow": (
        "theorem refute_core_contracts_i128_host_overflow : "
        "let u128Ty : MirTy := .int .i128 false "
        "let i128Ty : MirTy := .int .i128 true "
        "let u128Max : ScalarVal := "
        "⟨.i128, false, BitVec.ofNat 128 "
        "340282366920938463463374607431768211455⟩ "
        "let u128Zero : ScalarVal := ⟨.i128, false, 0⟩ "
        "let u128One : ScalarVal := ⟨.i128, false, 1⟩ "
        "let u128Two : ScalarVal := ⟨.i128, false, 2⟩ "
        "let i128Max : ScalarVal := "
        "⟨.i128, true, BitVec.ofNat 128 "
        "170141183460469231731687303715884105727⟩ "
        "let i128Min : ScalarVal := "
        "⟨.i128, true, BitVec.ofNat 128 "
        "170141183460469231731687303715884105728⟩ "
        "let i128One : ScalarVal := ⟨.i128, true, 1⟩ "
        "let i128NegOne : ScalarVal := "
        "⟨.i128, true, BitVec.ofNat 128 "
        "340282366920938463463374607431768211455⟩ "
        "execCoreContractOp MemoryState.empty "
        "(.numCheckedAdd .i128 false) "
        "[(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)] "
        "(.option u128Ty) = .ok (.optionVal none, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numCheckedSub .i128 false) "
        "[(u128Ty, .scalar u128Zero), (u128Ty, .scalar u128One)] "
        "(.option u128Ty) = .ok (.optionVal none, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numCheckedAdd .i128 true) "
        "[(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)] "
        "(.option i128Ty) = .ok (.optionVal none, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numCheckedMul .i128 false) "
        "[(u128Ty, .scalar u128Max), (u128Ty, .scalar u128Two)] "
        "(.option u128Ty) = .ok (.optionVal none, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numSaturatingAdd .i128 false) "
        "[(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)] "
        "u128Ty = .ok (.scalar u128Max, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numSaturatingAdd .i128 true) "
        "[(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)] "
        "i128Ty = .ok (.scalar i128Max, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numSaturatingAdd .i128 true) "
        "[(i128Ty, .scalar i128Min), (i128Ty, .scalar i128NegOne)] "
        "i128Ty = .ok (.scalar i128Min, MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numOverflowingAdd .i128 false) "
        "[(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)] "
        "(.tuple [u128Ty, .bool]) = "
        ".ok (.tuple [.scalar u128Zero, .bool true], MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numOverflowingSub .i128 false) "
        "[(u128Ty, .scalar u128Zero), (u128Ty, .scalar u128One)] "
        "(.tuple [u128Ty, .bool]) = "
        ".ok (.tuple [.scalar u128Max, .bool true], MemoryState.empty) ∧ "
        "execCoreContractOp MemoryState.empty "
        "(.numOverflowingAdd .i128 true) "
        "[(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)] "
        "(.tuple [i128Ty, .bool]) = "
        ".ok (.tuple [.scalar i128Min, .bool true], MemoryState.empty) "
        ":= ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩"
    ),
    # Eight multi-step setup refutations whose `.ok`/`.step` setup prefixes are
    # independently proved in `PositiveSanity.positive_pinned_setup_prefixes`,
    # so over-rejecting mutants fail the sanity check rather than registering
    # false kills. Unpinned refutations may never use `| .ok` / `| .step` arms.
    "refute_bytes_uninit_memory_read": (
        "theorem refute_bytes_uninit_memory_read : "
        "(match initState progIndirectUninitRead queryEmpty with "
        "| .ok s₀ => match evalStep progIndirectUninitRead 0 s₀ with "
        "| .step s₁ => match forceAllocation progIndirectUninitRead s₁ 1 with "
        "| .ok (s₂, _) => evalStep progIndirectUninitRead 0 s₂ = "
        ".fault .undefined | .error _ => False | _ => False "
        "| .error _ => False) := rfl"
    ),
    "refute_step_move_deinit_indirect": (
        "theorem refute_step_move_deinit_indirect : "
        "(match initState progUseAfterMove { args := [u32Val 7] } with "
        "| .ok s₀ => match forceAllocation progUseAfterMove s₀ 1 with "
        "| .ok (s₁, _) => match evalStep progUseAfterMove 0 s₁ with "
        "| .step s₂ => evalStep progUseAfterMove 0 s₂ = .fault .undefined "
        "| _ => False | .error _ => False | .error _ => False) := rfl"
    ),
    "refute_step_return_indirect_uninit": (
        "theorem refute_step_return_indirect_uninit : "
        "(match initState progReturnUninit queryEmpty with "
        "| .ok s₀ => match forceAllocation progReturnUninit s₀ 0 with "
        "| .ok (s₁, _) => evalStep progReturnUninit 0 s₁ = .fault .undefined "
        "| .error _ => False | .error _ => False) := rfl"
    ),
    "refute_step_force_alloc_dead_local": (
        "theorem refute_step_force_alloc_dead_local : "
        "(match initState progDeadLocalForForceAlloc queryEmpty with "
        "| .ok s₀ => match forceAllocation progDeadLocalForForceAlloc s₀ 1 "
        "with | .error .undefined => True | _ => False "
        "| .error _ => False) := trivial"
    ),
    "refute_step_v2_return_dangling_stack_ref": (
        "theorem refute_step_v2_return_dangling_stack_ref : "
        "(match initStateV2 progDanglingStackRefV2 "
        "{ args := [.scalar ⟨.i8, false, BitVec.ofNat 128 42⟩] } with "
        "| .ok s₀ => match evalStepV2 progDanglingStackRefV2 s₀ with "
        "| .step s₁ => match evalStepV2 progDanglingStackRefV2 s₁ with "
        "| .fault .undefined => True | _ => False | _ => False "
        "| .error _ => False) := trivial"
    ),
    "refute_step_v2_assert_abort_extract_caller_mem": (
        "theorem refute_step_v2_assert_abort_extract_caller_mem : "
        "(match initStateV2 progMutBeforeAbortV2 "
        "{ args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := cmBeforeAbort } "
        "with | .ok s₀ => match evalStepV2 progMutBeforeAbortV2 s₀ with "
        "| .step s₁ => match evalStepV2 progMutBeforeAbortV2 s₁ with "
        "| .done (.aborted cm') => cm' = cmAfterAbort | _ => False "
        "| _ => False | .error _ => False) := rfl"
    ),
    "refute_state_v2_init_uses_entry_memory_for_args": (
        "theorem refute_state_v2_init_uses_entry_memory_for_args : "
        "let rawU8Const : MirTy := .rawPtr .shared u8Ty "
        "let prog : Program := { scope := .unit pointerWidthBits := 64 "
        "mirProfileVersion := 2 bodies := [{ argumentCount := 1 "
        "locals := [u8Ty, rawU8Const, u8Ty, rawU8Const] basicBlocks := [{ "
        "statements := [ .storageLive 2, "
        ".assign { localId := 2, projection := [] } "
        "(.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 42)⟩)), "
        ".storageLive 3, .assign { localId := 3, projection := [] } "
        "(.addressOf .shared { localId := 2, projection := [] }), "
        ".assign { localId := 0, projection := [] } "
        "(.use (.copy { localId := 1, projection := [.deref] })) ] "
        "terminator := .return_ }] isUnsafe := true identity := \"\" }] } "
        "(match initStateV2 prog "
        "{ args := [.ptr ⟨some 2, 0, .isize⟩], "
        "callerMem := { allocations := [] } } with "
        "| .ok s0 => match evalStepV2 prog s0 with "
        "| .step s1 => match evalStepV2 prog s1 with "
        "| .step s2 => match evalStepV2 prog s2 with "
        "| .step s3 => match evalStepV2 prog s3 with "
        "| .step s4 => evalStepV2 prog s4 = .fault .undefined "
        "| _ => False | _ => False | _ => False | _ => False "
        "| .error _ => False) := rfl"
    ),
    "refute_step_v2_core_panic_abort_extract_caller_mem": (
        "theorem refute_step_v2_core_panic_abort_extract_caller_mem : "
        "(match initStateV2 progMutBeforeCorePanicV2 "
        "{ args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := cmBeforeAbort } "
        "with | .ok s₀ => match evalStepV2 progMutBeforeCorePanicV2 s₀ with "
        "| .step s₁ => match evalStepV2 progMutBeforeCorePanicV2 s₁ with "
        "| .done (.aborted cm') => cm' = cmAfterAbort | _ => False "
        "| _ => False | .error _ => False) := rfl"
    ),
    # Multi-step setup: the read through the stale pointer is reachable only
    # after `evalBoxFromVec` succeeds, which
    # `AllocSanity.alloc_sanity_index_and_realloc` requires of every mutant
    # for these same arguments.
    "refute_alloc_retire_heap_buffer": (
        "theorem refute_alloc_retire_heap_buffer : "
        "(match evalBoxFromVec acStaleMem acU8Ty acBufPtr 8 2 with "
        "| .ok (_, m') => readBytes m' ⟨2, 0⟩ 2 0 "
        "| .error _ => .ok []) = .error .undefined := rfl"
    ),
}

# Only non-guard helper theorem permitted in a refutation fixture: a shared
# fault-reachability lemma referenced by cataloged refutations.
ALLOWED_REFUTATION_HELPER_THEOREMS: dict[str, frozenset[str]] = {
    "BoundaryRefutations": frozenset({"reaches_fault_unreachable_v2"}),
}

_POS_CTOR_RE = re.compile(
    r"(?:\.|(?<![\w'])(?:_root_\.)?"
    r"(?:Except|StepOutcome|RunOutcome|Option|Sum"
    r"|Trusted\.MirSemantics\.\w+)\.)"
    r"(?:ok|step|returned|inr)\b"
    r"|(?<![\w'.])(?:ok|step|returned|inr)\b"
    r"|(?<![\w'])(?:_root_\.)?Option\.some\b"
    r"|\.\bsome\b"
    r"|(?<![:!<>])=\s*(?:\(\s*)*some\b"
    r"|(?:^|[\n:∧,])\s*(?:\(\s*)*some\b"
    r"|\bEq\s+(?:\(\s*)*some\b"
    r"|\bEq\b[^\n:=]*\s+\(?\s*some\b"
    r"|\|\s*(?:\(\s*)*some\b[^=>\n]*=>(?!\s*False\b)"
)
_OPEN_EXPORT_RE = re.compile(r"(?<![\w'])(open|export)\b([^\n]*)")
_ALLOWED_OPEN_TARGETS = frozenset({"Trusted.MirAst", "Trusted.MirSemantics"})
_DIRECT_SUCCESS_RE = re.compile(
    r"\.(?:isOk|isSome|isRight)\b"
    r"|\b(?:Except\.isOk|Option\.isSome|Sum\.isRight)\b"
    r"|(?<![:!<>])=\s*(?:\(\s*)*(?:(?:_root_\.)?Bool\.)?true\b"
    r"|(?:^|[\n:∧(])\s*(?:(?:_root_\.)?Bool\.)?true\s*(?:\)\s*)*=(?!=)"
    r"|\bEq\s+(?:\(\s*)*(?:(?:_root_\.)?Bool\.)?true\b"
    r"|\bEq\b[^\n:=]*\s+(?:(?:_root_\.)?Bool\.)?true\b"
    r"|(?:≠|!=)\s*(?:\(\s*)*(?:(?:_root_\.)?Bool\.)?false\b"
    r"|(?:(?:_root_\.)?Bool\.)?false\b[^=;|]*?(?:≠|!=)"
    r"|(?:¬|\b(?:_root_\.)?Not\b)\s*\(?[^()=|]*?(?:=\s*(?:(?:_root_\.)?Bool\.)?false\b"
    r"|(?:(?:_root_\.)?Bool\.)?false\b[^=|]*?=)"
    r"|(?:≠|!=)\s*(?:\.(?:fault|error|aborted)|\.done\s*\(\s*\.aborted|\bnone\b)"
    r"|(?:\.(?:fault|error|aborted)|\.done\s*\(\s*\.aborted)\b[^=;|]*?(?:≠|!=)"
    r"|(?:¬|\b(?:_root_\.)?Not\b)\s*\(?[^()=|]*?(?:=\s*(?:\.(?:fault|error|aborted)|\.done\s*\(\s*\.aborted)"
    r"|\.(?:fault|error|aborted)\b[^=|]*?=)"
    r"|(?:\.(?:fault|error|aborted)|\.done\s*\(\s*\.aborted|\b(?:(?:_root_\.)?Bool\.)?false\b)"
    r"[^|;]*?(?:→|->)\s*False\b"
    r"|(?:\.|(?<![\w'.]))"
    r"(?:rec|recOn|casesOn|brecOn|binductionOn|bindOn|ndrec|ndrecOn"
    r"|drec|drecOn|below|ibelow|elim|toBool"
    r"|isErr|isNone|isLeft|getD|map|bind)\b"
    r"|(?<![\w'])(?:_root_\.)?"
    r"(?:Except|StepOutcome|RunOutcome|Option|Sum"
    r"|Trusted\.MirSemantics\.\w+)\.noConfusion(?:Type)?\b"
    r"|(?<![\w'])(?:_root_\.)?(?:Decidable|Classical)\.\w+\b"
    r"|(?<![.\w'])(?:_root_\.)?(?:Eq\.(?:subst|mp|mpr)|cast|ite|dite|cond|decide)\b"
    r"|(?<![.\w'])\b(?:if|then|else)\b"
    r"|(?<![!=<>])!(?!=)"
    r"|(?<![\w'])(?:_root_\.)?(?:Bool\.not|Bool\.xor|BEq\.beq|bne)\b"
    r"|=="
    r"|(?<![\w'.])(?:(?:_root_\.)?Pure\.)?pure\b"
    r"|(?<![\w'.])return\b"
    r"|(?<![\w'])do\b"
    r"|(?<![\w'])(?:_root_\.)?(?:Bind\.bind|Seq\.seq|Functor\.map)\b"
)
_LAMBDA_TRUE_RE = re.compile(r"(?:(?<![\w'])fun\b|λ)[^=\n]*=>\s*True\b")
_NEG_BODY_VERIFIED_TRUE_RE = re.compile(
    r"¬\s*(?:BodyVerified(?:V2)?\b[^:=(){}]*\(\s*fun\s+_\s*=>\s*True\s*\)"
    r"|BodySatisfiesSafeContractV2\b[^:=(){}]*"
    r"\{\s*postAbort\s*:=\s*fun\s+_\s+_\s*=>\s*True\s*\})"
)
_HASH_COMMAND_RE = re.compile(r"(?<![\w'])#([A-Za-z_]\w*)")
_FORBIDDEN_META_CMD_RE = re.compile(
    r"(?<![.\w'])\b("
    r"run_cmd|run_tac|by_elab|initialize|builtin_initialize|elab|elab_rules|"
    r"syntax|macro|macro_rules|declare_syntax_cat|notation|infix|infixl|"
    r"infixr|prefix|postfix|attribute|set_option|deriving|section|"
    r"variable|universe|mutual|local|scoped|register_simp_attr|"
    r"init_quot"
    r")\b"
)
_ALLOWED_PREAMBLE_LINE_RE = re.compile(
    r"^(?:"
    r"prelude"
    r"|(?:public\s+)?import(?:\s+all)?\s+[A-Za-z_][A-Za-z0-9_'.]*"
    r"|namespace\s+GuardMutation"
    r"|open(?:\s+(?:Trusted\.MirAst|Trusted\.MirSemantics))+"
    r")$"
)
_TRUE_ARM_RE = re.compile(
    r"((?:\|\s*[^=|]+)+)=>\s*(?:True\b|(?:¬|\b(?:_root_\.)?Not\b)\s*False\b)"
)
_NEG_ARM_PAT_RE = re.compile(
    r"^(?:"
    r"\.(?:fault|error)(?:\s+(?:_|\.[A-Za-z_][A-Za-z0-9_']*))?"
    r"|(?:_root_\.)?(?:Except\.error|StepOutcome\.fault|RunOutcome\.fault)"
    r"(?:\s+(?:_|\.[A-Za-z_][A-Za-z0-9_']*))?"
    r"|(?:_root_\.)?(?:Option\.none|Bool\.false)"
    r"|none|false"
    r")$"
)
_WILDCARD_NON_FALSE_ARM_RE = re.compile(
    r"\|\s*(?:_|(?!(?:none|false)\b)[a-z][A-Za-z0-9_']*)\s*=>(?!\s*False\b)"
)
_POS_ARM_HEAD_RE = re.compile(
    r"^(?:\.(?:ok|step|returned|done|aborted)\b"
    r"|(?:_root_\.)?(?:Except\.ok|StepOutcome\.(?:step|done)"
    r"|RunOutcome\.(?:returned|aborted))\b)"
)
_ALLOWED_HELPER_DATA_TYPES: frozenset[str] = frozenset({
    "Program",
    "Body",
    "Allocation",
    "AllocByte",
    "List AllocByte",
    "Query",
    "CallerMemory",
    "Memory",
    "MemoryState",
    "FrameState",
    "State",
    "MirType",
    "MirTy",
    "List MirTy",
    "BasicBlock",
    "Statement",
    "StatementKind",
    "TerminatorKind",
    "Rvalue",
    "Operand",
    "Place",
    "Scalar",
    "ScalarVal",
    "Val",
    "LocalValue",
    "List LocalSlot",
    "List MirTy × List LocalSlot",
    "Nat",
    "Bool",
    "String",
    "PtrVal",
    "List Allocation",
    "UInt8",
})
_HELPER_PROOF_TOKEN_RE = re.compile(
    r"(?<![\w'.])(?:by|by_elab|run_tac|have|show|suffices|assert|calc|let"
    r"|match|WellFormed(?:V2)?|BodyVerified(?:V2)?"
    r"|BodySatisfiesSafeContractV2)\b"
)
_NEG_RHS_RE = re.compile(
    r"^(?:"
    r"\.(?:fault|error)(?:\s+(?:\.[A-Za-z_][A-Za-z0-9_']*"
    r"|\(\s*\.[A-Za-z_][A-Za-z0-9_']*(?:\s+[A-Za-z0-9_'.]+)*\s*\)"
    r"|[A-Za-z0-9_'.]+))*"
    r"|(?:_root_\.)?(?:Except\.error|StepOutcome\.fault"
    r"|RunOutcome\.fault)"
    r"\s+\.[A-Za-z_][A-Za-z0-9_']*"
    r"|(?:_root_\.)?(?:Option\.none|Bool\.false)"
    r"|none|false"
    r")$"
)
_NESTED_TYPE_FORBIDDEN_RE = re.compile(
    r"(?<![.\w'])\b(?:let|have|show|suffices|assert|calc|by|by_elab|run_tac)\b"
)
_NEG_PRED_HEAD_RE = re.compile(
    r"^¬\s*(?:Trusted\.MirSemantics\.)?"
    r"(?:WellFormed(?:V2)?|BodyVerified(?:V2)?"
    r"|BodySatisfiesSafeContractV2)\b"
)
_REACHES_NEG_RE = re.compile(
    r"^(?:Trusted\.MirSemantics\.)?ReachesResult(?:V2)?\b"
    r"[\s\S]*\(\s*\.fault\b[^()]*\)\s*$"
)
_ATOMIC_PROOF_RE = re.compile(
    r"^(?:rfl|trivial|refutes_wf_of_execFault\s+\(\s*fuel\s*:=\s*\d+\s*\)\s+rfl)$"
)
_BOUNDARY_ELIM_ALLOWED_IDENTS = frozenset({
    "h",
    "hFalse",
    "fun",
    "Bool",
    "noConfusion",
    "reachesResult_of_execFault",
    "reaches_fault_unreachable_v2",
    "refute_boundary_v2_wellformed_forbids_faults",
    "ReachesV2",
    "refl",
    "queryEmpty",
    "callerMem",
    "fuel",
    "rfl",
    "trivial",
    "undefined",
    "aborted",
    "_",
})
_REACH_BY_EXACT_ALLOWED_IDENTS = frozenset({
    "ReachesV2",
    "refl",
    "tail",
    "rfl",
    "trivial",
    "fun",
    "hWf",
    "undefined",
    "unsupported",
    "_",
})
_BY_CHANGE_STEP_RE = re.compile(
    r"^change\s+∃\s+s\s*:\s*State\s*,\s*"
    r"ReachesV2\s+[A-Za-z_][A-Za-z0-9_']*\s+_\s+s\s*∧\s*"
    r"StepV2\s+[A-Za-z_][A-Za-z0-9_']*\s+s\s*"
    r"\(\s*\.fault\s*\.(?:undefined|unsupported)\s*\)$"
)
_BY_HAVE_HEAD_RE = re.compile(
    r"^have\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*"
    r"ReachesResultV2\s+[A-Za-z_][A-Za-z0-9_']*\s+"
    r"[A-Za-z_][A-Za-z0-9_']*\s*"
    r"\(\s*\.fault\s*\.(?:undefined|unsupported)\s*\)\s*:=\s*(.*)$"
)


def _strip_outer_parens(expr: str) -> str:
    s = expr.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        closes_at_end = True
        for i, ch in enumerate(s):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    closes_at_end = False
                    break
        if closes_at_end and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def _extract_theorem_type_and_proof(body: str) -> tuple[str, str] | None:
    m_head = re.match(
        rf"\s*{_LEAN_DECL_MODIFIER_PREFIX}"
        r"(?:theorem|lemma)\s+[A-Za-z_][A-Za-z0-9_']*\s*:(?!=)",
        body,
    )
    if not m_head:
        return None
    colon_pos = m_head.end() - 1
    n = len(body)
    i = colon_pos + 1
    depth = 0
    pending_lets = 0
    while i < n:
        ch = body[i]
        if ch in "([{⟨":
            depth += 1
            i += 1
            continue
        if ch in ")]}⟩" and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0:
            if (
                body.startswith("let", i)
                and (
                    i == 0
                    or not (body[i - 1].isalnum() or body[i - 1] in "_'")
                )
                and (
                    i + 3 >= n
                    or not (body[i + 3].isalnum() or body[i + 3] in "_'")
                )
            ):
                pending_lets += 1
                i += 3
                continue
            if body.startswith(":=", i):
                if pending_lets > 0:
                    pending_lets -= 1
                    i += 2
                    continue
                return body[colon_pos + 1 : i], body[i + 2 :]
        i += 1
    return None


def _find_top_level_eq(expr: str) -> int:
    depth = 0
    i = 0
    n = len(expr)
    while i < n:
        ch = expr[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩" and depth > 0:
            depth -= 1
        elif depth == 0 and ch == "=":
            prev_ch = expr[i - 1] if i > 0 else ""
            next_ch = expr[i + 1] if i + 1 < n else ""
            if prev_ch not in ":!<>=" and next_ch not in "=>":
                return i
        i += 1
    return -1


def _has_top_level_connective(expr: str) -> bool:
    depth = 0
    i = 0
    n = len(expr)
    while i < n:
        ch = expr[i]
        if ch in "([{⟨":
            depth += 1
            i += 1
            continue
        if ch in ")]}⟩" and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0:
            if ch in "→↔∨∀∃≠":
                return True
            if expr.startswith(("->", "<->", "!="), i):
                return True
        i += 1
    return False


def _strip_and_validate_leading_lets(
    expr: str,
    *,
    allowed_bare_idents: frozenset[str] = frozenset(),
    pair_helpers: frozenset[str] = frozenset(),
) -> tuple[str, frozenset[str]] | None:
    s = expr
    bound: set[str] = set()
    while True:
        m_let = re.match(r"([ \t]*\n)*([ \t]*)let\b", s)
        if not m_let:
            return s.strip(), frozenset(bound)
        let_col = len(m_let.group(2))
        i = m_let.end()
        n = len(s)
        depth = 0
        colon_pos = -1
        assign_pos = -1
        end_pos = -1
        while i < n:
            ch = s[i]
            if ch in "([{⟨":
                depth += 1
                i += 1
                continue
            if ch in ")]}⟩" and depth > 0:
                depth -= 1
                i += 1
                continue
            if depth == 0:
                if assign_pos == -1:
                    if s.startswith(":=", i):
                        assign_pos = i
                        i += 2
                        continue
                    if ch == ":" and colon_pos == -1:
                        colon_pos = i
                        i += 1
                        continue
                else:
                    if ch == ";":
                        end_pos = i + 1
                        break
                    if ch == "\n":
                        j = i + 1
                        while j < n and s[j] in " \t":
                            j += 1
                        if j < n and s[j] != "\n":
                            next_col = j - (i + 1)
                            if next_col <= let_col:
                                end_pos = i + 1
                                break
            i += 1
        if colon_pos == -1 or assign_pos == -1 or end_pos == -1:
            return None
        binder = s[m_let.end() : colon_pos].strip()
        if not _is_valid_fresh_local_ident(binder):
            return None
        let_ty = " ".join(s[colon_pos + 1 : assign_pos].split())
        if let_ty not in _ALLOWED_HELPER_DATA_TYPES:
            return None
        rhs_end = end_pos - 1 if s[end_pos - 1] == ";" else end_pos
        rhs = s[assign_pos + 2 : rhs_end].strip()
        if (
            not rhs
            or _HELPER_PROOF_TOKEN_RE.search(rhs)
            or _has_forbidden_type_or_data_expr(
                rhs,
                pair_helpers=pair_helpers,
                allowed_bare_idents=allowed_bare_idents | frozenset(bound),
            )
            or re.search(r"(?<!:):(?!=[=]?)", rhs)
            or _find_top_level_eq(rhs) != -1
            or _has_top_level_connective(rhs)
        ):
            return None
        bound.add(binder)
        s = s[end_pos:]


def _split_top_level(expr: str, sep: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    i = 0
    n = len(expr)
    k = len(sep)
    while i < n:
        ch = expr[i]
        if ch in "([{⟨":
            depth += 1
            i += 1
            continue
        if ch in ")]}⟩" and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0 and expr.startswith(sep, i):
            parts.append(expr[start:i].strip())
            i += k
            start = i
            continue
        i += 1
    parts.append(expr[start:].strip())
    return parts


_FORBIDDEN_DATA_EXPR_RE = re.compile(
    r"@"
    r"|(?<![.\w'])\b(?:match|fun|if|then|else|let|have|show|suffices|assert"
    r"|calc|by|by_elab|run_tac|rfl|trivial|decide|of_decide_eq_true|ite|dite"
    r"|cast|absurd|congr|congrArg|congrFun|getElem)\b"
    r"|(?<![.\w'])\bcond\b(?!\s*:=)"
    r"|λ|=>"
    r"|[)\]}⟩]\."
    r"|(?<=[\w')\]}⟩])\["
    r"|(?:\.|(?<![\w'.]))"
    r"(?:rec|recOn|casesOn|brecOn|binductionOn|bindOn|ndrec|ndrecOn"
    r"|drec|drecOn|below|ibelow|elim|noConfusion|noConfusionType|toBool"
    r"|isErr|isNone|isLeft|getD|map|bind)\b"
)
_INERT_DATA_TOKEN_RE = re.compile(
    r"\s+"
    r"|:=|\"\"|''|[()\[\]{},⟨⟩]"
    r"|-?(?:0x[0-9a-fA-F]+|[0-9]+)(?=$|[\s()\[\]{},⟨⟩])"
    r"|\.[A-Za-z0-9_]+(?=$|[\s()\[\]{},⟨⟩])"
    r"|[^\s()\[\]{},⟨⟩]+"
)
_BARE_IDENT_RE = re.compile(r"(?<![.\w'])[^\s()\[\]{},⟨⟩.,:=]+")
_ALLOWED_QUALIFIED_DATA_TOKENS: frozenset[str] = frozenset({
    "BitVec.ofNat",
    "Int.ofNat",
    "Int.negSucc",
    "List.replicate",
    "MemoryState.empty",
    "Nat.pow",
    "body.locals",
    "frame.locals",
    "queryEmpty.callerMem",
})
# Closed set of target `MirSemantics` operations permitted strictly as the
# single flat outermost head of a refutation equality LHS or `match` scrutinee
# (never nested inside data arguments, `let` bindings, or helpers).
_ALLOWED_REFUTATION_HEAD_FNS: frozenset[str] = frozenset({
    "boxPointeeValidInMem",
    "boxValidInMem",
    "checkAggregateCopyHazardLoopV2",
    "checkAssignCopyHazardV2",
    "constantIndexOffset",
    "deallocateStack",
    "encodeValV2",
    "evalAddressOfRvalueV2",
    "evalAssertFailure",
    "evalCastKindV2",
    "evalCorePanicAbort",
    "evalFakeAddressOfRvalueV2",
    "evalNonRootReturn",
    "evalOperandToSlotV2",
    "evalPtrOffsetV2",
    "evalPtrToPtrCastV2",
    "evalRodataRefConstV2",
    "evalRvalueV2",
    "evalStatementV2",
    "evalStep",
    "evalStepV2",
    "evalTerminator",
    "evalTerminatorV2",
    "evalVecIndex",
    "evalVecWithCapacity",
    "execCoreCallOp",
    "execCoreContractOp",
    "forceAllocation",
    "heapBufValidInMem",
    "initState",
    "initStateV2",
    "isFakePtrMetadataLocalV2",
    "isSupportedV2LocalTy",
    "ownedHeapBufValidInMem",
    "ptrAddInMem",
    "readBytes",
    "readPlaceV2",
    "refValidInMem",
    "resolvePlaceDestV2",
    "sliceFromRawPartsCheck",
    "sliceGetUncheckedCheck",
    "sliceRefRawCheck",
    "spansPairwiseDisjoint",
    "validUtf8Bytes",
    "vecGrowCap",
    "vecValidInMem",
    "writeBytes",
    "writePlaceV2",
    "writeUninit",
    "zeroCapPtrValidInMem",
})
# Closed set of genuinely inert bare identifiers (pure AST/struct field names,
# basic data constructors/types, and inert constants) permitted inside data
# helpers, `let` RHSs, and arguments to target calls/predicates.
_ALLOWED_INERT_DATA_IDENTS: frozenset[str] = frozenset({
    "BitVec",
    "EffectMaskV2",
    "Int",
    "List",
    "MemoryState",
    "MirTy",
    "Nat",
    "_",
    "alignLog2",
    "allocId",
    "allocations",
    "allowAbort",
    "args",
    "argumentCount",
    "basicBlocks",
    "blockIdx",
    "bodies",
    "bytes",
    "callerMem",
    "cleanup",
    "cond",
    "defId",
    "discrSigned",
    "discrWidth",
    "discriminants",
    "effects",
    "emptyMemory",
    "entryMemory",
    "expected",
    "false",
    "hasLocalPanicHandler",
    "i8Ty",
    "i8Val",
    "id",
    "identity",
    "isUnsafe",
    "kind",
    "len",
    "live",
    "localId",
    "locals",
    "mirProfileVersion",
    "mkBinOpProg",
    "mkConstRetProg",
    "mkSingleBlockProg",
    "msg",
    "mutability",
    "nextAllocId",
    "none",
    "offset",
    "offsetBytes",
    "overflowChecks",
    "panicStrategy",
    "pointee",
    "pointerWidthBits",
    "postAbort",
    "profileV2TargetEndian",
    "projection",
    "ptr",
    "queryEmpty",
    "reprU8EnumTy",
    "retDst",
    "retDst?",
    "retTarget",
    "retTarget?",
    "scalarNatVal",
    "scope",
    "signed",
    "some",
    "statements",
    "stmtIdx",
    "tagRepr",
    "target",
    "terminator",
    "true",
    "u32Ty",
    "u32Val",
    "u8Ty",
    "unwind",
    "width",
    "with",
})
_CANONICAL_BODY_PRE_RE = re.compile(
    r"\(\s*fun\s+_\s*=>\s*(?:True|False)\s*\)\s*$"
)
_CANONICAL_CONTRACT_POST_RE = re.compile(
    r"\{\s*postAbort\s*:=\s*fun\s+_\s+_\s*=>\s*True\s*\}\s*$"
)
_NEG_BODY_OR_CONTRACT_HEAD_RE = re.compile(
    r"^¬\s*(?:Trusted\.MirSemantics\.)?"
    r"(?:BodyVerified(?:V2)?|BodySatisfiesSafeContractV2)\b"
)


# Built-in Lean keywords, prelude types/constructors, tactic/eliminator names,
# and semantic predicates that local `let`/`def`/`abbrev`/`fun`/`have` binders
# must never shadow inside closed refutation fixtures or pure-data helpers.
_FORBIDDEN_LOCAL_BINDER_NAMES: frozenset[str] = (
    frozenset({
        "_",
        "let",
        "fun",
        "have",
        "show",
        "suffices",
        "assert",
        "calc",
        "by",
        "by_elab",
        "run_tac",
        "match",
        "with",
        "where",
        "if",
        "then",
        "else",
        "do",
        "return",
        "def",
        "abbrev",
        "theorem",
        "lemma",
        "example",
        "axiom",
        "opaque",
        "inductive",
        "structure",
        "class",
        "instance",
        "import",
        "open",
        "export",
        "namespace",
        "end",
        "section",
        "variable",
        "universe",
        "private",
        "protected",
        "noncomputable",
        "partial",
        "unsafe",
        "mut",
        "true",
        "false",
        "True",
        "False",
        "Bool",
        "Prop",
        "Sort",
        "Type",
        "Unit",
        "Empty",
        "Nat",
        "Int",
        "String",
        "List",
        "Option",
        "Except",
        "StepOutcome",
        "RunOutcome",
        "Sum",
        "BitVec",
        "UInt8",
        "some",
        "none",
        "ok",
        "error",
        "fault",
        "step",
        "done",
        "returned",
        "aborted",
        "inl",
        "inr",
        "And",
        "Or",
        "Not",
        "Eq",
        "HEq",
        "Iff",
        "BEq",
        "Decidable",
        "Classical",
        "Pure",
        "Bind",
        "Seq",
        "Functor",
        "rfl",
        "decide",
        "sorry",
        "admit",
        "trivial",
        "pure",
        "bind",
        "map",
        "ite",
        "dite",
        "cond",
        "cast",
        "absurd",
        "congr",
        "congrArg",
        "congrFun",
        "getElem",
        "beq",
        "bne",
        "not",
        "xor",
        "refl",
        "tail",
        "rec",
        "recOn",
        "casesOn",
        "brecOn",
        "binductionOn",
        "bindOn",
        "ndrec",
        "ndrecOn",
        "drec",
        "drecOn",
        "below",
        "ibelow",
        "elim",
        "noConfusion",
        "noConfusionType",
        "toBool",
        "isOk",
        "isSome",
        "isRight",
        "isErr",
        "isNone",
        "isLeft",
        "getD",
        "ReachesV2",
        "ReachesResultV2",
        "StepV2",
        "State",
        "WellFormed",
        "WellFormedV2",
        "BodyVerified",
        "BodyVerifiedV2",
        "BodySatisfiesSafeContractV2",
    })
    | _ALLOWED_REFUTATION_HEAD_FNS
)


def _is_valid_fresh_local_ident(name: str) -> bool:
    """Return True if `name` is an unquoted ASCII binder name that does not
    shadow any built-in Lean constructor, keyword, or validator predicate."""
    return (
        bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name))
        and name not in _FORBIDDEN_LOCAL_BINDER_NAMES
    )


def _has_forbidden_type_or_data_expr(
    expr: str,
    *,
    allow_canonical_post_lambda: bool = False,
    pair_helpers: frozenset[str] = frozenset(),
    allowed_bare_idents: frozenset[str] = frozenset(),
) -> bool:
    """Return True if a type argument, scrutinee arg, or data RHS uses
    branching, eliminators, lambdas, proof terms, postfix/index projections,
    or any token (ASCII, Unicode, quoted, or symbolic) outside the closed
    inert-data allowlist."""
    s = expr
    if allow_canonical_post_lambda:
        if re.match(
            r"^¬\s*(?:Trusted\.MirSemantics\.)?BodyVerified(?:V2)?\b", s
        ):
            s = _CANONICAL_BODY_PRE_RE.sub("", s, count=1)
        elif re.match(
            r"^¬\s*(?:Trusted\.MirSemantics\.)?BodySatisfiesSafeContractV2\b", s
        ):
            s = _CANONICAL_CONTRACT_POST_RE.sub("", s, count=1)
    s = re.sub(
        r"\(\s*\{\}\s*:\s*EffectMaskV2\s*\)(?:\.allowAbort)?", "{}", s
    )
    if _FORBIDDEN_DATA_EXPR_RE.search(s):
        return True
    permitted_bare = _ALLOWED_INERT_DATA_IDENTS | allowed_bare_idents
    pos = 0
    n = len(s)
    while pos < n:
        m = _INERT_DATA_TOKEN_RE.match(s, pos)
        if not m:
            return True
        tok = m.group(0)
        pos = m.end()
        if (
            tok[0].isspace()
            or tok in (":=", '""', "''", "-", "(", ")", "[", "]", "{", "}", ",", "⟨", "⟩")
            or re.fullmatch(r"-?(?:0x[0-9a-fA-F]+|[0-9]+)", tok)
            or re.fullmatch(r"\.[A-Za-z0-9_]+", tok)
        ):
            continue
        if "." in tok:
            if tok in _ALLOWED_QUALIFIED_DATA_TOKENS:
                continue
            if tok.endswith((".1", ".2")) and tok[:-2] in pair_helpers:
                continue
            return True
        if tok not in permitted_bare:
            return True
    return False


def _is_allowed_head_application(
    expr: str,
    *,
    pair_helpers: frozenset[str],
    allowed_bare_idents: frozenset[str],
) -> bool:
    """Check that `expr` is a single flat application of one allowlisted
    target `MirSemantics` head function to strictly inert pure-data args."""
    s = _strip_outer_parens(expr)
    if re.fullmatch(r"\(\s*\{\}\s*:\s*EffectMaskV2\s*\)\.allowAbort", s):
        return True
    m_head = re.match(r"^([^\s()\[\]{},⟨⟩]+)(.*)$", s, re.S)
    if not m_head:
        return False
    head, args = m_head.group(1), m_head.group(2)
    if head not in _ALLOWED_REFUTATION_HEAD_FNS:
        return False
    return not _has_forbidden_type_or_data_expr(
        args,
        pair_helpers=pair_helpers,
        allowed_bare_idents=allowed_bare_idents,
    )


def _is_allowed_refutation_type(
    raw_type: str,
    *,
    pair_helpers: frozenset[str] = frozenset(),
    allowed_bare_idents: frozenset[str] = frozenset(),
) -> bool:
    let_res = _strip_and_validate_leading_lets(
        raw_type,
        allowed_bare_idents=allowed_bare_idents,
        pair_helpers=pair_helpers,
    )
    if let_res is None:
        return False
    stripped, let_binders = let_res
    scoped_idents = allowed_bare_idents | let_binders
    s = _strip_outer_parens(stripped)
    if not s:
        return False
    conjuncts = _split_top_level(s, "∧")
    if len(conjuncts) > 1:
        return all(
            _is_allowed_refutation_type(
                c,
                pair_helpers=pair_helpers,
                allowed_bare_idents=scoped_idents,
            )
            for c in conjuncts
        )
    s_no_empty_mask = re.sub(r"\(\s*\{\}\s*:\s*EffectMaskV2\s*\)", "{}", s)
    if _NESTED_TYPE_FORBIDDEN_RE.search(s_no_empty_mask) or re.search(
        r"(?<!:):(?!=[=]?)", s_no_empty_mask
    ):
        return False
    if _has_top_level_connective(s):
        return False
    m_neg_pred = _NEG_PRED_HEAD_RE.match(s)
    if m_neg_pred:
        if _find_top_level_eq(s) != -1:
            return False
        pred_rest = s[m_neg_pred.end() :]
        if _NEG_BODY_OR_CONTRACT_HEAD_RE.match(s):
            if re.match(
                r"^¬\s*(?:Trusted\.MirSemantics\.)?BodyVerified(?:V2)?\b", s
            ):
                pred_rest = _CANONICAL_BODY_PRE_RE.sub("", pred_rest, count=1)
            else:
                pred_rest = _CANONICAL_CONTRACT_POST_RE.sub(
                    "", pred_rest, count=1
                )
        return not _has_forbidden_type_or_data_expr(
            pred_rest,
            pair_helpers=pair_helpers,
            allowed_bare_idents=scoped_idents,
        )
    m_reach = _REACHES_NEG_RE.match(s)
    if m_reach:
        if _find_top_level_eq(s) != -1:
            return False
        reach_rest = re.sub(
            r"^(?:Trusted\.MirSemantics\.)?ReachesResult(?:V2)?\b",
            "",
            s,
            count=1,
        )
        return not _has_forbidden_type_or_data_expr(
            reach_rest,
            pair_helpers=pair_helpers,
            allowed_bare_idents=scoped_idents,
        )
    if re.match(r"^match\b", s):
        m_with = re.search(r"\bwith\b", s)
        if not m_with:
            return False
        scrutinee = s[len("match") : m_with.start()]
        if not _is_allowed_head_application(
            scrutinee,
            pair_helpers=pair_helpers,
            allowed_bare_idents=scoped_idents,
        ):
            return False
        arms_text = s[m_with.end() :].strip()
        if not arms_text.startswith("|"):
            return False
        arms: list[str] = []
        depth = 0
        nested_matches = 0
        arm_start: int | None = None
        i = 0
        n = len(arms_text)
        while i < n:
            ch = arms_text[i]
            if ch in "([{⟨":
                depth += 1
                i += 1
                continue
            if ch in ")]}⟩" and depth > 0:
                depth -= 1
                i += 1
                continue
            if depth == 0:
                if (
                    arms_text.startswith("match", i)
                    and (
                        i == 0
                        or not (
                            arms_text[i - 1].isalnum()
                            or arms_text[i - 1] in "_'"
                        )
                    )
                    and (
                        i + 5 >= n
                        or not (
                            arms_text[i + 5].isalnum()
                            or arms_text[i + 5] in "_'"
                        )
                    )
                ):
                    nested_matches += 1
                    i += 5
                    continue
                if ch == "|":
                    if nested_matches == 0:
                        if arm_start is not None:
                            arms.append(arms_text[arm_start:i].strip())
                        arm_start = i + 1
            i += 1
        if arm_start is not None:
            arms.append(arms_text[arm_start:].strip())
        if not arms:
            return False
        for arm in arms:
            arrow = arm.find("=>")
            if arrow == -1:
                return False
            pat = arm[:arrow].strip()
            rhs = _strip_outer_parens(arm[arrow + 2 :].strip())
            if rhs == "False":
                continue
            if rhs == "True":
                alts = [
                    " ".join(_strip_outer_parens(p).split())
                    for p in pat.split("|")
                    if p.strip()
                ]
                if not alts or any(
                    _POS_ARM_HEAD_RE.match(a)
                    or not _NEG_ARM_PAT_RE.fullmatch(a)
                    for a in alts
                ):
                    return False
                continue
            return False
        return True
    eq_idx = _find_top_level_eq(s)
    if eq_idx != -1:
        lhs = s[:eq_idx].strip()
        if not _is_allowed_head_application(
            lhs,
            pair_helpers=pair_helpers,
            allowed_bare_idents=scoped_idents,
        ):
            return False
        rhs = _strip_outer_parens(s[eq_idx + 1 :])
        if _NEG_RHS_RE.fullmatch(" ".join(rhs.split())):
            return True
    return False


def _is_closed_refutation_term(
    term: str,
    allowed_idents: frozenset[str],
    *,
    allow_assign_colon: bool = False,
) -> bool:
    if not term or "@" in term:
        return False
    if re.search(r"(?<!:):(?!=[=]?)", term):
        return False
    if not allow_assign_colon and ":=" in term:
        return False
    if re.search(r"(?<![:!<>])=(?![=>])", term):
        return False
    if any(
        c not in " \t\n()[]⟨⟩,.:=>"
        and not (c.isascii() and (c.isalnum() or c in "_'"))
        for c in term
    ):
        return False
    idents = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", term)
    return all(ident in allowed_idents for ident in idents)


def _is_allowed_by_reach_script(script: str) -> bool:
    norm = " ".join(script.split())
    if not norm or "@" in norm:
        return False
    tactic_kw_re = re.compile(r"(?<![.\w'])\b(unfold|change|have|exact)\b")
    starts: list[int] = []
    depth = 0
    i = 0
    n = len(norm)
    while i < n:
        ch = norm[i]
        if ch in "([{⟨":
            depth += 1
            i += 1
            continue
        if ch in ")]}⟩" and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0:
            m_kw = tactic_kw_re.match(norm, i)
            if m_kw:
                starts.append(i)
                i = m_kw.end()
                continue
        i += 1
    if not starts or starts[0] != 0:
        return False
    clauses = [
        norm[starts[k] : starts[k + 1] if k + 1 < len(starts) else n].strip()
        for k in range(len(starts))
    ]
    bound_haves: set[str] = set()
    saw_exact = False
    idx = 0
    while idx < len(clauses):
        cl = clauses[idx]
        if cl == "unfold ReachesResultV2":
            idx += 1
            continue
        if _BY_CHANGE_STEP_RE.fullmatch(cl):
            idx += 1
            continue
        m_have = _BY_HAVE_HEAD_RE.fullmatch(cl)
        if m_have:
            h_name, rhs = m_have.group(1), m_have.group(2).strip()
            if not _is_valid_fresh_local_ident(h_name):
                return False
            if rhs == "by":
                sub_end = idx + 1
                while sub_end < len(clauses) and not clauses[
                    sub_end
                ].startswith("exact "):
                    sub_end += 1
                if sub_end >= len(clauses):
                    return False
                sub_script = " ".join(clauses[idx + 1 : sub_end + 1])
                if not _is_allowed_by_reach_script(sub_script):
                    return False
                bound_haves.add(h_name)
                idx = sub_end + 1
                continue
            if not _is_closed_refutation_term(
                rhs, frozenset({"ReachesV2", "refl", "tail", "rfl", "_"})
            ):
                return False
            bound_haves.add(h_name)
            idx += 1
            continue
        if cl.startswith("exact "):
            term = cl[len("exact ") :].strip()
            if not _is_closed_refutation_term(
                term, _REACH_BY_EXACT_ALLOWED_IDENTS | frozenset(bound_haves)
            ):
                return False
            saw_exact = True
            idx += 1
            continue
        return False
    return saw_exact


def _is_allowed_refutation_proof(proof: str) -> bool:
    norm = " ".join(proof.split())
    if not norm or "@" in norm:
        return False
    if _ATOMIC_PROOF_RE.fullmatch(norm):
        return True
    if norm.startswith("⟨") and norm.endswith("⟩"):
        elems = _split_top_level(norm[1:-1], ",")
        if elems and all(_ATOMIC_PROOF_RE.fullmatch(e) for e in elems):
            return True
    m_fun = re.fullmatch(
        r"fun\s+([A-Za-z_][A-Za-z0-9_']*)\s*=>\s*(.+)", norm
    )
    if m_fun:
        bound_var, body_expr = m_fun.group(1), m_fun.group(2)
        if not _is_valid_fresh_local_ident(bound_var):
            return False
        return _is_closed_refutation_term(
            body_expr,
            _BOUNDARY_ELIM_ALLOWED_IDENTS | frozenset({bound_var}),
            allow_assign_colon=True,
        )
    if norm.startswith("by "):
        return _is_allowed_by_reach_script(norm[3:])
    return False


def _has_success_expectation(body: str) -> bool:
    if _POS_CTOR_RE.search(body):
        return True
    if _DIRECT_SUCCESS_RE.search(body):
        return True
    if _LAMBDA_TRUE_RE.search(
        _NEG_BODY_VERIFIED_TRUE_RE.sub("¬ BodyVerified <post>", body)
    ):
        return True
    if _WILDCARD_NON_FALSE_ARM_RE.search(body):
        return True
    for arm in _TRUE_ARM_RE.finditer(body):
        alts = [
            " ".join(_strip_outer_parens(p).split())
            for p in arm.group(1).split("|")
            if p.strip()
        ]
        if any(
            _POS_ARM_HEAD_RE.match(alt)
            or not _NEG_ARM_PAT_RE.fullmatch(alt)
            for alt in alts
        ):
            return True
    return False


def _is_allowed_data_helper(
    body: str,
    *,
    allowed_bare_idents: frozenset[str] = frozenset(),
    pair_helpers: frozenset[str] = frozenset(),
    allow_data_params: bool = False,
) -> bool:
    m_head = re.match(
        rf"\s*{_LEAN_DECL_MODIFIER_PREFIX}"
        r"(?:def|abbrev)\s+([^\s:(]+)",
        body,
    )
    if not m_head or not _is_valid_fresh_local_ident(m_head.group(1)):
        return False
    rest = body[m_head.end() :].lstrip()
    param_names: set[str] = set()
    if allow_data_params:
        while rest.startswith("("):
            m_param = re.match(
                r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^()]+?)\s*\)\s*",
                rest,
            )
            if not m_param:
                return False
            p_name = m_param.group(1)
            if not _is_valid_fresh_local_ident(p_name):
                return False
            p_ty = " ".join(m_param.group(2).split())
            if p_ty not in _ALLOWED_HELPER_DATA_TYPES:
                return False
            param_names.add(p_name)
            rest = rest[m_param.end() :]
    if not rest.startswith(":") or rest.startswith(":="):
        return False
    rest = rest[1:]
    m_end = re.search(r":=|\bwhere\b", rest)
    if not m_end:
        return False
    ret_type = " ".join(rest[: m_end.start()].split())
    if ret_type not in _ALLOWED_HELPER_DATA_TYPES:
        return False
    scoped = allowed_bare_idents | frozenset(param_names)
    let_res = _strip_and_validate_leading_lets(
        rest[m_end.end() :],
        allowed_bare_idents=scoped,
        pair_helpers=pair_helpers,
    )
    if let_res is None:
        return False
    rhs_after_lets, let_binders = let_res
    if not rhs_after_lets:
        return False
    if _HELPER_PROOF_TOKEN_RE.search(rhs_after_lets):
        return False
    if _has_forbidden_type_or_data_expr(
        rhs_after_lets,
        pair_helpers=pair_helpers,
        allowed_bare_idents=scoped | let_binders,
    ):
        return False
    if re.search(r"(?<!:):(?!=[=]?)", rhs_after_lets):
        return False
    if _find_top_level_eq(rhs_after_lets) != -1:
        return False
    return True


def _find_disallowed_directive_issues(cleaned: str) -> list[str]:
    """Return disallowed Lean `#`/elaborator/open/export/namespace issues."""
    issues: list[str] = []
    for cmd in _HASH_COMMAND_RE.findall(cleaned):
        issues.append(f"disallowed command #{cmd}")
    for meta_cmd in _FORBIDDEN_META_CMD_RE.findall(cleaned):
        issues.append(f"disallowed elaborator command {meta_cmd}")
    for kw, rest in _OPEN_EXPORT_RE.findall(cleaned):
        if kw == "export":
            issues.append("disallowed export directive")
            continue
        targets = rest.split()
        if not targets or any(t not in _ALLOWED_OPEN_TARGETS for t in targets):
            issues.append(f"disallowed open directive: open {rest.strip()}")
    for line in cleaned.splitlines():
        stripped = " ".join(line.split())
        if stripped.startswith("namespace ") and stripped != "namespace GuardMutation":
            issues.append(f"disallowed namespace directive: {stripped}")
    return issues


def _collect_imported_module_info(
    fixture_dir: Path, imported_mods: set[str]
) -> tuple[frozenset[str], frozenset[str], list[str]]:
    """Collect pure-data helper names (and pair helpers) from imported sanity
    modules, rejecting any shadowing or disallowed declarations/directives."""
    data_helpers: set[str] = set()
    pair_helpers: set[str] = set()
    issues: list[str] = []
    for mod in sorted(imported_mods):
        path = fixture_dir / f"{mod}.lean"
        if not path.is_file():
            continue
        cleaned = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        for d_issue in _find_disallowed_directive_issues(cleaned):
            issues.append(f"imported module {mod}: {d_issue}")
        matches = list(LEAN_DECL_TOKEN_RE.finditer(cleaned))
        for idx, m in enumerate(matches):
            kind = m.group(1)
            raw_name = m.group(2) or ""
            name = raw_name.strip("«»")
            if kind == "end":
                if name and name != "GuardMutation":
                    issues.append(
                        f"imported module {mod}: disallowed namespace end {name}"
                    )
                continue
            leaf = name.rsplit(".", 1)[-1]
            if not name or not _is_valid_fresh_local_ident(leaf):
                issues.append(
                    f"imported module {mod}: disallowed shadowing declaration {kind} {name or '<unnamed>'}"
                )
                continue
            if kind not in ("def", "abbrev"):
                continue
            end = (
                matches[idx + 1].start()
                if idx + 1 < len(matches)
                else len(cleaned)
            )
            body = cleaned[m.start() : end]
            if _is_allowed_data_helper(
                body,
                allowed_bare_idents=frozenset(data_helpers),
                pair_helpers=frozenset(pair_helpers),
                allow_data_params=True,
            ):
                data_helpers.add(name)
                if re.search(
                    r":\s*List\s+MirTy\s*×\s*List\s+LocalSlot\s*(?::=|\bwhere\b)",
                    body,
                ):
                    pair_helpers.add(name)
    return frozenset(data_helpers), frozenset(pair_helpers), issues


def _collect_imported_pure_data_helpers(
    fixture_dir: Path, imported_mods: set[str]
) -> tuple[frozenset[str], frozenset[str]]:
    """Collect pure-data helper names (and pair helpers) from imported sanity
    modules, accepting only helpers whose bodies pass `_is_allowed_data_helper`."""
    data_helpers, pair_helpers, _ = _collect_imported_module_info(
        fixture_dir, imported_mods
    )
    return data_helpers, pair_helpers


def find_forbidden_positive_checks(
    source: str,
    *,
    allowed_theorems: set[str],
    helper_theorems: set[str] | frozenset[str] | None = None,
    imported_data_helpers: frozenset[str] = frozenset(),
    imported_pair_helpers: frozenset[str] = frozenset(),
) -> list[str]:
    """Audit a refutation fixture against the closed refutation-only grammar.

    A refutation fixture is expected to fail to compile on its mutant, so any
    positive canary or embedded positive branch inside it could fail on a
    broken mutant and register as a false kill. Positive canaries belong only
    in sanity modules, which every mutant must still compile.
    """
    cleaned = strip_lean_comments_and_strings(source)
    helpers = helper_theorems or frozenset()
    issues = _find_disallowed_directive_issues(cleaned)
    matches = list(LEAN_DECL_TOKEN_RE.finditer(cleaned))
    preamble = cleaned[: matches[0].start()] if matches else cleaned
    if _has_success_expectation(preamble):
        issues.append("embedded success expectation in preamble")
    for raw_line in preamble.splitlines():
        line = " ".join(raw_line.split())
        if line and not _ALLOWED_PREAMBLE_LINE_RE.fullmatch(line):
            issues.append(f"disallowed preamble statement: {line}")
    local_data_helpers: set[str] = set(imported_data_helpers)
    pair_helpers: set[str] = set(imported_pair_helpers)
    seen_decl_lines: set[int] = set()
    for idx, m in enumerate(matches):
        kind = m.group(1)
        name = (m.group(2) or "").strip("«»")
        decl_line = cleaned.count("\n", 0, m.start()) + 1
        if decl_line in seen_decl_lines or _declaration_is_mid_line(
            cleaned, m.start()
        ):
            issues.append(f"multiple declarations on line {decl_line} ({name})")
        seen_decl_lines.add(decl_line)
        end = (
            matches[idx + 1].start() if idx + 1 < len(matches) else len(cleaned)
        )
        body = cleaned[m.start() : end]
        if kind in ("theorem", "lemma") and name.startswith("positive"):
            issues.append(f"positive declaration {name}")
        if kind == "end":
            if _has_success_expectation(body) or not re.fullmatch(
                r"\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*", body
            ):
                issues.append(f"disallowed trailing content after end {name}")
            continue
        if kind not in ("theorem", "lemma", "example"):
            if _has_success_expectation(body):
                issues.append(
                    f"embedded success expectation in {kind} {name}"
                )
            elif kind not in ("def", "abbrev") or not _is_allowed_data_helper(
                body,
                allowed_bare_idents=frozenset(local_data_helpers),
                pair_helpers=frozenset(pair_helpers),
            ):
                issues.append(f"disallowed non-data helper {kind} {name}")
            else:
                local_data_helpers.add(name)
                if re.search(
                    r":\s*List\s+MirTy\s*×\s*List\s+LocalSlot\s*(?::=|\bwhere\b)",
                    body,
                ):
                    pair_helpers.add(name)
            continue
        if kind == "example":
            issues.append("uncataloged example")
            continue
        if name not in allowed_theorems and name not in helpers:
            issues.append(f"uncataloged theorem {name}")
        if name in PINNED_EXACT_REFUTATIONS:
            norm_body = " ".join(body.split())
            if norm_body == PINNED_EXACT_REFUTATIONS[name]:
                continue
            issues.append(
                f"allowlisted {name} drifted from pinned refutation assertion"
            )
            continue
        parsed_thm = _extract_theorem_type_and_proof(body)
        structurally_valid = (
            parsed_thm is not None
            and _is_allowed_refutation_type(
                parsed_thm[0],
                pair_helpers=frozenset(pair_helpers),
                allowed_bare_idents=frozenset(local_data_helpers),
            )
            and _is_allowed_refutation_proof(parsed_thm[1])
        )
        if not _has_success_expectation(body) and structurally_valid:
            continue
        issues.append(f"embedded success expectation in {name}")
    return issues


def collect_fixture_local_imports(
    fixture_dir: Path,
    root: str,
    *,
    overrides: dict[str, str] | None = None,
) -> set[str]:
    """Return fixture-local modules transitively imported by `root`."""
    seen: set[str] = set()
    stack = [root]
    while stack:
        cur = stack.pop()
        if overrides is not None and cur in overrides:
            raw = overrides[cur]
        else:
            raw = (fixture_dir / f"{cur}.lean").read_text(encoding="utf-8")
        tokens = strip_lean_comments_and_strings(raw).split()
        i = 0
        while i < len(tokens):
            if tokens[i] == "import":
                j = i + 1
                if j < len(tokens) and tokens[j] == "all":
                    j += 1
                if j < len(tokens):
                    imp = tokens[j]
                    is_fixture = (fixture_dir / f"{imp}.lean").is_file()
                    if is_fixture and imp not in seen:
                        seen.add(imp)
                        stack.append(imp)
                    i = j + 1
                    continue
            i += 1
    return seen


def allowed_fixture_local_imports(guard: MirSemanticsGuard) -> set[str]:
    """Return fixture-local modules rebuilt against `guard`'s mutant."""
    allowed = {guard.sanity_module}
    if guard.sanity_module == "PositiveSanity":
        allowed |= set(
            FIXTURE_HELPERS_END_TO_END
            if guard.needs_wf_helper
            else FIXTURE_HELPERS_BOUNDARY
        )
    return allowed


def validate_refutation_modules(anneal_root: Path) -> list[str]:
    """Validate that refutation fixtures contain only refutations and rebuilt imports."""
    errors: list[str] = []
    fixture_dir = anneal_root / "ci/fixtures/guard_mutation"
    sanity_mods = {g.sanity_module for g in MIR_SEMANTICS_GUARDS}
    fixture_mods = {g.fixture_module for g in MIR_SEMANTICS_GUARDS}
    overlap = sorted(sanity_mods & fixture_mods)
    if overlap:
        errors.append(
            f"sanity and refutation modules must be disjoint, overlap={overlap}"
        )

    catalog_by_mod: dict[str, set[str]] = {}
    for g in MIR_SEMANTICS_GUARDS:
        catalog_by_mod.setdefault(g.fixture_module, set()).add(g.theorem_name)

    for mod in sorted(fixture_mods):
        path = fixture_dir / f"{mod}.lean"
        if not path.is_file():
            continue
        imported_local = collect_fixture_local_imports(fixture_dir, mod)
        imp_data, imp_pairs, imp_issues = _collect_imported_module_info(
            fixture_dir, imported_local
        )
        for issue in imp_issues:
            errors.append(f"refutation fixture {mod}: {issue}")
        found = find_forbidden_positive_checks(
            path.read_text(encoding="utf-8"),
            allowed_theorems=catalog_by_mod[mod],
            helper_theorems=ALLOWED_REFUTATION_HELPER_THEOREMS.get(
                mod, frozenset()
            ),
            imported_data_helpers=imp_data,
            imported_pair_helpers=imp_pairs,
        )
        for issue in found:
            errors.append(
                f"refutation fixture {mod}: {issue}; move any positive check "
                f"into its sanity module"
            )

    for g in MIR_SEMANTICS_GUARDS:
        allowed = allowed_fixture_local_imports(g)
        fix_path = fixture_dir / f"{g.fixture_module}.lean"
        if fix_path.is_file():
            imported = collect_fixture_local_imports(
                fixture_dir, g.fixture_module
            )
            extra = sorted(imported - allowed)
            if extra:
                errors.append(
                    f"{g.guard_id}: fixture {g.fixture_module} imports "
                    f"unrebuilt fixture-local module(s) {extra}; only "
                    f"{sorted(allowed)} are rebuilt against its mutant"
                )
        san_path = fixture_dir / f"{g.sanity_module}.lean"
        if san_path.is_file():
            san_imported = collect_fixture_local_imports(
                fixture_dir, g.sanity_module
            )
            san_allowed = allowed - {g.sanity_module}
            extra_san = sorted(san_imported - san_allowed)
            if extra_san:
                errors.append(
                    f"{g.guard_id}: sanity module {g.sanity_module} imports "
                    f"unrebuilt fixture-local module(s) {extra_san}; only "
                    f"{sorted(san_allowed)} are rebuilt before it"
                )
    return errors


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
        excluded_seed_mods = rebuilt_mods | set(BASELINE_ONLY_MEMORY_FIXTURES)
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
            if rel_mod is None or rel_mod in excluded_seed_mods:
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


def validate_catalog_invariants(anneal_root: Path) -> list[str]:
    """Check static catalog invariants without invoking Lean.

    Returns a list of error strings (empty when all invariants hold).
    """
    errors: list[str] = []
    seen_ids: set[str] = set()
    fixtures_dir = anneal_root / "ci/fixtures/guard_mutation"

    target_text_cache: dict[Path, str] = {}
    fixture_scan_cache: dict[Path, tuple[str, list[re.Match[str]]]] = {}
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
            text = target_text_cache.get(target_path)
            if text is None:
                text = target_path.read_text(encoding="utf-8")
                target_text_cache[target_path] = text
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
            scanned = fixture_scan_cache.get(fixture_path)
            if scanned is None:
                cleaned = strip_lean_comments_and_strings(
                    fixture_path.read_text(encoding="utf-8")
                )
                scanned = (cleaned, list(LEAN_DECL_TOKEN_RE.finditer(cleaned)))
                fixture_scan_cache[fixture_path] = scanned
            try:
                _find_theorem_line_span_in_cleaned(
                    scanned[0], scanned[1], guard.theorem_name
                )
            except ValueError as exc:
                errors.append(f"{guard.guard_id}: {exc}")

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

    errors.extend(validate_refutation_modules(anneal_root))

    return errors


def _select_guards(
    suite: str,
    name_filter: str | None,
) -> tuple[
    list[MirSemanticsGuard],
    list[AuditHeaderGuard],
    list[AuditBoundaryGuard],
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
    if name_filter:
        mir_guards = [g for g in mir_guards if name_filter in g.guard_id]
        audit_guards = [g for g in audit_guards if name_filter in g.guard_id]
        boundary_guards = [
            g for g in boundary_guards if name_filter in g.guard_id
        ]
    return mir_guards, audit_guards, boundary_guards


def run_guard_mutation_suite(
    *,
    anneal_root: Path,
    lean_bin: Path,
    suite: str = "all",
    name_filter: str | None = None,
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

    mir_guards, audit_guards, boundary_guards = _select_guards(
        suite, name_filter
    )
    if not mir_guards and not audit_guards and not boundary_guards:
        raise RuntimeError(
            f"no guards matched suite={suite!r} filter={name_filter!r}"
        )

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

            # Verify baseline helpers, positive sanity checks, baseline-only
            # exact assertions, and every negative refutation module pass
            # cleanly on unmodified TCB.
            needed_fixtures = sorted({g.fixture_module for g in mir_guards})
            needed_sanity = sorted({g.sanity_module for g in mir_guards})
            baseline_only = (
                list(BASELINE_ONLY_MEMORY_FIXTURES)
                if "MemorySanity" in needed_sanity
                else []
            )
            baseline_fixture_mods: list[str] = [
                *FIXTURE_HELPERS_END_TO_END,
                *needed_sanity,
                *baseline_only,
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
        # Suite 2 & 3: Audit header and boundary guards
        # --------------------------------------------------------------
        if audit_guards or boundary_guards:
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
        choices=("all", "mir_semantics", "audit_headers", "audit_boundary"),
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
        mir_guards, audit_guards, boundary_guards = _select_guards(
            args.suite, args.name_filter
        )
        for g in mir_guards:
            print(f"mir_semantics  {g.guard_id:36s} {g.target_file}")
        for g in audit_guards:
            print(f"audit_headers  {g.guard_id:36s} {g.target_file}")
        for g in boundary_guards:
            print(f"audit_boundary {g.guard_id:36s} {g.target_file}")
        total = len(mir_guards) + len(audit_guards) + len(boundary_guards)
        print(f"Total cataloged guards: {total}")
        return 0

    lean_bin = _resolve_lean_binary(args.lean)
    try:
        report = run_guard_mutation_suite(
            anneal_root=args.anneal_root,
            lean_bin=lean_bin,
            suite=args.suite,
            name_filter=args.name_filter,
            jobs=args.jobs,
            timeout_sec=args.timeout_sec,
        )
    except RuntimeError as exc:
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
