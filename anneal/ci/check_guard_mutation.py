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
    "Trusted/MirSemantics/Memory": (
        "Trusted/MirSemantics/Memory",
    ),
    "Trusted/MirSemantics/Bytes": (
        "Trusted/MirSemantics/Bytes",
        "Trusted/MirSemantics/State",
        "Trusted/MirSemantics/Step",
        "Trusted/MirSemantics/Boundary",
    ),
    "Trusted/MirSemantics/State": (
        "Trusted/MirSemantics/State",
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
    # Trusted/MirSemantics/Bytes.lean (5 validity and uninit-read guards)
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
        needs_wf_helper=False,
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
    # Profile v2 memory, step, type-admission, and boundary guards (47 guards)
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
            "      else if !Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 elemAlignLog2)) 0 then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok (.slicePtr p len)"
        ),
        replacement=(
            "      else if false then\n"
            "        .error .undefined\n"
            "      else\n"
            "        .ok (.slicePtr p len)"
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
            "      | none =>\n"
            "        if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 lay.size then\n"
            "          .error .undefined"
        ),
        replacement=(
            "      | none =>\n"
            "        if false || Nat.blt 0 lay.size then\n"
            "          .error .undefined"
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
            "          else if Mutability.beq reqMut .mut && !Mutability.beq a.mutability .mut then\n"
            "            .error .undefined"
        ),
        replacement=(
            "          else if false then\n"
            "            .error .undefined"
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
            "            match decodeValV2 profileV2TargetEndian pointee sliceBytes with\n"
            "            | .ok (some _) => .ok ()\n"
            "            | .ok none => .error .undefined\n"
            "            | .error k => .error k"
        ),
        replacement=(
            "            match decodeValV2 profileV2TargetEndian pointee sliceBytes with\n"
            "            | .ok (some _) => .ok ()\n"
            "            | .ok none => .ok ()\n"
            "            | .error k => .error k"
        ),
        fixture_module="ProfileV2Refutations",
        theorem_name="refute_bytes_v2_ref_valid_uninit_pointee",
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
