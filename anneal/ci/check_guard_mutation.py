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
  negative refutation or negative auditor fixture.
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
    """Single-guard mutation entry targeting `TrustedBoundary.lean` headers."""

    guard_id: str
    target_file: str
    description: str
    anchor: str
    replacement: str
    negative_source: str


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
    # Trusted/MirSemantics/Memory.lean (15 allocation/bounds/align/mut guards)
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
            "    match findAllocation place.allocId m.allocations with\n"
            "    | none => .error .undefined\n"
            "    | some a =>\n"
            "      if !a.live || !isInBounds a place.offset size ||"
        ),
        replacement=(
            "    match findAllocation place.allocId m.allocations with\n"
            "    | none => .ok []\n"
            "    | some a =>\n"
            "      if !a.live || !isInBounds a place.offset size ||"
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
            "      if !a.live || !isInBounds a place.offset size ||\n"
            "          !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "      if false || !isInBounds a place.offset size ||\n"
            "          !isAligned a place.offset alignLog2 then"
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
            "      if !a.live || !isInBounds a place.offset size ||\n"
            "          !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "      if !a.live || false ||\n"
            "          !isAligned a place.offset alignLog2 then"
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
            "      if !a.live || !isInBounds a place.offset size ||\n"
            "          !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "      if !a.live || !isInBounds a place.offset size ||\n"
            "          false then"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_read_misaligned",
        sanity_module="MemorySanity",
        needs_wf_helper=False,
    ),
    MirSemanticsGuard(
        guard_id="mem_write_missing_alloc",
        target_file="trusted/lean/Trusted/MirSemantics/Memory.lean",
        target_module="Trusted/MirSemantics/Memory",
        description="writeBytes rejects missing allocation id as UB",
        anchor=(
            "    match findAllocation place.allocId m.allocations with\n"
            "    | none => .error .undefined\n"
            "    | some a =>\n"
            "      if !a.live || !isInBounds a place.offset bytes.length ||"
        ),
        replacement=(
            "    match findAllocation place.allocId m.allocations with\n"
            "    | none => .ok m\n"
            "    | some a =>\n"
            "      if !a.live || !isInBounds a place.offset bytes.length ||"
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
            "      if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "          !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "      if false || !isInBounds a place.offset bytes.length ||\n"
            "          !isAligned a place.offset alignLog2 then"
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
            "      if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "          !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "      if !a.live || false ||\n"
            "          !isAligned a place.offset alignLog2 then"
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
            "      if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "          !isAligned a place.offset alignLog2 then"
        ),
        replacement=(
            "      if !a.live || !isInBounds a place.offset bytes.length ||\n"
            "          false then"
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
            "        match a.mutability with\n"
            "        | .shared => .error .undefined\n"
            "        | .mut =>\n"
            "          let bytes' := a.bytes.take place.offset ++ bytes ++"
        ),
        replacement=(
            "        match a.mutability with\n"
            "        | .shared => .ok m\n"
            "        | .mut =>\n"
            "          let bytes' := a.bytes.take place.offset ++ bytes ++"
        ),
        fixture_module="MemoryRefutations",
        theorem_name="refute_mem_write_readonly",
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
)


AUDIT_HEADER_GUARDS: tuple[AuditHeaderGuard, ...] = (
    AuditHeaderGuard(
        guard_id="audit_header_reject_lean_import",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="validateTargetImports rejects `import Lean` in target headers",
        anchor=(
            "    if imp.module == `Lean || root == `Lean ||\n"
            "        imp.module == `Lake || root == `Lake then"
        ),
        replacement=(
            "    if false ||\n"
            "        imp.module == `Lake || root == `Lake then"
        ),
        negative_source="import Lean\n",
    ),
    AuditHeaderGuard(
        guard_id="audit_header_reject_lake_import",
        target_file="trusted/audit/TrustedBoundary.lean",
        description="validateTargetImports rejects `import Lake` in target headers",
        anchor=(
            "    if imp.module == `Lean || root == `Lean ||\n"
            "        imp.module == `Lake || root == `Lake then"
        ),
        replacement=(
            "    if imp.module == `Lean || root == `Lean ||\n"
            "        false then"
        ),
        negative_source="import Lake\n",
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
    req_path = work_dir / "req.json"
    res_path = work_dir / "res.json"
    runner_path = work_dir / "run_tb.lean"
    req_path.write_text(
        json.dumps(
            {
                "mode": "headers",
                "sysroot": sysroot,
                "sources": [["Target", str(target_src)]],
            }
        ),
        encoding="utf-8",
    )
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
        # filesystems) to every unmodified `.olean` in `base_olean_dir`. Lean 4
        # resolves a root namespace (`Trusted.*`) from the first `LEAN_PATH`
        # entry containing that root directory, so giving each mutant one
        # complete `.olean` directory avoids partial-namespace lookup failures.
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
        for src_olean in base_olean_dir.rglob("*.olean"):
            rel_mod = src_olean.relative_to(base_olean_dir).with_suffix("")
            if rel_mod.as_posix() in rebuilt_mods:
                continue
            dst_olean = mut_olean_dir / src_olean.relative_to(base_olean_dir)
            dst_olean.parent.mkdir(parents=True, exist_ok=True)
            try:
                os.link(src_olean, dst_olean)
            except OSError:
                shutil.copy2(src_olean, dst_olean)

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
) -> tuple[list[MirSemanticsGuard], list[AuditHeaderGuard]]:
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

    mir_guards, audit_guards = _select_guards(suite, name_filter)
    if not mir_guards and not audit_guards:
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
        # Suite 2: TrustedBoundary.lean header guards baseline + mutants
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
            for guard in audit_guards:
                check_dir = base_path / f"base_{guard.guard_id}"
                check_dir.mkdir()
                rc, parsed, out = _run_audit_headers(
                    lean_bin,
                    tb_olean_dir,
                    sysroot,
                    guard.negative_source,
                    check_dir,
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
        mir_guards, audit_guards = _select_guards(args.suite, args.name_filter)
        for g in mir_guards:
            print(f"mir_semantics  {g.guard_id:36s} {g.target_file}")
        for g in audit_guards:
            print(f"audit_headers  {g.guard_id:36s} {g.target_file}")
        print(f"Total cataloged guards: {len(mir_guards) + len(audit_guards)}")
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
