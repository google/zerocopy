-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Omega
import Init.Grind
import Init.GrindInstances
import Init.Data.Int.OfNat

/-!
# Probe: `omega` and `grind` Under `prelude` and `TrustedBoundary.lean`

This file uses an explicit `prelude` header and no `#print axioms` commands so
that it satisfies `TrustedBoundary.lean` Phase 1 (`"preflight"`) command-kind
restrictions (`commandKinds`). See `DiagnoseReduce.lean` for the automated
axiom-footprint checks and kernel reduction diagnostics.
-/

-- 1. Pure congruence closure + E-matching via `grind`.
theorem test_grind_eq (f : Nat → Nat) (a b : Nat) (h : a = b) : f (f a) = f (f b) := by
  grind

-- 2. Anneal-style slice/array bounds obligation via `omega`.
theorem mir_slice_subslice_bounds_omega
    (base len sub_off sub_len idx : Nat)
    (h_sub : sub_off + sub_len ≤ len)
    (h_idx : idx < sub_len) :
    base + sub_off + idx < base + len := by
  omega

-- 3. Anneal-style struct field layout and padding offset obligation via
-- `omega`.
theorem mir_struct_field_layout_omega
    (f0_size f0_pad f1_size f1_pad total_size : Nat)
    (h_f0 : f0_size = 4)
    (h_pad0 : f0_pad = 4)
    (h_f1 : f1_size = 8)
    (h_pad1 : f1_pad = 0)
    (h_total : total_size = f0_size + f0_pad + f1_size + f1_pad) :
    f0_size + f0_pad = 8 ∧ total_size = 16 ∧ f0_size + f0_pad + f1_size ≤ total_size := by
  omega

-- 4. Same Anneal-style MIR/layout obligations proved via `grind` (`lia`).
theorem mir_slice_subslice_bounds_grind
    (base len sub_off sub_len idx : Nat)
    (h_sub : sub_off + sub_len ≤ len)
    (h_idx : idx < sub_len) :
    base + sub_off + idx < base + len := by
  grind

-- 5. Anneal-style `UInt64` / `USize` arithmetic obligation via `grind`
-- (`ToInt` + `lia`).
theorem mir_uint64_checked_index_grind
    (off len : UInt64)
    (h_off : off ≤ 1024)
    (h_len : len ≤ 4096) :
    off + len ≤ 5120 := by
  grind

-- 6. Commutative ring / stride arithmetic obligation via `grind` (`ring`).
theorem mir_stride_offset_ring_grind
    (base i j elem_stride : Int) :
    base + (i + j) * elem_stride = (base + i * elem_stride) + j * elem_stride := by
  grind
