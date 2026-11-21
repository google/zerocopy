-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-- Nominal struct layout of `U64Range { min: u64, max: u64 }`. -/
def u64RangeSty : StructTy :=
  { id := 3382529831, fields := [.int .i64 false, .int .i64 false] }

def u64Val (x : BitVec 64) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 x.toNat⟩

def u64RangeVal (lo hi : BitVec 64) : Val :=
  .structVal u64RangeSty [u64Val lo, u64Val hi]

/-- Soundness of Starnix `U64Range::add_range` (body 2) and
`U64Range::mul_range` (body 3): whenever concrete `x ∈ [a_lo, a_hi]` and
`y ∈ [b_lo, b_hi]`, both methods terminate cleanly and return an enclosing
interval containing `x + y` (resp. `x * y`). -/
noncomputable def u64RangeSpec (program : Program) : Prop :=
  (∀ a_lo x a_hi b_lo y b_hi : BitVec 64,
    a_lo ≤ x → x ≤ a_hi → b_lo ≤ y → y ≤ b_hi →
    ∃ r_lo r_hi : BitVec 64, ∃ cm : CallerMemory,
      Behavior (entryProgForBody program 2)
        { args := [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] }
        (.returned ⟨u64RangeVal r_lo r_hi, cm⟩) ∧
      r_lo ≤ x + y ∧ x + y ≤ r_hi) ∧
  (∀ a_lo x a_hi b_lo y b_hi : BitVec 64,
    a_lo ≤ x → x ≤ a_hi → b_lo ≤ y → y ≤ b_hi →
    ∃ r_lo r_hi : BitVec 64, ∃ cm : CallerMemory,
      Behavior (entryProgForBody program 3)
        { args := [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] }
        (.returned ⟨u64RangeVal r_lo r_hi, cm⟩) ∧
      r_lo ≤ BitVec.ofNat 64 (x.toNat * y.toNat) ∧
      BitVec.ofNat 64 (x.toNat * y.toNat) ≤ r_hi)

noncomputable def specs : Specs := ⟨fun _ _ => False, u64RangeSpec⟩

end Spec
