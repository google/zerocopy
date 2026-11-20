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

def u32Scalar (n : Nat) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩

/-- `selected(a, b)` delegates to `clamp_gap(a, b)`, always returns a `u32`
bounded above by `16`, and returns `16` whenever `a ≤ b`. -/
noncomputable def clampGapSpec (program : Program) : Prop :=
  ∀ a b : BitVec 32,
    ∃ out : Nat, ∃ cm : CallerMemory,
      out ≤ 16 ∧
      (a.toNat ≤ b.toNat → out = 16) ∧
      Behavior (entryProgForBody program 0)
        { args := [u32Scalar a.toNat, u32Scalar b.toNat] }
        (.returned ⟨u32Scalar out, cm⟩)

noncomputable def specs : Specs := ⟨fun _ _ => False, clampGapSpec⟩

end Spec
