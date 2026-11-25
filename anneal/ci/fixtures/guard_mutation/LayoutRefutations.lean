-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteWf

/-!
# Negative Refutations for `Trusted.MirSemantics.Layout` Guards

Each theorem exercises one layout-admission, size, or alignment guard in
`Trusted/MirSemantics/Layout.lean` (`layoutOfTy`, `intLayout`, and
`overflowPairLayout`).
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Duplicate-discriminant enum descriptor outside `enumAdmitted`. -/
noncomputable def invalidEnumTy : EnumTy := {
  id := 10
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [1, 1]
}

/-- Guard `layout_reject_unadmitted_enum`: `layoutOfTy` returns `none` and
`decodeVal` faults `.unsupported` for an enum failing `enumAdmitted`. -/
theorem refute_layout_reject_unadmitted_enum :
    layoutOfTy (.enum invalidEnumTy) = none ∧
    decodeVal .little (.enum invalidEnumTy) [.init 1 none] =
      .error .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `layout_reject_non_overflow_tuple`: `layoutOfTy` returns `none` for
non-overflow tuple types such as `(bool, bool)`, failing closed before touching
memory in `deinitIndirect`. -/
theorem refute_layout_reject_non_overflow_tuple :
    layoutOfTy (.tuple [.bool, .bool]) = none ∧
    deinitIndirect MemoryState.empty (.tuple [.bool, .bool]) ⟨99, 0⟩ =
      .error .unsupported :=
  ⟨rfl, rfl⟩

/-- Live mutable 8-byte, 8-byte-aligned allocation holding zeroed bytes. -/
noncomputable def mem8ByteAligned : MemoryState := {
  nextAllocId := 2
  allocations := [{
    allocId := 1
    alignLog2 := 3
    mutability := .mut
    bytes := List.replicate 8 (.init 0 none)
    live := true
  }]
}

/-- Guard `layout_isize_64bit_align`: loading `isize` at 4-byte offset inside
an 8-byte allocation faults `.undefined` because 64-bit `isize` has size `8`
and alignment `8` (`alignLog2 = 3`). -/
theorem refute_layout_isize_64bit_align :
    loadIndirect mem8ByteAligned (.int .isize true) ⟨1, 4⟩ =
      .error .undefined :=
  rfl

/-- Guard `layout_overflow_pair_size`: `decodeVal` rejects a 4-byte buffer for
`(u32, bool)` with `.unsupported` because `overflowPairLayout .i32` has size
`8` (integer plus bool plus alignment padding). -/
theorem refute_layout_overflow_pair_size :
    decodeVal .little (.tuple [u32Ty, .bool])
      (List.replicate 4 (.init 0 none)) = .error .unsupported :=
  rfl

end GuardMutation
