-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Bytes

/-!
# Negative Refutations for `Trusted.MirSemantics.Layout` Guards

Exercises every alignment and admission guard in
`Trusted/MirSemantics/Layout.lean`:

- `layoutOfTy`: unadmitted fieldless enums and unsupported types return `none`
  and fail closed with `.unsupported` in `loadIndirect`.
- `intLayout`, `layoutOfTy .char`, and `overflowPairLayout`: natural alignment
  requirements cause misaligned indirect loads at byte offset `1` to fault with
  `.undefined`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Live mutable 32-byte, 16-byte-aligned (`alignLog2 = 4`) zero-initialized
memory containing allocation id `1`, so offset `1` stays strictly in bounds for
every 16-byte or smaller type while violating any alignment > 1. -/
noncomputable def layoutRefuteMem : MemoryState :=
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 4
      mutability := .mut
      bytes := List.replicate 32 (.init 0 none)
      live := true
    }] }

/-- Unadmitted enum with duplicate discriminants `[10, 10]`. -/
noncomputable def layoutDupDiscrEnum : EnumTy := {
  id := 99
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [10, 10]
}

/-- Guard `layout_unadmitted_enum_none`: an unadmitted enum has no layout and
fails closed with `.unsupported` on `loadIndirect`. -/
theorem refute_layout_unadmitted_enum_none :
    layoutOfTy (.enum layoutDupDiscrEnum) = none ∧
    loadIndirect layoutRefuteMem (.enum layoutDupDiscrEnum) ⟨1, 0⟩ =
      .error .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `layout_unsupported_ty_none`: unmodeled types (`.ref`, non-overflow
tuples) have no layout and fail closed with `.unsupported`. -/
theorem refute_layout_unsupported_ty_none :
    layoutOfTy (.ref .shared (.int .i32 false)) = none ∧
    layoutOfTy (.tuple [.int .i32 false, .int .i32 false]) = none :=
  ⟨rfl, rfl⟩

/-- Guard `layout_int_i16_align`: misaligned `u16` load at offset `1` faults
with `.undefined`. -/
theorem refute_layout_int_i16_align :
    loadIndirect layoutRefuteMem (.int .i16 false) ⟨1, 1⟩ =
      .error .undefined :=
  rfl

/-- Guard `layout_int_i32_align`: misaligned `u32` load at offset `1` faults
with `.undefined`. -/
theorem refute_layout_int_i32_align :
    loadIndirect layoutRefuteMem (.int .i32 false) ⟨1, 1⟩ =
      .error .undefined :=
  rfl

/-- Guard `layout_int_i64_isize_align`: misaligned `u64` and `isize` loads at
offset `1` fault with `.undefined`. -/
theorem refute_layout_int_i64_isize_align :
    loadIndirect layoutRefuteMem (.int .i64 false) ⟨1, 1⟩ =
      .error .undefined ∧
    loadIndirect layoutRefuteMem (.int .isize true) ⟨1, 1⟩ =
      .error .undefined :=
  ⟨rfl, rfl⟩

/-- Guard `layout_int_i128_align`: misaligned `u128` load at offset `1` faults
with `.undefined`. -/
theorem refute_layout_int_i128_align :
    loadIndirect layoutRefuteMem (.int .i128 false) ⟨1, 1⟩ =
      .error .undefined :=
  rfl

/-- Guard `layout_char_align`: misaligned `char` load at offset `1` faults with
`.undefined`. -/
theorem refute_layout_char_align :
    loadIndirect layoutRefuteMem .char ⟨1, 1⟩ = .error .undefined :=
  rfl

/-- Guard `layout_overflow_pair_align`: misaligned `(u32, bool)` load at offset
`1` faults with `.undefined`. -/
theorem refute_layout_overflow_pair_align :
    loadIndirect layoutRefuteMem (.tuple [.int .i32 false, .bool]) ⟨1, 1⟩ =
      .error .undefined :=
  rfl

/-- Guard `layout_v2_struct_overlap`: a struct layout whose non-zero-sized
fields overlap has no Profile v2 layout. -/
theorem refute_layout_v2_struct_overlap :
    layoutOfTyV2 (.struct_ ⟨1, 2, 0, [0, 0]⟩ [.int .i8 false, .int .i8 false]) =
      none :=
  rfl

/-- Guard `layout_v2_struct_misaligned`: a struct layout placing a `u16` field
at an odd offset has no Profile v2 layout. -/
theorem refute_layout_v2_struct_misaligned :
    layoutOfTyV2 (.struct_ ⟨1, 4, 1, [1]⟩ [.int .i16 false]) = none :=
  rfl

end GuardMutation
