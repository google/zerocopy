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
# Negative Refutations for `Trusted.MirSemantics.Enum` Validity Guards

Exercises both clauses of `isUnicodeScalar` and every validity,
enum-admission, identity-uniqueness, value-typing, slot-initialization, and
Profile v2 overflow-pair pointee, `Vec`, `Box`, and slice element guard in
`Trusted/MirSemantics/Enum.lean`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Guard `enum_char_above_unicode_max`: code point `0x110000` exceeds the
maximum Unicode scalar value `0x10FFFF` and faults with `.undefined`. -/
theorem refute_enum_char_above_unicode_max :
    ReachesResult (mkConstRetProg .char 0x110000) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .char 0x110000) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_char_surrogate_gap`: UTF-16 surrogate code point `0xD800` is
not a Unicode scalar value and faults with `.undefined`. -/
theorem refute_enum_char_surrogate_gap :
    ReachesResult (mkConstRetProg .char 0xd800) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .char 0xd800) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_v2_overflow_pair_pointee`: no Profile v2 local may be a
reference or raw pointer to an overflow pair `(T, bool)`, so the pair's
unchecked byte layout stays unobservable. -/
theorem refute_enum_v2_overflow_pair_pointee :
    isSupportedV2LocalTy (.rawPtr .shared (.tuple [.int .i8 false, .bool])) =
      false ∧
    isSupportedV2LocalTy (.ref .mut (.tuple [.int .i32 true, .bool])) = false :=
  ⟨rfl, rfl⟩

/-- Anti-overreach canary: an overflow pair itself, and pointers to its
integer or `bool` field types, remain admitted local types. -/
theorem positive_enum_v2_overflow_pair_local :
    isSupportedV2LocalTy (.tuple [.int .i8 false, .bool]) = true ∧
    isSupportedV2LocalTy (.rawPtr .shared (.int .i8 false)) = true ∧
    isSupportedV2LocalTy (.ref .shared .bool) = true :=
  ⟨rfl, rfl, rfl⟩

/-- Guard `enum_v2_overflow_pair_vec_elem`: a `Vec`'s elements are
addressable, so no Profile v2 local may be a `Vec` of overflow pairs. -/
theorem refute_enum_v2_overflow_pair_vec_elem :
    isSupportedV2LocalTy (.vec (.tuple [.int .i8 false, .bool])) = false :=
  rfl

/-- Guard `enum_v2_overflow_pair_box_pointee`: no Profile v2 local may be a
`Box` of an overflow pair. -/
theorem refute_enum_v2_overflow_pair_box_pointee :
    isSupportedV2LocalTy (.box (.tuple [.int .i32 true, .bool])) = false :=
  rfl

/-- Guard `enum_v2_overflow_pair_slice_elem`: no Profile v2 local may be a
reference or raw pointer to a slice of overflow pairs. -/
theorem refute_enum_v2_overflow_pair_slice_elem :
    isSupportedV2LocalTy
        (.ref .shared (.slice (.tuple [.int .i8 false, .bool]))) = false ∧
    isSupportedV2LocalTy
        (.rawPtr .mut (.slice (.tuple [.int .i16 true, .bool]))) = false :=
  ⟨rfl, rfl⟩

/-- Anti-overreach canary: `Vec`, `Box`, and slices of scalar elements remain
admitted local types. -/
theorem positive_enum_v2_vec_box_slice_scalar_elems :
    isSupportedV2LocalTy (.vec (.int .i8 false)) = true ∧
    isSupportedV2LocalTy (.box (.int .i64 false)) = true ∧
    isSupportedV2LocalTy (.box (.slice .bool)) = true ∧
    isSupportedV2LocalTy (.ref .shared (.slice .char)) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Minimal valid unit body with the given identity string. -/
noncomputable def mkUnitBodyWithId (ident : String) : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  identity := ident
}

/-- Guard `enum_identity_empty_rejected`: `identityKey?` rejects a body
with an empty `identity` string so `bodiesHaveUniqueIdentities` returns
`false`. -/
theorem refute_enum_identity_empty_rejected :
    bodiesHaveUniqueIdentities [mkUnitBodyWithId ""] = false :=
  rfl

/-- Guard `enum_identity_duplicate_rejected`: `identityRbInsertAux` rejects
duplicate body identities so `bodiesHaveUniqueIdentities` returns `false`. -/
theorem refute_enum_identity_duplicate_rejected :
    bodiesHaveUniqueIdentities
      [mkUnitBodyWithId "crate::dup", mkUnitBodyWithId "crate::dup"] = false :=
  rfl

/-- Zero-variant scalar-tagged enum (vacuously satisfies `all` and pairwise
distinctness, isolating `!ety.discriminants.isEmpty`). -/
noncomputable def zeroVariantScalarEnum : EnumTy := {
  id := 10
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := []
}

/-- Guard `enum_admitted_nonempty`: 0-variant enum fails `enumAdmitted` and
refutes `WellFormed` at entry. -/
theorem refute_enum_admitted_nonempty :
    ReachesResult (mkSingleBlockProg 0 [.unit, .enum zeroVariantScalarEnum] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .enum zeroVariantScalarEnum] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_admitted_variant_count_bound`: any enum with `2^32` variants
fails `enumAdmitted` without constructing a `2^32`-element list. -/
theorem refute_enum_admitted_variant_count_bound (ety : EnumTy)
    (hLen : ety.discriminants.length = Nat.pow 2 32) :
    enumAdmitted ety = false := by
  unfold enumAdmitted
  rw [hLen]
  cases ety.discriminants.isEmpty <;> rfl

/-- Single-variant `.zeroSized` enum whose discriminant `256` overflows
`discrWidth = .i8` (using `.zeroSized` so the scalar tag roundtrip check does
not shadow the discriminant-width check). -/
noncomputable def overflowDiscrZstEnum : EnumTy := {
  id := 11
  discrWidth := .i8
  discrSigned := false
  tagRepr := .zeroSized
  discriminants := [256]
}

/-- Guard `enum_admitted_discr_fits_width`: discriminant `256` in a `u8`
discriminant enum fails `enumAdmitted` and refutes `WellFormed`. -/
theorem refute_enum_admitted_discr_fits_width :
    ReachesResult (mkSingleBlockProg 0 [.unit, .enum overflowDiscrZstEnum] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .enum overflowDiscrZstEnum] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Enum with duplicate discriminants `[10, 10]`. -/
noncomputable def dupDiscrEnum : EnumTy := {
  id := 12
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [10, 10]
}

/-- Guard `enum_admitted_discr_distinct`: duplicate discriminants fail
`enumAdmitted` and refute `WellFormed`. -/
theorem refute_enum_admitted_discr_distinct :
    ReachesResult (mkSingleBlockProg 0 [.unit, .enum dupDiscrEnum] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .enum dupDiscrEnum] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- `.zeroSized` enum claiming two distinct variants `[0, 1]`. -/
noncomputable def multiVariantZstEnum : EnumTy := {
  id := 13
  discrWidth := .i8
  discrSigned := false
  tagRepr := .zeroSized
  discriminants := [0, 1]
}

/-- Guard `enum_admitted_zst_single_variant`: `.zeroSized` enum with 2 variants
fails `enumAdmitted` and refutes `WellFormed`. -/
theorem refute_enum_admitted_zst_single_variant :
    ReachesResult (mkSingleBlockProg 0 [.unit, .enum multiVariantZstEnum] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .enum multiVariantZstEnum] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- `isize`-discriminant enum with `u8` tag whose discriminant `300` truncates
lossily to `44`. -/
noncomputable def lossyTagEnum : EnumTy := {
  id := 14
  discrWidth := .isize
  discrSigned := true
  tagRepr := .scalar .i8 false
  discriminants := [0, 300]
}

/-- Guard `enum_admitted_scalar_tag_lossless`: scalar tag that loses bits on
discriminant `300` fails `enumAdmitted` and refutes `WellFormed`. -/
theorem refute_enum_admitted_scalar_tag_lossless :
    ReachesResult (mkSingleBlockProg 0 [.unit, .enum lossyTagEnum] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .enum lossyTagEnum] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_ordering_invalid_tag_none`: `orderingOfTagBits` rejects invalid
tag `2` so an `Ordering` constant with bits `2` faults with `.undefined`. -/
theorem refute_enum_ordering_invalid_tag_none :
    ReachesResult (mkConstRetProg .ordering 2) queryEmpty (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .ordering 2) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_val_ty_enum_variant_in_bounds`: `Val.ty?` rejects an
out-of-range variant index (`5` for 2-variant `reprU8EnumTy`) with
`.unsupported`. -/
theorem refute_enum_val_ty_enum_variant_in_bounds :
    ReachesResult (mkSingleBlockProg 1 [.unit, .enum reprU8EnumTy] [])
      { args := [.enumVal reprU8EnumTy 5] } (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 1 [.unit, .enum reprU8EnumTy] [])
      { args := [.enumVal reprU8EnumTy 5] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_val_ty_overflow_pair_wf`: `Val.ty?` rejects an overflow pair
carrying a non-canonical `u8` scalar (`bits = 256`) with `.unsupported`. -/
theorem refute_enum_val_ty_overflow_pair_wf :
    ReachesResult (mkSingleBlockProg 1 [.unit, .tuple [u8Ty, .bool]] [])
      { args := [.tuple [u8Val 256, .bool false]] } (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 1 [.unit, .tuple [u8Ty, .bool]] [])
      { args := [.tuple [u8Val 256, .bool false]] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_check_args_length_mismatch`: `checkArgsMatch` rejects passing
0 arguments to a 1-argument function with `.unsupported`. -/
theorem refute_enum_check_args_length_mismatch :
    ReachesResult (mkSingleBlockProg 1 [.unit, u32Ty] []) queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 1 [.unit, u32Ty] []) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_supported_ty_reject_non_overflow_tuple`:
`isSupportedScalarOrUnitTy` rejects non-overflow-pair tuples `(u32, u32)`. -/
theorem refute_enum_supported_ty_reject_non_overflow_tuple :
    ReachesResult (mkSingleBlockProg 0 [.unit, .tuple [u32Ty, u32Ty]] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .tuple [u32Ty, u32Ty]] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_supported_ty_reject_ref_ptr`: `isSupportedScalarOrUnitTy`
rejects reference and raw-pointer local types. -/
theorem refute_enum_supported_ty_reject_ref_ptr :
    ReachesResult (mkSingleBlockProg 0 [.unit, .ref .shared u32Ty] [])
      queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 0 [.unit, .ref .shared u32Ty] [])
      queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program reading an uninitialized scalar-tagged enum local `_1`. -/
noncomputable def progReadUninitScalarEnum : Program :=
  mkSingleBlockProg 0 [.enum reprU8EnumTy, .enum reprU8EnumTy]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `enum_live_uninit_scalar_enum_uninit`: `liveUninitSlot` starts
scalar-tagged enums uninitialized (`.immediate none`) so reading one before
initialization faults with `.undefined`. -/
theorem refute_enum_live_uninit_scalar_enum_uninit :
    ReachesResult progReadUninitScalarEnum queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progReadUninitScalarEnum queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

end GuardMutation
