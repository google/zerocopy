/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import ModelLemmas
@[expose] public section

/-!
The callers establish the guards of the trusted conversion and copying helpers.
These are proofs of composition, not proofs of the opaque Rust helper bodies.
The result witnesses additionally check that the actual returned representation,
including the updated mutable slice, decodes successfully.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

private theorem decode_bool_option (value : Option Bool) :
    (inferInstance : RustModel (Option Bool)).decode value = some value := by
  cases value <;> rfl

private theorem decode_unsigned_list (values : List U8) :
    decodeList (modelUScalar .U8).decode values = some (values.map unsignedWord) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [decodeList, ih]

def byteSlice (raw : Slice U8) : SliceValue (UnsignedWord .U8) :=
  ⟨raw.val.map unsignedWord, by simpa only [List.length_map] using raw.property⟩

theorem decode_byte_slice (raw : Slice U8) :
    (modelSlice (α := U8)).decode raw = some (byteSlice raw) := by
  apply (decodeSlice_iff (modelUScalar .U8) raw (byteSlice raw)).mpr
  exact decode_unsigned_list raw.val

private theorem decode_copy_result (out : Bool × Slice U8) :
    (inferInstance : RustModel (Bool × Slice U8)).decode out =
      some (out.1, byteSlice out.2) := by
  have decoded := decode_byte_slice out.2
  simp only [RustModel.decode] at decoded ⊢
  rw [decoded]

theorem checked_bool_raw (byte : U8) :
    util.safety_checks.checked_bool byte ⦃ out =>
      out = if byte.val < 2 then some (decide (byte.val = 1)) else none ⦄ := by
  by_cases valid : byte.val < 2
  · simp [util.safety_checks.checked_bool, util.validity.bool_encoding, UScalar.lt_equiv,
      UScalar.ofNatCore_val_eq, util.transmute_unchecked, valid, bind_ok]
  · simp [util.safety_checks.checked_bool, util.validity.bool_encoding, UScalar.lt_equiv,
      UScalar.ofNatCore_val_eq, valid]

theorem checked_bool_spec : Specs.checked_bool_spec := by
  intro byte _ _
  apply WP.spec_mono (checked_bool_raw byte)
  intro result same
  exact ⟨result, decode_bool_option result, same⟩

theorem checked_copy_raw (src dst : Slice U8) :
    util.safety_checks.checked_copy src dst ⦃ out =>
      out.1 = decide (src.val.length ≤ dst.val.length) ∧
      out.2.val = if src.val.length ≤ dst.val.length
        then src.val ++ dst.val.drop src.val.length else dst.val ⦄ := by
  by_cases fits : src.val.length ≤ dst.val.length
  · simp [util.safety_checks.checked_copy, Slice.len, UScalar.le_equiv,
      util.copy_unchecked, fits, bind_ok]
  · simp [util.safety_checks.checked_copy, Slice.len, UScalar.le_equiv,
      fits]

theorem checked_copy_spec : Specs.checked_copy_spec := by
  intro src dst _ _ _ _
  apply WP.spec_mono (checked_copy_raw src dst)
  intro result facts
  exact ⟨(result.1, byteSlice result.2), decode_copy_result result, facts⟩

end Zerocopy.Proofs
