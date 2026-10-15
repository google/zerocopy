/- Copyright 2026 The Fuchsia Authors
SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT -/

module
public import Specs
public import BytesAdapter
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs.Raw

theorem owned_transmute_to_bytes (value : U32) :
    util.owned_transmute.to_bytes value ⦃ bytes =>
      bytes.val.map U8.bv = Rust.Bytes.encodeLE 4 value.val ⦄ := by
  have actual : util.owned_transmute.to_bytes value =
      .ok (core.num.U32.to_le_bytes value) := rfl
  rw [actual]
  simp only [WP.spec_ok]
  have digits : (core.num.U32.to_le_bytes value).val.map U8.bv = value.bv.toLEBytes := by
    simp only [core.num.U32.to_le_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  rw [digits]
  exact Rust.Bytes.AeneasAdapter.toLEBytes_eq_encodeLE (by decide) value.bv

theorem owned_transmute_from_bytes (bytes : Aeneas.Std.Array U8 4#usize) :
    util.owned_transmute.from_bytes bytes ⦃ value =>
      value.val = Rust.Bytes.decodeLE (bytes.val.map U8.bv) ⦄ := by
  have actual : util.owned_transmute.from_bytes bytes =
      .ok (core.num.U32.from_le_bytes bytes) := rfl
  rw [actual]
  simp only [WP.spec_ok, core.num.U32.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  exact Rust.Bytes.AeneasAdapter.fromLEBytes_toNat _

theorem owned_transmute_bool (byte : U8) :
    util.owned_transmute.checked_bool byte ⦃ output => match output with
      | none => 2 ≤ byte.val
      | some value => byte.val < 2 ∧ value = decide (byte.val = 1) ⦄ := by
  have actual : core.intrinsics.transmute Bool byte =
      if byte.val < 2 then .ok (decide (byte.val = 1)) else forbiddenExecution := rfl
  unfold util.owned_transmute.checked_bool
  simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq]
  by_cases below : byte.val < 2
  · simp only [if_pos below]
    rw [actual]
    simp only [if_pos below, bind_ok, WP.spec_ok]
    exact ⟨below, trivial⟩
  · simp only [if_neg below, WP.spec_ok]
    omega

theorem owned_transmute_round_trip_checks (value : U32) :
    util.owned_transmute.round_trip_checks value ⦃ _ => True ⦄ := by
  have digits : (core.num.U32.to_le_bytes value).val.map U8.bv = value.bv.toLEBytes := by
    simp only [core.num.U32.to_le_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  have identical : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes value) = value := by
    apply UScalar.eq_of_val_eq
    change (BitVec.fromLEBytes ((core.num.U32.to_le_bytes value).val.map U8.bv)).toNat = value.bv.toNat
    rw [digits, Rust.Bytes.AeneasAdapter.fromLEBytes_toNat]
    exact Rust.Bytes.AeneasAdapter.decodeLE_toLEBytes (by decide) value.bv
  have actualTo : util.owned_transmute.to_bytes value =
      .ok (core.num.U32.to_le_bytes value) := rfl
  have actualFrom : util.owned_transmute.from_bytes (core.num.U32.to_le_bytes value) =
      .ok (core.num.U32.from_le_bytes (core.num.U32.to_le_bytes value)) := rfl
  simp [util.owned_transmute.round_trip_checks, actualTo, actualFrom, identical, bind_ok]

end Zerocopy.Proofs.Raw
namespace Zerocopy.Proofs

theorem owned_transmute_to_bytes_spec : Specs.owned_transmute_to_bytes_spec := by
  intro value mathValue decoded
  have same := (decodeUScalar_iff value mathValue).mp decoded
  apply WP.spec_mono (Raw.owned_transmute_to_bytes value)
  intro bytes facts
  refine ⟨unsignedArray bytes, decodeArray_unsigned bytes, ?_⟩
  change _ = Rust.Bytes.encodeLE 4 mathValue.value
  rw [decodedArray_bytes_eq bytes (unsignedArray bytes) (decodeArray_unsigned bytes), ← same]
  exact facts

theorem owned_transmute_from_bytes_spec : Specs.owned_transmute_from_bytes_spec := by
  intro bytes mathBytes decoded
  apply WP.spec_mono (Raw.owned_transmute_from_bytes bytes)
  intro value facts
  refine ⟨unsignedWord value, rfl, ?_⟩
  change value.val = _
  rw [decodedArray_bytes_eq bytes mathBytes decoded]
  exact facts

theorem owned_transmute_bool_spec : Specs.owned_transmute_bool_spec := by
  intro byte mathByte decoded
  have same := (decodeUScalar_iff byte mathByte).mp decoded
  apply WP.spec_mono (Raw.owned_transmute_bool byte)
  intro output facts
  refine ⟨output, ?_, ?_⟩
  · cases output <;> rfl
  · cases output <;> simpa only [← same] using facts

theorem owned_transmute_round_trip_checks_spec : Specs.owned_transmute_round_trip_checks_spec := by
  intro value _ _
  apply WP.spec_mono (Raw.owned_transmute_round_trip_checks value)
  intro _ _
  exact ⟨(), rfl, trivial⟩

-- Invalid representations must fail before constructing a Boolean, even for
-- a True postcondition. Discarding the result cannot erase forbidden execution.
example : ¬ (core.intrinsics.transmute Bool 2#u8 ⦃ _ => True ⦄) := by
  change ¬ (Result.fail Error.undef : Result Bool) ⦃ _ => True ⦄
  simp

end Zerocopy.Proofs
