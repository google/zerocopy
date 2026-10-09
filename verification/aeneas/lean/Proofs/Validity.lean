/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.SafetyChecks
public import BytesAdapter
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- These are the predicates called by the production scalar validators. The
-- raw candidates include every u8/usize value, not just valid encodings.
theorem bool_encoding_raw (byte : U8) :
    util.validity.bool_encoding byte ⦃ out =>
      out = decide (byte.val = 0 ∨ byte.val = 1) ⦄ := by
  simp only [util.validity.bool_encoding, WP.spec_ok]
  apply Bool.eq_iff_iff.mpr
  simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, decide_eq_true_eq]
  omega

theorem nonzero_encoding_raw (n : Usize) :
    util.validity.nonzero_encoding n ⦃ out => out = decide (n.val ≠ 0) ⦄ := by
  simp only [util.validity.nonzero_encoding, WP.spec_ok]
  apply Bool.eq_iff_iff.mpr
  simp [bne_iff_ne, UScalar.eq_equiv]

theorem bool_encoding_spec : Specs.bool_encoding_spec := by
  intro byte _ _
  apply WP.spec_mono (bool_encoding_raw byte)
  intro out facts
  exact ⟨out, rfl, facts⟩

theorem nonzero_encoding_spec : Specs.nonzero_encoding_spec := by
  intro n _ _
  apply WP.spec_mono (nonzero_encoding_raw n)
  intro out facts
  exact ⟨out, rfl, facts⟩

-- Successful construction must return the original word, with a nonzero raw
-- representation. The decoder therefore cannot hide an invalid zero result.
theorem checked_nonzero_raw (n : Usize) :
    util.safety_checks.checked_nonzero n ⦃ out => match out with
      | none => n.val = 0
      | some value => value.val = n ∧ 0 < value.val.val ⦄ := by
  by_cases zero : n.val = 0
  · simp [util.safety_checks.checked_nonzero, util.validity.nonzero_encoding,
      UScalar.eq_equiv, zero, bind_ok]
  · have positive : 0 < n.val := by omega
    simp [util.safety_checks.checked_nonzero, util.validity.nonzero_encoding,
      core.num.nonzero.NonZero.new, bne_iff_ne, UScalar.eq_equiv, zero,
      positive, bind_ok]

theorem checked_nonzero_spec : Specs.checked_nonzero_spec := by
  intro n _ _
  apply WP.spec_mono (checked_nonzero_raw n)
  intro out facts
  cases out with
  | none => exact ⟨none, rfl, facts⟩
  | some value =>
    refine ⟨some ⟨unsignedWord value.val, facts.2⟩, ?_, facts⟩
    simp only [RustModel.decode, facts.2, ↓reduceDIte, Option.map_some]

-- The fixed array bridge reads bytes before their Boolean validity is known.
-- Both reads have statically proved bounds; construction uses the checked
-- scalar conversion, so no invalid Bool can disappear through the carrier.
theorem checked_bool_pair_raw (bytes : Aeneas.Std.Array U8 2#usize) :
    util.safety_checks.checked_bool_pair bytes ⦃ out => match out with
      | none => ∃ byte ∈ bytes.val, 2 ≤ byte.val
      | some values => values.val = bytes.val.map (fun byte => decide (byte.val = 1)) ∧
          ∀ byte ∈ bytes.val, byte.val < 2 ⦄ := by
  obtain ⟨left, right, same⟩ := List.length_eq_two.mp
    (show bytes.val.length = 2 by simp)
  by_cases hl : left.val ≤ 1 <;> by_cases hr : right.val ≤ 1 <;>
    simp [util.safety_checks.checked_bool_pair, Array.to_slice,
      util.validity.read_byte, util.safety_checks.checked_bool,
      util.validity.bool_encoding, util.transmute_unchecked,
      UScalar.lt_equiv, UScalar.ofNatCore_val_eq, lift, bind_ok, same, hl, hr] <;> omega

private theorem decode_bool_list (values : List Bool) :
    decodeList (modelBool).decode values = some values := by
  change decodeList some values = some values
  induction values with
  | nil => rfl
  | cons head tail ih => simp [decodeList, ih]

private def boolArray (raw : Aeneas.Std.Array Bool 2#usize) : ArrayValue Bool 2#usize :=
  ⟨raw.val, raw.property⟩

private theorem decode_bool_array (raw : Aeneas.Std.Array Bool 2#usize) :
    (modelArray 2#usize).decode raw = some (boolArray raw) := by
  apply (decodeArray_iff modelBool 2#usize raw (boolArray raw)).mpr
  exact decode_bool_list raw.val

theorem checked_bool_pair_spec : Specs.checked_bool_pair_spec := by
  intro bytes _ _
  apply WP.spec_mono (checked_bool_pair_raw bytes)
  intro out facts
  cases out with
  | none => exact ⟨none, rfl, facts⟩
  | some values =>
    exact ⟨some (boolArray values), by
      change Option.map some ((modelArray 2#usize).decode values) =
        some (some (boolArray values))
      rw [decode_bool_array values]
      rfl, facts⟩

-- Unlike the layout adapter, this loop may finish early with false. Use the
-- upstream decreasing-natural rule directly, retaining the checked prefix.
theorem bool_slice_loop_raw (bytes : Slice U8) (i : Usize)
    (bound : i.val ≤ bytes.val.length)
    (checked : ∀ j, j < i.val → (bytes.val[j]!).val < 2) :
    util.safety_checks.bool_slice_valid_loop bytes i ⦃ out =>
      out = decide (∀ byte ∈ bytes.val, byte.val < 2) ⦄ := by
  unfold util.safety_checks.bool_slice_valid_loop
  apply loop.spec_decr_nat
    (fun i : Usize => bytes.val.length - i.val)
    (fun i => i.val ≤ bytes.val.length ∧ ∀ j, j < i.val → (bytes.val[j]!).val < 2)
  · intro idx ⟨bound, checked⟩
    unfold util.safety_checks.bool_slice_valid_loop.body
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]
    split
    · rename_i inside
      simp only [util.validity.read_byte, inside, ↓reduceIte, bind_ok,
        util.validity.bool_encoding, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, decide_eq_true_eq]
      split
      · rename_i valid
        step with Usize.add_spec (x := idx) (y := 1#usize) (by
          have := bytes.property
          simp only [UScalar.ofNatCore_val_eq]
          omega) as ⟨next, advanced⟩
        refine ⟨by omega, ?_, by omega⟩
        intro j before
        by_cases earlier : j < idx.val
        · exact checked j earlier
        · have same : j = idx.val := by omega
          simpa only [same] using valid
      · rename_i invalid
        have rejected : ¬ (∀ byte ∈ bytes.val, byte.val < 2) := by
          intro all
          have member : bytes.val[idx.val]! ∈ bytes.val := by
            simpa only [getElem!_pos bytes.val idx.val inside] using List.getElem_mem inside
          exact invalid (all _ member)
        simp only [WP.spec_ok]
        exact (decide_eq_false rejected).symm
    · rename_i finished
      have at_end : idx.val = bytes.val.length := by omega
      have all : ∀ byte ∈ bytes.val, byte.val < 2 := by
        intro byte member
        obtain ⟨j, hj, same⟩ := List.getElem_of_mem member
        have good := checked j (by omega)
        simpa only [getElem!_pos bytes.val j hj, same] using good
      simp only [WP.spec_ok]
      exact (decide_eq_true all).symm
  · exact ⟨bound, checked⟩

theorem bool_slice_valid_spec : Specs.bool_slice_valid_spec := by
  intro bytes _ _
  apply WP.spec_mono (bool_slice_loop_raw bytes 0#usize (by simp) (by simp))
  intro out facts
  exact ⟨out, rfl, facts⟩

end Zerocopy.Proofs
