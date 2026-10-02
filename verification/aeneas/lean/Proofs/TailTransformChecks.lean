/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import Proofs.TailTransformReference
public import RequiredModelContracts.TailTransforms
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.TailTransforms
open TailChecks
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- A literal view of the extracted comparison block keeps its matcher stable
while proving all stored fields and both Option outcomes. It does not replace
or bypass either the production transformation or the independent reference.
-/
theorem word_bound (word : Usize) : word.val ≤ Usize.max := by
  simpa only [UScalar.rMax_eq_pow_numBits, Usize.max, Usize.numBits] using word.hrBounds

def advanceComparison (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (elem : Usize)
    (actual : Option (layout.TrailingSliceLayout Usize)) (expected : Option (Usize × Usize)) :
    Result (layout.TrailingSliceLayout Usize × Bool) :=
  match (generalizing := false) actual with
  | none => do
    let same ← match (generalizing := false) expected with
      | none => Result.ok true
      | some _ => Result.ok false
    Result.ok (tail, same)
  | some actual =>
    match (generalizing := false) expected with
    | none => Result.ok (tail, false)
    | some pair =>
      do
      let (base, new_phase) := pair
      let same ←
        if actual.offset = tail.offset then
          if actual.elem_size = elem then
            if actual.size_base = base then do
              let encoded ← lift (Usize.checked_add align.val new_phase)
              layout.tail_checks.same_optional_usize encoded
                (some actual.size_rounding_align_and_phase._0.val)
            else Result.ok false
          else Result.ok false
        else Result.ok false
      Result.ok (tail, same)

theorem advance_comparison (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase bytes elem : Usize)
    (actual : Option (layout.TrailingSliceLayout Usize)) (expected : Option (Usize × Usize))
    (actual_facts : (∀ t ∈ actual, encodingValid t.size_rounding_align_and_phase) ∧
      match actual with
      | none => Usize.max < ((witnessFormula tail align phase).advance bytes.val elem.val).base
      | some t => trailingFormula t = (witnessFormula tail align phase).advance bytes.val elem.val ∧
          ((witnessFormula tail align phase).advance bytes.val elem.val).base ≤ Usize.max)
    (expected_facts : match expected with
      | none => Usize.max < ((witnessFormula tail align phase).advance bytes.val elem.val).base
      | some (base, new_phase) =>
          base.val = ((witnessFormula tail align phase).advance bytes.val elem.val).base ∧
          new_phase.val = ((witnessFormula tail align phase).advance bytes.val elem.val).phase ∧
          ((witnessFormula tail align phase).advance bytes.val elem.val).base ≤ Usize.max) :
    advanceComparison tail align elem actual expected ⦃ pair => pair.1 = tail ∧ pair.2 = true ⦄ := by
  cases actual with
  | none =>
    cases expected with
    | none => simp [advanceComparison, WP.spec_ok]
    | some pair => simp only [] at actual_facts expected_facts; omega
  | some actual =>
    cases expected with
    | none => simp only [] at actual_facts expected_facts; omega
    | some pair =>
      rcases pair with ⟨base, new_phase⟩
      simp only [] at actual_facts expected_facts
      have formula_eq := actual_facts.2.1
      have offset_eq : actual.offset = tail.offset := UScalar.eq_of_val_eq
        (congrArg LayoutMath.Formula.offset formula_eq)
      have elem_eq : actual.elem_size = elem := UScalar.eq_of_val_eq
        (congrArg LayoutMath.Formula.elem formula_eq)
      have base_eq : actual.size_base = base := UScalar.eq_of_val_eq
        ((congrArg LayoutMath.Formula.base formula_eq).trans expected_facts.1.symm)
      have actual_positive : 0 < actual.size_rounding_align_and_phase._0.val.val :=
        actual_facts.1 actual (by simp)
      obtain ⟨value, decoded⟩ := rounding_decode_positive actual.size_rounding_align_and_phase actual_positive
      have encoded_value := (rounding_decode_iff actual.size_rounding_align_and_phase value).mp decoded
      have components := rounding_decode_components actual.size_rounding_align_and_phase value decoded
      have align_value : value.align = align.val.val := by
        rw [components.1]
        exact congrArg LayoutMath.Formula.align formula_eq
      have phase_value : value.phase = new_phase.val := by
        rw [components.2]
        exact (congrArg LayoutMath.Formula.phase formula_eq).trans expected_facts.2.1.symm
      have encoding : actual.size_rounding_align_and_phase._0.val.val = align.val.val + new_phase.val := by
        change actual.size_rounding_align_and_phase._0.val.val = value.align + value.phase at encoded_value
        simpa only [align_value, phase_value] using encoded_value
      have encoded : Usize.checked_add align.val new_phase =
          some actual.size_rounding_align_and_phase._0.val := by
        apply optional_value_injective
        rw [checked_add_value]
        exact (checkedNat_some _ _).mpr ⟨by rw [← encoding]; exact word_bound _, encoding.symm⟩
      simp only [advanceComparison, uncurry_apply_pair, offset_eq, elem_eq, base_eq, eq_self_iff_true, if_true, encoded, lift, bind_ok]
      step with same_optional_usize (some actual.size_rounding_align_and_phase._0.val)
        (some actual.size_rounding_align_and_phase._0.val) as ⟨same, same_iff⟩
      simp [same_iff, WP.spec_ok]

/- Same wrapped complete-size observations imply the same machine word: the
physical slice end cancels modulo the word size, then both residues are below
that modulus. This establishes exact output equality, not just a congruence.
-/
theorem padding_unique (tail : layout.TrailingSliceLayout Usize) (elems left right : Usize)
    (same : (left.val + tail.offset.val + elems.val * tail.elem_size.val) % UScalar.size .Usize =
      (right.val + tail.offset.val + elems.val * tail.elem_size.val) % UScalar.size .Usize) : left = right := by
  have modular : Nat.ModEq (UScalar.size .Usize)
      (left.val + (tail.offset.val + elems.val * tail.elem_size.val))
      (right.val + (tail.offset.val + elems.val * tail.elem_size.val)) := by
    change (_ % _ = _ % _)
    simpa only [Nat.add_assoc] using same
  have cancelled := Nat.ModEq.add_right_cancel'
    (tail.offset.val + elems.val * tail.elem_size.val) modular
  change left.val % UScalar.size .Usize = right.val % UScalar.size .Usize at cancelled
  rw [Nat.mod_eq_of_lt (UScalar.hSize left), Nat.mod_eq_of_lt (UScalar.hSize right)] at cancelled
  exact UScalar.eq_of_val_eq cancelled

theorem offset_and_padding_check (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase elems : Usize)
    (power : align.val.val.isPowerOfTwo) (phase_lt : phase.val < align.val.val)
    (encoding : tail.size_rounding_align_and_phase._0.val.val = align.val.val + phase.val) :
    (do
      let remainder ← tail.size_base % align.val
      let floor_base ← tail.size_base - remainder
      let offset ← layout.TrailingSliceLayout.size_offset tail
      let expected ← lift (Usize.checked_add floor_base phase)
      let same ← layout.tail_checks.same_optional_usize (some offset) expected
      massert same
      let actual ← layout.TrailingSliceLayoutUsize.padding_for_elems tail elems
      let expected ← layout.tail_transform_checks.reference_wrapping_padding tail align phase elems
      massert (actual = expected)) ⦃ _ => True ⦄ := by
  have positive := Nat.pos_of_isPowerOfTwo power
  have code_positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by omega
  have view := witness_view tail align phase power phase_lt encoding
  step with Usize.rem_spec tail.size_base (y := align.val) (by omega) as ⟨remainder, remainder_value⟩
  have remainder_bound := Nat.mod_le tail.size_base.val align.val.val
  step with Usize.sub_spec (x := tail.size_base) (y := remainder) (by omega) as ⟨floor, floor_value⟩
  step with Zerocopy.Proofs.Raw.size_offset_spec tail code_positive as ⟨offset, offset_value⟩
  change offset.val = tail.size_base.val - tail.size_base.val % (trailingFormula tail).align +
    (trailingFormula tail).phase at offset_value
  rw [view] at offset_value
  simp only [witnessFormula] at offset_value
  have addition : Usize.checked_add floor phase = some offset := by
    apply optional_value_injective
    rw [checked_add_value]
    exact (checkedNat_some _ _).mpr ⟨by have := word_bound offset; omega, by omega⟩
  simp only [addition, lift, bind_ok]
  step with same_optional_usize (some offset) (some offset) as ⟨same, same_iff⟩
  simp only [massert, same_iff.mpr trivial, if_true, bind_ok]
  step with Zerocopy.Proofs.Raw.padding_for_elems_spec tail elems code_positive as ⟨actual, actual_facts⟩
  step with reference_wrapping_padding tail align phase elems power as ⟨expected, expected_facts⟩
  rw [view] at actual_facts
  have same := padding_unique tail elems actual expected (by
    simpa only [Usize.size, Usize.numBits, UScalar.size, UScalarTy.Usize_numBits_eq]
      using actual_facts.trans expected_facts.symm)
  simp [massert, same, WP.spec_ok]

theorem tail_transformations_check (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase bytes elem elems : Usize) :
    layout.tail_transform_checks.tail_transformations_check tail align phase bytes elem elems ⦃ _ => True ⦄ := by
  unfold layout.tail_transform_checks.tail_transformations_check
  step with witness_matches tail align phase as ⟨guard_result, matches_facts⟩
  split
  · rename_i matches_true
    obtain ⟨power, phase_lt, encoding⟩ := matches_facts matches_true
    have positive := Nat.pos_of_isPowerOfTwo power
    have code_positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by omega
    have view := witness_view tail align phase power phase_lt encoding
    step with Zerocopy.Proofs.Raw.advance_spec tail bytes elem code_positive as ⟨actual, actual_valid, actual_facts⟩
    step with reference_advance tail align phase bytes elem power phase_lt as ⟨expected, expected_facts⟩
    rw [view] at actual_facts
    simp only [core.num.nonzero.NonZero.get, bind_ok]
    change (Aeneas.Std.bind (advanceComparison tail align elem actual expected) _) ⦃ _ ⦄
    step with advance_comparison tail align phase bytes elem actual expected ⟨actual_valid, actual_facts⟩ expected_facts
      as ⟨tail_copy, same, copy_eq, same_true⟩
    subst tail_copy
    simp only [massert, same_true, if_true, bind_ok]
    exact offset_and_padding_check tail align phase elems power phase_lt encoding
  · simp only [WP.spec_ok]

/- The original method theorem supplies equality for every natural-number
count. Here that stronger fact discharges a different executable observation:
independent checked Option sizes agree at the supplied machine-word count.
-/
theorem tail_size_sequence_check (left right : layout.TrailingSliceLayout Usize)
    (left_align : NonZeroUsize) (left_phase : Usize)
    (right_align : NonZeroUsize) (right_phase elems : Usize) :
    layout.tail_transform_checks.tail_size_sequence_check
      left right left_align left_phase right_align right_phase elems ⦃ _ => True ⦄ := by
  unfold layout.tail_transform_checks.tail_size_sequence_check
  step with witness_matches left left_align left_phase as ⟨left_matches, left_facts⟩
  split
  · rename_i left_true
    obtain ⟨left_power, left_phase_lt, left_encoding⟩ := left_facts left_true
    have left_positive := Nat.pos_of_isPowerOfTwo left_power
    have left_code_positive : 0 < left.size_rounding_align_and_phase._0.val.val := by omega
    have left_view := witness_view left left_align left_phase left_power left_phase_lt left_encoding
    step with witness_matches right right_align right_phase as ⟨right_matches, right_facts⟩
    split
    · rename_i right_true
      obtain ⟨right_power, right_phase_lt, right_encoding⟩ := right_facts right_true
      have right_positive := Nat.pos_of_isPowerOfTwo right_power
      have right_code_positive : 0 < right.size_rounding_align_and_phase._0.val.val := by omega
      have right_view := witness_view right right_align right_phase right_power right_phase_lt right_encoding
      step with Zerocopy.Proofs.Raw.same_size_sequence_spec left right left_code_positive right_code_positive
        as ⟨same_sequence, same_sequence_facts⟩
      split
      · rename_i sequence_true
        have sizes_equal := same_sequence_facts sequence_true elems.val
        rw [left_view, right_view] at sizes_equal
        step with reference_size left left_align left_phase elems left_positive as ⟨left_size, left_size_facts⟩
        step with reference_size right right_align right_phase elems right_positive as ⟨right_size, right_size_facts⟩
        have checked_equal : (witnessFormula left left_align left_phase).checkedSize Usize.max elems.val =
            (witnessFormula right right_align right_phase).checkedSize Usize.max elems.val := by
          simp only [LayoutMath.Formula.checkedSize, sizes_equal]
        have sizes_same := optional_value_injective
          (left_size_facts.trans (checked_equal.trans right_size_facts.symm))
        step with same_optional_usize left_size right_size as ⟨same, same_iff⟩
        simp [massert, same_iff.mpr sizes_same, WP.spec_ok]
      · simp only [WP.spec_ok]
    · simp only [WP.spec_ok]
  · simp only [WP.spec_ok]

/- The independent checked zero-size observation includes its None branch.
Overflow cannot be mistaken for no padding because a stored offset fits.
-/
theorem tail_dynamic_padding_check (runtime_layout : layout.DstLayout)
    (align : NonZeroUsize) (phase : Usize) :
    layout.tail_transform_checks.tail_dynamic_padding_check runtime_layout align phase ⦃ _ => True ⦄ := by
  unfold layout.tail_transform_checks.tail_dynamic_padding_check
  cases info_eq : runtime_layout.size_info with
  | Sized size =>
    step with Zerocopy.Proofs.Raw.requires_dynamic_padding_spec runtime_layout
      (by simp only [info_eq]) as ⟨actual, actual_facts⟩
    simp only [info_eq] at actual_facts
    have actual_false := actual_facts.mpr trivial
    simp [actual_false, massert, WP.spec_ok]
  | SliceDst tail =>
    step with witness_matches tail align phase as ⟨guard_result, guard_facts⟩
    split
    · rename_i guard_true
      obtain ⟨power, phase_lt, encoding⟩ := guard_facts guard_true
      have positive := Nat.pos_of_isPowerOfTwo power
      have code_positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by omega
      have view := witness_view tail align phase power phase_lt encoding
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      step with Usize.rem_spec tail.elem_size (y := align.val) (by omega)
        as ⟨stride_remainder, stride_value⟩
      step with reference_size tail align phase 0#usize positive as ⟨initial, initial_facts⟩
      step with same_optional_usize initial (some tail.offset) as ⟨zero_matches, zero_facts⟩
      have initial_iff : initial = some tail.offset ↔
          (witnessFormula tail align phase).size 0 = tail.offset.val := by
        constructor
        · intro equal
          rw [equal] at initial_facts
          exact (Zerocopy.Proofs.Raw.checked_some_size _ _ _ initial_facts).1.symm
        · intro equal
          apply optional_value_injective
          rw [initial_facts]
          simp only [LayoutMath.Formula.checkedSize, equal, word_bound tail.offset, if_true,
            Option.map_some]
      have no_dynamic_spec :
          (if zero_matches then Result.ok (decide (stride_remainder = 0#usize)) else Result.ok false) ⦃ (b : Bool) =>
            b = true ↔ (witnessFormula tail align phase).size 0 = tail.offset.val ∧
              tail.elem_size.val % align.val.val = 0 ⦄ := by
        cases zero_case : zero_matches with
        | false =>
          have not_equal : ¬(witnessFormula tail align phase).size 0 = tail.offset.val := by
            intro equal
            have is_true := zero_facts.mpr (initial_iff.mpr equal)
            rw [zero_case] at is_true
            contradiction
          simp [WP.spec_ok, not_equal]
        | true =>
          have equal := initial_iff.mp (zero_facts.mp zero_case)
          simp [WP.spec_ok, equal, UScalar.eq_equiv, stride_value]
      step with no_dynamic_spec as ⟨no_dynamic, no_dynamic_facts⟩
      step with Zerocopy.Proofs.Raw.requires_dynamic_padding_spec runtime_layout
        (by simpa only [info_eq] using code_positive) as ⟨actual, actual_facts⟩
      simp only [info_eq, view, witnessFormula] at actual_facts
      cases actual <;> cases no_dynamic <;> simp_all [witnessFormula, massert, WP.spec_ok]
    · simp only [WP.spec_ok]

end Zerocopy.Proofs.Raw.TailTransforms

namespace Zerocopy.Proofs
open AeneasSpecs

theorem tail_transformations_check_spec : Specs.tail_transformations_check_spec := by
  unfold Specs.tail_transformations_check_spec
  intros
  apply WP.spec_mono (Raw.TailTransforms.tail_transformations_check _ _ _ _ _ _)
  intro result facts
  exact ⟨(), rfl, trivial⟩

theorem tail_size_sequence_check_spec : Specs.tail_size_sequence_check_spec := by
  unfold Specs.tail_size_sequence_check_spec
  intros
  apply WP.spec_mono (Raw.TailTransforms.tail_size_sequence_check _ _ _ _ _ _ _)
  intro result facts
  exact ⟨(), rfl, trivial⟩

theorem tail_dynamic_padding_check_spec : Specs.tail_dynamic_padding_check_spec := by
  unfold Specs.tail_dynamic_padding_check_spec
  intros
  apply WP.spec_mono (Raw.TailTransforms.tail_dynamic_padding_check _ _ _)
  intro result facts
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
