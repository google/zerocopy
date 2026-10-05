/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Util
public import Obligations.Allocation
public import RepresentationLaws
public import Proofs.TailReference
public import Proofs.PointerMetadata
public import Proofs.TailTransformChecks
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Zerocopy.Proofs.Raw.Allocation

/- Allocator validity is a separate domain supplied by the completed Rust
layout contract and valid metadata. Decoding or Some alone does not imply it.
-/
def limit : Nat := 2 ^ (System.Platform.numBits - 1) - 1

def admittedAllocation (size alignment : Nat) : Prop :=
  alignment.isPowerOfTwo ∧ size % alignment = 0 ∧ size ≤ limit

theorem admitted_allocator_bound (size alignment : Nat)
    (admitted : admittedAllocation size alignment) :
    alignment.isPowerOfTwo ∧ LayoutMath.roundUp size alignment ≤ limit := by
  refine ⟨admitted.1, ?_⟩
  rw [LayoutMath.roundUp_eq _ _ admitted.2.1]
  exact admitted.2.2

/- Complete recursive descriptions derive the alignment part of this domain.
The signed-size premise is explicit: it corresponds to valid Rust metadata.
-/
theorem description_aligned (description : LayoutMath.Description)
    (valid : description.valid) (metadata : Nat) :
    description.size metadata % 2 ^ description.alignExponent = 0 := by
  cases description with
  | slice elem exponent =>
    simp only [LayoutMath.Description.valid] at valid
    simp only [LayoutMath.Description.size, LayoutMath.Description.alignExponent,
      Nat.mul_mod, valid, Nat.mul_zero, Nat.zero_mod]
  | record leading minimum packed tail =>
    exact (LayoutMath.roundUp_properties _ _ (Nat.two_pow_pos _)).2.2

theorem recursive_admitted_allocation (description : LayoutMath.Description)
    (valid : description.valid) (metadata : Nat)
    (fits : description.size metadata ≤ limit) :
    admittedAllocation (description.size metadata) (2 ^ description.alignExponent) := by
  exact ⟨⟨description.alignExponent, rfl⟩, description_aligned description valid metadata, fits⟩

/- Independently intended optional-value preservation, without a layout filter. -/
def preparedValue (size : Option Nat) (alignment : Nat) : Option (Nat × Nat) :=
  size.map (fun size => (size, alignment))

theorem preparedValue_input (size : Option Usize) (alignment : Nat) :
    preparedValue (size.map UScalar.val) alignment =
      size.map (fun size => (size.val, alignment)) := by
  cases size <;> rfl

theorem preparedValue_some (size : Option Nat) (alignment allocated result_align : Nat)
    (accepted : preparedValue size alignment = some (allocated, result_align)) :
    size = some allocated ∧ result_align = alignment := by
  cases size with
  | none => cases accepted
  | some size =>
    have same : (size, alignment) = (allocated, result_align) := Option.some.inj accepted
    cases same
    exact ⟨rfl, rfl⟩

/- Accepted metadata size is connected to an independent recursive description.
Exact complete size and tail containment follow before allocator validity is
introduced. The latter additionally needs the outer layout alignment and the
explicit signed-size condition of valid metadata.
-/
theorem recursive_allocation_contains_tail (description : LayoutMath.Description)
    (valid : description.valid) (metadata alignment allocated result_align : Nat)
    (metadata_size : Option Nat)
    (sized : metadata_size = description.compile.checkedSize Usize.max metadata)
    (accepted : preparedValue metadata_size alignment = some (allocated, result_align)) :
    allocated = description.size metadata ∧
    description.offset + metadata * description.elem ≤ allocated := by
  have facts := preparedValue_some metadata_size alignment allocated result_align accepted
  rw [sized] at facts
  unfold LayoutMath.Formula.checkedSize at facts
  split at facts
  · have exact_size : description.compile.size metadata = allocated := Option.some.inj facts.1
    have recursive_size := LayoutMath.compile_size description valid metadata
    refine ⟨exact_size.symm.trans recursive_size, ?_⟩
    rw [← exact_size, recursive_size]
    exact LayoutMath.description_contains_tail description metadata
  · cases facts.1

theorem recursive_allocation_valid (description : LayoutMath.Description)
    (valid : description.valid) (metadata alignment allocated result_align : Nat)
    (metadata_size : Option Nat)
    (sized : metadata_size = description.compile.checkedSize Usize.max metadata)
    (accepted : preparedValue metadata_size alignment = some (allocated, result_align))
    (alignment_matches : alignment = 2 ^ description.alignExponent)
    (metadata_valid : description.size metadata ≤ limit) :
    admittedAllocation allocated result_align ∧
    LayoutMath.roundUp allocated result_align ≤ limit := by
  have complete := (recursive_allocation_contains_tail description valid metadata alignment
    allocated result_align metadata_size sized accepted).1
  have unchanged := (preparedValue_some metadata_size alignment allocated result_align accepted).2
  have admitted := recursive_admitted_allocation description valid metadata metadata_valid
  rw [complete, unchanged, alignment_matches]
  exact ⟨admitted, (admitted_allocator_bound _ _ admitted).2⟩

theorem prepare (size : Option Usize) (align : NonZeroUsize) :
    util.allocation.prepare size align ⦃ result =>
      result.map (fun pair => (pair.1.val, pair.2.val.val)) =
        preparedValue (size.map UScalar.val) align.val.val ⦄ := by
  cases size <;> simp [util.allocation.prepare, preparedValue, WP.spec_ok]

/- The extracted assertions force exact preservation on every optional size,
including oversized and unaligned values. They do not certify allocator use.
-/
theorem assert_preparation (size : Option Usize) (align : NonZeroUsize) :
    util.allocation.assert_preparation size align ⦃ _ => True ⦄ := by
  unfold util.allocation.assert_preparation
  step with prepare size align as ⟨prepared, prepared_facts⟩
  cases size with
  | none =>
    have absent : prepared = none := by
      simpa only [preparedValue, Option.map_none, Option.map_eq_none_iff] using prepared_facts
    simp [absent, core.option.Option.is_none, WP.spec_ok]
  | some size =>
    cases prepared with
    | none => simp [preparedValue] at prepared_facts
    | some pair =>
      rcases pair with ⟨actual_size, actual_align⟩
      have pair_eq := Option.some.inj prepared_facts
      have size_value := congrArg Prod.fst pair_eq
      have align_value := congrArg Prod.snd pair_eq
      have size_same : actual_size = size := UScalar.eq_of_val_eq size_value
      have align_same : actual_align.val = align.val := UScalar.eq_of_val_eq align_value
      simp [size_same, align_same, core.num.nonzero.NonZero.get, WP.spec_ok]

end Zerocopy.Proofs.Raw.Allocation

namespace Zerocopy.Proofs
open AeneasSpecs

theorem allocation_prepare_spec : Specs.allocation_prepare_spec := by
  unfold Specs.allocation_prepare_spec
  representation_simps
  intro size align positive
  apply WP.spec_mono (Raw.Allocation.prepare size align)
  intro result facts
  refine ⟨?_, ?_⟩
  · change ∀ pair ∈ result, isValid pair
    cases result with
    | none => simp
    | some pair =>
      rcases pair with ⟨allocated, result_align⟩
      have accepted := Raw.Allocation.preparedValue_some (size.map UScalar.val)
        align.val.val allocated.val result_align.val.val facts.symm
      have output_positive : 0 < result_align.val.val := by
        simpa only [accepted.2] using positive
      have pair_valid : isValid (allocated, result_align) := (prod_valid_iff _).mpr
        ⟨by simp, (nonzero_valid_iff _).mpr output_positive⟩
      simpa using pair_valid
  · rw [Raw.Allocation.preparedValue_input] at facts
    exact facts
register_spec_step allocation_prepare_spec

theorem allocation_preparation_check_spec : Specs.allocation_preparation_check_spec := by
  unfold Specs.allocation_preparation_check_spec
  representation_simps
  intro size align positive
  apply WP.spec_mono (Raw.Allocation.assert_preparation size align)
  intro result facts
  exact ⟨(), rfl⟩
register_spec_step allocation_preparation_check_spec

end Zerocopy.Proofs

namespace Zerocopy.Proofs.Raw.Allocation
open Zerocopy.Proofs.Raw.TailChecks

/- Recover the unchanged optional metadata size from an accepted preparation. -/
theorem accepted_size (size : Option Usize) (align : NonZeroUsize)
    (allocated : Usize) (output_align : NonZeroUsize)
    (facts : (some (allocated, output_align)).map (fun pair => (pair.1.val, pair.2.val.val)) =
      preparedValue (size.map UScalar.val) align.val.val) : size = some allocated := by
  have accepted := preparedValue_some (size.map UScalar.val) align.val.val allocated.val
    output_align.val.val facts.symm
  apply optional_value_injective
  simpa only [Option.map_some] using accepted.1

/- Both the concrete trait path and the independent reference are executed.
A present concrete sizing result establishes representability; preparation
only preserves it and does not impose an allocator-validity filter.
-/
theorem assert_allocation_size (runtime_layout : layout.DstLayout)
    (rounding_align : NonZeroUsize) (phase metadata : Usize)
    (layout_positive : 0 < runtime_layout.align.val.val)
    (layout_canonical : canonicalLayout runtime_layout)
    (rounding_positive : 0 < rounding_align.val.val) :
    util.allocation.assert_allocation_size runtime_layout rounding_align phase metadata ⦃ _ => True ⦄ := by
  unfold util.allocation.assert_allocation_size
  cases info : runtime_layout.size_info with
  | Sized size =>
    step with PointerMetadata.pointer_metadata_unit_size_for_metadata_spec runtime_layout
      as ⟨actual, actual_value⟩
    simp only [info] at actual_value
    subst actual
    step with same_optional_usize (some size) (some size) as ⟨same, same_iff⟩
    simp only [same_iff.mpr (by simp), massert, if_true, bind_ok]
    step with assert_preparation (some size) runtime_layout.align
    step with prepare (some size) runtime_layout.align as ⟨prepared, prepared_facts⟩
    cases prepared with
    | none => simp only [WP.spec_ok]
    | some pair =>
      rcases pair with ⟨allocated, output_align⟩
      have same := accepted_size (some size) runtime_layout.align allocated output_align prepared_facts
      have size_same := Option.some.inj same
      subst allocated
      step with same_optional_usize (some size) (some size) as ⟨same, same_iff⟩
      simp [same_iff.mpr (by simp), WP.spec_ok]
  | SliceDst tail =>
    step with TailTransforms.witness_matches tail rounding_align phase as ⟨matching_result, matching⟩
    split
    · rename_i matches_true
      have witness := matching matches_true
      have canonical : 0 < tail.size_rounding_align_and_phase._0.val.val := by
        simpa only [canonicalLayout, info] using layout_canonical
      have view := witness_view tail rounding_align phase witness.1 witness.2.1 witness.2.2
      step with PointerMetadata.pointer_metadata_usize_size_for_metadata_spec metadata runtime_layout
        (by simpa only [info] using canonical) as ⟨actual, actual_value⟩
      simp only [info, view] at actual_value
      step with reference_size tail rounding_align phase metadata rounding_positive
        as ⟨expected, expected_value⟩
      have size_same : actual = expected := optional_value_injective
        (actual_value.trans expected_value.symm)
      step with same_optional_usize actual expected as ⟨same, same_iff⟩
      simp only [same_iff.mpr size_same, massert, if_true, bind_ok]
      step with assert_preparation actual runtime_layout.align
      step with prepare actual runtime_layout.align as ⟨prepared, prepared_facts⟩
      cases prepared with
      | none => simp only [WP.spec_ok]
      | some pair =>
        rcases pair with ⟨allocated, output_align⟩
        have actual_same := accepted_size actual runtime_layout.align allocated output_align prepared_facts
        have expected_same : expected = some allocated := size_same.symm.trans actual_same
        step with same_optional_usize expected (some allocated) as ⟨same, same_iff⟩
        simp only [same_iff.mpr expected_same, massert, if_true, bind_ok]
        rw [expected_same] at expected_value
        simp only [Option.map_some] at expected_value
        have size_facts := (checkedNat_some _ _).mp expected_value.symm
        have lower := LayoutMath.Formula.size_lower_bound
          (witnessFormula tail rounding_align phase) metadata.val
        have unrounded_bound : tail.size_base.val + phase.val + metadata.val * tail.elem_size.val ≤
            allocated.val := by
          simpa only [witnessFormula, ← size_facts.2] using lower
        have fits : allocated.val ≤ Usize.max := by scalar_tac
        step as ⟨start, start_facts⟩
        cases start with
        | none =>
          simp only [] at start_facts
          omega
        | some start =>
          simp only [] at start_facts
          have start_value : start.val = tail.size_base.val + phase.val := by omega
          simp only [UScalar.lt_equiv]
          split
          · simp only [WP.spec_ok]
          · rename_i offset_bound
            have contained : tail.offset.val + metadata.val * tail.elem_size.val ≤ allocated.val := by omega
            step as ⟨bytes, bytes_facts⟩
            cases bytes with
            | none => simp only [] at bytes_facts; omega
            | some bytes =>
              simp only [] at bytes_facts
              have bytes_value : bytes.val = metadata.val * tail.elem_size.val := by omega
              step as ⟨ending, ending_facts⟩
              cases ending with
              | none => simp only [] at ending_facts; omega
              | some ending =>
                simp only [] at ending_facts
                have ending_le : ending ≤ allocated := by scalar_tac
                simp [ending_le, WP.spec_ok]
    · simp only [WP.spec_ok]

end Zerocopy.Proofs.Raw.Allocation

namespace Zerocopy.Proofs

theorem allocation_size_check_spec : Specs.allocation_size_check_spec := by
  unfold Specs.allocation_size_check_spec
  representation_simps
  intro runtime_layout rounding_align phase metadata layout_valid rounding_positive
  have canonical : canonicalLayout runtime_layout := by
    cases info : runtime_layout.size_info with
    | Sized size => simp only [canonicalLayout, info]
    | SliceDst tail => simpa only [canonicalLayout, info] using layout_valid.2
  apply WP.spec_mono (Raw.Allocation.assert_allocation_size runtime_layout rounding_align phase metadata
    layout_valid.1 canonical rounding_positive)
  intro result facts
  exact ⟨(), rfl⟩
register_spec_step allocation_size_check_spec

end Zerocopy.Proofs
