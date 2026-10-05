/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import Proofs
public import Proofs.TailTransformReference
public import RequiredModelContracts.CastUnsized
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.CastUnsized
open TailChecks

theorem cast_unsized_layouts_match_spec (src dst : layout.DstLayout)
    (src_valid : layoutValid src) (dst_valid : layoutValid dst) :
    pointer.cast.cast_unsized_layouts_match src dst ⦃ accepted =>
      match src.size_info, dst.size_info with
      | .Sized src_size, .Sized dst_size => accepted = decide (src_size = dst_size)
      | .SliceDst src_tail, .SliceDst dst_tail => accepted = true →
        src.align = dst.align ∧ src_tail.offset = dst_tail.offset ∧
        ∀ count : Nat, completeLayoutSize src count = completeLayoutSize dst count
      | _, _ => accepted = false ⦄ := by
  unfold pointer.cast.cast_unsized_layouts_match
  cases src_info : src.size_info with
  | Sized src_size => cases dst.size_info <;> simp [WP.spec_ok]
  | SliceDst src_tail =>
    cases dst_info : dst.size_info with
    | Sized dst_size => simp [WP.spec_ok]
    | SliceDst dst_tail =>
      have src_positive : 0 < src_tail.size_rounding_align_and_phase._0.val.val := by
        simpa only [sizeInfoValid, src_info, trailingValid,
          scalar_valid_iff, true_and, encodingValid] using src_valid.2
      have dst_positive : 0 < dst_tail.size_rounding_align_and_phase._0.val.val := by
        simpa only [sizeInfoValid, dst_info, trailingValid,
          scalar_valid_iff, true_and, encodingValid] using dst_valid.2
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      split
      · rename_i align_same
        split
        · rename_i offset_same
          step with Zerocopy.Proofs.Raw.same_size_sequence_spec
            src_tail dst_tail src_positive dst_positive as ⟨accepted, sizes⟩
          rename_i yes
          refine ⟨?_, offset_same, ?_⟩
          · apply nonzero_raw_eq_of_value_eq
            exact congrArg UScalar.val align_same
          · intro count
            simpa only [completeLayoutSize, src_info, dst_info] using sizes yes count
        · simp [WP.spec_ok]
      · simp [WP.spec_ok]

/- Every accepted gate preserves size. The sized branch needs no alignment
premise and includes zero-sized layouts with different alignments. -/
theorem accepted_sizes (src dst : layout.DstLayout) (accepted : Bool)
    (yes : accepted = true)
    (facts : match src.size_info, dst.size_info with
      | .Sized src_size, .Sized dst_size => accepted = decide (src_size = dst_size)
      | .SliceDst src_tail, .SliceDst dst_tail => accepted = true →
        src.align = dst.align ∧ src_tail.offset = dst_tail.offset ∧
        ∀ count : Nat, completeLayoutSize src count = completeLayoutSize dst count
      | _, _ => accepted = false) :
    ∀ count : Nat, completeLayoutSize src count = completeLayoutSize dst count := by
  cases src_info : src.size_info <;> cases dst_info : dst.size_info
  · simp only [src_info, dst_info, yes] at facts
    have same : _ := of_decide_eq_true facts.symm
    simp only [completeLayoutSize, src_info, dst_info, same, implies_true]
  · simp_all
  · simp_all
  · simp only [src_info, dst_info] at facts
    exact (facts yes).2.2

theorem witness_matches (self : layout.DstLayout) (align : NonZeroUsize) (phase : Usize) :
    pointer.cast.checks.witness_matches self align phase
      ⦃ accepted => accepted = true → witnessMatches self align phase ⦄ := by
  unfold pointer.cast.checks.witness_matches
  cases info : self.size_info with
  | Sized size => simp [witnessMatches, info, WP.spec_ok]
  | SliceDst tail =>
    simpa only [witnessMatches, info] using TailTransforms.witness_matches tail align phase

theorem reference_size (self : layout.DstLayout) (align : NonZeroUsize)
    (phase metadata : Usize) (positive : 0 < align.val.val)
    (witness : witnessMatches self align phase) :
    pointer.cast.checks.reference_size self align phase metadata
      ⦃ result => result.map UScalar.val = checkedNat (completeLayoutSize self metadata.val) ⦄ := by
  unfold pointer.cast.checks.reference_size
  cases info : self.size_info with
  | Sized size =>
    have fits : size.val ≤ Usize.max := by scalar_tac
    simp only [WP.spec_ok, Option.map_some, completeLayoutSize, info, checkedNat, fits, if_true]
  | SliceDst tail =>
    simp only [witnessMatches, info] at witness
    have view := witness_view tail align phase witness.1 witness.2.1 witness.2.2
    apply WP.spec_mono (TailChecks.reference_size tail align phase metadata positive)
    intro result facts
    simpa only [completeLayoutSize, info, view, LayoutMath.Formula.checkedSize, checkedNat] using facts

theorem cast_unsized_check (src dst : layout.DstLayout)
    (src_align : NonZeroUsize) (src_phase : Usize) (dst_align : NonZeroUsize)
    (dst_phase metadata : Usize) (src_valid : layoutValid src) (dst_valid : layoutValid dst)
    (src_positive : 0 < src_align.val.val) (dst_positive : 0 < dst_align.val.val) :
    pointer.cast.checks.assert_cast_unsized src dst src_align src_phase dst_align dst_phase metadata
      ⦃ _ => True ⦄ := by
  unfold pointer.cast.checks.assert_cast_unsized
  step with witness_matches src src_align src_phase as ⟨src_matches, src_witness⟩
  split
  · rename_i src_yes
    step with witness_matches dst dst_align dst_phase as ⟨dst_matches, dst_witness⟩
    split
    · rename_i dst_yes
      step with cast_unsized_layouts_match_spec src dst src_valid dst_valid as ⟨accepted, gate_facts⟩
      split
      · rename_i yes
        have sizes := accepted_sizes src dst accepted yes gate_facts
        step with reference_size src src_align src_phase metadata src_positive (src_witness src_yes)
          as ⟨src_size, src_size_facts⟩
        step with reference_size dst dst_align dst_phase metadata dst_positive (dst_witness dst_yes)
          as ⟨dst_size, dst_size_facts⟩
        have size_same := optional_value_injective
          (src_size_facts.trans ((congrArg checkedNat (sizes metadata.val)).trans dst_size_facts.symm))
        step with same_optional_usize src_size dst_size as ⟨same, same_iff⟩
        have same_yes := same_iff.mpr size_same
        simp only [massert, same_yes, if_true, bind_ok]
        cases src_info : src.size_info with
        | Sized bytes => simp [WP.spec_ok]
        | SliceDst src_tail =>
          cases dst_info : dst.size_info with
          | Sized bytes => simp [WP.spec_ok]
          | SliceDst dst_tail =>
            simp only [src_info, dst_info] at gate_facts
            obtain ⟨align_same, offset_same, _⟩ := gate_facts yes
            simp [core.num.nonzero.NonZero.get, align_same, offset_same, WP.spec_ok]
      · simp [WP.spec_ok]
    · simp [WP.spec_ok]
  · simp [WP.spec_ok]

end Zerocopy.Proofs.Raw.CastUnsized

namespace Zerocopy.Proofs
open AeneasSpecs

theorem cast_unsized_layouts_match_spec : Specs.cast_unsized_layouts_match_spec := by
  unfold Specs.cast_unsized_layouts_match_spec
  representation_simps
  intro src dst src_valid dst_valid
  have src_admitted : layoutValid src := by
    simpa only [layoutValid, sizeInfoValid, trailingValid, scalar_valid_iff,
      true_and, encodingValid] using src_valid
  have dst_admitted : layoutValid dst := by
    simpa only [layoutValid, sizeInfoValid, trailingValid, scalar_valid_iff,
      true_and, encodingValid] using dst_valid
  apply WP.spec_mono (Raw.CastUnsized.cast_unsized_layouts_match_spec
    src dst src_admitted dst_admitted)
  intro accepted facts
  cases src_info : src.size_info <;> cases dst_info : dst.size_info <;>
    simpa only [src_info, dst_info, UScalar.eq_equiv] using facts
register_spec_step cast_unsized_layouts_match_spec

theorem cast_unsized_check_spec : Specs.cast_unsized_check_spec := by
  unfold Specs.cast_unsized_check_spec
  intro src dst src_align src_phase dst_align dst_phase metadata
    src_value src_decoded dst_value dst_decoded src_align_value src_align_decoded
    src_phase_value src_phase_decoded dst_align_value dst_align_decoded
    dst_phase_value dst_phase_decoded metadata_value metadata_decoded
  have src_valid := (layout_valid_iff src).mp ⟨src_value, src_decoded⟩
  have dst_valid := (layout_valid_iff dst).mp ⟨dst_value, dst_decoded⟩
  have src_positive := (nonzero_valid_iff src_align).mp ⟨src_align_value, src_align_decoded⟩
  have dst_positive := (nonzero_valid_iff dst_align).mp ⟨dst_align_value, dst_align_decoded⟩
  apply WP.spec_mono (Raw.CastUnsized.cast_unsized_check src dst src_align src_phase
    dst_align dst_phase metadata src_valid dst_valid src_positive dst_positive)
  intro result _facts
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
