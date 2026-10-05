/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import Proofs.TailReference
public import Proofs.TailTransformReference
public import SplitMath
public import RequiredModelContracts.Split
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.Split
open Zerocopy.Proofs.Raw
open Zerocopy.Proofs.Raw.TailChecks
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem right_len (total left : Usize) (index : left.val ≤ total.val) :
    split_at.split_right_len total left ⦃ right =>
      right.val = total.val - left.val ∧ right.val + left.val = total.val ∧
      right.val ≤ total.val ⦄ := by
  unfold split_at.split_right_len
  step with Usize.sub_spec index as ⟨right, value, _⟩
  exact ⟨value, by omega, by omega⟩

theorem zero_padding (padding : Usize) :
    split_at.split_zero_padding padding ⦃ accepted => (accepted = true ↔ padding.val = 0) ⦄ := by
  simp [split_at.split_zero_padding, WP.spec_ok, UScalar.eq_equiv]

/-- The actual modular padding computation supplies a sufficient boundary.
Both physical bytes and complete size are bounded, so congruence cannot hide
an overflow. No assumption about pointers enters this lemma. -/
theorem padding_boundary (tail : layout.TrailingSliceLayout Usize) (left : Usize)
    (positive : 0 < tail.size_rounding_align_and_phase._0.val.val)
    (physical : tail.offset.val + left.val * tail.elem_size.val ≤ Usize.max)
    (fits : (trailingFormula tail).size left.val ≤ Usize.max) :
    layout.TrailingSliceLayoutUsize.padding_for_elems tail left ⦃ padding =>
      padding.val = 0 → (trailingFormula tail).size left.val =
        tail.offset.val + left.val * tail.elem_size.val ⦄ := by
  apply WP.spec_mono (padding_for_elems_spec tail left positive)
  intro padding congruence zero
  rw [zero, Nat.zero_add, word_mod_of_le _ physical, word_mod_of_le _ fits] at congruence
  exact congruence.symm


/-- Execute the ordinary Rust root. Guards admit mismatched witnesses and
unrealizable descriptions without making assertions; fitting physical layouts
and valid indices reach all assertions, including zero strides and end splits. -/
theorem geometry_check (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase total left : Usize) :
    split_at.numerical_checks.check_split_geometry tail align phase total left ⦃ _ => True ⦄ := by
  unfold split_at.numerical_checks.check_split_geometry
  step with TailTransforms.witness_matches tail align phase as ⟨matched_gate, witness⟩
  split
  · rename_i matched
    obtain ⟨power, phase_lt, encoding⟩ := witness matched
    have align_positive := Nat.pos_of_isPowerOfTwo power
    have positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by omega
    have view := witness_view tail align phase power phase_lt encoding
    simp only [UScalar.lt_equiv]
    split
    · simp only [WP.spec_ok]
    · rename_i not_out_of_bounds
      have index : left.val ≤ total.val := by omega
      step with reference_size tail align phase total align_positive as ⟨source, source_value⟩
      cases source with
      | none => simp only [WP.spec_ok]
      | some source =>
        simp only [Option.map_some] at source_value
        rw [← view] at source_value
        have source_facts := checked_some_size _ _ source source_value
        step as ⟨tail_bytes, tail_bytes_facts⟩
        cases tail_bytes with
        | none => simp only [WP.spec_ok]
        | some tail_bytes =>
          simp only [] at tail_bytes_facts
          step as ⟨tail_end, tail_end_facts⟩
          cases tail_end with
          | none => simp only [WP.spec_ok]
          | some tail_end =>
            simp only [] at tail_end_facts
            simp only [UScalar.lt_equiv]
            split
            · simp only [WP.spec_ok]
            · rename_i contained
              have physical : tail.offset.val + total.val * tail.elem_size.val ≤
                  (trailingFormula tail).size total.val := by omega
              obtain ⟨count_total, right_count_bound, left_mono, left_fit, left_bytes_fit,
                right_bytes_fit, left_physical, byte_sum_raw, end_contained⟩ :=
                SplitMath.split_bounds (trailingFormula tail) total.val left.val Usize.max
                  (trailing_align_pos tail) index physical source_facts.2
              change left.val * tail.elem_size.val ≤ Usize.max at left_bytes_fit
              change (total.val - left.val) * tail.elem_size.val ≤ Usize.max at right_bytes_fit
              change tail.offset.val + left.val * tail.elem_size.val ≤ Usize.max at left_physical
              change tail.offset.val + left.val * tail.elem_size.val +
                (total.val - left.val) * tail.elem_size.val =
                tail.offset.val + total.val * tail.elem_size.val at byte_sum_raw
              have byte_sum : tail.offset.val + left.val * tail.elem_size.val +
                  (total.val - left.val) * tail.elem_size.val = tail_end.val := by omega
              step with size_for_elems_spec tail total positive as ⟨actual_source, actual_source_value⟩
              have source_same : actual_source = some source := optional_value_injective
                (actual_source_value.trans source_value.symm)
              step with same_optional_usize actual_source (some source) as ⟨same_source, same_source_iff⟩
              simp only [massert, same_source_iff.mpr source_same, if_true, bind_ok]
              step with size_for_elems_spec tail left positive as ⟨left_option, left_value⟩
              cases left_option with
              | none =>
                have overflow := checked_none_size _ _ left_value
                omega
              | some left_size =>
                simp only [Option.map_some] at left_value
                have left_facts := checked_some_size _ _ left_size left_value
                simp only [core.option.Option.unwrap, Result.ofOption, bind_ok]
                step with reference_size tail align phase left align_positive as ⟨reference_left, reference_left_value⟩
                rw [← view] at reference_left_value
                have left_same : reference_left = some left_size := optional_value_injective
                  (reference_left_value.trans left_value.symm)
                step with same_optional_usize reference_left (some left_size) as ⟨same_left, same_left_iff⟩
                simp only [massert, same_left_iff.mpr left_same, if_true, bind_ok]
                have left_below : left_size ≤ source := (UScalar.le_equiv _ _).mpr (by
                  omega)
                simp only [massert, left_below, if_true, bind_ok]
                step with right_len total left index as ⟨right, right_value, count_sum, right_below⟩
                step with Usize.add_spec (x := right) (y := left)
                  (by
                    have bound : total.val ≤ Usize.max := by scalar_tac
                    omega) as ⟨sum, sum_value⟩
                have sum_eq : sum = total := UScalar.eq_of_val_eq (by omega)
                simp only [massert, sum_eq, if_true, bind_ok]
                step as ⟨left_bytes, left_bytes_value⟩
                cases left_bytes with
                | none => simp only [] at left_bytes_value; omega
                | some left_bytes =>
                  simp only [] at left_bytes_value
                  simp only [core.option.Option.unwrap, Result.ofOption, bind_ok]
                  step as ⟨right_bytes, right_bytes_value⟩
                  cases right_bytes with
                  | none =>
                    simp only [] at right_bytes_value
                    rw [right_value] at right_bytes_value
                    omega
                  | some right_bytes =>
                    simp only [] at right_bytes_value
                    rw [right_value] at right_bytes_value
                    simp only [core.option.Option.unwrap, Result.ofOption, bind_ok]
                    step as ⟨right_start, right_start_value⟩
                    cases right_start with
                    | none => simp only [] at right_start_value; omega
                    | some right_start =>
                      simp only [] at right_start_value
                      simp only [core.option.Option.unwrap, Result.ofOption, bind_ok]
                      step as ⟨right_end, right_end_value⟩
                      cases right_end with
                      | none => simp only [] at right_end_value; omega
                      | some right_end =>
                        simp only [] at right_end_value
                        simp only [core.option.Option.unwrap, Result.ofOption, bind_ok]
                        have end_eq : right_end = tail_end := UScalar.eq_of_val_eq (by omega)
                        have end_below : tail_end ≤ source := (UScalar.le_equiv _ _).mpr (by omega)
                        simp only [massert, end_eq, end_below, if_true, bind_ok]
                        step with padding_boundary tail left positive left_physical left_fit
                          as ⟨padding, padding_zero⟩
                        step with zero_padding padding as ⟨accepted, acceptance⟩
                        have runtime_check :
                            (if accepted then massert (left_size = right_start) else Result.ok ())
                              ⦃ _ => True ⦄ := by
                          split
                          · rename_i accepted_true
                            have boundary := padding_zero (acceptance.mp accepted_true)
                            have same : left_size = right_start := UScalar.eq_of_val_eq (by omega)
                            simp [massert, same, WP.spec_ok]
                          · simp [WP.spec_ok]
                        simp only [massert] at runtime_check
                        step with runtime_check
                        step with requires_dynamic_padding_spec
                          (⟨align, .SliceDst tail, false⟩ : layout.DstLayout) positive
                          as ⟨dynamic, dynamic_iff⟩
                        have static_check :
                            (if dynamic then Result.ok () else massert (left_size = right_start))
                              ⦃ _ => True ⦄ := by
                          cases dynamic with
                          | true => simp [WP.spec_ok]
                          | false =>
                            have absent := dynamic_iff.mp rfl
                            have boundary := LayoutMath.no_dynamic_padding
                              (trailingFormula tail) absent.1 absent.2 left.val
                            change (trailingFormula tail).size left.val =
                              tail.offset.val + left.val * tail.elem_size.val at boundary
                            have same : left_size = right_start := UScalar.eq_of_val_eq (by omega)
                            simp [massert, same, WP.spec_ok]
                        simp only [massert] at static_check
                        step with static_check
                        have end_check :
                            (if left = total then massert (right_bytes = 0#usize) else Result.ok ())
                              ⦃ _ => True ⦄ := by
                          split
                          · rename_i at_end
                            have same : right_bytes = 0#usize := UScalar.eq_of_val_eq (by
                              have values := congrArg UScalar.val at_end
                              simp only [values, Nat.sub_self, Nat.zero_mul] at right_bytes_value
                              simp only [UScalar.ofNatCore_val_eq]
                              omega)
                            simp [massert, same, WP.spec_ok]
                          · simp [WP.spec_ok]
                        simp only [massert] at end_check
                        step with end_check
                        split
                        · rename_i zst
                          have same : right_bytes = 0#usize := UScalar.eq_of_val_eq (by
                            have zero : tail.elem_size.val = 0 := by
                              simpa only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] using zst
                            simp only [zero, Nat.mul_zero] at right_bytes_value
                            simp only [UScalar.ofNatCore_val_eq]
                            omega)
                          simp [massert, same, WP.spec_ok]
                        · simp [WP.spec_ok]
  · simp only [WP.spec_ok]

/-- Apply the production runtime gate to the numerical split geometry.
No successful gate is replaced by a mathematical algorithm. -/
theorem runtime_gate_disjoint (tail : layout.TrailingSliceLayout Usize)
    (total left : Usize) (positive : 0 < tail.size_rounding_align_and_phase._0.val.val)
    (index : left.val ≤ total.val)
    (physical : tail.offset.val + total.val * tail.elem_size.val ≤
      (trailingFormula tail).size total.val)
    (fits : (trailingFormula tail).size total.val ≤ Usize.max) :
    (do
      let padding ← layout.TrailingSliceLayoutUsize.padding_for_elems tail left
      split_at.split_zero_padding padding) ⦃ accepted => accepted = true →
        SplitMath.Disjoint ((trailingFormula tail).size left.val)
          (tail.offset.val + left.val * tail.elem_size.val)
          ((total.val - left.val) * tail.elem_size.val) ⦄ := by
  obtain ⟨_, _, _, left_fit, _, _, start_fit, _, _⟩ :=
    SplitMath.split_bounds (trailingFormula tail) total.val left.val Usize.max
      (trailing_align_pos tail) index physical fits
  step with padding_boundary tail left positive start_fit left_fit
    as ⟨padding, boundary⟩
  apply WP.spec_mono (zero_padding padding)
  intro accepted gate accepted_true
  exact SplitMath.runtime_disjoint (trailingFormula tail) total.val left.val
    (boundary (gate.mp accepted_true))

/-- The actual layout decision proves disjointness at every split index.
This theorem is stronger numerically than just the fitting machine indices;
containment and arithmetic-fit follow separately from split_bounds. -/
theorem static_gate_disjoint (runtime_layout : layout.DstLayout)
    (tail : layout.TrailingSliceLayout Usize)
    (tail_eq : runtime_layout.size_info = .SliceDst tail)
    (positive : 0 < tail.size_rounding_align_and_phase._0.val.val) :
    layout.DstLayout.requires_dynamic_padding runtime_layout
      ⦃ dynamic => dynamic = false → ∀ total left : Nat,
        SplitMath.Disjoint ((trailingFormula tail).size left)
          (tail.offset.val + left * tail.elem_size.val) ((total - left) * tail.elem_size.val) ⦄ := by
  have domain : match runtime_layout.size_info with
      | .Sized _ => True
      | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val := by
    simpa only [tail_eq] using positive
  apply WP.spec_mono (requires_dynamic_padding_spec runtime_layout domain)
  intro dynamic gate absent total left
  have properties := gate.mp absent
  simp only [tail_eq] at properties
  exact SplitMath.static_disjoint (trailingFormula tail) total left properties.1 properties.2

end Zerocopy.Proofs.Raw.Split

namespace Zerocopy.Proofs
open AeneasSpecs

theorem split_right_len_spec : Specs.split_right_len_spec := by
  intro total left totalValue totalDecoded leftValue leftDecoded index
  have totalSame := (decodeUScalar_iff total totalValue).mp totalDecoded
  have leftSame := (decodeUScalar_iff left leftValue).mp leftDecoded
  apply WP.spec_mono (Raw.Split.right_len total left (by
    simpa only [← totalSame, ← leftSame] using index))
  intro right facts
  refine ⟨unsignedWord right, rfl, ?_⟩
  dsimp only
  rw [← totalSame, ← leftSame]
  exact ⟨facts.2.1, facts.2.2⟩
register_spec_step split_right_len_spec

theorem split_zero_padding_spec : Specs.split_zero_padding_spec := by
  intro padding paddingValue paddingDecoded
  have same := (decodeUScalar_iff padding paddingValue).mp paddingDecoded
  apply WP.spec_mono (Raw.Split.zero_padding padding)
  intro accepted facts
  refine ⟨accepted, rfl, ?_⟩
  simpa only [← same] using facts
register_spec_step split_zero_padding_spec

theorem split_geometry_check_spec : Specs.split_geometry_check_spec := by
  unfold Specs.split_geometry_check_spec
  intros
  apply WP.spec_mono (Raw.Split.geometry_check _ _ _ _ _)
  intro result facts
  exact ⟨(), rfl, trivial⟩
register_spec_step split_geometry_check_spec

end Zerocopy.Proofs
