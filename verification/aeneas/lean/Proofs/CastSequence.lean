/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import CastMath
@[expose] public section

/-!
The cast selector compares complete size sequences after advancing the
destination's formula. A positive comparison certifies an affine map of
element counts; it says nothing about the physical trailing-field offsets.
Failure to represent the adjustment or a negative comparison promises no
inequality, since this recognizer intentionally need not be complete.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

theorem cast_size_sequences_spec (src dst : layout.TrailingSliceLayout Usize)
    (dst_base : Usize)
    (hsrc : 0 < src.size_rounding_align_and_phase._0.val.val)
    (hdst : 0 < dst.size_rounding_align_and_phase._0.val.val)
    (_positive : 0 < dst.elem_size.val)
    (divides : src.elem_size.val % dst.elem_size.val = 0) :
    layout.cast_from.CastPlan.size_sequences_match src dst dst_base
      ⦃ same => same = true → ∀ count : Nat,
        (trailingFormula src).size count =
          (trailingFormula dst).size
            (dst_base.val + count * (src.elem_size.val / dst.elem_size.val)) ⦄ := by
  unfold layout.cast_from.CastPlan.size_sequences_match
  cases hm : Usize.checked_mul dst_base dst.elem_size with
  | none => simp [lift, WP.spec_ok]
  | some bytes =>
    have bytes_value : bytes.val = dst_base.val * dst.elem_size.val := by
      have facts := Usize.checked_mul_bv_spec dst_base dst.elem_size
      simp only [hm] at facts
      exact facts.2.1
    simp only [lift, bind_ok]
    step with advance_spec dst bytes src.elem_size hdst as ⟨advanced, admitted, formula⟩
    cases advanced with
    | none => simp [WP.spec_ok]
    | some advanced =>
      have advanced_positive : 0 < advanced.size_rounding_align_and_phase._0.val.val :=
        admitted advanced (by simp)
      step with same_size_sequence_spec src advanced hsrc advanced_positive as ⟨same, equal⟩
      rename_i same_true count
      have sequences := equal same_true
      rw [formula.1, bytes_value] at sequences
      have stride : (trailingFormula src).elem =
          (src.elem_size.val / dst.elem_size.val) * (trailingFormula dst).elem := by
        exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divides)).symm
      exact LayoutMath.affine_size_of_advance (trailingFormula src) (trailingFormula dst)
        dst_base.val (src.elem_size.val / dst.elem_size.val) stride sequences count

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

theorem cast_size_sequences_spec : Specs.cast_size_sequences_spec := by
  unfold Specs.cast_size_sequences_spec
  representation_simps
  intro src dst dst_base hsrc hdst positive divides
  exact Raw.cast_size_sequences_spec src dst dst_base hsrc hdst positive divides
register_spec_step cast_size_sequences_spec

end Zerocopy.Proofs
