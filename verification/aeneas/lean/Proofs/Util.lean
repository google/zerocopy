/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by
  intro len align h
  have hpos := Nat.pos_of_isPowerOfTwo h
  unfold util.padding_needed_for
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step
  simp only [lift, bind_ok, WP.spec_ok]
  have hbound : (~~~(core.num.Usize.wrapping_sub len 1#usize) &&& mask).val
      < align.val.val := by
    have := Nat.and_le_right (n := (~~~(core.num.Usize.wrapping_sub len 1#usize)).val)
      (m := mask.val)
    rw [UScalar.val_and]
    omega
  have haligned := Arithmetic.padding_mask_aligned len align.val mask h (by omega)
  obtain ⟨hexact, hminimal, hzero⟩ :=
    Arithmetic.padding_properties _ _ _ hpos hbound haligned
  exact ⟨(UScalar.lt_equiv _ _).mpr hbound, hexact, haligned, hminimal, hzero⟩

theorem round_down_spec : Zerocopy.Specs.round_down_spec := by
  intro n align h
  have hpos := Nat.pos_of_isPowerOfTwo h
  unfold util.round_down_to_next_multiple_of_alignment
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step
  step
  step with UScalar.sub_bv_spec as ⟨mask, hval, hle, hbv⟩
  simp only [lift, bind_ok, WP.spec_ok]
  have hexact := Arithmetic.round_down_exact n align.val mask h hval
  obtain ⟨hbound, haligned, hnext, hgreatest⟩ :=
    Arithmetic.round_down_properties _ _ _ hpos hexact
  exact ⟨(UScalar.le_equiv _ _).mpr hbound, hexact, haligned, hnext, hgreatest⟩

theorem max_spec : Zerocopy.Specs.max_spec := by
  intro a b
  simp only [util.max, core.num.nonzero.NonZero.get, bind_ok]
  split
  · rename_i h
    exact WP.spec.ret ⟨(max_eq_right (le_of_lt h)).symm, Or.inr rfl,
      le_of_lt h, le_rfl⟩
  · rename_i h
    exact WP.spec.ret ⟨(max_eq_left (le_of_not_gt h)).symm, Or.inl rfl,
      le_rfl, le_of_not_gt h⟩

theorem min_spec : Zerocopy.Specs.min_spec := by
  intro a b
  simp only [util.min, core.num.nonzero.NonZero.get, bind_ok]
  split
  · rename_i h
    exact WP.spec.ret ⟨(min_eq_right (le_of_lt h)).symm, Or.inr rfl,
      le_of_lt h, le_rfl⟩
  · rename_i h
    exact WP.spec.ret ⟨(min_eq_left (le_of_not_gt h)).symm, Or.inl rfl,
      le_rfl, le_of_not_gt h⟩

end Zerocopy.Proofs
