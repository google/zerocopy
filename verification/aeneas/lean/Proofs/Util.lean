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
namespace Zerocopy.Proofs.Raw

-- Raw contract requirements intentionally retain their descriptive proof names.
set_option linter.unusedVariables false

theorem padding_lt_alignment :
  ∀ (len : Usize) (align : NonZeroUsize), ∀ (h : ((align.val : Nat).isPowerOfTwo : Prop)),
    @Zerocopy.util.padding_needed_for len align ⦃ p => p < align.val ∧
    let L : Nat := len
    let A : Nat := align.val
    let P : Nat := p
    P = (A - L % A) % A ∧ (L + P) % A = 0 ∧
      (∀ q : Nat, (L + q) % A = 0 → P ≤ q) ∧ (P = 0 ↔ L % A = 0) ⦄ := by
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

theorem round_down_spec :
  ∀ (n : Usize) (align : NonZeroUsize), ∀ (h : ((align.val : Nat).isPowerOfTwo : Prop)),
    @Zerocopy.util.round_down_to_next_multiple_of_alignment n align ⦃ m => m ≤ n ∧
    let N : Nat := n
    let A : Nat := align.val
    let M : Nat := m
    M = N - N % A ∧ M % A = 0 ∧ N < M + A ∧
      (∀ q : Nat, q ≤ N → q % A = 0 → q ≤ M) ⦄ := by
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

theorem max_spec :
  ∀ (a b : NonZeroUsize),
    @Zerocopy.util.max a b ⦃ r => r.val = max a.val b.val ∧ (r = a ∨ r = b) ∧
    a.val ≤ r.val ∧ b.val ≤ r.val ⦄ := by
  intro a b
  simp only [util.max, core.num.nonzero.NonZero.get, bind_ok]
  split
  · rename_i h
    exact WP.spec.ret ⟨(max_eq_right (le_of_lt h)).symm, Or.inr rfl,
      le_of_lt h, le_rfl⟩
  · rename_i h
    exact WP.spec.ret ⟨(max_eq_left (le_of_not_gt h)).symm, Or.inl rfl,
      le_rfl, le_of_not_gt h⟩

theorem min_spec :
  ∀ (a b : NonZeroUsize),
    @Zerocopy.util.min a b ⦃ r => r.val = min a.val b.val ∧ (r = a ∨ r = b) ∧
    r.val ≤ a.val ∧ r.val ≤ b.val ⦄ := by
  intro a b
  simp only [util.min, core.num.nonzero.NonZero.get, bind_ok]
  split
  · rename_i h
    exact WP.spec.ret ⟨(min_eq_right (le_of_lt h)).symm, Or.inr rfl,
      le_of_lt h, le_rfl⟩
  · rename_i h
    exact WP.spec.ret ⟨(min_eq_left (le_of_not_gt h)).symm, Or.inl rfl,
      le_rfl, le_of_not_gt h⟩

end Zerocopy.Proofs.Raw


namespace Zerocopy.Proofs

-- Raw extrema also cover zero stored wrappers. The annotated contracts use
-- the Rust representation domain and prove the selected wrapper valid.
theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by
  intro len align _ h
  exact Raw.padding_lt_alignment len align h
register_spec_step padding_lt_alignment

theorem round_down_spec : Zerocopy.Specs.round_down_spec := by
  intro n align _ h
  exact Raw.round_down_spec n align h
register_spec_step round_down_spec

theorem max_spec : Zerocopy.Specs.max_spec := by
  intro a b ha hb
  apply WP.spec_mono (Raw.max_spec a b)
  intro r facts
  refine ⟨?_, facts⟩
  rcases facts.2.1 with h | h
  · simpa only [h] using ha
  · simpa only [h] using hb
register_spec_step max_spec

theorem min_spec : Zerocopy.Specs.min_spec := by
  intro a b ha hb
  apply WP.spec_mono (Raw.min_spec a b)
  intro r facts
  refine ⟨?_, facts⟩
  rcases facts.2.1 with h | h
  · simpa only [h] using ha
  · simpa only [h] using hb
register_spec_step min_spec

end Zerocopy.Proofs
