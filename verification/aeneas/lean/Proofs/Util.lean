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

set_option linter.unusedVariables false

theorem padding_lt_alignment :
  ∀ (len : Usize) (align : NonZeroUsize), ∀ (h : (0 < align.val.val : Prop)),
    @Zerocopy.util.padding_needed_for len align ⦃ p => p.val < align.val.val ⦄ := by
  intro len align h
  unfold util.padding_needed_for
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step
  simp only [lift, bind_ok, WP.spec_ok, UScalar.val_and]
  have hbound :
      (~~~(core.num.Usize.wrapping_sub len 1#usize)).val &&& mask.val ≤ mask.val :=
    Nat.and_le_right
  omega

theorem round_down_spec :
  ∀ (n : Usize) (align : NonZeroUsize), ∀ (hpos : (0 < align.val.val : Prop)), ∀ (h : (align.val.val.isPowerOfTwo : Prop)),
    @Zerocopy.util.round_down_to_next_multiple_of_alignment n align ⦃ m => m.val ≤ n.val ∧ m.val % align.val.val = 0 ⦄ := by
  intro n align hpos h
  unfold util.round_down_to_next_multiple_of_alignment
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step
  step
  step with UScalar.sub_bv_spec as ⟨mask, hval, hle, hbv⟩
  simp only [lift, bind_ok, WP.spec_ok]
  constructor
  · simp only [UScalar.val_and]
    exact Nat.and_le_left
  · have clear : (n &&& ~~~mask).val &&& mask.val = 0 := by
      rw [← UScalar.val_and]
      change ((n.bv &&& ~~~mask.bv) &&& mask.bv).toNat = 0
      simp [BitVec.and_assoc]
    unfold Nat.isPowerOfTwo at h
    rcases h with ⟨k, hk⟩
    rw [hval, hk, Nat.and_two_pow_sub_one_eq_mod] at clear
    simpa only [hk] using clear

theorem max_spec :
  ∀ (a b : NonZeroUsize),
    @Zerocopy.util.max a b ⦃ r => r.val.val = Nat.max a.val.val b.val.val ⦄ := by
  intro a b
  apply WP.exists_imp_spec
  simp only [util.max, core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
  split
  · rename_i h
    exact ⟨b, rfl, (Nat.max_eq_right (by omega)).symm⟩
  · rename_i h
    exact ⟨a, rfl, (Nat.max_eq_left (by omega)).symm⟩

theorem min_spec :
  ∀ (a b : NonZeroUsize),
    @Zerocopy.util.min a b ⦃ r => r.val.val = Nat.min a.val.val b.val.val ⦄ := by
  intro a b
  apply WP.exists_imp_spec
  simp only [util.min, core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
  split
  · rename_i h
    exact ⟨b, rfl, (Nat.min_eq_right (by omega)).symm⟩
  · rename_i h
    exact ⟨a, rfl, (Nat.min_eq_left (by omega)).symm⟩

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs

theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by
  intro len align h
  exact Raw.padding_lt_alignment len align h
register_spec_step padding_lt_alignment

theorem round_down_spec : Zerocopy.Specs.round_down_spec := by
  intro n align hpos h
  exact Raw.round_down_spec n align hpos h
register_spec_step round_down_spec

theorem max_spec : Zerocopy.Specs.max_spec := by
  intro a b ha hb
  apply WP.spec_mono (Raw.max_spec a b)
  intro r facts
  refine ⟨?_, facts⟩
  change 0 < a.val.val at ha
  change 0 < b.val.val at hb
  change 0 < r.val.val
  rw [facts]
  simp only [Nat.max_def]
  split <;> assumption
register_spec_step max_spec

theorem min_spec : Zerocopy.Specs.min_spec := by
  intro a b ha hb
  apply WP.spec_mono (Raw.min_spec a b)
  intro r facts
  refine ⟨?_, facts⟩
  change 0 < a.val.val at ha
  change 0 < b.val.val at hb
  change 0 < r.val.val
  rw [facts]
  simp only [Nat.min_def]
  split <;> assumption
register_spec_step min_spec

end Zerocopy.Proofs
