/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.Util
public import Arithmetic
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs
theorem pad_to_align_spec : Zerocopy.Specs.pad_to_align_spec := by
  intro self h
  unfold layout.DstLayout.pad_to_align
  cases hs : self.size_info with
  | SliceDst dst =>
    simp only [hs] at h ⊢
    cases hshallow : self.statically_shallow_unpadded <;>
      cases self <;> simp_all [bind_ok]
  | Sized size =>
    simp only [hs] at h ⊢
    obtain ⟨hpow, hroom⟩ := h
    step with padding_lt_alignment size self.align hpow as
      ⟨padding, hbound, hexact, haligned, hminimal, hzero⟩
    have hbound := (UScalar.lt_equiv _ _).mp hbound
    have hadd := Usize.checked_add_bv_spec size padding
    cases hchecked : Usize.checked_add size padding with
    | none =>
      simp only [hchecked] at hadd
      omega
    | some padded =>
      simp only [hchecked] at hadd
      have hflag : (padding = 0#usize) = (size.val % self.align.val.val = 0) := by
        apply propext
        rw [← hzero]
        exact ⟨fun hp => by simp [hp], fun hp => UScalar.eq_of_val_eq (by simpa using hp)⟩
      cases hshallow : self.statically_shallow_unpadded <;>
        simp only [lift, bind_ok, Bool.false_eq_true, if_false, if_true]
      all_goals
        refine ⟨rfl, padded, rfl, by omega, by omega, by omega, ?_, ?_, ?_⟩
        · simpa only [hadd] using haligned
        · intro q hq hqa
          have := hminimal (q - size.val) (by
            rw [Nat.add_sub_of_le hq]
            exact hqa)
          omega
        · simp [hflag]
end Zerocopy.Proofs
