/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.Util
public import Contracts
public import Arithmetic
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs
contract pointer_width_spec
  for layout.POINTER_WIDTH_BITS
  ensures w => w.val = System.Platform.numBits
  proof:
    unfold layout.POINTER_WIDTH_BITS
    simp only [core.mem.size_of, ite_true, bind_ok]
    have hv : ({ bv := BitVec.ofNat _ (System.Platform.numBits / 8) } : Usize).val =
        System.Platform.numBits / 8 := by
      change (System.Platform.numBits / 8) % 2 ^ System.Platform.numBits = _
      rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> decide
    step as ⟨w, hw⟩
    · rw [hv]
      rcases System.Platform.numBits_eq with h | h <;>
        simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, h,
          UScalar.val] <;> decide
    · rw [hv] at hw
      rcases System.Platform.numBits_eq with h | h <;>
        simp only [h] at hw ⊢ <;> omega

theorem encoding_new_spec : Zerocopy.Specs.encoding_new_spec := by
  intro align phase ha hp
  unfold layout.RoundingAlignAndPhase.new
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨b, hb⟩
  have hbt : b = true := by
    have hb' : (b = true) = True := by simpa only [ha] using hb
    exact Eq.mpr hb' trivial
  simp only [massert, hbt, if_true, bind_ok, UScalar.lt_equiv, hp, lift]
  obtain ⟨k, hk⟩ := ha
  have hor : (align.val ||| phase).val = align.val.val + phase.val := by
    rw [UScalar.val_or, hk]
    have h := Nat.two_pow_add_eq_or_of_lt (show phase.val < 2 ^ k by omega) 1
    simpa only [Nat.mul_one] using h.symm
  have hnz : align.val ||| phase ≠ 0#usize := by
    intro hz
    have hz' := congrArg UScalar.val hz
    rw [hor] at hz'
    have hpos := Nat.two_pow_pos k
    change align.val.val + phase.val = 0 at hz'
    omega
  simp only [core.num.nonzero.NonZero.new, cast_eq, hnz, ↓reduceDIte, ↓reduceIte,
    bind_ok, WP.spec_ok]
  exact hor

theorem highest_bit_xor (k p : Nat) (hp : p < 2 ^ k) : (2 ^ k + p) ^^^ 2 ^ k = p := by
  have hjoin : 2 ^ k + p = 2 ^ k ||| p := by
    simpa only [Nat.mul_one] using Nat.two_pow_add_eq_or_of_lt hp 1
  rw [hjoin]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or]
  by_cases hi : i = k
  · subst i
    rw [Nat.testBit_two_pow_self, Nat.testBit_lt_two_pow hp]
    rfl
  · rw [Nat.testBit_two_pow_of_ne (Ne.symm hi)]
    simp


theorem encoding_components_spec : Zerocopy.Specs.encoding_components_spec := by
  intro self hn
  let k := Nat.log2 self.val.val
  have hbound := (Nat.log2_eq_iff (show self.val.val ≠ 0 by omega)).mp (show Nat.log2 self.val.val = k from rfl)
  have hsize := UScalar.hSize self.val
  rw [UScalar.size, UScalarTy.Usize_numBits_eq] at hsize
  have hk : k < System.Platform.numBits := by
    dsimp [k]
    rw [Nat.log2_eq_log_two]
    apply Nat.log_lt_of_lt_pow (by omega)
    exact hsize
  have hbits : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have hnzbv : self.val.bv ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    change self.val.val = 0 at this
    omega
  have hlz : (core.num.Usize.leading_zeros self.val).val = System.Platform.numBits - k - 1 := by
    change (BitVec.leadingZeros self.val.bv) % 2 ^ 32 = _
    unfold BitVec.leadingZeros
    rw [if_neg hnzbv]
    change (System.Platform.numBits - Nat.log 2 self.val.val - 1) % 2 ^ 32 = _
    rw [← Nat.log2_eq_log_two]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hcast : (UScalar.cast .Usize (core.num.Usize.leading_zeros self.val)).val =
      System.Platform.numBits - k - 1 := by
    rw [UScalar.cast_val_eq, hlz, UScalarTy.Usize_numBits_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  unfold layout.RoundingAlignAndPhase.components
  step with pointer_width_spec as ⟨w, hw⟩
  have hone : (1#usize).val = 1 := by simp
  have hwpos : (1#usize).val ≤ w.val := by rw [hone, hw]; omega
  step with Usize.sub_spec hwpos as ⟨w1, hw1, _⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok, lift]
  have hsub : (UScalar.cast .Usize (core.num.Usize.leading_zeros self.val)).val ≤ w1.val := by
    rw [hcast, hw1, hw]
    omega
  step with Usize.sub_spec hsub as ⟨shift, hshift, _⟩
  have hshift' : shift.val = k := by rw [hcast, hw1, hw] at hshift; omega
  step with Usize.ShiftLeft_spec 1#usize shift (by rw [hshift']; exact hk) as ⟨a, ha, _⟩
  have ha' : a.val = 2 ^ k := by
    rw [hshift'] at ha
    simp only [Nat.shiftLeft_eq, Nat.one_mul] at ha
    have hp : 2 ^ k < Usize.size := by
      rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
      omega
    simpa only [Nat.mod_eq_of_lt hp] using ha
  have haz : a ≠ 0#usize := by
    intro hz
    have hz' := congrArg UScalar.val hz
    rw [ha'] at hz'
    change 2 ^ k = 0 at hz'
    have := Nat.two_pow_pos k
    omega
  simp only [core.num.nonzero.NonZero.new, cast_eq, haz, ↓reduceDIte,
    ↓reduceIte, bind_ok, WP.spec_ok]
  have hp : self.val.val - 2 ^ k < 2 ^ k := by
    rw [Nat.pow_succ] at hbound
    omega
  have hx : (self.val ^^^ a).val = self.val.val - 2 ^ k := by
    rw [UScalar.val_xor, ha']
    have heq : self.val.val = 2 ^ k + (self.val.val - 2 ^ k) := by omega
    rw [heq]
    simpa only [Nat.add_sub_cancel_left] using highest_bit_xor k _ hp
  refine ⟨?_, ?_, ?_, ha', ?_⟩
  · exact ⟨k, ha'⟩
  · rw [hx, ha']
    exact hp
  · rw [hx, ha']
    omega
  · exact hx

theorem encoding_align_spec : Zerocopy.Specs.encoding_align_spec := by
  intro self hn
  unfold layout.RoundingAlignAndPhase.align
  step with encoding_components_spec self hn as ⟨a, p, _, _, _, ha, _⟩
  simpa only [WP.spec_ok] using ha

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
