/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.Util
public import MathViews
public import Aeneas
public import Loops
public import LayoutMath
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false

theorem pointer_width_spec :
    layout.POINTER_WIDTH_BITS
      ⦃ w => w.val = System.Platform.numBits ⦄ := by
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

theorem encoding_new_spec :
  ∀ (align : NonZeroUsize) (phase : Usize), ∀ (ha : (align.val.val.isPowerOfTwo : Prop)), ∀ (hp : (phase.val < align.val.val : Prop)),
    @Zerocopy.layout.RoundingAlignAndPhase.new align phase ⦃ encoded => encoded._0.val.val = align.val.val + phase.val ⦄ := by
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

theorem encoding_components_spec :
  ∀ (self : layout.RoundingAlignAndPhase), ∀ (hn : (0 < self._0.val.val : Prop)),
    @Zerocopy.layout.RoundingAlignAndPhase.components self ⦃ (align, phase) =>
    align.val.val.isPowerOfTwo ∧ phase.val < align.val.val ∧
    align.val.val + phase.val = self._0.val.val ∧
    align.val.val = 2 ^ Nat.log2 self._0.val.val ∧
    phase.val = self._0.val.val - 2 ^ Nat.log2 self._0.val.val ⦄ := by
  intro self hn
  let k := Nat.log2 self._0.val.val
  have hbound := (Nat.log2_eq_iff (show self._0.val.val ≠ 0 by omega)).mp (show Nat.log2 self._0.val.val = k from rfl)
  have hsize := UScalar.hSize self._0.val
  rw [UScalar.size, UScalarTy.Usize_numBits_eq] at hsize
  have hk : k < System.Platform.numBits := by
    dsimp [k]
    rw [Nat.log2_eq_log_two]
    apply Nat.log_lt_of_lt_pow (by omega)
    exact hsize
  have hbits : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have hnzbv : self._0.val.bv ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    change self._0.val.val = 0 at this
    omega
  have hlz : (core.num.Usize.leading_zeros self._0.val).val = System.Platform.numBits - k - 1 := by
    change (BitVec.leadingZeros self._0.val.bv) % 2 ^ 32 = _
    unfold BitVec.leadingZeros
    rw [if_neg hnzbv]
    change (System.Platform.numBits - Nat.log 2 self._0.val.val - 1) % 2 ^ 32 = _
    rw [← Nat.log2_eq_log_two]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hcast : (UScalar.cast .Usize (core.num.Usize.leading_zeros self._0.val)).val =
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
  have hsub : (UScalar.cast .Usize (core.num.Usize.leading_zeros self._0.val)).val ≤ w1.val := by
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
  have hp : self._0.val.val - 2 ^ k < 2 ^ k := by
    rw [Nat.pow_succ] at hbound
    omega
  have hx : (self._0.val ^^^ a).val = self._0.val.val - 2 ^ k := by
    rw [UScalar.val_xor, ha']
    have heq : self._0.val.val = 2 ^ k + (self._0.val.val - 2 ^ k) := by omega
    rw [heq]
    simpa only [Nat.add_sub_cancel_left] using highest_bit_xor k _ hp
  refine ⟨?_, ?_, ?_, ha', ?_⟩
  · exact ⟨k, ha'⟩
  · rw [hx, ha']
    exact hp
  · rw [hx, ha']
    omega
  · exact hx

theorem encoding_align_spec :
  ∀ (self : layout.RoundingAlignAndPhase), ∀ (hn : (0 < self._0.val.val : Prop)),
    @Zerocopy.layout.RoundingAlignAndPhase.align self ⦃ align => align.val.val = 2 ^ Nat.log2 self._0.val.val ⦄ := by
  intro self hn
  unfold layout.RoundingAlignAndPhase.align
  step with encoding_components_spec self hn as ⟨a, p, _, _, _, ha, _⟩
  simpa only [WP.spec_ok] using ha

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

macro "representation_simps" : tactic =>
  `(tactic| try simp only [encoding_valid_iff, nonzero_valid_iff, scalar_valid_iff,
    encodingValid, and_true, true_and,
    and_self, true_implies])


theorem encoding_new_spec : Zerocopy.Specs.encoding_new_spec := by
  unfold Zerocopy.Specs.encoding_new_spec
  representation_simps
  intro align phase _ ha hp
  apply WP.spec_mono (Raw.encoding_new_spec align phase ha hp)
  intro encoded he
  refine ⟨?_, he⟩
  rw [he]
  have := Nat.pos_of_isPowerOfTwo ha
  omega
register_spec_step encoding_new_spec

theorem encoding_components_spec : Zerocopy.Specs.encoding_components_spec := by
  unfold Zerocopy.Specs.encoding_components_spec
  representation_simps
  intro self hn
  apply WP.spec_mono (Raw.encoding_components_spec self hn)
  rintro ⟨align, phase⟩ facts
  exact ⟨Nat.pos_of_isPowerOfTwo facts.1, facts⟩
register_spec_step encoding_components_spec

theorem encoding_align_spec : Zerocopy.Specs.encoding_align_spec := by
  unfold Zerocopy.Specs.encoding_align_spec
  representation_simps
  intro self hn
  apply WP.spec_mono (Raw.encoding_align_spec self hn)
  intro align he
  refine ⟨?_, he⟩
  rw [he]
  exact Nat.two_pow_pos _
register_spec_step encoding_align_spec

end Zerocopy.Proofs
