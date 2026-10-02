/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.Util
public import Aeneas
public import Loops
public import LayoutModel
public import LayoutMath
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

-- Raw contract requirements intentionally retain their descriptive proof names.
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

theorem size_offset_spec :
  ∀ {E : Type} (self : layout.TrailingSliceLayout E), ∀ (hn : (0 < self.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.TrailingSliceLayout.size_offset E self ⦃ offset =>
    offset.val = self.size_base.val - self.size_base.val % (byteFormula self).align + (byteFormula self).phase ⦄ := by
  intro E self hn
  unfold layout.TrailingSliceLayout.size_offset
  step with encoding_components_spec _ hn as ⟨a, p, ha, hp, hsum, halign, hphase⟩
  step with round_down_spec self.size_base a ha as ⟨base, _, hb, hmod, _, _⟩
  simp only [UScalar.val_or]
  rw [LayoutMath.aligned_or _ _ _ ha hmod hp, hb]
  simp only [byteFormula]
  rw [← halign]
  omega

theorem max_trailing_bytes_spec :
  ∀ {E : Type} (self : layout.TrailingSliceLayout E) (available_bytes : Usize), ∀ (hn : (0 < self.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.TrailingSliceLayout.max_trailing_bytes E self available_bytes ⦃ r => r.map UScalar.val = (byteFormula self).capacity available_bytes.val ⦄ := by
  intro E self available hn
  unfold layout.TrailingSliceLayout.max_trailing_bytes
  step with encoding_components_spec _ hn as ⟨a, p, ha, hp, hsum, halign, hphase⟩
  have apos := Nat.pos_of_isPowerOfTwo ha
  have hview : byteFormula self = ⟨self.size_base.val, p.val, a.val.val, 0, self.offset.val⟩ := by
    unfold byteFormula
    dsimp only
    rw [← hphase, ← halign]
  let rp : Usize := if p = 0#usize then 0#usize else a.val
  have hrp : rp.val = LayoutMath.roundUp p.val a.val.val := by
    rw [LayoutMath.roundUp_phase _ _ apos hp]
    by_cases hz : p = 0#usize
    · simp only [rp, hz, if_true]
      rfl
    · have hzero : p.val ≠ 0 := by
        intro h
        exact hz (UScalar.eq_of_val_eq (by simpa using h))
      simp only [rp, hz, hzero, if_false]
  have hrmod : rp.val % a.val.val = 0 := by rw [hrp]; exact (LayoutMath.roundUp_properties _ _ apos).2.2
  have hrge : p.val ≤ rp.val := by rw [hrp]; exact (LayoutMath.roundUp_properties _ _ apos).1
  have hrlt : rp.val - p.val < a.val.val := by
    have := (LayoutMath.roundUp_properties p.val a.val.val apos).2.1
    omega
  have hbranch : (if p = 0#usize then Result.ok 0#usize else
    core.num.nonzero.NonZero.get Usize.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroUsizeInner a) = Result.ok rp := by
    simp only [core.num.nonzero.NonZero.get]
    by_cases h : p = 0#usize <;> simp only [h, if_true, if_false, rp]
  rw [hbranch]
  simp only [bind_ok]
  step as ⟨checked, hadd⟩
  cases checked with
  | none =>
    simp only [] at hadd
    have hav : available.val ≤ Usize.max := by scalar_tac
    have hmiss : ¬(byteFormula self).bytes 0 ≤ available.val := by
      rw [hview]
      simp only [LayoutMath.Formula.bytes, Nat.add_zero, ← hrp]
      omega
    simp only [WP.spec_ok, Option.map_none, LayoutMath.Formula.capacity, hmiss, if_false]
  | some minimum =>
    simp only [] at hadd
    step as ⟨checked, hsub⟩
    cases checked with
    | none =>
      simp only [] at hsub
      simp only []
      have hmiss : ¬(byteFormula self).bytes 0 ≤ available.val := by
        rw [hview]
        simp only [LayoutMath.Formula.bytes, Nat.add_zero, ← hrp]
        omega
      simp only [WP.spec_ok, Option.map_none, LayoutMath.Formula.capacity, hmiss, if_false]
    | some extra =>
      simp only [] at hsub
      simp only []
      step with round_down_spec extra a ha as ⟨aligned, hle, hal, hmod, _, _⟩
      step with Usize.sub_spec hrge as ⟨padding, hpadding, _⟩
      have hfit : (byteFormula self).bytes 0 ≤ available.val := by
        rw [hview]
        simp only [LayoutMath.Formula.bytes, Nat.add_zero, ← hrp]
        omega
      simp only [lift, bind_ok, WP.spec_ok, Option.map_some,
        LayoutMath.Formula.capacity, hfit, if_true]
      have hpl : padding.val < a.val.val := by
        dsimp only [rp] at hrlt
        omega
      rw [UScalar.val_or, LayoutMath.aligned_or _ _ _ ha hmod hpl]
      rw [hview]
      dsimp only
      have hbudget : available.val - self.size_base.val = rp.val + extra.val := by omega
      rw [hbudget, LayoutMath.floor_shift _ _ _ hrmod]
      congr 1
      have hrem := Nat.mod_le extra.val a.val.val
      dsimp only [rp] at *
      omega

theorem assume_shallow_unpadded_spec :
  ∀ (self : layout.DstLayout),
    @Zerocopy.layout.DstLayout.assume_shallow_unpadded self ⦃ r => r.align = self.align ∧ r.size_info = self.size_info ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro self
  simp only [layout.DstLayout.assume_shallow_unpadded, WP.spec_ok, and_self]

theorem for_type_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hn : (0 < align.val : Prop)),
    @Zerocopy.layout.DstLayout.for_type T ⦃ r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = false ⦄ := by
  intro T size align hs ha hn
  have haz : align ≠ 0#usize := by
    intro h
    have hv := congrArg UScalar.val h
    change align.val = 0 at hv
    omega
  unfold layout.DstLayout.for_type
  rw [ha]
  simp only [bind_ok, core.num.nonzero.NonZero.new, cast_eq, haz,
    ↓reduceDIte, ↓reduceIte, hs, WP.spec_ok, and_self]

theorem for_unpadded_type_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hn : (0 < align.val : Prop)),
    @Zerocopy.layout.DstLayout.for_unpadded_type T ⦃ r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro T size align hs ha hn
  unfold layout.DstLayout.for_unpadded_type
  step with for_type_spec T size align hs ha hn as ⟨dl, halign, hsize, _⟩
  step with assume_shallow_unpadded_spec dl as ⟨r, hr, hsi, hp⟩
  exact ⟨hr ▸ halign, hsi ▸ hsize, hp⟩

theorem for_slice_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hp : (align.val.isPowerOfTwo : Prop)),
    @Zerocopy.layout.DstLayout.for_slice T ⦃ r => r.align.val = align ∧ r.statically_shallow_unpadded = true ∧
    ∃ tail, r.size_info = layout.SizeInfo.SliceDst tail ∧
      tail.offset = 0#usize ∧ tail.elem_size = size ∧ tail.size_base = 0#usize ∧
      tail.size_rounding_align_and_phase._0.val.val = align.val ⦄ := by
  intro T size align hs ha hp
  have hpos := Nat.pos_of_isPowerOfTwo hp
  have haz : align ≠ 0#usize := by
    intro h
    have hv := congrArg UScalar.val h
    change align.val = 0 at hv
    omega
  unfold layout.DstLayout.for_slice
  rw [ha]
  simp only [bind_ok, core.num.nonzero.NonZero.new, cast_eq, haz,
    ↓reduceDIte, ↓reduceIte, hs]
  step with encoding_new_spec ⟨align⟩ 0#usize hp (by simpa using hpos) as ⟨encoded, he⟩
  refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  simpa using he

theorem max_elems_for_bytes_spec :
  ∀ (bytes : Usize) (elem_size : NonZeroUsize), ∀ (hn : (0 < elem_size.val.val : Prop)),
    @Zerocopy.layout.max_elems_for_bytes bytes elem_size ⦃ (elems, used) =>
    elems.val = bytes.val / elem_size.val.val ∧ used.val = elems.val * elem_size.val.val ∧
    used ≤ bytes ∧ bytes.val < (elems.val + 1) * elem_size.val.val ∧
    (∀ n : Nat, n * elem_size.val.val ≤ bytes.val ↔ n ≤ elems.val) ⦄ := by
  intro bytes elem hn
  unfold layout.max_elems_for_bytes
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step with Usize.div_spec bytes (y := elem.val) (by omega) as ⟨elems, he⟩
  have hfit : elems.val * elem.val.val ≤ bytes.val := by
    rw [he, Nat.mul_comm]
    exact Nat.mul_div_le _ _
  have hav : bytes.val ≤ Usize.max := by scalar_tac
  step as ⟨product, hmul⟩
  cases product with
  | none =>
    simp only [] at hmul
    omega
  | some used =>
    simp only [] at hmul
    simp only [WP.spec_ok]
    refine ⟨he, hmul.2.1, (UScalar.le_equiv _ _).mpr (by omega), ?_, ?_⟩
    · rw [he, Nat.mul_comm]
      exact Nat.lt_mul_div_succ _ hn
    · intro n
      rw [he]
      exact (Nat.le_div_iff_mul_le hn).symm

theorem requires_static_padding_spec :
  ∀ (self : layout.DstLayout),
    @Zerocopy.layout.DstLayout.requires_static_padding self ⦃ r => r = !self.statically_shallow_unpadded ⦄ := by
  intro self
  simp only [layout.DstLayout.requires_static_padding, WP.spec_ok]
  cases self.statically_shallow_unpadded <;> rfl

theorem wrapping_sub_cancel (x y : Usize) :
    ((core.num.Usize.wrapping_sub x y).val + y.val) % UScalar.size .Usize = x.val := by
  rw [core.num.Usize.wrapping_sub_val_eq, Nat.mod_add_mod]
  have hy := UScalar.hSize y
  rw [show x.val + (UScalar.size .Usize - y.val) + y.val =
    x.val + UScalar.size .Usize by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (UScalar.hSize x)

theorem padding_for_elems_spec :
  ∀ (self : layout.TrailingSliceLayout Usize) (elems : Usize), ∀ (hn : (0 < self.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.TrailingSliceLayoutUsize.padding_for_elems self elems ⦃ p => (p.val + self.offset.val + elems.val * self.elem_size.val) % UScalar.size .Usize =
    (trailingFormula self).size elems.val % UScalar.size .Usize ⦄ := by
  intro self elems hn
  unfold layout.TrailingSliceLayoutUsize.padding_for_elems
  step with encoding_components_spec _ hn as ⟨a, r, ha, hr, hsum, halign, hphase⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  have apos := Nat.pos_of_isPowerOfTwo ha
  step with Usize.sub_spec (show (1#usize).val ≤ a.val.val by simpa using (show 1 ≤ a.val.val by omega)) as ⟨mask, hm, _⟩
  simp only [lift, bind_ok]
  have low (x : Usize) : (x &&& mask).val = x.val % a.val.val := by
    obtain ⟨k, hk⟩ := ha
    rw [UScalar.val_and, hm, hk, Nat.and_two_pow_sub_one_eq_mod]
  let t := core.num.Usize.wrapping_mul elems (self.elem_size &&& mask) &&& mask
  have ht : t.val = (elems.val * self.elem_size.val) % a.val.val := by
    rw [low, core.num.Usize.wrapping_mul_val_eq, low,
      Nat.mod_mod_of_dvd _ (Arithmetic.alignment_dvd_size a.val ha)]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  let input := core.num.Usize.wrapping_add r t
  have hi : input.val % a.val.val =
      (r.val + elems.val * self.elem_size.val) % a.val.val := by
    rw [core.num.Usize.wrapping_add_val_eq,
      Nat.mod_mod_of_dvd _ (Arithmetic.alignment_dvd_size a.val ha), ht, Nat.add_mod_mod]
  step with Zerocopy.Proofs.padding_lt_alignment input a (Nat.pos_of_isPowerOfTwo ha) ha as ⟨rp, _, hp, _, _, _⟩
  have hp' : rp.val = (a.val.val - (r.val + elems.val * self.elem_size.val) % a.val.val) % a.val.val := by
    rw [hi] at hp
    exact hp
  simp only [core.num.Usize.wrapping_add_val_eq, Nat.add_assoc, Nat.mod_add_mod]
  rw [show
    (core.num.Usize.wrapping_sub (core.num.Usize.wrapping_add self.size_base r) self.offset).val +
      (rp.val + (self.offset.val + elems.val * self.elem_size.val)) =
    ((core.num.Usize.wrapping_sub (core.num.Usize.wrapping_add self.size_base r) self.offset).val +
      self.offset.val) + (elems.val * self.elem_size.val + rp.val) by omega,
    ← Nat.mod_add_mod, wrapping_sub_cancel, core.num.Usize.wrapping_add_val_eq, Nat.mod_add_mod]
  simp only [trailingFormula, byteFormula, LayoutMath.Formula.size, LayoutMath.Formula.bytes,
    LayoutMath.roundUp]
  rw [← hphase, ← halign, hp']
  congr 1
  omega

theorem trailing_align_pos (self : layout.TrailingSliceLayout Usize) :
    0 < (trailingFormula self).align := Nat.two_pow_pos _

theorem trailing_product_le_size (self : layout.TrailingSliceLayout Usize) (n : Nat) :
    n * self.elem_size.val ≤ (trailingFormula self).size n := by
  have h := (LayoutMath.roundUp_properties
    ((trailingFormula self).phase + n * self.elem_size.val)
    (trailingFormula self).align (trailing_align_pos self)).1
  unfold trailingFormula byteFormula LayoutMath.Formula.size LayoutMath.Formula.bytes at *
  dsimp only at *
  omega

theorem word_mod_of_le (n : Nat) (h : n ≤ Usize.max) : n % UScalar.size .Usize = n := by
  apply Nat.mod_eq_of_lt
  have hp := Nat.two_pow_pos System.Platform.numBits
  simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, UScalar.size] at h ⊢
  omega

theorem size_for_elems_spec :
  ∀ (self : layout.TrailingSliceLayout Usize) (elems : Usize), ∀ (hn : (0 < self.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.TrailingSliceLayoutUsize.size_for_elems self elems ⦃ r => r.map UScalar.val = (trailingFormula self).checkedSize Usize.max elems.val ⦄ := by
  intro self elems hn
  unfold layout.TrailingSliceLayoutUsize.size_for_elems
  step with max_trailing_bytes_spec self core.num.Usize.MAX hn as ⟨cap, hc⟩
  have hc' := LayoutMath.capacity_spec (byteFormula self) core.num.Usize.MAX.val
    (show 0 < (byteFormula self).align from Nat.two_pow_pos _)
  simp only [core.num.Usize.MAX, UScalar.ofNatCore_val_eq] at hc'
  have hprod := trailing_product_le_size self elems.val
  cases cap with
  | none =>
    simp only [Option.map_none] at hc
    rw [← hc] at hc'
    have hmiss := hc' (elems.val * self.elem_size.val)
    change Usize.max < (trailingFormula self).size elems.val at hmiss
    simp only [WP.spec_ok, Option.map_none, LayoutMath.Formula.checkedSize,
      show ¬(trailingFormula self).size elems.val ≤ Usize.max by omega, if_false]
  | some cap =>
    simp only [Option.map_some] at hc
    rw [← hc] at hc'
    have hiff := hc' (elems.val * self.elem_size.val)
    change (trailingFormula self).size elems.val ≤ Usize.max ↔
      elems.val * self.elem_size.val ≤ cap.val at hiff
    step as ⟨product, hm⟩
    cases product with
    | none =>
      simp only [] at hm
      have hmiss : ¬(trailingFormula self).size elems.val ≤ Usize.max := by
        rw [Nat.mul_comm] at hm
        omega
      simp only [WP.spec_ok, Option.map_none, LayoutMath.Formula.checkedSize, hmiss, if_false]
    | some bytes =>
      simp only [] at hm
      simp only [UScalar.lt_equiv]
      split
      · rename_i hbig
        have hmiss : ¬(trailingFormula self).size elems.val ≤ Usize.max := by
          rw [Nat.mul_comm] at hm
          omega
        simp only [WP.spec_ok, Option.map_none, LayoutMath.Formula.checkedSize, hmiss, if_false]
      · rename_i hsmall
        have hfit : (trailingFormula self).size elems.val ≤ Usize.max := by
          apply hiff.mpr
          rw [hm.2.1, Nat.mul_comm] at hsmall
          omega
        simp only [lift, bind_ok]
        step with padding_for_elems_spec self elems hn as ⟨p, hp⟩
        have hsz : Usize.size = UScalar.size .Usize := by
          simp only [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq, UScalar.size]
        rw [hsz] at hp
        simp only [Option.map_some,
          LayoutMath.Formula.checkedSize, hfit, if_true,
          core.num.Usize.wrapping_add_val_eq, Nat.mod_add_mod]
        rw [hm.2.1, Nat.mul_comm]
        rw [show self.offset.val + elems.val * self.elem_size.val + p.val =
          p.val + self.offset.val + elems.val * self.elem_size.val by omega,
          hp, word_mod_of_le _ hfit]

theorem try_nonzero_spec :
  ∀ (self : layout.SizeInfo Usize),
    @Zerocopy.layout.SizeInfoUsize.try_to_nonzero_elem_size self ⦃ r => match self with
    | .Sized size => r = some (.Sized size)
    | .SliceDst tail =>
      if tail.elem_size = 0#usize then r = none else
        ∃ t, r = some (.SliceDst t) ∧ t.offset = tail.offset ∧
          t.size_base = tail.size_base ∧
          t.size_rounding_align_and_phase = tail.size_rounding_align_and_phase ∧
          t.elem_size.val = tail.elem_size ⦄ := by
  intro self
  cases self with
  | Sized size => simp [layout.SizeInfoUsize.try_to_nonzero_elem_size]
  | SliceDst tail =>
    unfold layout.SizeInfoUsize.try_to_nonzero_elem_size core.num.nonzero.NonZero.new
    by_cases hz : tail.elem_size = 0#usize
    · simp only [cast_eq, hz, ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok]
    · simp only [cast_eq, hz, ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem min_align_eq : layout.DstLayout.MIN_ALIGN = .ok ⟨1#usize⟩ := by
  simp [layout.DstLayout.MIN_ALIGN, core.num.nonzero.NonZero.new]

theorem new_zst_spec :
  ∀ (repr_align : Option NonZeroUsize), ∀ (hp : (∀ a ∈ repr_align, a.val.val.isPowerOfTwo : Prop)),
    @Zerocopy.layout.DstLayout.new_zst repr_align ⦃ r => r.align = repr_align.getD ⟨1#usize⟩ ∧
    r.size_info = .Sized 0#usize ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro repr_align hp
  unfold layout.DstLayout.new_zst
  have ha : (repr_align.getD ⟨1#usize⟩).val.val.isPowerOfTwo := by
    cases repr_align with
    | none => exact ⟨0, by simp⟩
    | some a => exact hp a rfl
  cases repr_align
  all_goals
    simp only [min_align_eq, Option.getD_none, Option.getD_some,
      core.num.nonzero.NonZero.get, bind_ok] at ha ⊢
    step as ⟨b, hb⟩
    have hbt : b = true := by
      have hb' : (b = true) = True := by simpa only [ha, Nat.isPowerOfTwo_one] using hb
      exact Eq.mpr hb' trivial
    simp [massert, hbt, bind_ok, WP.spec_ok]

theorem decoded_encoding (a p : Nat) (ha : a.isPowerOfTwo) (hp : p < a) :
    2 ^ Nat.log2 (a + p) = a ∧ a + p - 2 ^ Nat.log2 (a + p) = p := by
  obtain ⟨k, hk⟩ := ha
  have hpos := Nat.two_pow_pos k
  have hlog : Nat.log2 (a + p) = k := by
    apply (Nat.log2_eq_iff (by omega)).mpr
    rw [Nat.pow_succ]
    omega
  rw [hlog, ← hk]
  omega

theorem trailing_view (self : layout.TrailingSliceLayout Usize) (a p : Nat)
    (ha : a.isPowerOfTwo) (hp : p < a)
    (hn : self.size_rounding_align_and_phase._0.val.val = a + p) :
    trailingFormula self = ⟨self.size_base.val, p, a, self.elem_size.val, self.offset.val⟩ := by
  obtain ⟨hd, _⟩ := decoded_encoding a p ha hp
  simp only [trailingFormula, byteFormula, hn, hd, Nat.add_sub_cancel_left]

theorem pad_to_align_spec :
  ∀ (self : layout.DstLayout), ∀ (ha : (self.align.val.val.isPowerOfTwo : Prop)), ∀ (hfit : (match self.size_info with
    | .Sized size => LayoutMath.roundUp size.val self.align.val.val ≤ Usize.max
    | .SliceDst tail =>
      0 < tail.size_rounding_align_and_phase._0.val.val ∧
      (if (trailingFormula tail).align < self.align.val.val then
        LayoutMath.roundUp tail.size_base.val (trailingFormula tail).align +
          (trailingFormula tail).phase ≤ Usize.max
       else LayoutMath.roundUp tail.size_base.val self.align.val.val ≤ Usize.max) : Prop)),
    @Zerocopy.layout.DstLayout.pad_to_align self ⦃ r => canonicalLayout r ∧ r.align = self.align ∧ match self.size_info with
    | .Sized size => ∃ padded,
      r.size_info = .Sized padded ∧ padded.val = LayoutMath.roundUp size.val self.align.val.val ∧
      r.statically_shallow_unpadded = (self.statically_shallow_unpadded && decide (size.val % self.align.val.val = 0))
    | .SliceDst tail => ∃ t,
      r.size_info = .SliceDst t ∧ trailingFormula t = (trailingFormula tail).pad self.align.val.val ∧
      r.statically_shallow_unpadded = self.statically_shallow_unpadded ⦄ := by
  intro self ha hfit
  unfold layout.DstLayout.pad_to_align
  cases hs : self.size_info with
  | Sized size =>
    simp only [hs] at hfit
    step with Zerocopy.Proofs.padding_lt_alignment size self.align (Nat.pos_of_isPowerOfTwo ha) ha as ⟨p, _, hp, _, _, hz⟩
    have hsum : size.val + p.val = LayoutMath.roundUp size.val self.align.val.val := by
      rw [hp]
      rfl
    step as ⟨checked, hc⟩
    cases checked with
    | none => simp only [] at hc; omega
    | some padded =>
      simp only [] at hc
      have hzero : (p = 0#usize) = (size.val % self.align.val.val = 0) := by
        apply propext
        simpa only [UScalar.eq_equiv, show (0#usize).val = 0 by simp] using hz
      cases hb : self.statically_shallow_unpadded <;>
        simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
          if_false, if_true, WP.spec_ok, canonicalLayout]
      all_goals exact ⟨True.intro, by trivial, _, by trivial, by omega, by simp only [hzero]⟩
  | SliceDst tail =>
    simp only [hs] at hfit
    step with encoding_components_spec _ hfit.1 as ⟨a, p, hap, hpa, henc, halign, hphase⟩
    have hv := trailing_view tail a.val.val p.val hap hpa henc.symm
    rw [hv] at hfit
    dsimp only at hfit
    simp only [core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
    split
    · rename_i hab
      have hbound := hfit.2
      simp only [hab, if_true] at hbound
      step with Zerocopy.Proofs.padding_lt_alignment tail.size_base a (Nat.pos_of_isPowerOfTwo hap) hap as ⟨bp, _, hbp, _, _, _⟩
      have hb : tail.size_base.val + bp.val = LayoutMath.roundUp tail.size_base.val a.val.val := by rw [hbp]; rfl
      step as ⟨checked, hc⟩
      cases checked with
      | none => simp only [] at hc; omega
      | some base =>
        simp only [] at hc
        step as ⟨checked, hbytes⟩
        cases checked with
        | none => simp only [] at hbytes; omega
        | some bytes =>
          simp only [] at hbytes
          simp only []
          have apos := Nat.pos_of_isPowerOfTwo ha
          step with Usize.sub_spec (show (1#usize).val ≤ self.align.val.val by simpa using (show 1 ≤ self.align.val.val by omega)) as ⟨mask, hm, _⟩
          have hlow : (bytes &&& mask).val = bytes.val % self.align.val.val := by
            obtain ⟨k, hk⟩ := ha
            rw [UScalar.val_and, hm, hk, Nat.and_two_pow_sub_one_eq_mod]
          simp only [lift, bind_ok]
          step with round_down_spec bytes self.align ha as ⟨normalized, _, hnorm, _, _, _⟩
          step with encoding_new_spec self.align (bytes &&& mask) ha (by rw [hlow]; exact Nat.mod_lt _ apos) as ⟨encoded, he⟩
          have hencoded : encodingValid encoded := by
            unfold encodingValid
            rw [he]
            omega
          have hnew := trailing_view
            ({ tail with size_base := normalized, size_rounding_align_and_phase := encoded })
            self.align.val.val (bytes.val % self.align.val.val) ha (Nat.mod_lt _ apos)
            (by rw [he, hlow])
          cases hflag : self.statically_shallow_unpadded <;>
            simp only [Bool.false_eq_true, decide_true,
              if_true, if_false, WP.spec_ok, canonicalLayout]
          all_goals
            refine ⟨hencoded, by trivial, _, by trivial, ?_, by trivial⟩
            rw [hnew, hv]
            simp only [LayoutMath.Formula.pad, hab, if_true]
            rw [hnorm, hbytes.2.1, hc.2.1, hb]
    · rename_i hab
      have hbound := hfit.2
      simp only [hab, if_false] at hbound
      step with Zerocopy.Proofs.padding_lt_alignment tail.size_base self.align (Nat.pos_of_isPowerOfTwo ha) ha as ⟨bp, _, hbp, _, _, _⟩
      have hb : tail.size_base.val + bp.val = LayoutMath.roundUp tail.size_base.val self.align.val.val := by rw [hbp]; rfl
      step as ⟨checked, hc⟩
      cases checked with
      | none => simp only [] at hc; omega
      | some base =>
        simp only [] at hc
        have hnew := trailing_view ({ tail with size_base := base }) a.val.val p.val hap hpa henc.symm
        cases hflag : self.statically_shallow_unpadded <;>
          simp only [Bool.false_eq_true, decide_true,
            if_true, if_false, WP.spec_ok, canonicalLayout]
        all_goals
          refine ⟨hfit.1, by trivial, _, by trivial, ?_, by trivial⟩
          rw [hnew, hv]
          simp only [LayoutMath.Formula.pad, hab, if_false]
          rw [hc.2.1, hb]

theorem current_max_align_spec :
    layout.DstLayout.CURRENT_MAX_ALIGN
      ⦃ a => a.val.val = 2 ^ 29 ⦄ := by
  unfold layout.DstLayout.CURRENT_MAX_ALIGN
  step as ⟨i, hi, _⟩
  · have := System.Platform.numBits_eq
    scalar_tac
  · have hv : i.val = 2 ^ 29 := by
      rw [Nat.shiftLeft_eq, Nat.one_mul] at hi
      have hfit : 2 ^ 29 < Usize.size := by
        rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
        rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
      simpa only [Nat.mod_eq_of_lt hfit] using hi
    have hnz : i ≠ 0#usize := by
      intro h
      have := congrArg UScalar.val h
      rw [hv] at this
      change 2 ^ 29 = 0 at this
      omega
    simp only [core.num.nonzero.NonZero.new, cast_eq, hnz,
      ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok]
    exact hv

theorem theoretical_max_align_spec :
    layout.DstLayout.THEORETICAL_MAX_ALIGN
      ⦃ a => a.val.val = 2 ^ (System.Platform.numBits - 1) ⦄ := by
  unfold layout.DstLayout.THEORETICAL_MAX_ALIGN
  step with pointer_width_spec as ⟨w, hw⟩
  have hb : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  step with Usize.sub_spec (show (1#usize).val ≤ w.val by simpa only [show (1#usize).val = 1 by simp, hw] using (show 1 ≤ System.Platform.numBits by omega)) as ⟨shift, hs, _⟩
  have hs' : shift.val = System.Platform.numBits - 1 := by
    simpa only [hw, show (1#usize).val = 1 by simp] using hs
  step with Usize.ShiftLeft_spec 1#usize shift (by rw [hs']; omega) as ⟨a, hav, _⟩
  have hv : a.val = 2 ^ (System.Platform.numBits - 1) := by
    rw [hs', Nat.shiftLeft_eq, Nat.one_mul] at hav
    have hfit : 2 ^ (System.Platform.numBits - 1) < Usize.size := by
      rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
    simpa only [Nat.mod_eq_of_lt hfit] using hav
  have hnz : a ≠ 0#usize := by
    intro h
    have := congrArg UScalar.val h
    rw [hv] at this
    change 2 ^ (System.Platform.numBits - 1) = 0 at this
    have := Nat.two_pow_pos (System.Platform.numBits - 1)
    omega
  simp only [core.num.nonzero.NonZero.new, cast_eq, hnz,
    ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok]
  exact hv

theorem fill_low_bits (n k : Nat) : n ||| (2 ^ k - 1) = n - n % 2 ^ k + (2 ^ k - 1) := by
  have h : (n - n % 2 ^ k) % 2 ^ k = 0 := by
    rw [← Nat.div_mul_self_eq_mod_sub_self, Nat.mul_mod_left]
  rw [← LayoutMath.aligned_or _ _ _ ⟨k, rfl⟩ h (by have := Nat.two_pow_pos k; omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < k
  · simp only [hi, decide_true, Bool.or_true]
  · simp only [hi, decide_false, Bool.or_false]
    rw [← Nat.div_mul_self_eq_mod_sub_self, ← Nat.shiftLeft_eq]
    rw [Nat.testBit_shiftLeft]
    rw [Nat.testBit_div_two_pow]
    simp only [show k ≤ i by omega, decide_true, Bool.true_and,
      show i - k + k = i by omega]

theorem advance_spec :
  ∀ (self : layout.TrailingSliceLayout Usize) (bytes elem_size : Usize), ∀ (hn : (0 < self.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.TrailingSliceLayoutUsize.advance self bytes elem_size ⦃ result => (∀ t ∈ result, encodingValid t.size_rounding_align_and_phase) ∧ match result with
    | none => Usize.max < ((trailingFormula self).advance bytes.val elem_size.val).base
    | some t => trailingFormula t = (trailingFormula self).advance bytes.val elem_size.val ∧
      ((trailingFormula self).advance bytes.val elem_size.val).base ≤ Usize.max ⦄ := by
  intro self bytes elem hn
  unfold layout.TrailingSliceLayoutUsize.advance
  step with encoding_components_spec _ hn as ⟨a, p, ha, hp, hsum, halign, hphase⟩
  have hv := trailing_view self a.val.val p.val ha hp hsum.symm
  have apos := Nat.pos_of_isPowerOfTwo ha
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step with Usize.sub_spec (show (1#usize).val ≤ a.val.val by simpa using (show 1 ≤ a.val.val by omega)) as ⟨mask, hm, _⟩
  step with Usize.sub_spec (show self.size_base.val ≤ core.num.Usize.MAX.val by scalar_tac) as ⟨available, hav, _⟩
  let pc := available ||| mask
  have hpc : pc.val = (Usize.max - self.size_base.val) -
      (Usize.max - self.size_base.val) % a.val.val + (a.val.val - 1) := by
    obtain ⟨k, hk⟩ := ha
    rw [UScalar.val_or, hm, hav]
    rw [hk, fill_low_bits]
  have hpbound : p.val ≤ pc.val := by
    have hor : mask.val ≤ pc.val := by
      rw [UScalar.val_or]
      exact Nat.right_le_or
    omega
  simp only [lift, bind_ok]
  step with Usize.sub_spec hpbound as ⟨advance, hadv, _⟩
  dsimp only [pc] at *
  simp only [UScalar.lt_equiv]
  split
  · rename_i hlarge
    simp only [WP.spec_ok, hv, LayoutMath.Formula.advance]
    constructor
    · simp
    · have hcap := LayoutMath.floor_capacity (p.val + bytes.val)
        (Usize.max - self.size_base.val) a.val.val apos
      have hbase : self.size_base.val ≤ Usize.max := by scalar_tac
      have hrem := Nat.mod_le (p.val + bytes.val) a.val.val
      omega
  · rename_i hsmall
    have hshift : p.val + bytes.val ≤ (available ||| mask).val := by omega
    have hword : (available ||| mask).val ≤ Usize.max := by
      have h := UScalar.hSize (available ||| mask)
      simp only [UScalar.size, Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq] at h ⊢
      have := Nat.two_pow_pos System.Platform.numBits
      omega
    step with Usize.add_spec (x := p) (y := bytes) (by omega) as ⟨shifted, hshifted⟩
    have hlow : (shifted &&& mask).val = shifted.val % a.val.val := by
      obtain ⟨k, hk⟩ := ha
      rw [UScalar.val_and, hm, hk, Nat.and_two_pow_sub_one_eq_mod]
    step with round_down_spec shifted a ha as ⟨whole, _, hwhole, _, _, _⟩
    have hbase : self.size_base.val + whole.val ≤ Usize.max := by
      have hcap := (LayoutMath.floor_capacity (p.val + bytes.val)
        (Usize.max - self.size_base.val) a.val.val apos).mpr (by omega)
      rw [hwhole, hshifted]
      have hb : self.size_base.val ≤ Usize.max := by scalar_tac
      omega
    step with Usize.add_spec (x := self.size_base) (y := whole) hbase as ⟨base, hb⟩
    step with encoding_new_spec a (shifted &&& mask) ha (by rw [hlow]; exact Nat.mod_lt _ apos) as ⟨encoded, he⟩
    have hnew := trailing_view
      ({ self with elem_size := elem, size_base := base, size_rounding_align_and_phase := encoded })
      a.val.val (shifted.val % a.val.val) ha (Nat.mod_lt _ apos) (by rw [he, hlow])
    have hencoded : encodingValid encoded := by
      unfold encodingValid
      rw [he]
      omega
    simp only [hnew, hv, LayoutMath.Formula.advance]
    refine ⟨?_, ?_, ?_⟩
    · simpa using hencoded
    · rw [hshifted, hb, hwhole, hshifted]
      congr 1
      have := Nat.mod_le (p.val + bytes.val) a.val.val
      omega
    · rw [hwhole, hshifted] at hbase
      have := Nat.mod_le (p.val + bytes.val) a.val.val
      omega

theorem checked_some_size (f : LayoutMath.Formula) (n : Nat) (size : Usize)
    (h : some size.val = f.checkedSize Usize.max n) :
    size.val = f.size n ∧ f.size n ≤ Usize.max := by
  unfold LayoutMath.Formula.checkedSize at h
  split at h <;> simp_all

theorem checked_none_size (f : LayoutMath.Formula) (n : Nat)
    (h : none = f.checkedSize Usize.max n) : Usize.max < f.size n := by
  unfold LayoutMath.Formula.checkedSize at h
  split at h <;> simp_all

theorem requires_dynamic_padding_spec :
  ∀ (self : layout.DstLayout), ∀ (hn : (match self.size_info with
    | .Sized _ => True
    | .SliceDst tail => 0 < tail.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.DstLayout.requires_dynamic_padding self ⦃ r => (r = false ↔ match self.size_info with
    | .Sized _ => True
    | .SliceDst tail => (trailingFormula tail).size 0 = tail.offset.val ∧
      tail.elem_size.val % (trailingFormula tail).align = 0) ⦄ := by
  intro self hn
  unfold layout.DstLayout.requires_dynamic_padding
  cases hs : self.size_info with
  | Sized size => simp [WP.spec_ok]
  | SliceDst tail =>
    simp only [hs] at hn
    step with size_for_elems_spec tail 0#usize hn as ⟨initial, hi⟩
    cases initial with
    | none =>
      dsimp only
      have hmiss := checked_none_size _ _ hi
      have hoff : tail.offset.val ≤ Usize.max := by scalar_tac
      apply WP.spec.ret
      simp only [Bool.true_eq_false, false_iff]
      intro h
      omega
    | some initial =>
      dsimp only
      have hv := checked_some_size _ _ initial hi
      step with encoding_align_spec _ hn as ⟨a, ha⟩
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      have hap : 0 < a.val.val := by rw [ha]; exact Nat.two_pow_pos _
      step with Usize.rem_spec tail.elem_size (y := a.val) (by omega) as ⟨remainder, hr⟩
      simp only [bne_iff_ne]
      split
      · rename_i hne
        apply WP.spec.ret
        simp only [Bool.true_eq_false, false_iff]
        intro h
        apply hne
        apply UScalar.eq_of_val_eq
        omega
      · rename_i heq
        have heq' : initial.val = tail.offset.val := by
          have h : initial = tail.offset := not_ne_iff.mp heq
          exact congrArg UScalar.val h
        apply WP.spec.ret
        simp only [decide_eq_false_iff_not, not_not, UScalar.eq_equiv,
          show (0#usize).val = 0 by simp, hr, ← heq', ← hv.1, true_and]
        rw [ha]
        rfl

theorem packing_limit_spec (packed : Option NonZeroUsize)
    (hp : ∀ a ∈ packed, a.val.val.isPowerOfTwo) :
    (match packed with | none => layout.DstLayout.THEORETICAL_MAX_ALIGN | some a => Result.ok a)
      ⦃ a => a.val.val = packingValue packed ∧ a.val.val.isPowerOfTwo ⦄ := by
  cases packed with
  | none =>
    step with theoretical_max_align_spec as ⟨a, ha⟩
    exact ⟨ha, ⟨_, ha⟩⟩
  | some a =>
    simp only [WP.spec_ok, packingValue, Option.map_some, Option.getD_some]
    exact ⟨by trivial, hp a rfl⟩

-- Aeneas shares a generated matcher with the alignment encoder. The model
-- comparison checks that matcher; this proof deliberately names it.
set_option linter.auxLemma false in
theorem extend_spec :
  ∀ (self field : layout.DstLayout) (repr_packed : Option NonZeroUsize) (size : Usize), ∀ (hs : (self.size_info = .Sized size : Prop)), ∀ (hself : (self.align.val.val.isPowerOfTwo ∧ self.align.val.val ≤ 2 ^ 29 : Prop)), ∀ (hfield : (field.align.val.val.isPowerOfTwo ∧ field.align.val.val ≤ 2 ^ 29 : Prop)), ∀ (hpacked : (∀ a ∈ repr_packed, a.val.val.isPowerOfTwo ∧ a.val.val ≤ 2 ^ 29 : Prop)), ∀ (hfit : (match field.size_info with
    | .Sized field_size => placement size field repr_packed + field_size.val ≤ Usize.max
    | .SliceDst t => placement size field repr_packed + t.offset.val ≤ Usize.max ∧
      placement size field repr_packed + t.size_base.val ≤ Usize.max : Prop)),
    @Zerocopy.layout.DstLayout.extend self field repr_packed ⦃ r => r.align.val.val = max self.align.val.val (fieldAlignment field repr_packed) ∧
    r.statically_shallow_unpadded = (self.statically_shallow_unpadded &&
      field.statically_shallow_unpadded && decide (size.val % fieldAlignment field repr_packed = 0)) ∧
    match field.size_info with
    | .Sized field_size => ∃ s, r.size_info = .Sized s ∧
      s.val = placement size field repr_packed + field_size.val
    | .SliceDst t => ∃ u, r.size_info = .SliceDst u ∧
      u.offset.val = placement size field repr_packed + t.offset.val ∧
      u.size_base.val = placement size field repr_packed + t.size_base.val ∧
      u.elem_size = t.elem_size ∧
      u.size_rounding_align_and_phase = t.size_rounding_align_and_phase ⦄ := by
  intro self field packed size hs hself hfield hpacked hfit
  unfold layout.DstLayout.extend
  step with packing_limit_spec packed (fun a h => (hpacked a h).1) as ⟨limit, hl, hlpow⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨b, hb⟩
  have hbt : b = true := by
    have hb' : (b = true) = True := by simpa only [hlpow] using hb
    exact Eq.mpr hb' trivial
  simp only [massert, hbt, if_true, bind_ok]
  step with current_max_align_spec as ⟨maximum, hmaximum⟩
  have hsa : self.align.val ≤ maximum.val := (UScalar.le_equiv _ _).mpr (by omega)
  have hfa : field.align.val ≤ maximum.val := (UScalar.le_equiv _ _).mpr (by omega)
  simp only [hsa, hfa, if_true, bind_ok]
  have hpackcheck : layout.RoundingAlignAndPhase.new.match_1
    (fun _ => Result (Option NonZeroUsize)) packed (fun _ => Result.ok none)
    (fun a => do
      if a.val ≤ maximum.val then Result.ok () else Result.fail .assertionFailure
      Result.ok packed) = Result.ok packed := by
    cases packed with
    | none => rfl
    | some a =>
      have ha : a.val ≤ maximum.val := (UScalar.le_equiv _ _).mpr (by
        have := (hpacked a rfl).2
        omega)
      simp only [ha, if_true, bind_ok]
  rw [hpackcheck]
  simp only [bind_ok]
  step with min_spec field.align limit as ⟨fa, hmin, hchoice, _, _⟩
  have hfp : fa.val.val.isPowerOfTwo := by
    rcases hchoice with h | h
    · simpa only [h] using hfield.1
    · simpa only [h] using hlpow
  have hfv : fa.val.val = fieldAlignment field packed := by
    rw [hmin, Arithmetic.coe_min, hl]
    rfl
  step with max_spec self.align fa as ⟨align, hmax, _, _, _⟩
  have halign : align.val.val = max self.align.val.val (fieldAlignment field packed) := by
    rw [hmax, Arithmetic.coe_max, hfv]
  rw [hs]
  step with Zerocopy.Proofs.padding_lt_alignment size fa (Nat.pos_of_isPowerOfTwo hfp) hfp as ⟨pad, _, hpad, _, _, hzero⟩
  have ho : size.val + pad.val = placement size field packed := by
    rw [hpad, hfv]
    rfl
  have hzero' : (pad = 0#usize) = (size.val % fieldAlignment field packed = 0) := by
    apply propext
    simpa only [UScalar.eq_equiv, show (0#usize).val = 0 by simp, hfv] using hzero
  step as ⟨checked, hsum⟩
  cases checked with
  | none =>
    simp only [] at hsum
    cases hf : field.size_info <;> simp only [hf] at hfit <;> omega
  | some offset =>
    simp only [] at hsum
    have hoff : offset.val = placement size field packed := by omega
    cases hf : field.size_info with
    | Sized field_size =>
      simp only [hf] at hfit
      step as ⟨checked, hsized⟩
      cases checked with
      | none => simp only [] at hsized; omega
      | some total =>
        simp only [] at hsized
        simp only []
        cases self.statically_shallow_unpadded <;> cases field.statically_shallow_unpadded <;>
          simp only [Bool.false_eq_true, Bool.false_and, Bool.true_and,
            if_false, if_true, WP.spec_ok, hzero']
        all_goals
          exact ⟨halign, by trivial, total, by trivial, by omega⟩
    | SliceDst tail =>
      simp only [hf] at hfit
      step as ⟨checked, hoffset⟩
      cases checked with
      | none => simp only [] at hoffset; omega
      | some physical =>
        simp only [] at hoffset
        simp only []
        step as ⟨checked, hbase⟩
        cases checked with
        | none => simp only [] at hbase; omega
        | some base =>
          simp only [] at hbase
          simp only []
          cases self.statically_shallow_unpadded <;> cases field.statically_shallow_unpadded <;>
            simp only [Bool.false_eq_true, Bool.false_and, Bool.true_and,
              if_false, if_true, WP.spec_ok, hzero']
          all_goals
            exact ⟨halign, by trivial, { tail with offset := physical, size_base := base },
              by trivial, by dsimp only; omega, by dsimp only; omega, rfl, rfl⟩

theorem power_dvd_of_le (a b : Nat) (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo)
    (hle : a ≤ b) : a ∣ b := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  rw [hi, hj] at hle ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle)

theorem same_size_sequence_spec :
  ∀ (self other : layout.TrailingSliceLayout Usize), ∀ (hs : (0 < self.size_rounding_align_and_phase._0.val.val : Prop)), ∀ (ho : (0 < other.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.TrailingSliceLayoutUsize.has_same_size_sequence self other ⦃ b => b = true → ∀ n : Nat, (trailingFormula self).size n = (trailingFormula other).size n ⦄ := by
  intro self other hs ho
  unfold layout.TrailingSliceLayoutUsize.has_same_size_sequence
  simp only [bne_iff_ne]
  split
  · simp [WP.spec_ok]
  · rename_i he
    have helem : self.elem_size = other.elem_size := not_ne_iff.mp he
    step with size_for_elems_spec self 0#usize hs as ⟨s, hsize⟩
    step with size_for_elems_spec other 0#usize ho as ⟨o, hother⟩
    cases s with
    | none => simp [WP.spec_ok]
    | some s =>
      cases o with
      | none => simp [WP.spec_ok]
      | some o =>
        dsimp only
        split
        · rename_i hsame
          have hz : (trailingFormula self).size 0 = (trailingFormula other).size 0 := by
            have h1 := (checked_some_size _ _ s hsize).1
            have h2 := (checked_some_size _ _ o hother).1
            have hh := congrArg UScalar.val hsame
            omega
          step with encoding_components_spec _ hs as ⟨a, p, ha, hp, _, hav, hpv⟩
          step with encoding_components_spec _ ho as ⟨b, q, hb, hq, _, hbv, hqv⟩
          simp only [core.num.nonzero.NonZero.get, bind_ok]
          have hmax : (if a.val > b.val then Result.ok a.val else Result.ok b.val) =
              Result.ok (max a.val b.val) := by
            by_cases h : a.val > b.val
            · simp only [h, if_true, max_eq_left (le_of_lt h)]
            · simp only [h, if_false, max_eq_right (le_of_not_gt h)]
          rw [hmax]
          simp only [bind_ok]
          have hmaxp : 0 < (max a.val b.val).val := by
            rw [Arithmetic.coe_max]
            exact Nat.lt_of_lt_of_le (Nat.pos_of_isPowerOfTwo ha) (Nat.le_max_left _ _)
          step with Usize.rem_spec self.elem_size (y := max a.val b.val) (by omega) as ⟨rem, hr⟩
          split
          · rename_i hrem
            apply WP.spec.ret
            intro _ n
            have hm : self.elem_size.val % (max a.val b.val).val = 0 := by
              have := congrArg UScalar.val hrem
              simpa only [show (0#usize).val = 0 by simp, hr] using this
            have hmaxpow : (max a.val b.val).val.isPowerOfTwo := by
              rw [Arithmetic.coe_max]
              by_cases h : a.val.val ≤ b.val.val
              · simpa only [Nat.max_eq_right h] using hb
              · simpa only [Nat.max_eq_left (by omega : b.val.val ≤ a.val.val)] using ha
            have hda := power_dvd_of_le _ _ ha hmaxpow (by rw [Arithmetic.coe_max]; exact Nat.le_max_left _ _)
            have hdb := power_dvd_of_le _ _ hb hmaxpow (by rw [Arithmetic.coe_max]; exact Nat.le_max_right _ _)
            have hma : self.elem_size.val % a.val.val = 0 := by
              rw [← Nat.mod_mod_of_dvd _ hda, hm, Nat.zero_mod]
            have hmb : other.elem_size.val % b.val.val = 0 := by
              rw [← helem, ← Nat.mod_mod_of_dvd _ hdb, hm, Nat.zero_mod]
            apply LayoutMath.same_sequence_sound _ _ _ n
            refine ⟨congrArg UScalar.val helem, hz, Or.inl ?_⟩
            simp only [trailingFormula, byteFormula]
            rw [← hav, ← hbv]
            exact ⟨hma, hmb⟩
          · split
            · simp [WP.spec_ok]
            · rename_i heqa
              apply WP.spec.ret
              simp only [decide_eq_true_eq]
              intro heqp n
              apply LayoutMath.same_sequence_sound _ _ _ n
              refine ⟨congrArg UScalar.val helem, hz, Or.inr ?_⟩
              have haeq : a.val = b.val := not_ne_iff.mp heqa
              have haveq := congrArg UScalar.val haeq
              have hpveq := congrArg UScalar.val heqp
              simp only [trailingFormula, byteFormula]
              rw [← hpv, ← hqv, ← hav, ← hbv]
              exact ⟨haveq, hpveq⟩
        · simp [WP.spec_ok]

theorem cast_offset_spec (cast : layout.CastType) (length : Usize) :
    (match cast with | .Prefix => Result.ok 0#usize | .Suffix => Result.ok length)
      ⦃ offset => offset.val = castSide cast length.val ∧ offset ≤ length ⦄ := by
  cases cast <;> simp [castSide, WP.spec_ok]

theorem cast_split_spec (cast : layout.CastType) (length size elems : Usize)
    (h : size.val ≤ length.val) :
    (match cast with
      | .Prefix => Result.ok (core.result.Result.Ok (elems, size))
      | .Suffix => do
        let split ← length - size
        Result.ok (core.result.Result.Ok (elems, split)) :
      Result (core.result.Result (Usize × Usize) layout.MetadataCastError))
      ⦃ r => ∃ split, r = .Ok (elems, split) ∧
        split.val = castSplit cast length.val size.val ⦄ := by
  cases cast with
  | Prefix => exact WP.spec.ret ⟨size, rfl, rfl⟩
  | Suffix =>
    step with Usize.sub_spec h as ⟨split, hs, _⟩
    exact ⟨split, rfl, hs⟩

theorem validate_cast_spec :
  ∀ (self : layout.DstLayout) (addr bytes_len : Usize) (cast_type : layout.CastType), ∀ (ha : (0 < self.align.val.val : Prop)), ∀ (hroom : (addr.val + bytes_len.val ≤ Usize.max : Prop)), ∀ (ht : (match self.size_info with
    | .Sized _ => True
    | .SliceDst tail => 0 < tail.size_rounding_align_and_phase._0.val.val ∧ 0 < tail.elem_size.val : Prop)),
    @Zerocopy.layout.DstLayout.validate_cast_and_convert_metadata self addr bytes_len cast_type ⦃ r => castSpec self addr.val bytes_len.val cast_type r ⦄ := by
  intro self addr length cast ha hroom ht
  unfold layout.DstLayout.validate_cast_and_convert_metadata
  cases hs : self.size_info with
  | Sized size =>
    step with try_nonzero_spec (.Sized size) as ⟨converted, hconverted⟩
    rw [hconverted]
    step as ⟨checked, haddr⟩
    cases checked with
    | none => simp only [] at haddr; omega
    | some ending =>
      simp only [] at haddr
      simp only [Option.isSome_some, massert, if_true, bind_ok]
      step with cast_offset_spec cast length as ⟨offset, ho, hle⟩
      have hlen := (UScalar.le_equiv _ _).mp hle
      step with Usize.add_spec (x := addr) (y := offset) (by omega) as ⟨aligned, haligned⟩
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      step with Usize.rem_spec aligned (y := self.align.val) (by omega) as ⟨rem, hr⟩
      simp only [bne_iff_ne]
      split
      · rename_i hne
        apply WP.spec.ret
        unfold castSpec
        have hv : rem.val ≠ 0 := by
          intro h
          apply hne
          exact (UScalar.eq_equiv _ _).mpr h
        rw [hr, haligned, ho] at hv
        exact hv
      · rename_i heq
        have hzero : (addr.val + castSide cast length.val) % self.align.val.val = 0 := by
          have h : rem = 0#usize := not_ne_iff.mp heq
          have hv := congrArg UScalar.val h
          rw [hr, haligned, ho] at hv
          exact hv
        have htotal : (decide (size > length) || decide (size ≤ length)) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact lt_or_ge length size
        simp only [UScalar.lt_equiv, UScalar.le_equiv] at htotal ⊢
        simp only [htotal, if_true, bind_ok]
        split
        · rename_i hbig
          apply WP.spec.ret
          simp only [castSpec, hs]
          exact ⟨hzero, hbig⟩
        · rename_i hsmall
          step with cast_split_spec cast length size 0#usize (by omega) as ⟨r, split, hr, hv⟩
          rw [hr]
          simp only [castSpec, hs, show (0#usize).val = 0 by simp]
          exact ⟨hzero, trivial, by omega, hv⟩
  | SliceDst tail =>
    simp only [hs] at ht
    step with try_nonzero_spec (.SliceDst tail) as ⟨converted, hconverted⟩
    have hne : tail.elem_size ≠ 0#usize := by
      intro h
      have hv := congrArg UScalar.val h
      change tail.elem_size.val = 0 at hv
      omega
    simp only [hne, if_false] at hconverted
    obtain ⟨t, hconverted, hoffset, hbase, hcode, helem⟩ := hconverted
    rw [hconverted]
    step as ⟨checked, haddr⟩
    cases checked with
    | none => simp only [] at haddr; omega
    | some ending =>
      simp only [] at haddr
      simp only [Option.isSome_some, massert, if_true, bind_ok]
      step with cast_offset_spec cast length as ⟨offset, ho, hle⟩
      have hlen := (UScalar.le_equiv _ _).mp hle
      step with Usize.add_spec (x := addr) (y := offset) (by omega) as ⟨aligned, haligned⟩
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      step with Usize.rem_spec aligned (y := self.align.val) (by omega) as ⟨rem, hr⟩
      simp only [bne_iff_ne]
      split
      · rename_i hne
        apply WP.spec.ret
        unfold castSpec
        have hv : rem.val ≠ 0 := by
          intro h
          apply hne
          exact (UScalar.eq_equiv _ _).mpr h
        rw [hr, haligned, ho] at hv
        exact hv
      · rename_i heq
        have hzero : (addr.val + castSide cast length.val) % self.align.val.val = 0 := by
          have h : rem = 0#usize := not_ne_iff.mp heq
          have hv := congrArg UScalar.val h
          rw [hr, haligned, ho] at hv
          exact hv
        have htn : 0 < t.size_rounding_align_and_phase._0.val.val := by rw [hcode]; exact ht.1
        have hte : 0 < t.elem_size.val.val := by rw [helem]; exact ht.2
        have hview : byteFormula t = byteFormula tail := by simp only [byteFormula, hbase, hcode, hoffset]
        step with max_trailing_bytes_spec t length htn as ⟨capacity, hc⟩
        rw [hview] at hc
        cases capacity with
        | none =>
          have hmiss := LayoutMath.capacity_spec (byteFormula tail) length.val (Nat.two_pow_pos _)
          rw [← hc] at hmiss
          apply WP.spec.ret
          refine ⟨hzero, ?_⟩
          simp only [hs]
          intro n
          exact hmiss (n * tail.elem_size.val)
        | some capacity =>
          dsimp only
          step with max_elems_for_bytes_spec capacity t.elem_size hte as ⟨elems, used, hen, _, _, _, _⟩
          step with encoding_align_spec t.size_rounding_align_and_phase htn as ⟨a, ha⟩
          have hav : a.val.val = (trailingFormula tail).align := by
            simpa only [trailingFormula, byteFormula, hcode] using ha
          step with Usize.rem_spec capacity (y := t.elem_size.val) (by omega) as ⟨unused, hu⟩
          have hap : a.val.val.isPowerOfTwo := ⟨_, by simpa only [hcode] using ha⟩
          step with round_down_spec unused a hap as ⟨unused_aligned, _, huf, _, _, _⟩
          have hcap : (trailingFormula tail).capacity length.val = some capacity.val := hc.symm
          have hmax := LayoutMath.maximal_metadata _ _ _ ht.2 hcap (trailing_align_pos tail)
          have hfit : (trailingFormula tail).size elems.val ≤ length.val := by
            apply (hmax elems.val).mpr
            rw [hen, helem]
            exact le_rfl
          have hmin := (LayoutMath.capacity_spec (trailingFormula tail) length.val (trailing_align_pos tail))
          rw [hcap] at hmin
          have hminfit := (hmin 0).mpr (by omega)
          have hbfit : t.size_base.val ≤ length.val := by
            rw [hbase]
            simp only [trailingFormula, byteFormula, LayoutMath.Formula.bytes] at hminfit
            omega
          step with Usize.sub_spec hbfit as ⟨available, hb, _⟩
          step with round_down_spec available a hap as ⟨budget, _, hbudget, _, _, _⟩
          have hused := LayoutMath.capacity_object_size (trailingFormula tail) length.val capacity.val
            (trailing_align_pos tail) hcap
          change (trailingFormula tail).size (capacity.val / tail.elem_size.val) =
            tail.size_base.val + (length.val - tail.size_base.val -
              (length.val - tail.size_base.val) % (trailingFormula tail).align) -
              (capacity.val % tail.elem_size.val -
                capacity.val % tail.elem_size.val % (trailingFormula tail).align) at hused
          rw [← hav, ← hbase] at hused
          have hunused : unused.val = capacity.val % tail.elem_size.val := by rw [hu, helem]
          have hbval : budget.val = length.val - t.size_base.val -
              (length.val - t.size_base.val) % a.val.val := by rw [hbudget, hb]
          have hus : unused_aligned.val ≤ budget.val := by
            have hmod := Nat.mod_le capacity.val tail.elem_size.val
            have hcapval : capacity.val = length.val - t.size_base.val -
                (length.val - t.size_base.val) % a.val.val - (trailingFormula tail).phase := by
              unfold LayoutMath.Formula.capacity at hcap
              simp only [hminfit, if_true, Option.some.injEq] at hcap
              have hav' : a.val.val = 2 ^ tail.size_rounding_align_and_phase._0.val.val.log2 := hav
              simpa only [trailingFormula, byteFormula, ← hav', ← hbase] using hcap.symm
            rw [huf, hbval, hunused]
            omega
          step with Usize.sub_spec hus as ⟨remaining, hremaining, _⟩
          have hsum : t.size_base.val + remaining.val ≤ Usize.max := by
            have hlenfit : length.val ≤ Usize.max := by scalar_tac
            rw [hremaining]
            have hbudget_bound : budget.val ≤ length.val - t.size_base.val := by rw [hbval]; omega
            omega
          step with Usize.add_spec (x := t.size_base) (y := remaining) hsum as ⟨size, hsize⟩
          have hexact : size.val = (trailingFormula tail).size elems.val := by
            rw [hen, helem]
            rw [hused]
            rw [hsize, hremaining, huf, hunused, hbval]
            rw [huf, hunused, hbval] at hus
            omega
          have hsizefit : size ≤ length := (UScalar.le_equiv _ _).mpr (by rw [hexact]; exact hfit)
          simp only [hsizefit, if_true, bind_ok]
          step with cast_split_spec cast length size elems (by rw [hexact]; exact hfit) as ⟨r, split, hr, hv⟩
          rw [hr]
          simp only [castSpec, hs]
          refine ⟨hzero, hfit, ?_, ?_⟩
          · intro n
            rw [hmax n, hen, helem]
            rfl
          · simpa only [hexact] using hv

theorem metadata_exact_spec :
  ∀ (self : layout.DstLayout) (size : Usize), ∀ (ha : (0 < self.align.val.val : Prop)), ∀ (ht : (match self.size_info with
    | .Sized _ => True
    | .SliceDst tail => tail.elem_size.val ≠ 0 →
      0 < tail.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.DstLayout.metadata_for_exact_size self size ⦃ r => metadataSpec self size.val r ⦄ := by
  intro self size ha ht
  unfold layout.DstLayout.metadata_for_exact_size
  cases hs : self.size_info with
  | Sized s => simp only [WP.spec_ok, metadataSpec, hs]
  | SliceDst tail =>
    simp only [hs] at ht ⊢
    cases hz : tail.elem_size.val with
    | zero =>
      simp only [WP.spec_ok, metadataSpec, hs, hz, if_true]
    | succ k =>
      simp only []
      have he : 0 < tail.elem_size.val := by omega
      have hn : tail.elem_size.val ≠ 0 := by omega
      step with validate_cast_spec self 0#usize size .Prefix ha (by scalar_tac)
        (by simp only [hs]; exact ⟨ht hn, he⟩) as ⟨cast, hc⟩
      cases cast with
      | Err err =>
        cases err with
        | Alignment =>
          simp only [castSpec, castSide, Nat.zero_add, Nat.zero_mod,
            ] at hc
          exact False.elim (hc rfl)
        | Size =>
          simp only [castSpec, castSide, hs,
            Nat.zero_add, Nat.zero_mod, true_and] at hc
          apply WP.spec.ret
          simp only [metadataSpec, hs, hn, if_false]
          intro n h
          have := hc n
          omega
      | Ok pair =>
        rcases pair with ⟨elems, bytes⟩
        change (if bytes = size then Result.ok (some elems) else Result.ok none)
          ⦃ r => metadataSpec self size.val r ⦄
        simp only [castSpec, castSide, castSplit, hs,
          Nat.zero_add, Nat.zero_mod, true_and] at hc
        split
        · rename_i hsame
          apply WP.spec.ret
          simp only [metadataSpec, hs, hn, if_false]
          have hbytes := congrArg UScalar.val hsame
          exact ⟨by omega, hc.2.1⟩
        · rename_i hdiff
          apply WP.spec.ret
          simp only [metadataSpec, hs, hn, if_false]
          intro n h
          have hle : n ≤ elems.val := (hc.2.1 n).mp (by omega)
          have hmono := LayoutMath.Formula.size_mono (trailingFormula tail)
            (trailing_align_pos tail) hle
          apply hdiff
          apply (UScalar.eq_equiv _ _).mpr
          omega

theorem extend_value_spec (self field : layout.DstLayout) (packed : Option NonZeroUsize)
    (hself : alignmentDomain self.align.val.val)
    (hfield : alignmentDomain field.align.val.val)
    (hpacked : ∀ a ∈ packed, alignmentDomain a.val.val)
    (hcanonical : canonicalLayout field)
    (hfit : (layoutValue self).extendFits (layoutValue field) (packingValue packed) Usize.max) :
    layout.DstLayout.extend self field packed
      ⦃ r => layoutValue r = (layoutValue self).extend (layoutValue field) (packingValue packed) ∧ canonicalLayout r ⦄ := by
  cases hs : self.size_info with
  | SliceDst tail => simp [layoutValue, hs, LayoutMath.LayoutValue.extendFits] at hfit
  | Sized size =>
    have hf : match field.size_info with
      | .Sized s => placement size field packed + s.val ≤ Usize.max
      | .SliceDst t => placement size field packed + t.offset.val ≤ Usize.max ∧
        placement size field packed + t.size_base.val ≤ Usize.max := by
      cases hfs : field.size_info <;>
        simpa only [layoutValue, hs, hfs, LayoutMath.LayoutValue.extendFits,
          placement, fieldAlignment, trailingFormula, byteFormula] using hfit
    apply WP.spec_mono (extend_spec self field packed size hs hself hfield hpacked hf)
    rintro r ⟨ha, hu, hr⟩
    cases hfs : field.size_info with
    | Sized s =>
      simp only [hfs] at hr
      obtain ⟨bytes, hb, hv⟩ := hr
      simp only [layoutValue, hb, hs, hfs, LayoutMath.LayoutValue.extend,
        canonicalLayout, ha, hu, hv, placement, fieldAlignment]
      exact ⟨rfl, trivial⟩
    | SliceDst t =>
      simp only [hfs] at hr
      simp only [canonicalLayout, hfs] at hcanonical
      obtain ⟨u, hsi, ho, hb, he, hc⟩ := hr
      simp only [layoutValue, hsi, hs, hfs, LayoutMath.LayoutValue.extend,
        canonicalLayout, ha, hu, trailingFormula, byteFormula, ho, hb, he, hc,
        placement, fieldAlignment]
      exact ⟨rfl, hcanonical⟩

attribute [step] extend_value_spec

theorem pad_value_spec (self : layout.DstLayout)
    (ha : self.align.val.val.isPowerOfTwo)
    (hc : canonicalLayout self)
    (hf : (layoutValue self).padFits Usize.max) :
    layout.DstLayout.pad_to_align self
      ⦃ r => layoutValue r = (layoutValue self).pad ∧ canonicalLayout r ⦄ := by
  have hfit : match self.size_info with
    | .Sized s => LayoutMath.roundUp s.val self.align.val.val ≤ Usize.max
    | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val ∧
      (if (trailingFormula t).align < self.align.val.val then
        LayoutMath.roundUp t.size_base.val (trailingFormula t).align +
          (trailingFormula t).phase ≤ Usize.max
       else LayoutMath.roundUp t.size_base.val self.align.val.val ≤ Usize.max) := by
    cases hs : self.size_info with
    | Sized s => simpa only [layoutValue, hs, LayoutMath.LayoutValue.padFits] using hf
    | SliceDst t =>
      simp only [canonicalLayout, hs] at hc
      simp only []
      refine ⟨hc, ?_⟩
      simpa only [layoutValue, hs, LayoutMath.LayoutValue.padFits,
        trailingFormula, byteFormula] using hf
  apply WP.spec_mono (pad_to_align_spec self ha hfit)
  rintro r ⟨hcanonical, hr, hp⟩
  refine ⟨?_, hcanonical⟩
  cases hs : self.size_info with
  | Sized s =>
    simp only [hs] at hp
    obtain ⟨p, hsi, hv, hu⟩ := hp
    simp only [layoutValue, hsi, hs, LayoutMath.LayoutValue.pad, hr, hv, hu]
  | SliceDst t =>
    simp only [hs] at hp
    obtain ⟨u, hsi, hv, hu⟩ := hp
    simp only [layoutValue, hsi, hs, LayoutMath.LayoutValue.pad, hr, hv, hu]

attribute [step] pad_value_spec

theorem construction_prefix_step (fields : Slice layout.DstLayout) (initial : LayoutMath.LayoutValue)
    (packed : Option NonZeroUsize) (i : Nat) (hi : i < fields.val.length) :
    constructionPrefix fields initial packed (i + 1) =
      (constructionPrefix fields initial packed i).extend (layoutValue fields.val[i]) (packingValue packed) := by
  unfold constructionPrefix
  rw [LayoutMath.LayoutValue.prefixValue_step _ _ _ _ (by simpa only [List.length_map] using hi)]
  simp only [List.getElem_map]

theorem constructor_loop_spec (packed : Option NonZeroUsize) (fields : Slice layout.DstLayout)
    (initial : LayoutMath.LayoutValue) (self : layout.DstLayout) (i : Usize)
    (hp : ∀ a ∈ packed, alignmentDomain a.val.val)
    (hd : constructionDomain fields initial packed)
    (hi : i.val ≤ fields.val.length)
    (hv : layoutValue self = constructionPrefix fields initial packed i.val)
    (hc : canonicalLayout self) :
    layout.DstLayout.for_repr_c_struct_loop packed fields self i
      ⦃ r => layoutValue r = constructionPrefix fields initial packed fields.val.length ∧ canonicalLayout r ⦄ := by
  unfold layout.DstLayout.for_repr_c_struct_loop
  apply AeneasContracts.indexed_loop_spec fields.val.length layoutValue
    (constructionPrefix fields initial packed) canonicalLayout
  · intro value idx hi hv hc
    unfold layout.DstLayout.for_repr_c_struct_loop.body
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]
    split
    · rename_i hlt
      have hlt' : idx.val < fields.val.length := hlt
      step with Slice.index_usize_spec fields idx hlt' as ⟨field, hf⟩
      obtain ⟨hself, hfield, hcanon, hfits⟩ := hd idx.val hlt'
      have hsa : alignmentDomain value.align.val.val := by
        have hh := congrArg LayoutMath.LayoutValue.align hv
        change value.align.val.val = _ at hh
        rw [hh]
        exact hself
      have hfa : alignmentDomain field.align.val.val := by rw [hf]; exact hfield
      have hca : canonicalLayout field := by rw [hf]; exact hcanon
      have hfit : (layoutValue value).extendFits (layoutValue field) (packingValue packed) Usize.max := by
        rw [hv, hf]
        exact hfits
      step as ⟨next, hnext, hcn⟩
      have hroom : idx.val + (1#usize).val ≤ Usize.max := by
        have := fields.property
        change idx.val + 1 ≤ Usize.max
        omega
      step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨j, hj⟩
      change j.val = idx.val + 1 at hj
      refine ⟨hlt', hj, ?_, hcn⟩
      rw [hj, construction_prefix_step fields initial packed idx.val hlt', hnext, hv, hf]
    · rename_i hdone
      have heq : idx.val = fields.val.length := by omega
      exact WP.spec.ret ⟨heq, hv, hc⟩
  · exact hi
  · exact hv
  · exact hc

theorem for_repr_c_struct_spec :
  ∀ (repr_align repr_packed : Option NonZeroUsize) (fields : Slice layout.DstLayout), ∀ (ha : (∀ a ∈ repr_align, alignmentDomain a.val.val : Prop)), ∀ (hp : (∀ a ∈ repr_packed, alignmentDomain a.val.val : Prop)), ∀ (hd : (constructionDomain fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) repr_packed : Prop)), ∀ (hlast : (alignmentDomain
    (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) repr_packed fields.val.length).align : Prop)), ∀ (hfit : ((constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align))
    repr_packed fields.val.length).padFits Usize.max : Prop)),
    @Zerocopy.layout.DstLayout.for_repr_c_struct repr_align repr_packed fields ⦃ r => layoutValue r =
    (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) repr_packed fields.val.length).pad ∧ canonicalLayout r ⦄ := by
  intro repr_align packed fields ha hp hd hlast hfit
  unfold layout.DstLayout.for_repr_c_struct
  step with new_zst_spec repr_align (fun a h => (ha a h).1) as ⟨start, halign, hsize, hunpadded⟩
  have hv : layoutValue start = constructionPrefix fields
      (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed (0#usize).val := by
    simp only [constructionPrefix, LayoutMath.LayoutValue.prefixValue, show (0#usize).val = 0 by simp,
      List.take_zero, List.foldl_nil, layoutValue, hsize, hunpadded, halign,
      initialAlignment, LayoutMath.LayoutValue.initial]
    cases repr_align <;> rfl
  have hc : canonicalLayout start := by simp only [canonicalLayout, hsize]
  step with constructor_loop_spec packed fields _ start 0#usize hp hd (by simp) hv hc as ⟨complete, hv, hc⟩
  step with pad_value_spec complete (by
    have hh := congrArg LayoutMath.LayoutValue.align hv
    change complete.align.val.val = _ at hh
    rw [hh]
    exact hlast.1) hc (by rw [hv]; exact hfit) as ⟨result, hr, hcanonical⟩
  exact ⟨by rw [hr, hv], hcanonical⟩

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

-- Unfold only representation domains. The model calls and authored outcome
-- predicates remain the independently verified raw contracts below.
macro "representation_simps" : tactic =>
  `(tactic| try simp only [encoding_valid_iff, trailing_valid_iff, size_info_valid_iff,
    layout_valid_iff, nonzero_valid_iff, cast_result_valid_iff, cast_type_valid_iff, scalar_valid_iff,
    encodingValid, trailingValid, sizeInfoValid, layoutValid, and_true, true_and,
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

theorem size_offset_spec : Zerocopy.Specs.size_offset_spec := by
  unfold Zerocopy.Specs.size_offset_spec
  representation_simps
  intro E self validity hv
  exact Raw.size_offset_spec self hv.2
register_spec_step size_offset_spec

theorem max_trailing_bytes_spec : Zerocopy.Specs.max_trailing_bytes_spec := by
  unfold Zerocopy.Specs.max_trailing_bytes_spec
  representation_simps
  intro E self available validity hv
  exact Raw.max_trailing_bytes_spec self available hv.2
register_spec_step max_trailing_bytes_spec

theorem padding_for_elems_spec : Zerocopy.Specs.padding_for_elems_spec := by
  unfold Zerocopy.Specs.padding_for_elems_spec
  representation_simps
  intro self elems hv
  exact Raw.padding_for_elems_spec self elems hv
register_spec_step padding_for_elems_spec

theorem size_for_elems_spec : Zerocopy.Specs.size_for_elems_spec := by
  unfold Zerocopy.Specs.size_for_elems_spec
  representation_simps
  intro self elems hv
  exact Raw.size_for_elems_spec self elems hv
register_spec_step size_for_elems_spec

theorem same_size_sequence_spec : Zerocopy.Specs.same_size_sequence_spec := by
  unfold Zerocopy.Specs.same_size_sequence_spec
  representation_simps
  intro self other hs ho
  exact Raw.same_size_sequence_spec self other hs ho
register_spec_step same_size_sequence_spec

theorem max_elems_for_bytes_spec : Zerocopy.Specs.max_elems_for_bytes_spec := by
  unfold Zerocopy.Specs.max_elems_for_bytes_spec
  intro bytes elem hn
  exact Raw.max_elems_for_bytes_spec bytes elem hn
register_spec_step max_elems_for_bytes_spec

theorem assume_shallow_unpadded_spec : Zerocopy.Specs.assume_shallow_unpadded_spec := by
  unfold Zerocopy.Specs.assume_shallow_unpadded_spec
  representation_simps
  intro self hv
  apply WP.spec_mono (Raw.assume_shallow_unpadded_spec self)
  intro r facts
  refine ⟨?_, facts⟩
  simpa only [facts.1, facts.2.1] using hv
register_spec_step assume_shallow_unpadded_spec

theorem for_type_spec : Zerocopy.Specs.for_type_spec := by
  unfold Zerocopy.Specs.for_type_spec
  representation_simps
  intro T validity size align hs ha hn
  apply WP.spec_mono (Raw.for_type_spec T size align hs ha hn)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1, hn, and_self]
register_spec_step for_type_spec

theorem for_unpadded_type_spec : Zerocopy.Specs.for_unpadded_type_spec := by
  unfold Zerocopy.Specs.for_unpadded_type_spec
  representation_simps
  intro T validity size align hs ha hn
  apply WP.spec_mono (Raw.for_unpadded_type_spec T size align hs ha hn)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1, hn, and_self]
register_spec_step for_unpadded_type_spec

theorem for_slice_spec : Zerocopy.Specs.for_slice_spec := by
  unfold Zerocopy.Specs.for_slice_spec
  representation_simps
  intro T validity size align hs ha hp
  apply WP.spec_mono (Raw.for_slice_spec T size align hs ha hp)
  intro r facts
  refine ⟨?_, facts⟩
  rcases facts with ⟨halign, _, tail, hsi, _, _, _, hcode⟩
  simp only [halign, hsi]
  have := Nat.pos_of_isPowerOfTwo hp
  simpa only [hcode, and_self] using this
register_spec_step for_slice_spec

theorem requires_static_padding_spec : Zerocopy.Specs.requires_static_padding_spec := by
  unfold Zerocopy.Specs.requires_static_padding_spec
  representation_simps
  intro self _
  exact Raw.requires_static_padding_spec self
register_spec_step requires_static_padding_spec

theorem requires_dynamic_padding_spec : Zerocopy.Specs.requires_dynamic_padding_spec := by
  unfold Zerocopy.Specs.requires_dynamic_padding_spec
  representation_simps
  intro self hv
  apply Raw.requires_dynamic_padding_spec self
  cases hs : self.size_info with
  | Sized _ => trivial
  | SliceDst _ => simpa only [hs] using hv.2
register_spec_step requires_dynamic_padding_spec

theorem metadata_exact_spec : Zerocopy.Specs.metadata_exact_spec := by
  unfold Zerocopy.Specs.metadata_exact_spec
  representation_simps
  intro self size _ ha ht
  exact Raw.metadata_exact_spec self size ha ht
register_spec_step metadata_exact_spec

theorem validate_cast_spec : Zerocopy.Specs.validate_cast_spec := by
  unfold Zerocopy.Specs.validate_cast_spec
  representation_simps
  intro self addr length side _ ha hroom ht
  exact Raw.validate_cast_spec self addr length side ha hroom ht
register_spec_step validate_cast_spec

end Zerocopy.Proofs

namespace Zerocopy.Proofs
open AeneasSpecs

theorem advance_spec : Zerocopy.Specs.advance_spec := by
  unfold Zerocopy.Specs.advance_spec
  representation_simps
  intro self bytes elem hv
  exact Raw.advance_spec self bytes elem hv
register_spec_step advance_spec

theorem try_nonzero_spec : Zerocopy.Specs.try_nonzero_spec := by
  unfold Zerocopy.Specs.try_nonzero_spec
  representation_simps
  intro self hv
  apply WP.spec_mono (Raw.try_nonzero_spec self)
  intro r facts
  constructor
  swap
  · cases self <;> simpa using facts
  cases self with
  | Sized size =>
    simp only [] at facts
    rw [facts]
    simp
  | SliceDst tail =>
    simp only [] at facts hv
    by_cases hz : tail.elem_size = 0#usize
    · simp only [hz, if_true] at facts
      rw [facts]
      simp
    · simp only [hz, if_false] at facts
      rcases facts with ⟨next, hr, _, _, hcode, helem⟩
      rw [hr]
      simp only [Option.mem_some_iff, forall_eq', hcode]
      have hnz : tail.elem_size.val ≠ 0 := by
        intro h
        apply hz
        exact UScalar.eq_of_val_eq (by simpa using h)
      exact ⟨by simpa only [helem] using Nat.pos_of_ne_zero hnz, hv⟩
register_spec_step try_nonzero_spec

theorem new_zst_spec : Zerocopy.Specs.new_zst_spec := by
  unfold Zerocopy.Specs.new_zst_spec
  representation_simps
  intro repr_align hv hp
  apply WP.spec_mono (Raw.new_zst_spec repr_align hp)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1]
  cases repr_align with
  | none => simp
  | some a => simpa only [Option.getD_some, and_true] using Nat.pos_of_isPowerOfTwo (hp a rfl)
register_spec_step new_zst_spec

theorem extend_spec : Zerocopy.Specs.extend_spec := by
  unfold Zerocopy.Specs.extend_spec
  representation_simps
  intro self field packed size hvself hvfield _ hs hself hfield hpacked hfit
  apply WP.spec_mono (Raw.extend_spec self field packed size hs hself hfield hpacked hfit)
  intro r facts
  refine ⟨?_, facts⟩
  refine ⟨?_, ?_⟩
  · rw [facts.1]
    have := Nat.pos_of_isPowerOfTwo hself.1
    omega
  · cases hsi : field.size_info with
    | Sized size =>
      simp only [hsi] at facts
      rcases facts.2.2 with ⟨bytes, hr, _⟩
      simp only [hr]
    | SliceDst tail =>
      simp only [hsi] at facts hvfield
      rcases facts.2.2 with ⟨next, hr, _, _, _, hcode⟩
      simp only [hr, hcode]
      exact hvfield.2
register_spec_step extend_spec

theorem pad_to_align_spec : Zerocopy.Specs.pad_to_align_spec := by
  unfold Zerocopy.Specs.pad_to_align_spec
  representation_simps
  intro self hv ha hfit
  apply WP.spec_mono (Raw.pad_to_align_spec self ha hfit)
  rintro r ⟨hc, facts⟩
  refine ⟨?_, facts⟩
  refine ⟨?_, ?_⟩
  · simpa only [facts.1] using hv.1
  · cases hs : r.size_info with
    | Sized _ => trivial
    | SliceDst _ => simpa only [canonicalLayout, hs] using hc
register_spec_step pad_to_align_spec

theorem for_repr_c_struct_spec : Zerocopy.Specs.for_repr_c_struct_spec := by
  unfold Zerocopy.Specs.for_repr_c_struct_spec
  representation_simps
  intro repr_align packed fields _ _ _ ha hp hd hlast hfit
  apply WP.spec_mono (Raw.for_repr_c_struct_spec repr_align packed fields ha hp hd hlast hfit)
  rintro r ⟨hr, hc⟩
  refine ⟨?_, hr⟩
  refine ⟨?_, ?_⟩
  · have halign := congrArg LayoutMath.LayoutValue.align hr
    change r.align.val.val = _ at halign
    rw [halign]
    exact Nat.pos_of_isPowerOfTwo hlast.1
  · cases hs : r.size_info with
    | Sized _ => trivial
    | SliceDst _ => simpa only [canonicalLayout, hs] using hc
register_spec_step for_repr_c_struct_spec

end Zerocopy.Proofs
