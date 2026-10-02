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
public import Loops
public import LayoutModel
public import LayoutMath
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

theorem size_offset_spec : Zerocopy.Specs.size_offset_spec := by
  intro E self hn
  unfold layout.TrailingSliceLayout.size_offset
  step with encoding_components_spec _ hn as ⟨a, p, ha, hp, hsum, halign, hphase⟩
  step with round_down_spec self.size_base a ha as ⟨base, _, hb, hmod, _, _⟩
  simp only [UScalar.val_or]
  rw [LayoutMath.aligned_or _ _ _ ha hmod hp, hb]
  simp only [byteFormula]
  rw [← halign]
  omega

theorem max_trailing_bytes_spec : Zerocopy.Specs.max_trailing_bytes_spec := by
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

theorem assume_shallow_unpadded_spec : Zerocopy.Specs.assume_shallow_unpadded_spec := by
  intro self
  simp only [layout.DstLayout.assume_shallow_unpadded, WP.spec_ok, and_self]

theorem for_type_spec : Zerocopy.Specs.for_type_spec := by
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

theorem for_unpadded_type_spec : Zerocopy.Specs.for_unpadded_type_spec := by
  intro T size align hs ha hn
  unfold layout.DstLayout.for_unpadded_type
  step with for_type_spec T size align hs ha hn as ⟨dl, halign, hsize, _⟩
  step with assume_shallow_unpadded_spec dl as ⟨r, hr, hsi, hp⟩
  exact ⟨hr ▸ halign, hsi ▸ hsize, hp⟩

theorem for_slice_spec : Zerocopy.Specs.for_slice_spec := by
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

theorem max_elems_for_bytes_spec : Zerocopy.Specs.max_elems_for_bytes_spec := by
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

theorem requires_static_padding_spec : Zerocopy.Specs.requires_static_padding_spec := by
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

theorem padding_for_elems_spec : Zerocopy.Specs.padding_for_elems_spec := by
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
  step with padding_lt_alignment input a ha as ⟨rp, _, hp, _, _, _⟩
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

theorem size_for_elems_spec : Zerocopy.Specs.size_for_elems_spec := by
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

theorem try_nonzero_spec : Zerocopy.Specs.try_nonzero_spec := by
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

theorem new_zst_spec : Zerocopy.Specs.new_zst_spec := by
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

end Zerocopy.Proofs
