/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Raw.Encoding
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false
theorem assume_shallow_unpadded_spec :
  ∀ (self : layout.DstLayout),
    @Zerocopy.layout.DstLayout.assume_shallow_unpadded self ⦃ r => r.align = self.align ∧ r.size_info = self.size_info ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro self
  simp only [layout.DstLayout.assume_shallow_unpadded, WP.spec_ok, and_self]

/- Construct a fixed layout from explicit modeled size and alignment reads.
Those reads are data premises supplied by the external ABI bridge, not axioms
asserting that an arbitrary modeled size is the layout of a Rust type.
-/
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

/- Construct the same fixed layout with its asserted unpadded flag. The caller's
separate padding justification is outside this numerical contract.
-/
theorem for_unpadded_type_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hn : (0 < align.val : Prop)),
    @Zerocopy.layout.DstLayout.for_unpadded_type T ⦃ r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro T size align hs ha hn
  unfold layout.DstLayout.for_unpadded_type
  step with for_type_spec T size align hs ha hn as ⟨dl, halign, hsize, _⟩
  step with assume_shallow_unpadded_spec dl as ⟨r, hr, hsi, hp⟩
  exact ⟨hr ▸ halign, hsi ▸ hsize, hp⟩

/- Construct a trailing layout with element size as stride and the modeled ABI
alignment as its rounding alignment. The primitive read premises stay
explicit.
-/
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

theorem requires_static_padding_spec :
  ∀ (self : layout.DstLayout),
    @Zerocopy.layout.DstLayout.requires_static_padding self ⦃ r => r = !self.statically_shallow_unpadded ⦄ := by
  intro self
  simp only [layout.DstLayout.requires_static_padding, WP.spec_ok]
  cases self.statically_shallow_unpadded <;> rfl

/- Explain both zero-stride rejection and successful conversion. The raw lemma
retains broad representation coverage; the canonical spec adds recursive
admission rather than silently changing that useful raw theorem.
-/
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

/- Preserve the inner complete-size calculation while adding outer padding. The
proof separately tracks physical offset, normalized base/phase, alignment,
and the unpadded flag; equal total sizes alone would be insufficient.
-/
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
    step with Zerocopy.Proofs.Raw.padding_lt_alignment size self.align ha as ⟨p, _, hp, _, _, hz⟩
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
      step with Zerocopy.Proofs.Raw.padding_lt_alignment tail.size_base a hap as ⟨bp, _, hbp, _, _, _⟩
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
      step with Zerocopy.Proofs.Raw.padding_lt_alignment tail.size_base self.align ha as ⟨bp, _, hbp, _, _, _⟩
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

/- Changing the byte origin must preserve the complete-size formula. Carry
aligned bytes into base and keep the residual phase without losing physical
offset.
-/
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

end Zerocopy.Proofs.Raw
