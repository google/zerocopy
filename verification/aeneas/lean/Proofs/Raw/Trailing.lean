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
/- Reading physical offset must preserve the raw word even though the element
carrier can be generic. No size normalization is needed for this observation.
-/
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

/- Solve the rounded complete-size inequality for the greatest byte budget. The
proof must preserve rounding plateaus and the case where even zero bytes do
not fit; dividing by element stride belongs to a later operation.
-/
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

theorem wrapping_sub_cancel (x y : Usize) :
    ((core.num.Usize.wrapping_sub x y).val + y.val) % UScalar.size .Usize = x.val := by
  rw [core.num.Usize.wrapping_sub_val_eq, Nat.mod_add_mod]
  have hy := UScalar.hSize y
  rw [show x.val + (UScalar.size .Usize - y.val) + y.val =
    x.val + UScalar.size .Usize by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (UScalar.hSize x)

/- Compute padding with wrapping machine arithmetic. The raw theorem records the
modular result; physical padding follows only when the complete size fits.
-/
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
  step with Zerocopy.Proofs.Raw.padding_lt_alignment input a ha as ⟨rp, _, hp, _, _, _⟩
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

/- Distinguish a successful checked size from overflow using the unbounded
complete-size formula. Rust None is a successful payload, not a panic.
-/
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

theorem power_dvd_of_le (a b : Nat) (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo)
    (hle : a ≤ b) : a ∣ b := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  rw [hi, hj] at hle ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle)

/- Prove that a positive comparison implies equal sizes for all metadata. The
negative branch deliberately promises no inequality between the sequences.
-/
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

end Zerocopy.Proofs.Raw
