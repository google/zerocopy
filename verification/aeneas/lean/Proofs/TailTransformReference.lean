/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import Proofs.TailReference
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.TailTransforms
open TailChecks
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- This guard exposes the exact stored alignment/phase witness. It adds no
physical-layout restriction and has coverage from encoding_witness_coverage.
-/
theorem witness_matches (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase : Usize) :
    layout.tail_transform_checks.witness_matches tail align phase ⦃ b =>
      b = true → align.val.val.isPowerOfTwo ∧ phase.val < align.val.val ∧
        tail.size_rounding_align_and_phase._0.val.val = align.val.val + phase.val ⦄ := by
  unfold layout.tail_transform_checks.witness_matches
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨power, power_iff⟩
  split
  · rename_i power_true
    have power_fact : align.val.val.isPowerOfTwo := Eq.mp power_iff power_true
    simp only [UScalar.lt_equiv]
    split
    · rename_i phase_lt
      step as ⟨encoded, encoded_facts⟩
      step with same_optional_usize encoded (some tail.size_rounding_align_and_phase._0.val)
        as ⟨code_matches, matches_iff⟩
      rename_i matches_true
      have same_code := matches_iff.mp matches_true
      rw [same_code] at encoded_facts
      exact ⟨power_fact, phase_lt, encoded_facts.2.1⟩
    · simp [WP.spec_ok]
  · simp [WP.spec_ok]

/- A representable power of two is at most half the word modulus. Thus two
alignment remainders can be added without overflow, even at the largest
compressed alignment. This is a derived machine-width fact, not a new guard.
-/
theorem remainder_pair_fits (align : NonZeroUsize) (phase bytes : Usize)
    (power : align.val.val.isPowerOfTwo) (phase_lt : phase.val < align.val.val) :
    phase.val + bytes.val % align.val.val ≤ Usize.max := by
  have positive := Nat.pos_of_isPowerOfTwo power
  have remainder_lt := Nat.mod_lt bytes.val positive
  have alignment_lt := UScalar.hSize align.val
  obtain ⟨factor, modulus_eq⟩ := Arithmetic.alignment_dvd_size align.val power
  have factor_ge : 2 ≤ factor := by
    by_contra small
    have cases : factor = 0 ∨ factor = 1 := by omega
    rcases cases with zero | one
    · simp only [zero, Nat.mul_zero] at modulus_eq
      omega
    · simp only [one, Nat.mul_one] at modulus_eq
      omega
  have half := Nat.mul_le_mul_left align.val.val factor_ge
  rw [← modulus_eq] at half
  have max_eq : Usize.max + 1 = UScalar.size .Usize := by
    simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, UScalar.size]
    have positive := Nat.two_pow_pos System.Platform.numBits
    omega
  omega

/- The reference splits bytes before adding phase, but preserves exactly the
natural-number normalized base and phase. Each None branch means that base,
and only that base, exceeds the machine-word maximum.
-/
theorem reference_advance (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase bytes elem : Usize)
    (power : align.val.val.isPowerOfTwo) (phase_lt : phase.val < align.val.val) :
    layout.tail_transform_checks.reference_advance tail align phase bytes ⦃ result =>
      let next := (witnessFormula tail align phase).advance bytes.val elem.val
      match result with
      | none => Usize.max < next.base
      | some (base, new_phase) => base.val = next.base ∧
          new_phase.val = next.phase ∧ next.base ≤ Usize.max ⦄ := by
  have positive := Nat.pos_of_isPowerOfTwo power
  have remainder_bound := Nat.mod_le bytes.val align.val.val
  have sum_fits := remainder_pair_fits align phase bytes power phase_lt
  have phase_mod : (phase.val + bytes.val % align.val.val) % align.val.val =
      (phase.val + bytes.val) % align.val.val := by
    rw [Nat.add_mod phase.val bytes.val, Nat.add_mod phase.val (bytes.val % align.val.val),
      Nat.mod_mod]
  have shifted_mod_le := Nat.mod_le (phase.val + bytes.val % align.val.val) align.val.val
  have full_mod_le := Nat.mod_le (phase.val + bytes.val) align.val.val
  unfold layout.tail_transform_checks.reference_advance
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step with Usize.rem_spec bytes (y := align.val) (by omega) as ⟨remainder, remainder_value⟩
  step with Usize.sub_spec (x := bytes) (y := remainder) (by omega) as ⟨whole, whole_value⟩
  step as ⟨shifted, shifted_facts⟩
  cases shifted with
  | none =>
    simp only [] at shifted_facts
    omega
  | some shifted =>
    simp only [] at shifted_facts
    step with Usize.rem_spec shifted (y := align.val) (by omega) as ⟨new_phase, new_phase_value⟩
    have phase_value : new_phase.val = (phase.val + bytes.val) % align.val.val := by
      rw [new_phase_value, shifted_facts.2.1, remainder_value, phase_mod]
    have carry_bound := Nat.mod_le shifted.val align.val.val
    step with Usize.sub_spec (x := shifted) (y := new_phase) (by omega) as ⟨carry, carry_value⟩
    have normalized : tail.size_base.val + whole.val + carry.val =
        ((witnessFormula tail align phase).advance bytes.val elem.val).base := by
      simp only [witnessFormula, LayoutMath.Formula.advance]
      omega
    step as ⟨base, base_facts⟩
    cases base with
    | none =>
      simp only [] at base_facts
      simp only [WP.spec_ok]
      omega
    | some base =>
      simp only [] at base_facts
      step as ⟨result, result_facts⟩
      cases result with
      | none =>
        simp only [] at result_facts
        simp only [WP.spec_ok]
        omega
      | some result =>
        simp only [] at result_facts
        simp only [WP.spec_ok, witnessFormula, LayoutMath.Formula.advance]
        exact ⟨by omega, phase_value, by omega⟩

/- Establish the same modular observation as the production padding method,
using full wrapped multiplication and quotient/remainder rounding instead of
its masked optimization. Modular cancellation later gives exact word equality.
-/
theorem reference_wrapping_padding (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase elems : Usize) (power : align.val.val.isPowerOfTwo) :
    layout.tail_transform_checks.reference_wrapping_padding tail align phase elems ⦃ result =>
      (result.val + tail.offset.val + elems.val * tail.elem_size.val) % UScalar.size .Usize =
        (witnessFormula tail align phase).size elems.val % UScalar.size .Usize ⦄ := by
  have positive := Nat.pos_of_isPowerOfTwo power
  let trailing := core.num.Usize.wrapping_mul elems tail.elem_size
  let input := core.num.Usize.wrapping_add phase trailing
  have input_mod : input.val % align.val.val =
      (phase.val + elems.val * tail.elem_size.val) % align.val.val := by
    simp only [input, trailing, core.num.Usize.wrapping_add_val_eq,
      core.num.Usize.wrapping_mul_val_eq]
    rw [Nat.mod_mod_of_dvd _ (Arithmetic.alignment_dvd_size align.val power)]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Arithmetic.alignment_dvd_size align.val power),
      ← Nat.add_mod]
  have result_facts (padding : Usize)
      (padding_value : padding.val =
        (align.val.val - (phase.val + elems.val * tail.elem_size.val) % align.val.val) % align.val.val) :
      let rounded := core.num.Usize.wrapping_add input padding
      let complete := core.num.Usize.wrapping_add tail.size_base rounded
      let slice_end := core.num.Usize.wrapping_add tail.offset trailing
      ((core.num.Usize.wrapping_sub complete slice_end).val + tail.offset.val +
        elems.val * tail.elem_size.val) % UScalar.size .Usize =
          (witnessFormula tail align phase).size elems.val % UScalar.size .Usize := by
    dsimp only
    let complete := core.num.Usize.wrapping_add tail.size_base
      (core.num.Usize.wrapping_add input padding)
    let slice_end := core.num.Usize.wrapping_add tail.offset trailing
    change ((core.num.Usize.wrapping_sub complete slice_end).val + tail.offset.val +
      elems.val * tail.elem_size.val) % _ = _
    rw [Nat.add_assoc, Nat.add_mod, Nat.add_mod tail.offset.val,
      ← core.num.Usize.wrapping_mul_val_eq]
    change (((core.num.Usize.wrapping_sub complete slice_end).val) % _ +
      ((tail.offset.val % _ + trailing.val) % _)) % _ = _
    have slice_value : (tail.offset.val % UScalar.size .Usize + trailing.val) %
        UScalar.size .Usize = slice_end.val := by
      simp only [slice_end, core.num.Usize.wrapping_add_val_eq, Nat.mod_add_mod]
    rw [slice_value]
    change (((core.num.Usize.wrapping_sub complete slice_end).val) % _ + slice_end.val) % _ = _
    rw [Nat.mod_eq_of_lt (UScalar.hSize (core.num.Usize.wrapping_sub complete slice_end)),
      wrapping_sub_cancel]
    simp only [complete, core.num.Usize.wrapping_add_val_eq, Nat.mod_add_mod,
      input, trailing, core.num.Usize.wrapping_mul_val_eq, Nat.add_mod_mod,
      witnessFormula, LayoutMath.Formula.size, LayoutMath.Formula.bytes, LayoutMath.roundUp,
      padding_value]
  unfold layout.tail_transform_checks.reference_wrapping_padding
  simp only [lift, bind_ok, core.num.nonzero.NonZero.get]
  change (do
    let remainder ← input % align.val
    let padding ← if remainder = 0#usize then Result.ok 0#usize else align.val - remainder
    Result.ok (core.num.Usize.wrapping_sub
      (core.num.Usize.wrapping_add tail.size_base (core.num.Usize.wrapping_add input padding))
      (core.num.Usize.wrapping_add tail.offset trailing))) ⦃ _ ⦄
  step with Usize.rem_spec input (y := align.val) (by omega) as ⟨remainder, remainder_value⟩
  change remainder.val = input.val % align.val.val at remainder_value
  have remainder_lt := Nat.mod_lt input.val positive
  simp only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  split
  · rename_i zero
    simp only [bind_ok, WP.spec_ok]
    apply result_facts
    simp only [UScalar.ofNatCore_val_eq]
    rw [← input_mod, ← remainder_value, zero, Nat.sub_zero, Nat.mod_self]
  · rename_i nonzero
    step with Usize.sub_spec (x := align.val) (y := remainder) (by omega) as ⟨padding, padding_value⟩
    apply result_facts
    rw [← input_mod]
    rw [Nat.mod_eq_of_lt (show align.val.val - input.val % align.val.val < align.val.val by omega)]
    omega

end Zerocopy.Proofs.Raw.TailTransforms
