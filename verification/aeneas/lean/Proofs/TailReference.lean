/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
public import RepresentationLaws
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.TailChecks
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def witnessFormula (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase : Usize) : LayoutMath.Formula :=
  ⟨tail.size_base.val, phase.val, align.val.val, tail.elem_size.val, tail.offset.val⟩

def checkedNat (n : Nat) : Option Nat := if n ≤ Usize.max then some n else none

@[simp] theorem checkedNat_none (n : Nat) : checkedNat n = none ↔ Usize.max < n := by
  simp [checkedNat]

@[simp] theorem checkedNat_some (n value : Nat) :
    checkedNat n = some value ↔ n ≤ Usize.max ∧ n = value := by
  unfold checkedNat
  split <;> simp_all

theorem checked_add_value (x y : Usize) :
    (Usize.checked_add x y).map UScalar.val = checkedNat (x.val + y.val) := by
  have h := Usize.checked_add_bv_spec x y
  cases output_eq : Usize.checked_add x y with
  | none =>
    simp only [output_eq] at h ⊢
    simp [checkedNat, show ¬x.val + y.val ≤ Usize.max by omega]
  | some result =>
    simp only [output_eq] at h ⊢
    simp [checkedNat, h.1, h.2.1]

theorem checked_mul_value (x y : Usize) :
    (Usize.checked_mul x y).map UScalar.val = checkedNat (x.val * y.val) := by
  have h := Usize.checked_mul_bv_spec x y
  cases output_eq : Usize.checked_mul x y with
  | none =>
    simp only [output_eq] at h ⊢
    simp [checkedNat, show ¬x.val * y.val ≤ Usize.max by omega]
  | some result =>
    simp only [output_eq] at h ⊢
    simp [checkedNat, h.1, h.2.1]

theorem same_optional_usize (left right : Option Usize) :
    layout.tail_checks.same_optional_usize left right ⦃ b => (b = true ↔ left = right) ⦄ := by
  cases left <;> cases right <;>
    simp [layout.tail_checks.same_optional_usize, WP.spec_ok]

theorem optional_value_injective {left right : Option Usize}
    (same : left.map UScalar.val = right.map UScalar.val) : left = right := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some right => cases same
  | some left =>
    cases right with
    | none => cases same
    | some right =>
      congr 1
      exact UScalar.eq_of_val_eq (Option.some.inj same)

/- This is coverage of the Rust witness guard, rather than an additional
restriction on the compressed representation. Every positive stored word
decodes to a power of two and a phase below it.
-/
theorem encoding_witness_coverage (tail : layout.TrailingSliceLayout Usize)
    (positive : 0 < tail.size_rounding_align_and_phase._0.val.val) :
    ∃ a p : Nat, a.isPowerOfTwo ∧ p < a ∧
      a + p = tail.size_rounding_align_and_phase._0.val.val := by
  obtain ⟨value, decoded⟩ := rounding_decode_positive tail.size_rounding_align_and_phase positive
  have h := (rounding_decode_iff tail.size_rounding_align_and_phase value).mp decoded
  exact ⟨value.align, value.phase, value.align_pow2, value.phase_lt, h.symm⟩

theorem witness_view (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase : Usize) (power : align.val.val.isPowerOfTwo)
    (phase_lt : phase.val < align.val.val)
    (encoding : tail.size_rounding_align_and_phase._0.val.val = align.val.val + phase.val) :
    trailingFormula tail = witnessFormula tail align phase := by
  let value : layout.RoundingAlignAndPhase.RoundingValue :=
    { align := align.val.val, phase := phase.val, align_pow2 := power,
      phase_lt := phase_lt, fits := by rw [← encoding]; scalar_tac }
  have decoded := (rounding_decode_iff tail.size_rounding_align_and_phase value).mpr encoding
  have components := rounding_decode_components tail.size_rounding_align_and_phase value decoded
  simp only [value] at components
  rw [encoding] at components
  simp only [trailingFormula, byteFormula, witnessFormula, ← components.1,
    encoding, Nat.add_sub_cancel_left]

def witnessMatches (runtime_layout : layout.DstLayout)
    (align : NonZeroUsize) (phase : Usize) : Prop :=
  match runtime_layout.size_info with
  | .Sized _ => True
  | .SliceDst tail => align.val.val.isPowerOfTwo ∧ phase.val < align.val.val ∧
      tail.size_rounding_align_and_phase._0.val.val = align.val.val + phase.val

theorem reference_round_up (bytes : Usize) (align : NonZeroUsize)
    (positive : 0 < align.val.val) :
    layout.tail_checks.reference_round_up bytes align ⦃ result =>
      result.map UScalar.val = checkedNat (LayoutMath.roundUp bytes.val align.val.val) ⦄ := by
  unfold layout.tail_checks.reference_round_up
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step with Usize.rem_spec bytes (y := align.val) (by omega) as ⟨remainder, remainder_value⟩
  have remainder_lt := Nat.mod_lt bytes.val positive
  simp only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  split
  · rename_i zero
    have rounded : LayoutMath.roundUp bytes.val align.val.val = bytes.val := by
      apply LayoutMath.roundUp_eq
      omega
    simp only [bind_ok, WP.spec_ok]
    rw [checked_add_value, rounded, UScalar.ofNatCore_val_eq, Nat.add_zero]
  · rename_i nonzero
    step with Usize.sub_spec (x := align.val) (y := remainder) (by omega) as ⟨padding, padding_value⟩
    rw [checked_add_value]
    congr 1
    unfold LayoutMath.roundUp
    have padding_lt : align.val.val - bytes.val % align.val.val < align.val.val := by omega
    rw [Nat.mod_eq_of_lt padding_lt]
    omega

theorem reference_size (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase elems : Usize) (positive : 0 < align.val.val) :
    layout.tail_checks.reference_size tail align phase elems ⦃ result =>
      result.map UScalar.val = (witnessFormula tail align phase).checkedSize Usize.max elems.val ⦄ := by
  let f := witnessFormula tail align phase
  have lower := (LayoutMath.roundUp_properties
    (phase.val + elems.val * tail.elem_size.val) align.val.val positive).1
  have size_eq : f.size elems.val = tail.size_base.val +
      LayoutMath.roundUp (phase.val + elems.val * tail.elem_size.val) align.val.val := rfl
  unfold layout.tail_checks.reference_size
  step as ⟨product, product_facts⟩
  cases product with
  | none =>
    simp only [] at product_facts
    have overflow : Usize.max < f.size elems.val := by omega
    simp [LayoutMath.Formula.checkedSize, ← size_eq, f, overflow, Nat.not_le.mpr overflow]
  | some bytes =>
    simp only [] at product_facts
    step as ⟨input, input_facts⟩
    cases input with
    | none =>
      simp only [] at input_facts
      have overflow : Usize.max < f.size elems.val := by omega
      simp [LayoutMath.Formula.checkedSize, ← size_eq, f, overflow, Nat.not_le.mpr overflow]
    | some input =>
      simp only [] at input_facts
      step with reference_round_up input align positive as ⟨rounded, rounded_facts⟩
      have input_value : input.val = phase.val + elems.val * tail.elem_size.val := by omega
      rw [input_value] at rounded_facts
      cases rounded with
      | none =>
        simp only [Option.map_none] at rounded_facts
        have overflow_round := (checkedNat_none _).mp rounded_facts.symm
        have overflow : Usize.max < f.size elems.val := by omega
        simp [LayoutMath.Formula.checkedSize, ← size_eq, f, Nat.not_le.mpr overflow]
      | some rounded =>
        simp only [Option.map_some] at rounded_facts
        have rounded_value := (checkedNat_some _ _).mp rounded_facts.symm
        simp only [WP.spec_ok]
        rw [checked_add_value]
        change checkedNat _ = _
        rw [← rounded_value.2]
        rfl

theorem capacity_condition (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase budget : Usize) (positive : 0 < align.val.val) :
    (witnessFormula tail align phase).bytes 0 ≤ budget.val ↔
      tail.size_base.val ≤ budget.val ∧
      phase.val ≤ (budget.val - tail.size_base.val) -
        (budget.val - tail.size_base.val) % align.val.val := by
  have nonnegative := (LayoutMath.roundUp_properties phase.val align.val.val positive).1
  have round_condition := LayoutMath.roundUp_le_budget phase.val align.val.val
    (budget.val - tail.size_base.val) positive
  change tail.size_base.val + LayoutMath.roundUp (phase.val + 0) align.val.val ≤ _ ↔ _
  rw [Nat.add_zero]
  constructor
  · intro fit
    exact ⟨by omega, round_condition.mp (by omega)⟩
  · rintro ⟨base_fits, phase_fits⟩
    have := round_condition.mpr phase_fits
    omega

theorem reference_capacity (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase budget : Usize) (positive : 0 < align.val.val) :
    layout.tail_checks.reference_capacity tail align phase budget ⦃ result =>
      result.map UScalar.val = (witnessFormula tail align phase).capacity budget.val ⦄ := by
  have condition := capacity_condition tail align phase budget positive
  unfold layout.tail_checks.reference_capacity
  step as ⟨after_base, base_facts⟩
  cases after_base with
  | none =>
    simp only [] at base_facts
    have miss : ¬(witnessFormula tail align phase).bytes 0 ≤ budget.val := by
      intro fit
      have := condition.mp fit
      omega
    simp [LayoutMath.Formula.capacity, miss]
  | some after_base =>
    simp only [] at base_facts
    simp only [core.num.nonzero.NonZero.get, bind_ok]
    step with Usize.rem_spec after_base (y := align.val) (by omega) as ⟨remainder, remainder_value⟩
    have remainder_bound := Nat.mod_le after_base.val align.val.val
    step with Usize.sub_spec (x := after_base) (y := remainder) (by omega) as ⟨rounded, rounded_value⟩
    have rounded_budget : rounded.val = (budget.val - tail.size_base.val) -
        (budget.val - tail.size_base.val) % align.val.val := by
      rw [rounded_value, remainder_value, base_facts.2.1]
    have phase_facts := Usize.checked_sub_bv_spec rounded phase
    cases result_eq : Usize.checked_sub rounded phase with
    | none =>
      simp only [result_eq] at phase_facts
      have miss : ¬(witnessFormula tail align phase).bytes 0 ≤ budget.val := by
        intro fit
        have := condition.mp fit
        omega
      simp [result_eq, LayoutMath.Formula.capacity, miss]
    | some result =>
      simp only [result_eq] at phase_facts
      have fit : (witnessFormula tail align phase).bytes 0 ≤ budget.val :=
        condition.mpr ⟨base_facts.1, by omega⟩
      simp only [result_eq, WP.spec_ok, Option.map_some, LayoutMath.Formula.capacity, fit, if_true]
      dsimp only [witnessFormula]
      congr 1
      omega

end Zerocopy.Proofs.Raw.TailChecks
