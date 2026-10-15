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

theorem metadata_unique (runtime_layout : layout.DstLayout) (size : Nat)
    (left right : Option Usize)
    (left_spec : metadataSpec runtime_layout size left)
    (right_spec : metadataSpec runtime_layout size right) : left = right := by
  cases info_eq : runtime_layout.size_info with
  | Sized bytes =>
    simp only [metadataSpec, info_eq] at left_spec right_spec
    rw [left_spec, right_spec]
  | SliceDst tail =>
    by_cases zero : tail.elem_size.val = 0
    · simp only [metadataSpec, info_eq, zero, if_true] at left_spec right_spec
      rw [left_spec, right_spec]
    · simp only [metadataSpec, info_eq, zero, if_false] at left_spec right_spec
      cases left with
      | none =>
        cases right with
        | none => rfl
        | some right => exact False.elim (left_spec right.val right_spec.1)
      | some left =>
        cases right with
        | none => exact False.elim (right_spec left.val left_spec.1)
        | some right =>
          have le_right := (right_spec.2 left.val).mp (by omega)
          have le_left := (left_spec.2 right.val).mp (by omega)
          congr 1
          exact UScalar.eq_of_val_eq (by omega)

theorem cast_unique (runtime_layout : layout.DstLayout) (addr length : Nat)
    (side : layout.CastType)
    (left right : core.result.Result (Usize × Usize) layout.MetadataCastError)
    (left_spec : castSpec runtime_layout addr length side left)
    (right_spec : castSpec runtime_layout addr length side right) : left = right := by
  cases left with
  | Ok left =>
    rcases left with ⟨left_elems, left_split⟩
    cases right with
    | Err error =>
      cases error with
      | Alignment => exact False.elim (right_spec left_spec.1)
      | Size =>
        cases info_eq : runtime_layout.size_info with
        | Sized bytes => simp only [castSpec, info_eq] at left_spec right_spec; omega
        | SliceDst tail =>
          simp only [castSpec, info_eq] at left_spec right_spec
          have miss := right_spec.2 left_elems.val
          omega
    | Ok right =>
      rcases right with ⟨right_elems, right_split⟩
      cases info_eq : runtime_layout.size_info with
      | Sized bytes =>
        simp only [castSpec, info_eq] at left_spec right_spec
        have elems_eq : left_elems = right_elems := UScalar.eq_of_val_eq (by omega)
        have split_eq : left_split = right_split := UScalar.eq_of_val_eq (by omega)
        rw [elems_eq, split_eq]
      | SliceDst tail =>
        simp only [castSpec, info_eq] at left_spec right_spec
        have le_right := (right_spec.2.2.1 left_elems.val).mp left_spec.2.1
        have le_left := (left_spec.2.2.1 right_elems.val).mp right_spec.2.1
        have elems_eq : left_elems = right_elems := UScalar.eq_of_val_eq (by omega)
        have split_eq : left_split = right_split := UScalar.eq_of_val_eq (by
          rw [elems_eq] at left_spec
          omega)
        rw [elems_eq, split_eq]
  | Err left_error =>
    cases right with
    | Ok right =>
      rcases right with ⟨right_elems, right_split⟩
      cases left_error with
      | Alignment => exact False.elim (left_spec right_spec.1)
      | Size =>
        cases info_eq : runtime_layout.size_info with
        | Sized bytes => simp only [castSpec, info_eq] at left_spec right_spec; omega
        | SliceDst tail =>
          simp only [castSpec, info_eq] at left_spec right_spec
          have miss := left_spec.2 right_elems.val
          omega
    | Err right_error =>
      cases left_error <;> cases right_error <;> simp_all [castSpec]

theorem reference_cast (runtime_layout : layout.DstLayout) (align : NonZeroUsize)
    (phase addr length : Usize) (side : layout.CastType)
    (layout_positive : 0 < runtime_layout.align.val.val)
    (align_positive : 0 < align.val.val)
    (room : addr.val + length.val ≤ Usize.max)
    (witness : witnessMatches runtime_layout align phase)
    (stride : match runtime_layout.size_info with | .Sized _ => True | .SliceDst t => 0 < t.elem_size.val) :
    layout.tail_checks.reference_cast runtime_layout align phase addr length side ⦃ result =>
      castSpec runtime_layout addr.val length.val side result ⦄ := by
  have anchor_spec : (match side with
      | .Prefix => Result.ok addr
      | .Suffix => addr + length) ⦃ anchor => anchor.val = addr.val + castSide side length.val ⦄ := by
    cases side with
    | Prefix => simp [WP.spec_ok, castSide]
    | Suffix =>
      apply WP.spec_mono (Usize.add_spec (x := addr) (y := length) room)
      intro result facts
      simpa only [castSide] using facts
  unfold layout.tail_checks.reference_cast
  change ((match side with
    | .Prefix => Result.ok addr
    | .Suffix => addr + length) >>= _) ⦃ result => castSpec runtime_layout addr.val length.val side result ⦄
  step with anchor_spec as ⟨anchor, anchor_value⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step with Usize.rem_spec anchor (y := runtime_layout.align.val) (by omega) as ⟨remainder, remainder_value⟩
  rw [anchor_value] at remainder_value
  simp only [bne_iff_ne, UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  split
  · rename_i not_aligned
    simp only [ne_eq, UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at not_aligned
    apply WP.spec.ret
    change (addr.val + castSide side length.val) % runtime_layout.align.val.val ≠ 0
    rwa [← remainder_value]
  · rename_i aligned
    simp only [ne_eq, not_not, UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at aligned
    have anchor_aligned : (addr.val + castSide side length.val) % runtime_layout.align.val.val = 0 := by omega
    cases info_eq : runtime_layout.size_info with
    | Sized size =>
      simp only [info_eq, bind_ok]
      split
      · rename_i size_fits
        have fits : size.val ≤ length.val := (UScalar.le_equiv _ _).mp size_fits
        cases side with
        | Prefix =>
          simp only [bind_ok, WP.spec_ok, castSpec, info_eq, castSplit, UScalar.ofNatCore_val_eq]
          exact ⟨anchor_aligned, rfl, fits, rfl⟩
        | Suffix =>
          step with Usize.sub_spec (x := length) (y := size) fits as ⟨split, split_value⟩
          simp only [castSpec, info_eq, castSplit, UScalar.ofNatCore_val_eq]
          exact ⟨anchor_aligned, trivial, fits, split_value⟩
      · rename_i size_misses
        simp only [bind_ok, WP.spec_ok, castSpec, info_eq]
        exact ⟨anchor_aligned, by scalar_tac⟩
    | SliceDst tail =>
      simp only [witnessMatches, info_eq] at witness
      simp only [info_eq] at stride ⊢
      have formula_eq := witness_view tail align phase witness.1 witness.2.1 witness.2.2
      let f := witnessFormula tail align phase
      step with reference_capacity tail align phase length align_positive as ⟨capacity, capacity_value⟩
      have capacity_spec := LayoutMath.capacity_spec f length.val align_positive
      cases capacity with
      | none =>
        simp only [Option.map_none] at capacity_value
        rw [← capacity_value] at capacity_spec
        simp only [bind_ok, WP.spec_ok, castSpec, info_eq]
        refine ⟨anchor_aligned, ?_⟩
        intro n
        rw [formula_eq]
        exact capacity_spec (n * tail.elem_size.val)
      | some capacity =>
        simp only [Option.map_some] at capacity_value
        step with Usize.div_spec capacity (y := tail.elem_size) (by omega) as ⟨elems, elems_value⟩
        have greatest : ∀ n, f.size n ≤ length.val ↔ n ≤ elems.val := by
          have maximal := LayoutMath.maximal_metadata f length.val capacity.val stride
            capacity_value.symm align_positive
          simpa only [f, witnessFormula, elems_value] using maximal
        have selected_fits := (greatest elems.val).mpr (by rfl)
        have checked_fits : f.size elems.val ≤ Usize.max := by scalar_tac
        step with reference_size tail align phase elems align_positive as ⟨selected_size, selected_value⟩
        have selected_exact : selected_size.map UScalar.val = some (f.size elems.val) := by
          change selected_size.map UScalar.val = f.checkedSize Usize.max elems.val at selected_value
          simpa only [LayoutMath.Formula.checkedSize, checked_fits, if_true] using selected_value
        cases selected_size with
        | none => cases selected_exact
        | some selected_size =>
          have size_value : selected_size.val = f.size elems.val := Option.some.inj selected_exact
          have fits : selected_size.val ≤ length.val := by rw [size_value]; exact selected_fits
          change selected_size.val = (witnessFormula tail align phase).size elems.val at size_value
          cases side with
          | Prefix =>
            simp only [bind_ok, WP.spec_ok, castSpec, info_eq, castSplit]
            rw [formula_eq]
            exact ⟨anchor_aligned, selected_fits, greatest, size_value⟩
          | Suffix =>
            simp only [bind_ok]
            step with Usize.sub_spec (x := length) (y := selected_size) fits as ⟨split, split_value⟩
            simp only [castSpec, info_eq, castSplit]
            rw [formula_eq]
            exact ⟨anchor_aligned, selected_fits, greatest, by omega⟩

theorem reference_metadata (runtime_layout : layout.DstLayout) (align : NonZeroUsize)
    (phase size : Usize) (align_positive : 0 < align.val.val)
    (witness : witnessMatches runtime_layout align phase) :
    layout.tail_checks.reference_metadata runtime_layout align phase size ⦃ result =>
      metadataSpec runtime_layout size.val result ⦄ := by
  unfold layout.tail_checks.reference_metadata
  cases info_eq : runtime_layout.size_info with
  | Sized bytes => simp only [WP.spec_ok, metadataSpec, info_eq]
  | SliceDst tail =>
    simp only [witnessMatches, info_eq] at witness
    have formula_eq := witness_view tail align phase witness.1 witness.2.1 witness.2.2
    let f := witnessFormula tail align phase
    simp only [info_eq, UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
    split
    · rename_i zero
      simp only [WP.spec_ok, metadataSpec, info_eq, zero, if_true]
    · rename_i nonzero
      have stride : 0 < tail.elem_size.val := by omega
      step with reference_capacity tail align phase size align_positive as ⟨capacity, capacity_value⟩
      have capacity_spec := LayoutMath.capacity_spec f size.val align_positive
      cases capacity with
      | none =>
        simp only [Option.map_none] at capacity_value
        rw [← capacity_value] at capacity_spec
        simp only [WP.spec_ok, metadataSpec, info_eq, nonzero, if_false]
        intro n exact_size
        have misses := capacity_spec (n * tail.elem_size.val)
        rw [formula_eq] at exact_size
        change size.val < f.size n at misses
        change f.size n = size.val at exact_size
        omega
      | some capacity =>
        simp only [Option.map_some] at capacity_value
        step with Usize.div_spec capacity (y := tail.elem_size) (by omega) as ⟨elems, elems_value⟩
        have greatest : ∀ n, f.size n ≤ size.val ↔ n ≤ elems.val := by
          have maximal := LayoutMath.maximal_metadata f size.val capacity.val stride
            capacity_value.symm align_positive
          simpa only [f, witnessFormula, elems_value] using maximal
        have selected_fits := (greatest elems.val).mpr (by rfl)
        have checked_fits : f.size elems.val ≤ Usize.max := by scalar_tac
        step with reference_size tail align phase elems align_positive as ⟨selected_size, selected_value⟩
        have selected_exact : selected_size.map UScalar.val = some (f.size elems.val) := by
          change selected_size.map UScalar.val = f.checkedSize Usize.max elems.val at selected_value
          simpa only [LayoutMath.Formula.checkedSize, checked_fits, if_true] using selected_value
        cases selected_size with
        | none => cases selected_exact
        | some selected_size =>
          have size_value : selected_size.val = f.size elems.val := Option.some.inj selected_exact
          step with same_optional_usize (some selected_size) (some size) as ⟨same, same_iff⟩
          split
          · rename_i same_true
            have same_size := Option.some.inj (same_iff.mp same_true)
            simp only [WP.spec_ok, metadataSpec, info_eq, nonzero, if_false]
            rw [formula_eq]
            exact ⟨by rw [← size_value, same_size], greatest⟩
          · rename_i different
            have different_size : selected_size ≠ size := by
              intro same_size
              exact different (same_iff.mpr (by rw [same_size]))
            simp only [WP.spec_ok, metadataSpec, info_eq, nonzero, if_false]
            intro n exact_size
            rw [formula_eq] at exact_size
            change f.size n = size.val at exact_size
            have count_le := (greatest n).mp (by omega)
            have monotone := LayoutMath.Formula.size_mono f align_positive count_le
            apply different_size
            apply UScalar.eq_of_val_eq
            omega

end Zerocopy.Proofs.Raw.TailChecks
