/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import Proofs.TailReference
public import RequiredModelContracts.TailChecks
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.TailChecks
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- The roots execute the production operation and the separate reference,
then prove the actual Rust assertion. The reference lemmas retain their own
arithmetic derivations; neither side is substituted for an extracted body.
-/
theorem trailing_arithmetic_check (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase elems budget : Usize) :
    layout.tail_checks.trailing_arithmetic_check tail align phase elems budget ⦃ _ => True ⦄ := by
  unfold layout.tail_checks.trailing_arithmetic_check
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨power, power_iff⟩
  split
  · rename_i power_true
    have power_fact : align.val.val.isPowerOfTwo := Eq.mp power_iff power_true
    have align_positive := Nat.pos_of_isPowerOfTwo power_fact
    simp only [UScalar.lt_equiv]
    split
    · rename_i phase_lt
      step as ⟨encoded, encoded_facts⟩
      step with same_optional_usize encoded (some tail.size_rounding_align_and_phase._0.val)
        as ⟨code_matches, matches_iff⟩
      split
      · rename_i matches_true
        have encoded_eq := matches_iff.mp matches_true
        rw [encoded_eq] at encoded_facts
        simp only [] at encoded_facts
        have encoding : tail.size_rounding_align_and_phase._0.val.val = align.val.val + phase.val :=
          encoded_facts.2.1
        have positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by omega
        have formula_eq := witness_view tail align phase power_fact phase_lt encoding
        step with Zerocopy.Proofs.Raw.size_for_elems_spec tail elems positive as ⟨actual_size, actual_size_value⟩
        step with reference_size tail align phase elems align_positive as ⟨expected_size, expected_size_value⟩
        rw [formula_eq] at actual_size_value
        have size_same : actual_size = expected_size := optional_value_injective
          (actual_size_value.trans expected_size_value.symm)
        step with same_optional_usize actual_size expected_size as ⟨same_size, same_size_iff⟩
        have size_true := same_size_iff.mpr size_same
        simp only [massert, size_true, if_true, bind_ok]
        step with Zerocopy.Proofs.Raw.max_trailing_bytes_spec tail budget positive as ⟨actual_capacity, actual_capacity_value⟩
        step with reference_capacity tail align phase budget align_positive as ⟨expected_capacity, expected_capacity_value⟩
        have byte_capacity : (byteFormula tail).capacity budget.val =
            (trailingFormula tail).capacity budget.val := rfl
        rw [byte_capacity, formula_eq] at actual_capacity_value
        have capacity_same : actual_capacity = expected_capacity := optional_value_injective
          (actual_capacity_value.trans expected_capacity_value.symm)
        step with same_optional_usize actual_capacity expected_capacity as ⟨same_capacity, same_capacity_iff⟩
        have capacity_true := same_capacity_iff.mpr capacity_same
        simp [massert, capacity_true, WP.spec_ok]
      · simp only [WP.spec_ok]
    · simp only [WP.spec_ok]
  · simp only [WP.spec_ok]

theorem encoding_guard_spec (runtime_layout : layout.DstLayout)
    (align : NonZeroUsize) (phase : Usize) :
    (match (generalizing := false) runtime_layout.size_info with
      | .Sized _ => Result.ok (runtime_layout.size_info, true)
      | .SliceDst tail => do
        let power ← core.num.Usize.is_power_of_two align.val
        let code_matches ←
          if power then
            if phase < align.val then
              do
              let encoded ← lift (Usize.checked_add align.val phase)
              layout.tail_checks.same_optional_usize encoded (some tail.size_rounding_align_and_phase._0.val)
            else Result.ok false
          else Result.ok false
        Result.ok (runtime_layout.size_info, code_matches)) ⦃ pair =>
      pair.1 = runtime_layout.size_info ∧
        (pair.2 = true → witnessMatches runtime_layout align phase) ⦄ := by
  cases info_eq : runtime_layout.size_info with
  | Sized bytes => simp [WP.spec_ok, witnessMatches, info_eq]
  | SliceDst tail =>
    step as ⟨power, power_iff⟩
    split
    · rename_i power_true
      have power_fact : align.val.val.isPowerOfTwo := Eq.mp power_iff power_true
      simp only [UScalar.lt_equiv]
      split
      · rename_i phase_lt
        step as ⟨encoded, encoded_facts⟩
        step with same_optional_usize encoded
          (some tail.size_rounding_align_and_phase._0.val) as ⟨code_matches, matches_iff⟩
        simp only [WP.spec_ok, Prod.fst, Prod.snd, witnessMatches, info_eq]
        intro matches_true
        have same_code := matches_iff.mp matches_true
        rw [same_code] at encoded_facts
        exact ⟨power_fact, phase_lt, encoded_facts.2.1⟩
      · simp [bind_ok, WP.spec_ok]
    · simp [bind_ok, WP.spec_ok]

theorem witness_positive (runtime_layout : layout.DstLayout)
    (align : NonZeroUsize) (phase : Usize)
    (witness : witnessMatches runtime_layout align phase) :
    match runtime_layout.size_info with
    | .Sized _ => True
    | .SliceDst tail => 0 < tail.size_rounding_align_and_phase._0.val.val := by
  cases info_eq : runtime_layout.size_info with
  | Sized bytes => trivial
  | SliceDst tail =>
    simp only [witnessMatches, info_eq] at witness
    have positive := Nat.pos_of_isPowerOfTwo witness.1
    omega

theorem layout_observations_check (runtime_layout : layout.DstLayout)
    (align : NonZeroUsize) (phase size addr length : Usize) (side : layout.CastType)
    (layout_positive : 0 < runtime_layout.align.val.val) (align_positive : 0 < align.val.val) :
    layout.tail_checks.layout_observations_check runtime_layout align phase size addr length side ⦃ _ => True ⦄ := by
  unfold layout.tail_checks.layout_observations_check
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  change (Aeneas.Std.bind (match (generalizing := false) runtime_layout.size_info with
      | .Sized _ => Result.ok (runtime_layout.size_info, true)
      | .SliceDst tail => do
        let power ← core.num.Usize.is_power_of_two align.val
        let code_matches ←
          if power then
            if phase < align.val then
              do
              let encoded ← lift (Usize.checked_add align.val phase)
              layout.tail_checks.same_optional_usize encoded (some tail.size_rounding_align_and_phase._0.val)
            else Result.ok false
          else Result.ok false
        Result.ok (runtime_layout.size_info, code_matches)) _) ⦃ _ ⦄
  step with encoding_guard_spec runtime_layout align phase as ⟨info, code_matches, same_info, when_matches⟩
  subst info
  split
  · rename_i matches_true
    have witness := when_matches matches_true
    have positive := witness_positive runtime_layout align phase witness
    have meta_domain : match runtime_layout.size_info with
      | .Sized _ => True
      | .SliceDst tail => tail.elem_size.val ≠ 0 → 0 < tail.size_rounding_align_and_phase._0.val.val := by
      cases info_eq : runtime_layout.size_info with
      | Sized bytes => trivial
      | SliceDst tail =>
        simp only [info_eq] at positive ⊢
        intro nonzero
        exact positive
    step with Zerocopy.Proofs.Raw.metadata_exact_spec runtime_layout size layout_positive meta_domain
      as ⟨actual_metadata, actual_metadata_spec⟩
    step with reference_metadata runtime_layout align phase size align_positive witness
      as ⟨expected_metadata, expected_metadata_spec⟩
    have metadata_same := metadata_unique runtime_layout size.val actual_metadata expected_metadata
      actual_metadata_spec expected_metadata_spec
    step with same_optional_usize actual_metadata expected_metadata as ⟨same_metadata, same_metadata_iff⟩
    have metadata_true := same_metadata_iff.mpr metadata_same
    simp only [massert, metadata_true, if_true, bind_ok]
    cases info_eq : runtime_layout.size_info with
    | Sized bytes =>
      simp only [info_eq, bind_ok]
      have updated_eq : { runtime_layout with size_info := .Sized bytes } = runtime_layout := by
        rw [← info_eq]
      rw [updated_eq]
      step as ⟨ending, ending_facts⟩
      cases ending with
      | none => simp [Option.isSome, WP.spec_ok]
      | some ending =>
        simp only [] at ending_facts
        simp only [Option.isSome, if_true]
        have room : addr.val + length.val ≤ Usize.max := ending_facts.1
        step with Zerocopy.Proofs.Raw.validate_cast_spec runtime_layout addr length side layout_positive room
          (by simp only [info_eq]) as ⟨actual, actual_spec⟩
        step with reference_cast runtime_layout align phase addr length side layout_positive align_positive room witness
          (by simp only [info_eq]) as ⟨expected, expected_spec⟩
        have same := cast_unique runtime_layout addr.val length.val side actual expected actual_spec expected_spec
        subst expected
        cases actual with
        | Ok pair => rcases pair with ⟨elems, split⟩; simp [massert, WP.spec_ok]
        | Err error => cases error <;> simp [massert, WP.spec_ok]
    | SliceDst tail =>
      simp only [info_eq, bind_ok]
      simp only [info_eq] at positive
      have updated_eq : { runtime_layout with size_info := .SliceDst tail } = runtime_layout := by
        rw [← info_eq]
      rw [updated_eq]
      step as ⟨ending, ending_facts⟩
      cases ending with
      | none => simp [Option.isSome, WP.spec_ok]
      | some ending =>
        simp only [] at ending_facts
        simp only [Option.isSome, if_true, bne_iff_ne]
        split
        · rename_i stride_nonzero
          have stride : 0 < tail.elem_size.val := by scalar_tac
          have room : addr.val + length.val ≤ Usize.max := ending_facts.1
          step with Zerocopy.Proofs.Raw.validate_cast_spec runtime_layout addr length side layout_positive room
            (by simpa only [info_eq] using And.intro positive stride) as ⟨actual, actual_spec⟩
          step with reference_cast runtime_layout align phase addr length side layout_positive align_positive room witness
            (by simpa only [info_eq] using stride) as ⟨expected, expected_spec⟩
          have same := cast_unique runtime_layout addr.val length.val side actual expected actual_spec expected_spec
          subst expected
          cases actual with
          | Ok pair => rcases pair with ⟨elems, split⟩; simp [massert, WP.spec_ok]
          | Err error => cases error <;> simp [massert, WP.spec_ok]
        · simp only [WP.spec_ok]
  · simp only [WP.spec_ok]

end Zerocopy.Proofs.Raw.TailChecks

namespace Zerocopy.Proofs
open AeneasSpecs

theorem trailing_arithmetic_check_spec : Specs.trailing_arithmetic_check_spec := by
  unfold Specs.trailing_arithmetic_check_spec
  intros
  apply WP.spec_mono (Raw.TailChecks.trailing_arithmetic_check _ _ _ _ _)
  intro result facts
  exact ⟨(), rfl, trivial⟩

theorem layout_observations_check_spec : Specs.layout_observations_check_spec := by
  unfold Specs.layout_observations_check_spec
  intro runtime_layout align phase size addr length side runtime_value runtime_decoded
    align_value align_decoded phase_value phase_decoded size_value size_decoded
    addr_value addr_decoded length_value length_decoded side_value side_decoded
  have runtime_valid := (layout_valid_iff runtime_layout).mp ⟨runtime_value, runtime_decoded⟩
  have align_valid := (nonzero_valid_iff align).mp ⟨align_value, align_decoded⟩
  apply WP.spec_mono (Raw.TailChecks.layout_observations_check runtime_layout align phase size addr length side
    runtime_valid.1 align_valid)
  intro result facts
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
