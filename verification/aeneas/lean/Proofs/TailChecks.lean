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

end Zerocopy.Proofs.Raw.TailChecks

namespace Zerocopy.Proofs
open AeneasSpecs

theorem trailing_arithmetic_check_spec : Specs.trailing_arithmetic_check_spec := by
  unfold Specs.trailing_arithmetic_check_spec
  intros
  apply WP.spec_mono (Raw.TailChecks.trailing_arithmetic_check _ _ _ _ _)
  intro result facts
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
