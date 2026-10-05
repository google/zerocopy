/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Obligations.Allocation
public import Specs
public import MathViews
public import RequiredModelContracts.PrimitiveChecks
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Zerocopy.Proofs

/- Consume the authored promise for this arbitrary outcome. Neither adapter
executes the implementation or uses its correctness theorem.
-/
@[contract_simps] theorem required_allocation_prepare (size : Option Usize)
    (align : NonZeroUsize) (run : Result (Option (Usize × NonZeroUsize)))
    (provided : Specs.allocation_prepare_spec_contract size align run) :
    Obligations.allocation_prepare_spec_contract size align run := by
  intro positive
  have size_valid : isValid size := by simp
  obtain ⟨size_value, size_decoded⟩ := size_valid
  let align_value : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have align_decoded := (decodeNonZeroUScalar_iff align align_value).mpr rfl
  apply WP.spec_mono (provided size_value size_decoded align_value align_decoded)
  rintro result ⟨_value, _decoded, facts⟩
  exact facts

@[contract_simps] theorem required_allocation_preparation_check (size : Option Usize)
    (align : NonZeroUsize) (run : Result Unit)
    (provided : Specs.allocation_preparation_check_spec_contract size align run) :
    Obligations.allocation_preparation_check_spec_contract size align run := by
  intro positive
  have size_valid : isValid size := by simp
  obtain ⟨size_value, size_decoded⟩ := size_valid
  let align_value : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have align_decoded := (decodeNonZeroUScalar_iff align align_value).mpr rfl
  apply WP.spec_mono (provided size_value size_decoded align_value align_decoded)
  rintro result ⟨_value, _decoded, facts⟩
  trivial

@[contract_simps] theorem required_allocation_size_check (runtime_layout : layout.DstLayout)
    (rounding_align : NonZeroUsize) (phase metadata : Usize) (run : Result Unit)
    (provided : Specs.allocation_size_check_spec_contract
      runtime_layout rounding_align phase metadata run) :
    Obligations.allocation_size_check_spec_contract
      runtime_layout rounding_align phase metadata run := by
  intro layout_positive layout_canonical rounding_positive
  obtain ⟨layout_value, layout_decoded⟩ :=
    layout_admitted_of_canonical runtime_layout layout_positive layout_canonical
  let rounding_value : NonZeroUsizeValue := ⟨unsignedWord rounding_align.val, rounding_positive⟩
  have rounding_decoded := (decodeNonZeroUScalar_iff rounding_align rounding_value).mpr rfl
  apply WP.spec_mono (provided layout_value layout_decoded rounding_value rounding_decoded
    (unsignedWord phase) rfl (unsignedWord metadata) rfl)
  intro result facts
  trivial

end Zerocopy.Proofs
