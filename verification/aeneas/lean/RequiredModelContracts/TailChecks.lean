/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.TailChecks
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs
set_option linter.unusedVariables false

/- Recover the full raw domain from the actual decoders before consuming the
supplied arbitrary-outcome contract. These adapters do not run either check.
-/
@[contract_simps] theorem required_trailing_arithmetic_check
    (tail : layout.TrailingSliceLayout Usize) (align : NonZeroUsize)
    (phase elems budget : Usize) (run : Result Unit)
    (provided : Specs.trailing_arithmetic_check_spec_contract tail align phase elems budget run) :
    Obligations.trailing_arithmetic_check_spec_contract tail align phase elems budget run := by
  intro positive align_positive
  have valid_tail : isValid tail := (trailing_valid_iff tail).mpr ⟨by simp, positive⟩
  obtain ⟨tail_value, decoded_tail⟩ := valid_tail
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, align_positive⟩
  have decoded_align := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided tail_value decoded_tail av decoded_align
    (unsignedWord phase) rfl (unsignedWord elems) rfl (unsignedWord budget) rfl)
  rintro result ⟨value, decoded, facts⟩
  trivial

@[contract_simps] theorem required_layout_observations_check
    (runtime_layout : layout.DstLayout) (align : NonZeroUsize)
    (phase size addr length : Usize) (side : layout.CastType) (run : Result Unit)
    (provided : Specs.layout_observations_check_spec_contract
      runtime_layout align phase size addr length side run) :
    Obligations.layout_observations_check_spec_contract
      runtime_layout align phase size addr length side run := by
  intro valid_runtime align_positive
  obtain ⟨layout_value, decoded_layout⟩ := (layout_valid_iff runtime_layout).mpr valid_runtime
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, align_positive⟩
  have decoded_align := (decodeNonZeroUScalar_iff align av).mpr rfl
  obtain ⟨side_value, decoded_side⟩ := (cast_type_valid_iff side).mpr trivial
  apply WP.spec_mono (provided layout_value decoded_layout av decoded_align
    (unsignedWord phase) rfl (unsignedWord size) rfl (unsignedWord addr) rfl
    (unsignedWord length) rfl side_value decoded_side)
  rintro result ⟨value, decoded, facts⟩
  trivial

end Zerocopy.Proofs
