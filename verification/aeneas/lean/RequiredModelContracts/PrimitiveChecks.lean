/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredModelContracts
@[expose] public section

/-!
The independent expectations require successful execution on the original
Rust input domains. These implications check that the generated unit-returning
specifications retain that promise for an arbitrary execution outcome.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[contract_simps] theorem required_primitive_layout_checks (T : Type)
    (run : Result Unit) (provided : Specs.primitive_layout_checks_spec_contract T run) :
    Obligations.primitive_layout_checks_spec_contract T run := by
  intro validity
  apply WP.spec_mono (provided)
  intro _ _
  trivial

@[contract_simps] theorem required_empty_layout_checks (repr_align : Option NonZeroUsize)
    (run : Result Unit) (provided : Specs.empty_layout_checks_spec_contract repr_align run) :
    Obligations.empty_layout_checks_spec_contract repr_align run := by
  intro positive
  have admitted : isValid repr_align := by
    rw [option_valid_iff]
    intro align member
    exact (nonzero_valid_iff align).mpr (positive align member)
  obtain ⟨value, decoded⟩ := admitted
  apply WP.spec_mono (provided value decoded)
  intro _ _
  trivial

end Zerocopy.Proofs
