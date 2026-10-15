/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.Zeroed
public import RequiredContracts
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- Compare arbitrary outcomes without assuming the function's own correctness.
-- The expectation states each decoding stage instead of repeating zeroedValue.
@[contract_simps] theorem required_new_zeroed (Self : Type) [meaning : RustModel Self]
    (run : Result Self) (provided : Specs.new_zeroed_spec_contract Self run) :
    Obligations.new_zeroed_spec_contract Self meaning run := by
  intro dictionary law
  obtain ⟨raw, executed, mathematical, decoded, zeroed⟩ :=
    (WP.spec_equiv_exists run _).mp (provided dictionary)
  obtain ⟨decoder, available, physical, _⟩ :=
    (meaning.zeroedResult_eq_ok_iff raw).mp zeroed
  exact ⟨raw, mathematical, decoder, executed, available, physical, decoded⟩


end Zerocopy.Proofs
