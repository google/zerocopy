/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredContracts
public import Specs
public import Proofs.SafetyChecks
public import Obligations.SafetyChecks
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- These implications quantify over an arbitrary execution. They do not use
-- the successful behavior of the extracted caller to strengthen its contract.
@[contract_simps] theorem required_checked_bool (byte : U8)
    (run : Result (Option Bool))
    (provided : Specs.checked_bool_spec_contract byte run) :
    Obligations.checked_bool_spec_contract byte run := by
  apply WP.spec_mono (provided (unsignedWord byte) rfl)
  rintro output ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_checked_copy (src dst : Slice U8)
    (run : Result (Bool × Slice U8))
    (provided : Specs.checked_copy_spec_contract src dst run) :
    Obligations.checked_copy_spec_contract src dst run := by
  apply WP.spec_mono (provided (byteSlice src) (decode_byte_slice src)
    (byteSlice dst) (decode_byte_slice dst))
  rintro output ⟨_, _, facts⟩
  exact facts

end Zerocopy.Proofs
