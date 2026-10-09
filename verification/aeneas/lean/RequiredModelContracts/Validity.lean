/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredContracts
public import Proofs.Validity
public import Obligations.Validity
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- Supply an independent admission witness for EVERY raw input. The subsequent
-- implications consume only the authored postcondition, for any execution.
@[contract_simps] theorem required_bool_encoding (byte : U8) (run : Result Bool)
    (provided : Specs.bool_encoding_spec_contract byte run) :
    Obligations.bool_encoding_spec_contract byte run := by
  apply WP.spec_mono (provided (unsignedWord byte) rfl)
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_nonzero_encoding (n : Usize) (run : Result Bool)
    (provided : Specs.nonzero_encoding_spec_contract n run) :
    Obligations.nonzero_encoding_spec_contract n run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl)
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_checked_nonzero (n : Usize)
    (run : Result (Option (core.num.nonzero.NonZero Usize
      core.num.niche_types.NonZeroUsizeInner)))
    (provided : Specs.checked_nonzero_spec_contract n run) :
    Obligations.checked_nonzero_spec_contract n run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl)
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_checked_bool_pair (bytes : Aeneas.Std.Array U8 2#usize)
    (run : Result (Option (Aeneas.Std.Array Bool 2#usize)))
    (provided : Specs.checked_bool_pair_spec_contract bytes run) :
    Obligations.checked_bool_pair_spec_contract bytes run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes))
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_bool_slice_valid (bytes : Slice U8) (run : Result Bool)
    (provided : Specs.bool_slice_valid_spec_contract bytes run) :
    Obligations.bool_slice_valid_spec_contract bytes run := by
  apply WP.spec_mono (provided (byteSlice bytes) (decode_byte_slice bytes))
  rintro out ⟨_, _, facts⟩
  exact facts

end Zerocopy.Proofs
