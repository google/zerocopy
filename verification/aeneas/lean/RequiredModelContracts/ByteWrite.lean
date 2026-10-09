/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredContracts
public import Proofs.ByteWrite
public import Obligations.ByteWrite
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- Challenge each contract with an arbitrary execution outcome. Using only the
-- actual function's good behavior here could hide an accidentally weaker spec.
@[contract_simps] theorem required_write_exact (src dst : Slice U8)
    (run : Result (Bool × Slice U8))
    (provided : Specs.write_exact_spec_contract src dst run) :
    Obligations.write_exact_spec_contract src dst run := by
  apply WP.spec_mono (provided (byteSlice src) (decode_byte_slice src)
    (byteSlice dst) (decode_byte_slice dst))
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_write_prefix (src dst : Slice U8)
    (run : Result (Bool × Slice U8))
    (provided : Specs.write_prefix_spec_contract src dst run) :
    Obligations.write_prefix_spec_contract src dst run := by
  apply WP.spec_mono (provided (byteSlice src) (decode_byte_slice src)
    (byteSlice dst) (decode_byte_slice dst))
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_write_suffix (src dst : Slice U8)
    (run : Result (Bool × Slice U8))
    (provided : Specs.write_suffix_spec_contract src dst run) :
    Obligations.write_suffix_spec_contract src dst run := by
  apply WP.spec_mono (provided (byteSlice src) (decode_byte_slice src)
    (byteSlice dst) (decode_byte_slice dst))
  rintro out ⟨_, _, facts⟩
  exact facts

@[contract_simps] theorem required_write_be_word_prefix (n : U16) (dst : Slice U8)
    (run : Result (Bool × Slice U8))
    (provided : Specs.write_be_word_prefix_spec_contract n dst run) :
    Obligations.write_be_word_prefix_spec_contract n dst run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl
    (byteSlice dst) (decode_byte_slice dst))
  rintro out ⟨_, _, facts⟩
  exact facts

end Zerocopy.Proofs
