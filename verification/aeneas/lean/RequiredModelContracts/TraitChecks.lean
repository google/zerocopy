/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.TraitChecks
public import MathViews
@[expose] public section

/-!
The adapters recover raw observations from a provided contract for one arbitrary
outcome. Generic types need no stored-value model restrictions: the identity
model instantiates the universally quantified model dictionary. Trait evidence
is supplied only for the original computational dictionary, never for a
substitute implementation. None of these adapters executes the function.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[contract_simps] theorem required_byte_codec_roundtrip (C : Type)
    (dictionary : trait_checks.ByteCodec C) (byte : U8) (run : Result U8)
    (provided : Specs.byte_codec_roundtrip_spec_contract C dictionary byte run) :
    Obligations.byte_codec_roundtrip_spec_contract C dictionary byte run := by
  intro law
  letI : RustModel C := { Model := C, «decode» := some }
  letI := law
  apply WP.spec_mono (provided (unsignedWord byte) rfl)
  rintro result ⟨mathematical, decoded, same⟩
  apply UScalar.eq_of_val_eq
  exact ((decodeUScalar_iff result mathematical).mp decoded).trans
    (congrArg UnsignedWord.value same)

@[contract_simps] theorem required_forwarded_byte_codec (byte : U8) (run : Result U8)
    (provided : Specs.forwarded_byte_codec_spec_contract byte run) :
    Obligations.forwarded_byte_codec_spec_contract byte run := by
  apply WP.spec_mono (provided (unsignedWord byte) rfl)
  rintro result ⟨mathematical, decoded, same⟩
  apply UScalar.eq_of_val_eq
  exact ((decodeUScalar_iff result mathematical).mp decoded).trans
    (congrArg UnsignedWord.value same)

end Zerocopy.Proofs
