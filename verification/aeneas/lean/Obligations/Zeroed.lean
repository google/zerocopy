/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import TraitLaws
public import RustRepresentation
@[expose] public section

/-!
The independent outcome family requires successful execution, an available
physical decoder accepting the initialized all-zero representation, and an
accepted mathematical value through the retained provider. It does not define
the expected outcome in terms of the extracted default method or its guarded
implementation. The concrete proposition specializes the same family to that
method only after the arbitrary-outcome expectation has been stated.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Obligations

def new_zeroed_spec_contract (Self : Type) (meaning : RustModel Self)
    (run : Result Self) : Prop :=
  ∀ (dictionary : FromZeros Self) [_law : @TraitLaws.from_zeros_valid Self dictionary meaning],
    ∃ raw value decoder, run = .ok raw ∧ meaning.representation = some decoder ∧
      decoder.run (List.replicate decoder.byteSize (Rust.Storage.AMByte.init 0)) = some raw ∧
      meaning.decode raw = some value

def new_zeroed_spec : Prop :=
  ∀ (Self : Type) [_meaning : RustModel Self],
    new_zeroed_spec_contract Self _meaning (FromZeros.new_zeroed.default Self)

end Zerocopy.Obligations
