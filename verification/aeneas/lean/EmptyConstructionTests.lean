/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
import all RustModel
import all ModelPrelude
@[expose] public section

/-!
Empty storage supplies no constructor permission or library invariant. These
model controls distinguish a supplied Lean inhabitant, an explicit physical
representation decoder, and admission by the retained mathematical provider.
They execute no invalid Rust construction.
-/
open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace EmptyConstructionTests

-- An uninhabited raw carrier needs no fabricated inhabitant to fail closed.
@[reducible] def modelEmpty : RustModel Empty where
  Model := Unit
  decode raw := nomatch raw

example : ¬ @RustModel.initializedRepresentation Empty modelEmpty := by
  simp [RustModel.initializedRepresentation, RustModel.representation]

example : modelEmpty.decodeBitsResult [] = .fail .undef := rfl
example : modelEmpty.decodeBytesResult [] = .fail .undef := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode]
example : ¬ WP.spec (modelEmpty.decodeBytesResult []) (fun _ => True) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation]
example : ¬ WP.dspec (modelEmpty.decodeBytesResult []) (fun _ => True) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation]

inductive StateToken where
  | mk
  deriving Inhabited

-- Lean's Inhabited instance alone does not install physical semantics. This
-- provider even accepts its raw value mathematically, but byte construction
-- still has no physical representation decoder.
@[reducible] def inhabitedOnly : RustModel StateToken where
  Model := Unit
  decode _ := some ()

example : ¬ @RustModel.initializedRepresentation StateToken inhabitedOnly := by
  simp [RustModel.initializedRepresentation, RustModel.representation]

example : (default : StateToken) = .mk := rfl
example : inhabitedOnly.decode .mk = some () := rfl
example : inhabitedOnly.decodeBytesResult [] = .fail .undef := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode]

-- Model an external admission condition explicitly. The physical decoder may
-- supply the unit-like raw constructor while the full provider still rejects
-- that value when the required external state is absent.
@[reducible] def stateModel (masked : Bool) : RustModel StateToken where
  Model := Unit
  decode _ := if masked then some () else none
  representation := some (emptyDecoder StateToken.mk)

example : (stateModel false).decodeBitsResult [] = .ok StateToken.mk := rfl
example : (stateModel true).decodeBytesResult [] = .ok () := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode,
    emptyDecoder, BitDecoder.run]
example : (stateModel false).decodeBytesResult [] = .fail .undef := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode,
    emptyDecoder, BitDecoder.run]
example : ¬ WP.spec ((stateModel false).decodeBytesResult []) (fun _ => True) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode,
    emptyDecoder, BitDecoder.run]
example : ¬ WP.dspec ((stateModel false).decodeBytesResult []) (fun _ => True) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode,
    emptyDecoder, BitDecoder.run]

-- Both states satisfy the physical initialization law. That law cannot prove
-- admission by the library provider, let alone a Rust constructor precondition.
example (masked : Bool) :
    @RustModel.initializedRepresentation StateToken (stateModel masked) :=
  emptyDecoder_initialized StateToken.mk

-- PhantomData stores no T. Its explicit raw constructor and empty decoder
-- therefore need neither a T value nor a RustModel T, even for uninhabited T.
example : (modelPhantomData Empty).decodeBitsResult [] =
    .ok (Zerocopy.core.marker.PhantomData.mk : Zerocopy.core.marker.PhantomData Empty) := rfl
example : (modelPhantomData Empty).decodeBytesResult [] = .ok () := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.decode,
    emptyDecoder, BitDecoder.run]

end EmptyConstructionTests
