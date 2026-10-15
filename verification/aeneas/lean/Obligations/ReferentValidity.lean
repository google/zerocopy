/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import TraitLaws
public import Rust.Referent
@[expose] public section

/-!
The expectations below state the byte-content implication directly. Each safe
representation must pass the installed physical decoder and the retained
mathematical decoder. The same byte list and its width survive the transfer;
the width comparison remains a guard. These expectations concern contents only.
-/
open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Obligations

def stateCode : Rust.Referent.State → ValidityMarker
  | .uninit => .uninit
  | .initialized => .initialized
  | .safe => .safe

def contents {Raw : Type} (meaning : RustModel Raw) (physical : BitDecoder Raw)
    (state : Rust.Referent.State) (bytes : List AMByte) : Prop :=
  match state with
  | .uninit => True
  | .initialized => Rust.Storage.Initialized bytes
  | .safe => ∃ raw mathematical,
      physical.run bytes = some raw ∧ meaning.decode raw = some mathematical

def contentTransfer {Src Dst : Type} (source : RustModel Src)
    (sourcePhysical : BitDecoder Src) (destination : RustModel Dst)
    (destinationPhysical : BitDecoder Dst)
    (sourceState destinationState : Rust.Referent.State) : Prop :=
  sourcePhysical.byteSize = destinationPhysical.byteSize → ∀ bytes,
    bytes.length = sourcePhysical.byteSize → contents source sourcePhysical sourceState bytes →
    bytes.length = destinationPhysical.byteSize ∧
      contents destination destinationPhysical destinationState bytes

def installedContentTransfer {Src Dst : Type} (source : RustModel Src)
    (destination : RustModel Dst) (sourceState destinationState : Rust.Referent.State) : Prop :=
  ∀ sourcePhysical destinationPhysical,
    source.representation = some sourcePhysical →
    destination.representation = some destinationPhysical →
    contentTransfer source sourcePhysical destination destinationPhysical sourceState destinationState

def require_transfer_spec_contract (Src Dst SV DV : Type)
    (dictionary : pointer.transmute.TransmuteFrom Dst Src SV DV) (run : Result Unit) : Prop :=
  ∀ [source : RustModel Src] [destination : RustModel Dst]
    [sourceMeaning : RustModel SV] [destinationMeaning : RustModel DV],
    TraitLaws.transmute_from Dst Src SV DV dictionary →
    run ⦃ _ => ∀ sourceState destinationState,
      sourceMeaning.validityMarker = some (stateCode sourceState) →
      destinationMeaning.validityMarker = some (stateCode destinationState) →
      installedContentTransfer source destination sourceState destinationState ⦄

def require_transfer_spec : Prop :=
  ∀ (Src Dst SV DV : Type) (dictionary : pointer.transmute.TransmuteFrom Dst Src SV DV),
    require_transfer_spec_contract Src Dst SV DV dictionary
      (pointer.referent_checks.require_transfer dictionary)

def require_type_independent_spec_contract (Src Dst SV DV : Type)
    (dictionary : pointer.invariant.CastableFrom Dst Src SV DV) (run : Result Unit) : Prop :=
  ∀ [RustModel Src] [RustModel Dst] [RustModel SV] [RustModel DV],
    TraitLaws.castable_from Dst Src SV DV dictionary →
    run ⦃ _ =>
      (SV = pointer.invariant.Uninit ∧ DV = pointer.invariant.Uninit) ∨
      (SV = pointer.invariant.Initialized ∧ DV = pointer.invariant.Initialized) ⦄

def require_type_independent_spec : Prop :=
  ∀ (Src Dst SV DV : Type) (dictionary : pointer.invariant.CastableFrom Dst Src SV DV),
    require_type_independent_spec_contract Src Dst SV DV dictionary
      (pointer.referent_checks.require_type_independent dictionary)

def compose_safe_transfers_spec_contract (Src Mid Dst : Type)
    (first : pointer.transmute.TransmuteFrom Mid Src pointer.invariant.Safe pointer.invariant.Safe)
    (second : pointer.transmute.TransmuteFrom Dst Mid pointer.invariant.Safe pointer.invariant.Safe)
    (run : Result Unit) : Prop :=
  ∀ [source : RustModel Src] [_middle : RustModel Mid] [destination : RustModel Dst],
    TraitLaws.transmute_from Mid Src pointer.invariant.Safe pointer.invariant.Safe first →
    TraitLaws.transmute_from Dst Mid pointer.invariant.Safe pointer.invariant.Safe second →
    RustModel.sameSize Src Mid →
    run ⦃ _ => installedContentTransfer source destination .safe .safe ⦄

def compose_safe_transfers_spec : Prop :=
  ∀ (Src Mid Dst : Type)
    (first : pointer.transmute.TransmuteFrom Mid Src pointer.invariant.Safe pointer.invariant.Safe)
    (second : pointer.transmute.TransmuteFrom Dst Mid pointer.invariant.Safe pointer.invariant.Safe),
    compose_safe_transfers_spec_contract Src Mid Dst first second
      (pointer.referent_checks.compose_safe_transfers first second)

def concrete_transfers_spec_contract (run : Result Unit) : Prop :=
  run ⦃ _ =>
    contentTransfer modelBool boolDecoder (modelUScalar .U8) u8BitDecoder .safe .initialized ∧
    contentTransfer (modelUScalar .U8) u8BitDecoder modelBool boolDecoder .initialized .uninit ∧
    ((pointer.invariant.Initialized = pointer.invariant.Uninit ∧
      pointer.invariant.Initialized = pointer.invariant.Uninit) ∨
     (pointer.invariant.Initialized = pointer.invariant.Initialized ∧
      pointer.invariant.Initialized = pointer.invariant.Initialized)) ⦄

def concrete_transfers_spec : Prop :=
  concrete_transfers_spec_contract pointer.referent_checks.concrete_transfers

end Zerocopy.Obligations
