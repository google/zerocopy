/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.ReferentValidity
public import ReferentValidity
@[expose] public section

/-!
These adapters consume a supplied contract for an arbitrary outcome. They keep
the original dictionaries and all retained providers, then recover the direct
byte-content expectation. No adapter executes an extracted function.
-/
open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Proofs

private theorem safeBytes_contents {Raw : Type} (meaning : RustModel Raw)
    (physical : BitDecoder Raw) (installed : meaning.representation = some physical)
    (bytes : List AMByte) :
    Referent.safeBytes meaning bytes ↔ Obligations.contents meaning physical .safe bytes := by
  constructor
  · rintro ⟨decoder, available, raw, mathematical, language, decoded⟩
    have same : decoder = physical := Option.some.inj (available.symm.trans installed)
    subst decoder
    exact ⟨raw, mathematical, language, decoded⟩
  · rintro ⟨raw, mathematical, language, decoded⟩
    exact ⟨physical, installed, raw, mathematical, language, decoded⟩

private theorem allowed_contents {Raw : Type} (meaning : RustModel Raw)
    (physical : BitDecoder Raw) (installed : meaning.representation = some physical)
    (state : Rust.Referent.State) (bytes : List AMByte) :
    Rust.Referent.Allowed physical.byteSize (Referent.safeBytes meaning) state bytes ↔
      bytes.length = physical.byteSize ∧ Obligations.contents meaning physical state bytes := by
  cases state with
  | uninit => rfl
  | initialized => rfl
  | safe => exact and_congr_right (fun _ => safeBytes_contents meaning physical installed bytes)

private theorem contentTransfer_of_adapter {Src Dst : Type}
    (source : RustModel Src) (destination : RustModel Dst)
    (sourceState destinationState : Rust.Referent.State)
    (transfer : Referent.transfer source destination sourceState destinationState) :
    Obligations.installedContentTransfer source destination sourceState destinationState := by
  intro sourcePhysical destinationPhysical sourceInstalled destinationInstalled same bytes width content
  have result := transfer ⟨sourcePhysical, sourceInstalled⟩
    ⟨destinationPhysical, destinationInstalled⟩ same bytes
    ((allowed_contents source sourcePhysical sourceInstalled sourceState bytes).mpr ⟨width, content⟩)
  exact (allowed_contents destination destinationPhysical destinationInstalled destinationState bytes).mp result

@[contract_simps] theorem required_require_transfer (Src Dst SV DV : Type)
    (dictionary : pointer.transmute.TransmuteFrom Dst Src SV DV) (run : Result Unit)
    (provided : Specs.require_transfer_spec_contract Src Dst SV DV dictionary run) :
    Obligations.require_transfer_spec_contract Src Dst SV DV dictionary run := by
  intro source destination sourceMeaning destinationMeaning law
  letI := law
  apply WP.spec_mono provided
  rintro _ ⟨_, _, transfer⟩ sourceState destinationState sourceCode destinationCode
  apply contentTransfer_of_adapter source destination sourceState destinationState
  apply Referent.transmute_sound Src Dst SV DV sourceState destinationState
  · cases sourceState <;> exact sourceCode
  · cases destinationState <;> exact destinationCode
  · exact transfer

@[contract_simps] theorem required_require_type_independent (Src Dst SV DV : Type)
    (dictionary : pointer.invariant.CastableFrom Dst Src SV DV) (run : Result Unit)
    (provided : Specs.require_type_independent_spec_contract Src Dst SV DV dictionary run) :
    Obligations.require_type_independent_spec_contract Src Dst SV DV dictionary run := by
  intro source destination sourceMeaning destinationMeaning law
  letI := law
  apply WP.spec_mono provided
  rintro _ ⟨_, _, pair⟩
  exact pair

@[contract_simps] theorem required_compose_safe_transfers (Src Mid Dst : Type)
    (first : pointer.transmute.TransmuteFrom Mid Src pointer.invariant.Safe pointer.invariant.Safe)
    (second : pointer.transmute.TransmuteFrom Dst Mid pointer.invariant.Safe pointer.invariant.Safe)
    (run : Result Unit)
    (provided : Specs.compose_safe_transfers_spec_contract Src Mid Dst first second run) :
    Obligations.compose_safe_transfers_spec_contract Src Mid Dst first second run := by
  intro source middle destination firstLaw secondLaw same
  letI := firstLaw
  letI := secondLaw
  apply WP.spec_mono (provided same)
  rintro _ ⟨_, _, transfer⟩
  apply contentTransfer_of_adapter source destination .safe .safe
  exact Referent.transmute_sound Src Dst pointer.invariant.Safe pointer.invariant.Safe
    .safe .safe rfl rfl transfer

@[contract_simps] theorem required_concrete_transfers (run : Result Unit)
    (provided : Specs.concrete_transfers_spec_contract run) :
    Obligations.concrete_transfers_spec_contract run := by
  apply WP.spec_mono provided
  rintro _ ⟨_, _, first, second, pair⟩
  refine ⟨?_, ?_, pair⟩
  · exact contentTransfer_of_adapter modelBool (modelUScalar .U8) .safe .initialized
      (Referent.transmute_sound Bool U8 pointer.invariant.Safe pointer.invariant.Initialized
        .safe .initialized rfl rfl first) boolDecoder u8BitDecoder rfl rfl
  · exact contentTransfer_of_adapter (modelUScalar .U8) modelBool .initialized .uninit
      (Referent.transmute_sound U8 Bool pointer.invariant.Initialized pointer.invariant.Uninit
        .initialized .uninit rfl rfl second) u8BitDecoder boolDecoder rfl rfl

end Zerocopy.Proofs
