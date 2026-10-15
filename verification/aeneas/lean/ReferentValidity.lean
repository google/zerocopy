/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Models
public import Zerocopy.Funs
public import Rust.Referent
@[expose] public section

/-!
The Rust validity markers describe permitted referent contents, not pointer
permissions. This adapter connects their exact extracted identities to the
shared byte-domain algebra. Physical and mathematical decoding must both
succeed for `Safe`; initialization alone does not construct a typed value.

A `View` names an available decoder from the retained model. Missing support
cannot supply a view, while an explicitly empty decoder can: an uninhabited
type has no safe representations, even when its width is zero. Laws quantify
over views and remain conditional on the documented Rust correspondence of
those decoders. They introduce no layout or inhabitedness axiom.

`AsInitialized` is not interpreted. The `forget` constructor
proves the state-independent weakening to `Uninit`. Every other supported
transfer needs one of the three modeled states and an ordinary checked proof.
-/

open Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Referent

abbrev Kind := ValidityMarker
abbrev SafeState := pointer.invariant.Safe
abbrev InitializedState := pointer.invariant.Initialized
abbrev UninitState := pointer.invariant.Uninit

def nativeKind : Kind → pointer.invariant.ValidityKind
  | .uninit => .Uninit
  | .asInitialized => .AsInitialized
  | .initialized => .Initialized
  | .safe => .Safe

/-- The retained type model supplies the marker's meaning. Check that the
actual Rust dictionary evaluates to that code; missing metadata is rejected. -/
def kindMatches (V : Type) [meaning : RustModel V]
    (kind : Result pointer.invariant.ValidityKind) : Prop :=
  ∃ marker, meaning.validityMarker = some marker ∧ kind = .ok (nativeKind marker)

def nativeState : Rust.Referent.State → Kind
  | .uninit => .uninit
  | .initialized => .initialized
  | .safe => .safe

/-- The decoder is not an independently selectable replacement for the model. -/
structure View {Raw : Type} (meaning : RustModel Raw) where
  decoder : BitDecoder Raw
  installed : meaning.representation = some decoder

/-- All representations accepted by both stages, without choosing an encoding. -/
def safeBytes {Raw : Type} (meaning : RustModel Raw) (bytes : List AMByte) : Prop :=
  ∃ decoder, meaning.representation = some decoder ∧
    ∃ raw value, decoder.run bytes = some raw ∧ meaning.decode raw = some value

theorem safeBytes_view {Raw : Type} (meaning : RustModel Raw) (view : View meaning)
    (bytes : List AMByte) :
    safeBytes meaning bytes ↔
      Rust.Referent.Safe view.decoder.asStorageDecoder meaning.decode () bytes := by
  constructor
  · rintro ⟨decoder, installed, raw, value, physical, mathematical⟩
    have same : decoder = view.decoder := Option.some.inj (installed.symm.trans view.installed)
    subst decoder
    exact ⟨raw, value, by simpa only [BitDecoder.run_asStorageDecoder] using physical,
      mathematical⟩
  · rintro ⟨raw, value, physical, mathematical⟩
    exact ⟨view.decoder, view.installed, raw, value,
      by simpa only [BitDecoder.run_asStorageDecoder] using physical, mathematical⟩

def transfer {Src Dst : Type} (source : RustModel Src) (destination : RustModel Dst)
    (sourceState destinationState : Rust.Referent.State) : Prop :=
  ∀ (sourceView : View source) (destinationView : View destination),
    Rust.Referent.Transfer sourceView.decoder.byteSize (safeBytes source) sourceState
      destinationView.decoder.byteSize (safeBytes destination) destinationState

/-- This is evidence of supported reasoning, not a false interpretation of an
unsupported state's byte domain. Forgetting a promise needs no such domain. -/
inductive Supports {Src Dst : Type} (source : RustModel Src) (destination : RustModel Dst) :
    Kind → Kind → Prop where
  | forget (kind : Kind) : Supports source destination kind .uninit
  | modeled (sourceState destinationState : Rust.Referent.State)
      (proof : transfer source destination sourceState destinationState) :
      Supports source destination (nativeState sourceState) (nativeState destinationState)

/-- All four original Rust type arguments retain their meanings. State
metadata is separate from the referent's physical and mathematical decoders. -/
def transmuteFrom (Src Dst SV DV : Type) [source : RustModel Src]
    [destination : RustModel Dst] [sourceState : RustModel SV]
    [destinationState : RustModel DV] : Prop :=
  ∃ first second, sourceState.validityMarker = some first ∧
    destinationState.validityMarker = some second ∧
    Supports source destination first second

/-- The source contract names exactly these two pairs. Even an accidental
equality of safe domains must not authorize `Safe` here. -/
def typeIndependentPair (SV DV : Type) : Prop :=
  (SV = pointer.invariant.Uninit ∧ DV = pointer.invariant.Uninit) ∨
  (SV = pointer.invariant.Initialized ∧ DV = pointer.invariant.Initialized)

theorem safe_to_initialized (Src Dst : Type) [source : RustModel Src]
    [destination : RustModel Dst] (initialized : RustModel.initializedRepresentation Src) :
    transmuteFrom Src Dst SafeState InitializedState := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  apply Supports.modeled .safe .initialized
  intro sv dv same bytes admitted
  refine ⟨admitted.1.trans same, ?_⟩
  obtain ⟨decoder, installed, raw, _, physical, _⟩ := admitted.2
  have initializes : decoder.Initialized := by
    simpa only [RustModel.initializedRepresentation, installed] using initialized
  exact initializes bytes raw physical

theorem initialized_to_safe (Src Dst : Type) [source : RustModel Src]
    [destination : RustModel Dst] (complete : RustModel.completeRepresentation Dst) :
    transmuteFrom Src Dst InitializedState SafeState := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  apply Supports.modeled .initialized .safe
  intro sv dv same bytes admitted
  refine ⟨admitted.1.trans same, dv.decoder, dv.installed, ?_⟩
  have completes := complete
  simp only [RustModel.completeRepresentation, dv.installed] at completes
  exact completes bytes (admitted.1.trans same) admitted.2

theorem initialized_identity (Src Dst : Type) [RustModel Src] [RustModel Dst] :
    transmuteFrom Src Dst InitializedState InitializedState := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  exact Supports.modeled .initialized .initialized
    (fun sv dv => Rust.Referent.initialized_identity _ _ _ _)

theorem forget (Src Dst V : Type) [RustModel Src] [RustModel Dst]
    [meaning : RustModel V] (known : ∃ marker, meaning.validityMarker = some marker) :
    transmuteFrom Src Dst V UninitState := by
  obtain ⟨marker, identified⟩ := known
  exact ⟨marker, .uninit, identified, rfl, Supports.forget marker⟩

/-- Wrapper proofs reduce to their two actual decoder domains. The theorem
does not assume a reversible mathematical model or a canonical byte encoding. -/
theorem safe_transfer_of_implication (Src Dst : Type) [source : RustModel Src]
    [destination : RustModel Dst]
    (preserves : ∀ bytes, safeBytes source bytes → safeBytes destination bytes) :
    transmuteFrom Src Dst SafeState SafeState := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  exact Supports.modeled .safe .safe (fun sv dv =>
    Rust.Referent.safe_transfer_of_implication _ _ _ _ (fun bytes _ => preserves bytes))

theorem nativeState_injective : Function.Injective nativeState := by
  intro left right same
  cases left <;> cases right <;> simp_all [nativeState]

/-- Eliminate supported reasoning into a real byte-domain implication. This
also justifies forgetting any modeled source state without an interpretation
of the unsupported states. -/
theorem Supports.sound {Src Dst : Type} {source : RustModel Src}
    {destination : RustModel Dst} {first second : Kind}
    (supported : Supports source destination first second) :
    ∀ sourceState destinationState,
      first = nativeState sourceState → second = nativeState destinationState →
      transfer source destination sourceState destinationState := by
  cases supported with
  | forget kind =>
    intro sourceState destinationState _ destinationIs
    cases destinationState <;> simp only [nativeState] at destinationIs
    · intro sv dv
      exact Rust.Referent.to_uninit _ _ _ _ sourceState
    · contradiction
    · contradiction
  | modeled first second proof =>
    intro sourceState destinationState sourceIs destinationIs
    cases nativeState_injective sourceIs
    cases nativeState_injective destinationIs
    exact proof

/-- Expose the actual content implication, independently of its evidence
constructors. The required-contract checks consume this theorem. -/
theorem transmute_sound (Src Dst SV DV : Type) [source : RustModel Src]
    [destination : RustModel Dst] [sourceMeaning : RustModel SV]
    [destinationMeaning : RustModel DV] (sourceState destinationState : Rust.Referent.State)
    (sourceCode : sourceMeaning.validityMarker = some (nativeState sourceState))
    (destinationCode : destinationMeaning.validityMarker = some (nativeState destinationState))
    (proof : transmuteFrom Src Dst SV DV) :
    transfer source destination sourceState destinationState := by
  obtain ⟨first, second, sourceIs, destinationIs, supported⟩ := proof
  exact supported.sound sourceState destinationState
    (Option.some.inj (sourceIs.symm.trans sourceCode))
    (Option.some.inj (destinationIs.symm.trans destinationCode))

theorem safe_transfer_iff (Src Dst : Type) [source : RustModel Src]
    [destination : RustModel Dst] :
    transmuteFrom Src Dst SafeState SafeState ↔ transfer source destination .safe .safe :=
  ⟨transmute_sound Src Dst SafeState SafeState .safe .safe rfl rfl,
    fun proof => ⟨.safe, .safe, rfl, rfl, Supports.modeled .safe .safe proof⟩⟩

/-- Equal source and intermediate widths make conditional transfers compose.
The final width remains guarded by the result's own implication. -/
theorem safe_trans (Src Mid Dst : Type) [source : RustModel Src]
    [middle : RustModel Mid] [destination : RustModel Dst]
    (first : transmuteFrom Src Mid SafeState SafeState)
    (second : transmuteFrom Mid Dst SafeState SafeState)
    (same : RustModel.sameSize Src Mid) :
    transmuteFrom Src Dst SafeState SafeState := by
  apply (safe_transfer_iff Src Dst).mpr
  intro sourceView destinationView
  obtain ⟨width, _, _, sourceSize, middleSize⟩ := same
  cases available : middle.representation with
  | none => simp [available] at middleSize
  | some decoder =>
    simp only [sourceView.installed, Option.map_some, Option.some.injEq] at sourceSize
    simp only [available, Option.map_some, Option.some.injEq] at middleSize
    exact Rust.Referent.transfer_trans _ _ _ _ _ _ .safe .safe .safe
      ((safe_transfer_iff Src Mid).mp first sourceView ⟨decoder, available⟩)
      ((safe_transfer_iff Mid Dst).mp second ⟨decoder, available⟩ destinationView)
      (sourceSize.trans middleSize.symm)

end Zerocopy.Referent
