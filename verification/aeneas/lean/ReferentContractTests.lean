/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
import all Proofs.ReferentValidity
import RequiredContracts
import RequiredModelContracts.ReferentValidity
import all ModelPrelude

/-!
These checks protect the meanings behind the inline invariants. A validity
marker is an empty Rust type with a type-level code, not a value constructor.
Its actual associated constant must agree with that code. Unknown metadata
and missing physical decoding remain separate failures.
-/

open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.ReferentTests

-- Pin constants directly, independently of the code-to-KIND conversion helper.
example : pointer.invariant.Uninit.Insts.ZerocopyPointerInvariantValidity.KIND =
    pointer.invariant.ValidityKind.Uninit := by
  simp [pointer.invariant.Uninit.Insts.ZerocopyPointerInvariantValidity.KIND]

example : pointer.invariant.AsInitialized.Insts.ZerocopyPointerInvariantValidity.KIND =
    pointer.invariant.ValidityKind.AsInitialized := by
  simp [pointer.invariant.AsInitialized.Insts.ZerocopyPointerInvariantValidity.KIND]

example : pointer.invariant.Initialized.Insts.ZerocopyPointerInvariantValidity.KIND =
    pointer.invariant.ValidityKind.Initialized := by
  simp [pointer.invariant.Initialized.Insts.ZerocopyPointerInvariantValidity.KIND]

example : pointer.invariant.Safe.Insts.ZerocopyPointerInvariantValidity.KIND =
    pointer.invariant.ValidityKind.Safe := by
  simp [pointer.invariant.Safe.Insts.ZerocopyPointerInvariantValidity.KIND]

example : (inferInstance : RustModel pointer.invariant.Uninit).validityMarker =
    some .uninit := rfl
example : (inferInstance : RustModel pointer.invariant.AsInitialized).validityMarker =
    some .asInitialized := rfl
example : (inferInstance : RustModel pointer.invariant.Initialized).validityMarker =
    some .initialized := rfl
example : (inferInstance : RustModel pointer.invariant.Safe).validityMarker =
    some .safe := rfl

-- These providers have not created values of the empty marker carriers.
example (raw : pointer.invariant.Uninit) : False := nomatch raw
example (raw : pointer.invariant.AsInitialized) : False := nomatch raw
example (raw : pointer.invariant.Initialized) : False := nomatch raw
example (raw : pointer.invariant.Safe) : False := nomatch raw

@[reducible] def unknownMeaning : RustModel Nat := { Model := Nat, «decode» := some }

example (kind : Result pointer.invariant.ValidityKind) :
    ¬@Referent.kindMatches Nat unknownMeaning kind := by
  rintro ⟨marker, impossible, _⟩
  cases impossible

example (V : Type) [RustModel V] :
    ¬Referent.kindMatches V (.fail .undef) := by
  rintro ⟨_, _, impossible⟩
  exact fail_not_ok impossible

example : ¬Nonempty (Referent.View unknownMeaning) := by
  rintro ⟨⟨decoder, impossible⟩⟩
  cases impossible

theorem two_not_safe_bool :
    ¬Referent.safeBytes (inferInstance : RustModel Bool) [AMByte.init 2] := by
  rintro ⟨decoder, installed, raw, _, accepted, _⟩
  have same : decoder = boolDecoder := Option.some.inj installed.symm
  subst decoder
  rw [boolDecoder_run_two] at accepted
  contradiction

/-- Initialization alone cannot justify reinterpreting byte 2 as a boolean. -/
example : ¬Referent.transmuteFrom U8 Bool pointer.invariant.Initialized
    pointer.invariant.Safe := by
  intro proof
  have transfers := Referent.transmute_sound U8 Bool pointer.invariant.Initialized
    pointer.invariant.Safe .initialized .safe rfl rfl proof
  have bad := transfers ⟨u8BitDecoder, rfl⟩ ⟨boolDecoder, rfl⟩ rfl
    [AMByte.init 2] ⟨rfl, by simp [Initialized]⟩
  exact two_not_safe_bool bad.2

/-- Unsupported AsInitialized reasoning has no evidence constructor. The
separate forgetting constructor still permits every source to become Uninit. -/
example (Src Dst : Type) [source : RustModel Src] [destination : RustModel Dst] :
    ¬Referent.Supports source destination .asInitialized .safe := by
  have excluded : ∀ first second, Referent.Supports source destination first second →
      first = .asInitialized → second = .safe → False := by
    intro first second supported
    cases supported with
    | forget kind => intro _ impossible; cases impossible
    | modeled first second proof =>
      intro impossible _
      cases first <;> cases impossible
  intro supported
  exact excluded _ _ supported rfl rfl

example (SV DV : Type) : Referent.typeIndependentPair SV DV ↔
    (SV = pointer.invariant.Uninit ∧ DV = pointer.invariant.Uninit) ∨
    (SV = pointer.invariant.Initialized ∧ DV = pointer.invariant.Initialized) := Iff.rfl

-- Execution safety cannot become conditional on finding a modeled state. Even
-- an AsInitialized marker must not let a forbidden result satisfy this family.
example (Src Dst SV DV : Type) [source : RustModel Src] [destination : RustModel Dst]
    [sourceMeaning : RustModel SV] [destinationMeaning : RustModel DV]
    (dictionary : pointer.transmute.TransmuteFrom Dst Src SV DV)
    (law : TraitLaws.transmute_from Dst Src SV DV dictionary) :
    ¬Obligations.require_transfer_spec_contract Src Dst SV DV dictionary (.fail .undef) := by
  intro promised
  have forbidden := @promised source destination sourceMeaning destinationMeaning law
  simp at forbidden

-- These are valid Lean proofs of weaker statements. The native proof audit
-- must reject them even though the kernel accepts their bodies.
private theorem extraPremise (Src Dst : Type) [RustModel Src] [RustModel Dst] (_extra : True) :
    TraitLaws.transmute_from Dst Src pointer.invariant.Initialized pointer.invariant.Initialized
      (pointer.transmute.TransmuteFromDstSrcInitializedInitialized.Blanket Src Dst) :=
  ⟨Referent.initialized_identity Src Dst⟩

/-- error: Trait implementation proof omitted required inputs or added premises -/
#guard_msgs in
run_elab do
  AeneasSpecs.auditTraitImplementationProof
    ``TraitLaws.transmute_from
    ``pointer.transmute.TransmuteFromDstSrcInitializedInitialized.Blanket
    ``extraPremise

@[reducible] private def replacementMeaning (T : Type) : RustModel T :=
  { Model := T, «decode» := some }

private theorem replacedProviders (Src Dst : Type) [_source : RustModel Src]
    [_destination : RustModel Dst] :
    @TraitLaws.transmute_from Dst Src pointer.invariant.Initialized pointer.invariant.Initialized
      (pointer.transmute.TransmuteFromDstSrcInitializedInitialized.Blanket Src Dst)
      (replacementMeaning Dst) (replacementMeaning Src) _ _ :=
by
  letI : RustModel Src := replacementMeaning Src
  letI : RustModel Dst := replacementMeaning Dst
  exact ⟨Referent.initialized_identity Src Dst⟩

/-- error: Trait implementation proof changed its dictionary or canonical provider -/
#guard_msgs in
run_elab do
  AeneasSpecs.auditTraitImplementationProof
    ``TraitLaws.transmute_from
    ``pointer.transmute.TransmuteFromDstSrcInitializedInitialized.Blanket
    ``replacedProviders

end Zerocopy.ReferentTests
