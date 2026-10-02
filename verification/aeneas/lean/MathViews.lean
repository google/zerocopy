/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Models
public import ModelLemmas
public import SpecPrelude
public import ContractSimps
@[expose] public section

/-!
Contracts automatically require values to decode. Raw implementation proofs
instead use concrete conditions such as a nonzero alignment word. This module
proves that the actual decoders admit exactly those independently stated raw
domains, and supplies equations for normalizing retained provider
projections.

The predicates below are observations used by proofs, not competing validity
instances. The selected RustModel decoder remains authoritative for
admission. The different theorem spellings match expressions produced at
different stages: isValid, a provider's decode projection, or the owner's
named decoder. Each is proved from the same decoder; none chooses an
interpretation from a model type.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs
set_option linter.unusedSimpArgs false

-- Raw observations remain available independently of function contracts.
-- They record the full positive encoding domain, including arbitrary stored
-- words, and do not register a separately selectable validity interpretation.
def encodingValid (code : layout.RoundingAlignAndPhase) : Prop :=
  0 < code._0.val.val

@[contract_simps] theorem admission_eq {Raw : Type u} (provider : RustModel Raw)
    (raw : Raw) : (∃ value, provider.decode raw = some value) =
      @isValid Raw provider raw := rfl

-- Eliminating an unused mathematical witness is ordinary existential logic.
-- These lemmas apply only when the authored predicate does not depend on it.
@[contract_simps] theorem option_decoded_pre_iff {M : Type u} (d : Option M) (P : Prop) :
    (∀ m, d = some m → P) ↔ ((∃ m, d = some m) → P) := by
  constructor
  · rintro h ⟨m, hm⟩; exact h m hm
  · intro h m hm; exact h ⟨m, hm⟩

@[contract_simps] theorem option_decoded_post_iff {M : Type u} (d : Option M) (P : Prop) :
    (∃ m, d = some m ∧ P) ↔ (∃ m, d = some m) ∧ P := by
  constructor
  · rintro ⟨m, hm, hp⟩; exact ⟨⟨m, hm⟩, hp⟩
  · rintro ⟨⟨m, hm⟩, hp⟩; exact ⟨m, hm, hp⟩

@[simp, contract_simps] theorem scalar_valid_iff (x : UScalar ty) : isValid x ↔ True := by
  simp [isValid, RustModel.decode, modelUScalar]

@[simp, contract_simps] theorem nonzero_valid_iff (a : NonZeroUsize) :
    isValid a ↔ 0 < a.val.val := by
  unfold isValid
  constructor
  · rintro ⟨m, hm⟩
    have he := (decodeNonZeroUScalar_iff a m).mp hm
    rw [he]; exact m.positive
  · intro hp
    exact ⟨⟨unsignedWord a.val, hp⟩, (decodeNonZeroUScalar_iff a ⟨unsignedWord a.val, hp⟩).mpr rfl⟩

@[simp, contract_simps] theorem bool_valid_iff (x : Bool) : isValid x ↔ True := by
  simp [isValid, RustModel.decode, modelBool]

@[simp, contract_simps] theorem encoding_valid_iff (code : layout.RoundingAlignAndPhase) :
    isValid code ↔ encodingValid code := by
  by_cases hp : 0 < code._0.val.val <;>
    simp [isValid, RustModel.decode, layout.RoundingAlignAndPhase.aeneasModel,
      layout.RoundingAlignAndPhase.decode, layout.RoundingAlignAndPhase.decodeFields,
      modelNonZeroUScalar, hp, encodingValid]

@[contract_simps] theorem scalar_admitted_iff (x : UScalar ty) :
    (∃ value, RustModel.decode x = some value) ↔ True := scalar_valid_iff x

@[contract_simps] theorem nonzero_admitted_iff (x : NonZeroUsize) :
    (∃ value, RustModel.decode x = some value) ↔ 0 < x.val.val := nonzero_valid_iff x

@[contract_simps] theorem encoding_admitted_iff (x : layout.RoundingAlignAndPhase) :
    (∃ value, RustModel.decode x = some value) ↔ encodingValid x := encoding_valid_iff x

@[contract_simps] theorem bool_admitted_iff (x : Bool) :
    (∃ value, RustModel.decode x = some value) ↔ True := bool_valid_iff x

@[contract_simps] theorem option_admitted_iff {α : Type} [RustModel α] (x : Option α) :
    (∃ value : Option (ModelOf α), RustModel.decode x = some value) ↔
      ∀ v ∈ x, isValid v := option_valid_iff x

@[contract_simps] theorem slice_admitted_iff {α : Type} [RustModel α] (x : Slice α) :
    (∃ value, RustModel.decode x = some value) ↔ ∀ v ∈ x.val, isValid v := slice_valid_iff x

-- A named decoder can also occur after a surrounding structural traversal
-- exposes the retained dictionary. These are the same admission equivalences.
@[contract_simps] theorem encoding_decoder_admitted_iff (raw : layout.RoundingAlignAndPhase) :
    (∃ value, layout.RoundingAlignAndPhase.decode raw = some value) ↔
      encodingValid raw := encoding_valid_iff raw

@[contract_simps] theorem normalized_nat_pos_iff (n : Nat) :
    Nat.le (Nat.succ 0) n ↔ 0 < n := Nat.succ_le_iff

attribute [contract_simps] option_valid_iff prod_valid_iff result_valid_iff

attribute [contract_simps] and_true true_and and_self true_implies forall_true_iff
attribute [contract_simps] encodingValid

@[simp, contract_simps] theorem rounding_model_decode_eq
    (raw : layout.RoundingAlignAndPhase) :
    RustModel.decode raw = layout.RoundingAlignAndPhase.decode raw := rfl

end Zerocopy.Proofs
