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
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs
set_option linter.unusedSimpArgs false

-- Raw observations remain available independently of function contracts.
-- They record the full positive encoding domain, including arbitrary stored
-- words, and do not register a separately selectable validity interpretation.
def encodingValid (code : layout.RoundingAlignAndPhase) : Prop :=
  0 < code._0.val.val

def trailingValid {E : Type} [RustModel E] (tail : layout.TrailingSliceLayout E) : Prop :=
  isValid tail.elem_size ∧ encodingValid tail.size_rounding_align_and_phase

def sizeInfoValid {E : Type} [RustModel E] (info : layout.SizeInfo E) : Prop :=
  match info with
  | .Sized _ => True
  | .SliceDst tail => trailingValid tail

def layoutValid (self : layout.DstLayout) : Prop :=
  0 < self.align.val.val ∧ sizeInfoValid self.size_info

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

@[simp, contract_simps] theorem trailing_valid_iff {E : Type} [RustModel E]
    (tail : layout.TrailingSliceLayout E) : isValid tail ↔ trailingValid tail := by
  change (∃ value, layout.TrailingSliceLayout.decode E tail = some value) ↔ _
  unfold trailingValid
  simp only [layout.TrailingSliceLayout.decode, layout.TrailingSliceLayout.decodeFields,
    decodeUScalar, admitted_bind, admitted_some,
    and_true, true_and, option_decoded_post_iff, admission_eq, encoding_valid_iff]
  change (isValid tail.elem_size ∧ isValid tail.size_rounding_align_and_phase) ↔ _
  rw [encoding_valid_iff]

@[simp, contract_simps] theorem size_info_valid_iff {E : Type} [RustModel E]
    (info : layout.SizeInfo E) : isValid info ↔ sizeInfoValid info := by
  change (∃ value, layout.SizeInfo.decode E info = some value) ↔ _
  cases info <;>
    simp only [layout.SizeInfo.decode, layout.SizeInfo.decodeFields,
      decodeUScalar, admitted_bind, admitted_some,
      and_true, true_and, admission_eq, sizeInfoValid, trailing_valid_iff]
  change isValid _ ↔ _
  exact trailing_valid_iff _

@[simp, contract_simps] theorem layout_valid_iff (self : layout.DstLayout) :
    isValid self ↔ layoutValid self := by
  change (∃ value, layout.DstLayout.decode self = some value) ↔ _
  unfold layoutValid
  simp only [layout.DstLayout.decode, layout.DstLayout.decodeFields,
    admitted_bind, admitted_some, and_true,
    option_decoded_post_iff, admission_eq, nonzero_valid_iff, size_info_valid_iff,
    bool_valid_iff]
  change (isValid self.align ∧ isValid self.size_info ∧ isValid self.statically_shallow_unpadded) ↔ _
  simp only [nonzero_valid_iff, size_info_valid_iff, bool_valid_iff, and_true]

@[contract_simps] theorem scalar_admitted_iff (x : UScalar ty) :
    (∃ value, RustModel.decode x = some value) ↔ True := scalar_valid_iff x

@[contract_simps] theorem nonzero_admitted_iff (x : NonZeroUsize) :
    (∃ value, RustModel.decode x = some value) ↔ 0 < x.val.val := nonzero_valid_iff x

@[contract_simps] theorem encoding_admitted_iff (x : layout.RoundingAlignAndPhase) :
    (∃ value, RustModel.decode x = some value) ↔ encodingValid x := encoding_valid_iff x

@[contract_simps] theorem trailing_admitted_iff {E : Type} [RustModel E] (x : layout.TrailingSliceLayout E) :
    (∃ value, RustModel.decode x = some value) ↔ trailingValid x := trailing_valid_iff x

@[contract_simps] theorem size_info_admitted_iff {E : Type} [RustModel E] (x : layout.SizeInfo E) :
    (∃ value, RustModel.decode x = some value) ↔ sizeInfoValid x := size_info_valid_iff x

@[contract_simps] theorem layout_admitted_iff (x : layout.DstLayout) :
    (∃ value, RustModel.decode x = some value) ↔ layoutValid x := layout_valid_iff x

@[contract_simps] theorem bool_admitted_iff (x : Bool) :
    (∃ value, RustModel.decode x = some value) ↔ True := bool_valid_iff x

@[contract_simps] theorem option_admitted_iff {α : Type} [RustModel α] (x : Option α) :
    (∃ value : Option (ModelOf α), RustModel.decode x = some value) ↔
      ∀ v ∈ x, isValid v := option_valid_iff x

@[contract_simps] theorem slice_admitted_iff {α : Type} [RustModel α] (x : Slice α) :
    (∃ value, RustModel.decode x = some value) ↔ ∀ v ∈ x.val, isValid v := slice_valid_iff x

-- A named decoder can also occur after a surrounding structural traversal
-- exposes the retained dictionary. These are the same admission equivalences.
theorem encoding_decoder_admitted_iff (raw : layout.RoundingAlignAndPhase) :
    (∃ value, layout.RoundingAlignAndPhase.decode raw = some value) ↔
      encodingValid raw := encoding_valid_iff raw

theorem trailing_decoder_admitted_iff {E : Type} [RustModel E]
    (raw : layout.TrailingSliceLayout E) :
    (∃ value, layout.TrailingSliceLayout.decode E raw = some value) ↔
      trailingValid raw := trailing_valid_iff raw

theorem size_info_decoder_admitted_iff {E : Type} [RustModel E] (raw : layout.SizeInfo E) :
    (∃ value, layout.SizeInfo.decode E raw = some value) ↔
      sizeInfoValid raw := size_info_valid_iff raw

theorem layout_decoder_admitted_iff (raw : layout.DstLayout) :
    (∃ value, layout.DstLayout.decode raw = some value) ↔
      layoutValid raw := layout_valid_iff raw

@[contract_simps] theorem normalized_nat_pos_iff (n : Nat) :
    Nat.le (Nat.succ 0) n ↔ 0 < n := Nat.succ_le_iff

attribute [contract_simps] option_valid_iff prod_valid_iff result_valid_iff

attribute [contract_simps] and_true true_and and_self true_implies forall_true_iff
attribute [contract_simps] encodingValid trailingValid sizeInfoValid layoutValid

end Zerocopy.Proofs
