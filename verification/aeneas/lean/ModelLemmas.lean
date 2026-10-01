/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
@[expose] public section
open Aeneas Aeneas.Std
namespace AeneasSpecs
set_option linter.unusedSimpArgs false

theorem admitted_bind {α β : Type} (d : Option α) (f : α → Option β) :
    (∃ result, d.bind f = some result) ↔
      ∃ value, d = some value ∧ ∃ result, f value = some result := by
  cases d <;> simp

@[simp] theorem admitted_some {α : Type} (value : α) :
    (∃ result, some value = some result) ↔ True := by simp


theorem admitted_none {α : Type} : (∃ value : α, none = some value) ↔ False := by simp

theorem admitted_dite {α : Type} (P : Prop) [Decidable P] (value : P → α) :
    (∃ result, (if h : P then some (value h) else none) = some result) ↔ P := by
  by_cases h : P <;> simp [h]

@[simp] theorem option_valid_iff {α : Type} [RustModel α] (raw : Option α) :
    isValid raw ↔ ∀ x ∈ raw, isValid x := by
  cases raw <;> simp [isValid, RustModel.decode, modelOption, Option.map_eq_some_iff]

@[simp] theorem prod_valid_iff {α β : Type} [RustModel α] [RustModel β]
    (raw : α × β) : isValid raw ↔ isValid raw.1 ∧ isValid raw.2 := by
  rcases raw with ⟨a, b⟩
  simp only [isValid, RustModel.decode, modelProd]
  cases ha : RustModel.decode a <;> cases hb : RustModel.decode b <;> simp [ha, hb]

@[simp] theorem result_valid_iff {α β : Type} [RustModel α] [RustModel β]
    (raw : core.result.Result α β) :
    isValid raw ↔ match raw with | .Ok a => isValid a | .Err b => isValid b := by
  cases raw <;> simp [isValid, RustModel.decode, modelRustResult, Option.map_eq_some_iff]

theorem decodeList_admitted {α β : Type} (d : α → Option β) (raw : List α) :
    (∃ values, decodeList d raw = some values) ↔
      ∀ x ∈ raw, ∃ value, d x = some value := by
  induction raw with
  | nil => simp [decodeList]
  | cons x xs ih =>
    cases hx : d x <;> cases ht : decodeList d xs <;>
      simp only [hx, ht, Option.some.injEq, reduceCtorEq, exists_eq_left,
        not_exists, forall_const, List.mem_cons, forall_eq_or_imp] at ih ⊢ <;>
      simp_all [decodeList]

@[simp] theorem list_valid_iff {α : Type} [m : RustModel α] (raw : List α) :
    isValid raw ↔ ∀ x ∈ raw, isValid x := decodeList_admitted m.decode raw

@[simp] theorem slice_valid_iff {α : Type} [m : RustModel α] (raw : Slice α) :
    isValid raw ↔ ∀ x ∈ raw.val, isValid x := by
  unfold isValid
  dsimp only [RustModel.decode, modelSlice]
  split
  · rename_i h
    simp only [reduceCtorEq]
    constructor
    · rintro ⟨_, bad⟩; contradiction
    intro hall
    obtain ⟨values, hv⟩ := (decodeList_admitted m.decode raw.val).mpr hall
    rw [h] at hv; contradiction
  · rename_i values h
    simp only [Option.some.injEq, exists_eq', true_iff]
    exact (decodeList_admitted m.decode raw.val).mp ⟨values, h⟩

-- Exposing the child carrier and decoder as separate parameters lets ordinary
-- simplification match a normalized nested associated type without trying to
-- infer its raw carrier from its mathematical carrier.
theorem option_admitted_explicit_iff {Raw Math : Type}
    (decoder : Raw → Option Math) (raw : Option Raw) :
    (∃ value : Option Math,
      (@modelOption Raw ⟨Math, decoder⟩).decode raw = some value) ↔
      ∀ x ∈ raw, ∃ value, decoder x = some value := by
  cases raw <;> simp [RustModel.decode, modelOption, Option.map_eq_some_iff]

/-- Structural traversal preserves the accepted mathematical element witnesses. -/
theorem decodeList_eq_some_iff {α β : Type u} (d : α → Option β)
    (raw : List α) (values : List β) :
    decodeList d raw = some values ↔
      List.Forall₂ (fun x value => d x = some value) raw values := by
  induction raw generalizing values with
  | nil => cases values <;> simp [decodeList]
  | cons x xs ih =>
    cases values with
    | nil => cases hx : d x <;> cases ht : decodeList d xs <;> simp [decodeList, hx, ht]
    | cons value values =>
      cases hx : d x <;> cases ht : decodeList d xs <;>
        simp only [decodeList, hx, ht, Option.bind_some, Option.bind_none,
          Option.some.injEq, reduceCtorEq, List.cons.injEq,
          List.forall₂_cons] at ih ⊢ <;> simp_all

/-- Bounded container decomposition exposes the traversed list, while proof
irrelevance identifies the length evidence already stored in its carrier. -/
theorem decodeSlice_iff {α : Type u} (m : RustModel α) (raw : Slice α)
    (value : SliceValue m.Model) :
    (@modelSlice α m).decode raw = some value ↔
      decodeList m.decode raw.val = some value.val := by
  change (match h : decodeList m.decode raw.val with
    | none => none
    | some values => some ⟨values, (decodeList_length m.decode h) ▸ raw.property⟩) = some value ↔ _
  split
  · rename_i h; simp [h]
  · rename_i values h
    simp only [Option.some.injEq]
    constructor
    · intro he; cases he; exact h
    · intro he; apply Subtype.ext; exact Option.some.inj (h.symm.trans he)

theorem decodeArray_iff {α : Type u} (m : RustModel α) (n : Usize)
    (raw : Aeneas.Std.Array α n) (value : ArrayValue m.Model n) :
    (@modelArray α n m).decode raw = some value ↔
      decodeList m.decode raw.val = some value.val := by
  change (match h : decodeList m.decode raw.val with
    | none => none
    | some values => some ⟨values, (decodeList_length m.decode h) ▸ raw.property⟩) = some value ↔ _
  split
  · rename_i h; simp [h]
  · rename_i values h
    simp only [Option.some.injEq]
    constructor
    · intro he; cases he; exact h
    · intro he; apply Subtype.ext; exact Option.some.inj (h.symm.trans he)

end AeneasSpecs
