/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import CompositionReference
@[expose] public section

/-!
The constructor has two ordinary Rust loops: one checks every supplied witness,
then the independent constructor folds Option-valued checked field placement.
The invariants below retain all completed append domains, including failure
propagation, so final success cannot silently skip an overflowing field.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.CompositionReference
open Zerocopy.Proofs
set_option linter.unusedSimpArgs false

def fieldsMatchThrough (fields : Slice layout.DstLayout) (references : Slice ReferenceLayout)
    (count : Nat) : Prop :=
  ∀ j (hf : j < fields.val.length) (hr : j < references.val.length), j < count →
    Matches fields.val[j] references.val[j]

theorem fieldsMatchThrough_succ (fields : Slice layout.DstLayout) (references : Slice ReferenceLayout)
    (i : Nat) (hf : i < fields.val.length) (hr : i < references.val.length) :
    fieldsMatchThrough fields references (i + 1) ↔
      fieldsMatchThrough fields references i ∧ Matches fields.val[i] references.val[i] := by
  constructor
  · intro all
    exact ⟨fun j hj hrj before => all j hj hrj (by omega), all i hf hr (by omega)⟩
  · rintro ⟨before, current⟩ j hj hrj next
    by_cases old : j < i
    · exact before j hj hrj old
    · have same : j = i := by omega
      subst j
      exact current

def referencePrefix (fields : Slice ReferenceLayout) (minimum : Nat)
    (packed : Option NonZeroUsize) (i : Nat) : LayoutMath.LayoutValue :=
  LayoutMath.LayoutValue.prefixValue (fields.val.map value) (LayoutMath.LayoutValue.initial minimum)
    (packingValue packed) i

def referenceHistory (fields : Slice ReferenceLayout) (minimum : Nat)
    (packed : Option NonZeroUsize) (count : Nat) : Prop :=
  ∀ j (hj : j < fields.val.length), j < count →
    alignmentDomain (referencePrefix fields minimum packed j).align ∧
    alignmentDomain fields.val[j].align.val ∧ valid fields.val[j] ∧
    (referencePrefix fields minimum packed j).extendFits (value fields.val[j])
      (packingValue packed) Usize.max

def referenceState (fields : Slice ReferenceLayout) (minimum : Nat)
    (packed : Option NonZeroUsize) (state : Option ReferenceLayout) (i : Nat) : Prop :=
  ∀ current, state = some current →
    value current = referencePrefix fields minimum packed i ∧ valid current ∧
    alignmentDomain current.align.val ∧
    (0 < i → ∀ a ∈ packed, alignmentDomain a.val.val) ∧
    referenceHistory fields minimum packed i

theorem referencePrefix_step (fields : Slice ReferenceLayout) (minimum : Nat)
    (packed : Option NonZeroUsize) (i : Nat) (hi : i < fields.val.length) :
    referencePrefix fields minimum packed (i + 1) =
      (referencePrefix fields minimum packed i).extend (value fields.val[i]) (packingValue packed) := by
  unfold referencePrefix
  rw [LayoutMath.LayoutValue.prefixValue_step (fields.val.map value)
    (LayoutMath.LayoutValue.initial minimum) (packingValue packed) i (by simpa using hi)]
  simp only [List.getElem_map]

theorem max_domain (a b : Nat) (ha : alignmentDomain a) (hb : alignmentDomain b) :
    alignmentDomain (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

theorem packed_domain (field : Nat) (packed : Option NonZeroUsize)
    (hf : alignmentDomain field) (hp : ∀ a ∈ packed, alignmentDomain a.val.val) :
    alignmentDomain (min field (packingValue packed)) := by
  cases packed with
  | none =>
    have limit : 2 ^ 29 ≤ packingValue none := by
      rcases System.Platform.numBits_eq with h | h <;> simp [packingValue, h]
    have bound := hf.2
    simpa only [min_eq_left (show field ≤ packingValue none by omega)] using hf
  | some cap =>
    have hc := hp cap rfl
    rcases le_total field cap.val.val with h | h
    · simpa only [packingValue, Option.map_some, Option.getD_some, min_eq_left h] using hf
    · simpa only [packingValue, Option.map_some, Option.getD_some, min_eq_right h] using hc

theorem extended_domain (preceding field : LayoutMath.LayoutValue) (packed : Option NonZeroUsize)
    (ha : alignmentDomain preceding.align) (hf : alignmentDomain field.align)
    (hp : ∀ a ∈ packed, alignmentDomain a.val.val)
    (fit : preceding.extendFits field (packingValue packed) Usize.max) :
    alignmentDomain (preceding.extend field (packingValue packed)).align := by
  cases hs : preceding.payload with
  | trailing _ => simp [LayoutMath.LayoutValue.extendFits, hs] at fit
  | fixed _ =>
    simpa only [LayoutMath.LayoutValue.extend, hs] using max_domain _ _ ha (packed_domain _ _ hf hp)

end Zerocopy.CompositionReference

namespace Zerocopy.Proofs.Raw
open Zerocopy.CompositionReference
set_option linter.unusedSimpArgs false

theorem composition_matching_loop_spec (fields : Slice layout.DstLayout)
    (references : Slice ReferenceLayout) (lengths : fields.val.length = references.val.length)
    (matching : Bool) (i : Usize) (hi : i.val ≤ fields.val.length)
    (hv : (matching = true) = fieldsMatchThrough fields references i.val) :
    layout.composition_checks.check_constructor_loop fields references matching i
      ⦃ out => (out = true) = fieldsMatchThrough fields references fields.val.length ⦄ := by
  unfold layout.composition_checks.check_constructor_loop
  apply WP.spec_mono (AeneasContracts.indexed_loop_spec fields.val.length
    (fun b : Bool => b = true) (fieldsMatchThrough fields references) (fun _ => True) _
    ?_ matching i hi hv trivial)
  · intro out facts
    exact facts.1
  · intro matching idx hi hv _
    unfold layout.composition_checks.check_constructor_loop.body
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, and_true]
    split
    · rename_i hlt
      have hrl : idx.val < references.val.length := by omega
      have hroom : idx.val + (1#usize).val ≤ Usize.max := by
        have := fields.property
        change idx.val + 1 ≤ Usize.max
        omega
      split
      · rename_i yes
        have previous : fieldsMatchThrough fields references idx.val := Eq.mp hv yes
        step with Slice.index_usize_spec fields idx hlt as ⟨field, hf⟩
        step with Slice.index_usize_spec references idx hrl as ⟨reference, hr⟩
        step with composition_matches_spec field reference as ⟨checked, hc⟩
        have next_view : (checked = true) = fieldsMatchThrough fields references (idx.val + 1) := by
          apply propext
          rw [fieldsMatchThrough_succ fields references idx.val hlt hrl]
          simpa only [previous, true_and, hf, hr] using hc
        step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨j, hj⟩
        change j.val = idx.val + 1 at hj
        simpa only [hlt, hj, true_and] using next_view
      · rename_i no
        simp only [bind_ok]
        have next_view : (false = true) = fieldsMatchThrough fields references (idx.val + 1) := by
          apply propext
          rw [fieldsMatchThrough_succ fields references idx.val hlt hrl]
          have np : ¬fieldsMatchThrough fields references idx.val := by
            intro hp
            exact no (Eq.mpr hv hp)
          simp [np]
        step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨j, hj⟩
        change j.val = idx.val + 1 at hj
        simpa only [hlt, hj, true_and] using next_view
    · have same : idx.val = fields.val.length := by omega
      exact WP.spec.ret ⟨same, hv⟩

theorem composition_reference_loop_spec (packed : Option NonZeroUsize)
    (fields : Slice ReferenceLayout) (minimum : Nat) (state : Option ReferenceLayout) (i : Usize)
    (fields_valid : ∀ j (hj : j < fields.val.length), valid fields.val[j])
    (hi : i.val ≤ fields.val.length) (hv : referenceState fields minimum packed state i.val) :
    layout.composition_checks.reference_constructor_loop packed fields state i
      ⦃ out => referenceState fields minimum packed out fields.val.length ⦄ := by
  unfold layout.composition_checks.reference_constructor_loop
  apply loop.spec_decr_nat
    (fun s : Option ReferenceLayout × Usize => fields.val.length - s.2.val)
    (fun s => s.2.val ≤ fields.val.length ∧ referenceState fields minimum packed s.1 s.2.val)
  · rintro ⟨state, idx⟩ ⟨hi, hv⟩
    dsimp only at hi hv
    unfold layout.composition_checks.reference_constructor_loop.body
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]
    split
    · rename_i hlt
      have hroom : idx.val + (1#usize).val ≤ Usize.max := by
        have := fields.property
        change idx.val + 1 ≤ Usize.max
        omega
      cases state with
      | none =>
        simp only [bind_ok]
        step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨j, hj⟩
        change j.val = idx.val + 1 at hj
        refine ⟨by omega, ?_, by omega⟩
        intro expected same
        cases same
      | some preceding =>
        step with Slice.index_usize_spec fields idx hlt as ⟨field, hf⟩
        step with composition_reference_extend_spec preceding field packed as ⟨next, hn⟩
        cases next with
        | none =>
          step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨j, hj⟩
          change j.val = idx.val + 1 at hj
          refine ⟨by omega, ?_, by omega⟩
          intro expected same
          cases same
        | some next =>
          obtain ⟨preceding_domain, field_domain, packed_domain, fits, output, validity⟩ := hn next rfl
          obtain ⟨preceding_view, _, _, _, history⟩ := hv preceding rfl
          have valid_next : valid next := validity (by rw [hf]; exact fields_valid idx.val hlt)
          have domain_next : alignmentDomain next.align.val := by
            have domain := extended_domain (value preceding) (value field) packed preceding_domain
              field_domain packed_domain fits
            have alignment := congrArg LayoutMath.LayoutValue.align output
            change next.align.val = _ at alignment
            rw [← alignment] at domain
            exact domain
          have next_view : value next = referencePrefix fields minimum packed (idx.val + 1) := by
            rw [referencePrefix_step fields minimum packed idx.val hlt, ← preceding_view, ← hf]
            exact output
          step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨jnext, hjnext⟩
          change jnext.val = idx.val + 1 at hjnext
          refine ⟨by omega, ?_, by omega⟩
          rw [hjnext]
          intro expected same
          cases same
          refine ⟨next_view, valid_next, domain_next, fun _ => packed_domain, ?_⟩
          intro j hj before
          by_cases old : j < idx.val
          · exact history j hj old
          · have same : j = idx.val := by omega
            subst j
            refine ⟨?_, ?_, fields_valid idx.val hlt, ?_⟩
            · have alignment := congrArg LayoutMath.LayoutValue.align preceding_view
              change preceding.align.val = _ at alignment
              simpa only [← alignment] using preceding_domain
            · simpa only [← hf] using field_domain
            · simpa only [preceding_view, hf] using fits
    · have same : idx.val = fields.val.length := by omega
      exact WP.spec.ret (same ▸ hv)
  · exact ⟨hi, hv⟩

theorem composition_reference_constructor_spec (repr_align packed : Option NonZeroUsize)
    (fields : Slice ReferenceLayout)
    (fields_valid : ∀ j (hj : j < fields.val.length), valid fields.val[j]) :
    layout.composition_checks.reference_constructor repr_align packed fields
      ⦃ result => ∀ expected, result = some expected →
        (∀ a ∈ repr_align, alignmentDomain a.val.val) ∧
        (0 < fields.val.length → ∀ a ∈ packed, alignmentDomain a.val.val) ∧
        referenceHistory fields (initialAlignment repr_align) packed fields.val.length ∧
        alignmentDomain (referencePrefix fields (initialAlignment repr_align) packed fields.val.length).align ∧
        (referencePrefix fields (initialAlignment repr_align) packed fields.val.length).padFits Usize.max ∧
        value expected = (referencePrefix fields (initialAlignment repr_align) packed fields.val.length).pad ∧
        valid expected ⦄ := by
  unfold layout.composition_checks.reference_constructor
  let align : Usize := match repr_align with | none => 1#usize | some a => a.val
  have alignment_read : (match (generalizing := false) repr_align with
    | none => Result.ok 1#usize
    | some a => core.num.nonzero.NonZero.get
      Usize.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroUsizeInner a) = Result.ok align := by
    cases repr_align <;> rfl
  change (Aeneas.Std.bind (match (generalizing := false) repr_align with
    | none => Result.ok 1#usize
    | some a => core.num.nonzero.NonZero.get
      Usize.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroUsizeInner a) _) ⦃ _ ⦄
  rw [alignment_read]
  simp only [bind_ok]
  have ha : align.val = initialAlignment repr_align := by
    cases repr_align <;> simp only [align, initialAlignment, Option.map_some,
      Option.getD_some, Option.map_none, Option.getD_none]
    simp
  step with composition_alignment_spec align as ⟨enabled, he⟩
  split
  · rename_i yes
    have domain := he.mp yes
    have initial_domain : alignmentDomain (initialAlignment repr_align) := by rw [← ha]; exact domain
    have admitted : ∀ a ∈ repr_align, alignmentDomain a.val.val := by
      cases repr_align with
      | none => simp
      | some a =>
        intro b member
        have same : b = a := by simpa [eq_comm] using member
        subst b
        simpa only [initialAlignment, Option.map_some, Option.getD_some] using initial_domain
    have start : referenceState fields (initialAlignment repr_align) packed
        (some ⟨align, .Fixed 0#usize, true⟩) (0#usize).val := by
      intro current same
      cases same
      refine ⟨?_, trivial, domain, ?_, ?_⟩
      · simp only [value, referencePrefix, LayoutMath.LayoutValue.prefixValue,
          LayoutMath.LayoutValue.initial, ha, show (0#usize).val = 0 by simp,
          List.take_zero, List.foldl_nil]
      · intro impossible
        simp at impossible
      · intro j hj impossible
        simp at impossible
    step with composition_reference_loop_spec packed fields (initialAlignment repr_align)
      (some ⟨align, .Fixed 0#usize, true⟩) 0#usize fields_valid (by simp) start
      as ⟨complete, completed⟩
    cases complete with
    | none => simp
    | some complete =>
      obtain ⟨view, _, final_domain, packed_domain, history⟩ := completed complete rfl
      apply WP.spec_mono (composition_reference_pad_spec complete)
      intro result facts expected same
      obtain ⟨_, fits, output, validity⟩ := facts expected same
      refine ⟨admitted, packed_domain, history, ?_, ?_, ?_, validity⟩
      · have alignment := congrArg LayoutMath.LayoutValue.align view
        change complete.align.val = _ at alignment
        simpa only [← alignment] using final_domain
      · simpa only [view] using fits
      · simpa only [view] using output
  · simp

/- Packing is read only while appending a field. The empty constructor also
terminates when its unused packing word is not an admitted power of two. -/
theorem composition_empty_production_loop (packed : Option NonZeroUsize)
    (fields : Slice layout.DstLayout) (start : layout.DstLayout) (empty : fields.val.length = 0) :
    layout.DstLayout.for_repr_c_struct_loop packed fields start 0#usize ⦃ out => out = start ⦄ := by
  unfold layout.DstLayout.for_repr_c_struct_loop
  apply loop.spec_decr_nat (fun _ => 0) (fun s => s = (start, 0#usize))
  · intro state same
    cases same
    unfold layout.DstLayout.for_repr_c_struct_loop.body
    simp [UScalar.lt_equiv, Slice.len_val, Slice.length, empty]
  · rfl

theorem composition_production_constructor_spec (repr_align packed : Option NonZeroUsize)
    (fields : Slice layout.DstLayout)
    (ha : ∀ a ∈ repr_align, alignmentDomain a.val.val)
    (hp : 0 < fields.val.length → ∀ a ∈ packed, alignmentDomain a.val.val)
    (hd : constructionDomain fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed)
    (hlast : alignmentDomain
      (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed fields.val.length).align)
    (hfit : (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align))
      packed fields.val.length).padFits Usize.max) :
    layout.DstLayout.for_repr_c_struct repr_align packed fields ⦃ r =>
      layoutValue r = (constructionPrefix fields (LayoutMath.LayoutValue.initial
        (initialAlignment repr_align)) packed fields.val.length).pad ∧ canonicalLayout r ⦄ := by
  by_cases nonempty : 0 < fields.val.length
  · exact for_repr_c_struct_spec repr_align packed fields ha (hp nonempty) hd hlast hfit
  · have empty : fields.val.length = 0 := by omega
    unfold layout.DstLayout.for_repr_c_struct
    step with new_zst_spec repr_align (fun a h => (ha a h).1) as ⟨start, halign, hsize, hunpadded⟩
    have view : layoutValue start = constructionPrefix fields
        (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed fields.val.length := by
      simp only [constructionPrefix, LayoutMath.LayoutValue.prefixValue, empty,
        List.take_zero, List.foldl_nil, layoutValue, hsize, hunpadded, halign,
        initialAlignment, LayoutMath.LayoutValue.initial]
      cases repr_align <;> rfl
    have canonical : canonicalLayout start := by simp only [canonicalLayout, hsize]
    step with composition_empty_production_loop packed fields start empty as ⟨complete, same⟩
    subst complete
    step with pad_value_spec start (by
      have alignment := congrArg LayoutMath.LayoutValue.align view
      change start.align.val.val = _ at alignment
      rw [alignment]
      exact hlast.1) canonical (by rw [view]; exact hfit) as ⟨result, output, canonical⟩
    exact ⟨by rw [output, view], canonical⟩

end Zerocopy.Proofs.Raw
