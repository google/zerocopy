/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Loops
public import Obligations
public import ModelLemmas
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

def nestedStateView (state : Usize × Usize) : Nat × Nat := (state.1.val, state.2.val)

theorem nested_round_up_spec (size align : Usize) :
    layout.nested_reference.round_up size align
      ⦃ rounded => rounded.map UScalar.val =
        if align.val = 0 then none
        else if LayoutMath.roundUp size.val align.val ≤ Usize.max
          then some (LayoutMath.roundUp size.val align.val) else none ⦄ := by
  unfold layout.nested_reference.round_up
  by_cases hz : align = 0#usize
  · subst align
    simp
  · simp only [hz, if_false]
    have ha : 0 < align.val := by
      have hn : align.val ≠ 0 := by
        intro h
        apply hz
        exact UScalar.eq_of_val_eq (by simpa using h)
      omega
    step with Usize.rem_spec size (y := align) (by omega) as ⟨remainder, hr⟩
    by_cases hrz : remainder = 0#usize
    · have hr0 : size.val % align.val = 0 := by
        have h := congrArg UScalar.val hrz
        simpa only [hr, show (0#usize).val = 0 by simp] using h
      simp only [hrz, if_true, WP.spec_ok, Option.map_some,
        show ¬align.val = 0 by omega, if_false, LayoutMath.roundUp_eq _ _ hr0,
        show size.val ≤ Usize.max by scalar_tac, if_true]
    · simp only [hrz, if_false]
      have hrem := Nat.mod_lt size.val ha
      step with Usize.sub_spec (x := align) (y := remainder) (by rw [hr]; omega)
        as ⟨padding, hp, _⟩
      have hrpos : 0 < size.val % align.val := by
        have hn : remainder.val ≠ 0 := by
          intro h
          apply hrz
          exact UScalar.eq_of_val_eq (by simpa using h)
        omega
      have hp' : padding.val = (align.val - size.val % align.val) % align.val := by
        have hm : (align.val - size.val % align.val) % align.val =
            align.val - size.val % align.val := Nat.mod_eq_of_lt (by omega)
        rw [hp, hr, hm]
      have hchecked := Usize.checked_add_bv_spec size padding
      cases hc : Usize.checked_add size padding <;>
        simp only [hc] at hchecked
      · have hn : ¬LayoutMath.roundUp size.val align.val ≤ Usize.max := by
          unfold LayoutMath.roundUp
          omega
        simp only [Option.map_none, show ¬align.val = 0 by omega, if_false, hn]
      · rename_i rounded
        have hs : LayoutMath.roundUp size.val align.val ≤ Usize.max := by
          unfold LayoutMath.roundUp
          omega
        simp only [Option.map_some, show ¬align.val = 0 by omega, if_false, hs, if_true]
        congr 1
        unfold LayoutMath.roundUp
        omega

theorem nested_apply_layer_spec (layer : layout.nested_reference.NestedLayer)
    (size alignment : Usize) (ha : alignment.val.isPowerOfTwo) :
    layout.nested_reference.apply_layer layer size alignment
      ⦃ result => result.map nestedStateView =
        NestedReference.checkedLayer layer (some (size.val, alignment.val)) ⦄ := by
  classical
  unfold layout.nested_reference.apply_layer
  step as ⟨packedPow, hp⟩
  cases packedPow with
  | false =>
    have hn : ¬layer.packed.val.isPowerOfTwo := by
      intro h
      have := (Iff.of_eq hp).mpr h
      contradiction
    have hl : ¬NestedReference.layerValid layer := by
      intro h
      exact hn h.1
    simp only [Bool.false_eq_true, if_false, WP.spec_ok, Option.map_none,
      NestedReference.checkedLayer, hl, if_false]
  | true =>
    have hp' : layer.packed.val.isPowerOfTwo := (Iff.of_eq hp).mp rfl
    simp only [if_true]
    step as ⟨minimumPow, hm⟩
    cases minimumPow with
    | false =>
      have hn : ¬layer.min_align.val.isPowerOfTwo := by
        intro h
        have := (Iff.of_eq hm).mpr h
        contradiction
      have hl : ¬NestedReference.layerValid layer := by
        intro h
        exact hn h.2.1
      simp only [Bool.false_eq_true, if_false, WP.spec_ok, Option.map_none,
        NestedReference.checkedLayer, hl, if_false]
    | true =>
      have hm' : layer.min_align.val.isPowerOfTwo := (Iff.of_eq hm).mp rfl
      simp only [if_true, UScalar.lt_equiv]
      split
      · rename_i hlarge
        have hl : ¬NestedReference.layerValid layer := by
          intro h
          exact not_lt_of_ge h.2.2 hlarge
        simp only [WP.spec_ok, Option.map_none, NestedReference.checkedLayer, hl, if_false]
      · rename_i hsmall
        have hl : NestedReference.layerValid layer := ⟨hp', hm', by omega⟩
        let field := min alignment layer.packed
        have hfieldRaw : (if alignment < layer.packed then Result.ok alignment else .ok layer.packed) =
            Result.ok field := by
          by_cases h : alignment < layer.packed
          · simp only [h, if_true, field, min_eq_left (le_of_lt h)]
          · simp only [h, if_false, field, min_eq_right (le_of_not_gt h)]
        have hfield : (if alignment.val < layer.packed.val then Result.ok alignment else .ok layer.packed) =
            Result.ok field := by simpa only [UScalar.lt_equiv] using hfieldRaw
        simp only [hfield, bind_ok]
        have hf : field.val = min alignment.val layer.packed.val := Arithmetic.coe_min _ _
        have hfp : field.val.isPowerOfTwo := by
          rw [hf]
          by_cases h : alignment.val ≤ layer.packed.val
          · simpa only [Nat.min_eq_left h] using ha
          · simpa only [Nat.min_eq_right (by omega : layer.packed.val ≤ alignment.val)] using hp'
        have hfpos := Nat.pos_of_isPowerOfTwo hfp
        step with nested_round_up_spec layer.prefix_bytes field as ⟨offset, hoffset⟩
        change offset.map UScalar.val = if field.val = 0 then none else
          if LayoutMath.roundUp layer.prefix_bytes.val field.val ≤ Usize.max then
            some (LayoutMath.roundUp layer.prefix_bytes.val field.val) else none at hoffset
        simp only [show ¬field.val = 0 by omega, if_false] at hoffset
        let outer := max layer.min_align field
        have houtRaw : (if layer.min_align < field then Result.ok field else .ok layer.min_align) =
            Result.ok outer := by
          by_cases h : layer.min_align < field
          · simp only [h, if_true, outer, max_eq_right (le_of_lt h)]
          · simp only [h, if_false, outer, max_eq_left (le_of_not_gt h)]
        have hout : (if layer.min_align.val < field.val then Result.ok field else .ok layer.min_align) =
            Result.ok outer := by simpa only [UScalar.lt_equiv] using houtRaw
        have ho : outer.val = max layer.min_align.val field.val := Arithmetic.coe_max _ _
        have hopos : 0 < outer.val := by
          rw [ho]
          have := Nat.le_max_right layer.min_align.val field.val
          omega
        let target := NestedReference.step layer (size.val, alignment.val)
        have htarget : target =
            (LayoutMath.roundUp (LayoutMath.roundUp layer.prefix_bytes.val field.val + size.val)
              outer.val, outer.val) := by
          simp only [target, NestedReference.step, hf, ho]
        have hcontains : LayoutMath.roundUp layer.prefix_bytes.val field.val ≤ target.1 := by
          rw [htarget]
          simp only [LayoutMath.roundUp]
          omega
        have hmodel : NestedReference.checkedLayer layer (some (size.val, alignment.val)) =
            if target.1 ≤ Usize.max then some target else none := by
          simp only [NestedReference.checkedLayer, hl, if_true, Option.bind_some]
          rfl
        simp only [hmodel]
        cases offset with
        | none =>
          have hnot : ¬LayoutMath.roundUp layer.prefix_bytes.val field.val ≤ Usize.max := by
            split at hoffset <;> simp_all
          have hn : ¬target.1 ≤ Usize.max := by omega
          simp only [WP.spec_ok, Option.map_none, hn, if_false]
        | some offset =>
          have hv : offset.val = LayoutMath.roundUp layer.prefix_bytes.val field.val := by
            split at hoffset <;> simp_all
          simp only [hout, bind_ok]
          step as ⟨unpadded, hu⟩
          cases unpadded with
          | none =>
            have hsum : Usize.max < offset.val + size.val := hu
            have hn : ¬target.1 ≤ Usize.max := by
              rw [htarget]
              simp only [LayoutMath.roundUp] at hv ⊢
              omega
            simp only [WP.spec_ok, Option.map_none, hn, if_false]
          | some unpadded =>
            have husize : unpadded.val = offset.val + size.val := hu.2.1
            step with nested_round_up_spec unpadded outer as ⟨rounded, hr⟩
            change rounded.map UScalar.val = if outer.val = 0 then none else
              if LayoutMath.roundUp unpadded.val outer.val ≤ Usize.max then
                some (LayoutMath.roundUp unpadded.val outer.val) else none at hr
            simp only [show ¬outer.val = 0 by omega, if_false] at hr
            have hround : LayoutMath.roundUp unpadded.val outer.val = target.1 := by
              rw [husize, hv, htarget]
            rw [hround] at hr
            cases rounded with
            | none =>
              have hn : ¬target.1 ≤ Usize.max := by split at hr <;> simp_all
              simp only [WP.spec_ok, Option.map_none, hn, if_false]
            | some rounded =>
              have ht : target.1 ≤ Usize.max := by split at hr <;> simp_all
              have hsize : rounded.val = target.1 := by split at hr <;> simp_all
              have halign : outer.val = target.2 := by rw [htarget]
              simp only [WP.spec_ok, Option.map_some, nestedStateView, ht, if_true, hsize, halign,
                Prod.mk.eta]

/-- The reverse loop retains complete recursive size at every layer. Its
termination measure is the remaining layer index; no bound limits nesting. -/
theorem nested_reference_loop_spec
    (leading : Slice layout.nested_reference.NestedLayer) (elem alignment metadata : Nat)
    (state : Option (Usize × Usize)) (i : Usize)
    (hi : i.val ≤ leading.val.length)
    (hv : state.map nestedStateView =
      NestedReference.checkedState (leading.val.drop i.val) elem alignment metadata) :
    layout.nested_reference.size_for_metadata_loop leading state i
      ⦃ out => out.map nestedStateView =
        NestedReference.checkedState leading.val elem alignment metadata ⦄ := by
  unfold layout.nested_reference.size_for_metadata_loop
  apply loop.spec_decr_nat
    (fun s : Option (Usize × Usize) × Usize => s.2.val)
    (fun s => s.2.val ≤ leading.val.length ∧ s.1.map nestedStateView =
      NestedReference.checkedState (leading.val.drop s.2.val) elem alignment metadata)
  · rintro ⟨state, idx⟩ ⟨hi, hv⟩
    dsimp only at hi hv ⊢
    unfold layout.nested_reference.size_for_metadata_loop.body
    simp only [bne_iff_ne]
    split
    · rename_i hn
      have hpos : 0 < idx.val := by
        have hz : idx.val ≠ 0 := by
          intro h
          apply hn
          exact UScalar.eq_of_val_eq (by simpa using h)
        omega
      step with Usize.sub_spec (x := idx) (y := 1#usize) (by simp; omega)
        as ⟨j, hj, _⟩
      have hj' : j.val + 1 = idx.val := by
        change j.val = idx.val - 1 at hj
        omega
      have hjlt : j.val < leading.val.length := by omega
      step with Slice.index_usize_spec leading j hjlt as ⟨layer, hlayer⟩
      have hmath : NestedReference.checkedState (leading.val.drop j.val) elem alignment metadata =
          NestedReference.checkedLayer layer
            (NestedReference.checkedState (leading.val.drop idx.val) elem alignment metadata) := by
        rw [NestedReference.checkedState_drop leading.val elem alignment metadata j.val hjlt,
          hj', hlayer]
      cases state with
      | none =>
        have hnext : (none : Option (Usize × Usize)).map nestedStateView =
            NestedReference.checkedState (leading.val.drop j.val) elem alignment metadata := by
          rw [hmath, ← hv]
          simp [NestedReference.checkedLayer]
        apply WP.spec.ret
        change j.val ≤ leading.val.length ∧
          (none : Option (Usize × Usize)).map nestedStateView =
            NestedReference.checkedState (leading.val.drop j.val) elem alignment metadata ∧
          j.val < idx.val
        exact ⟨by omega, hnext, by omega⟩
      | some pair =>
        have heq : NestedReference.checkedState (leading.val.drop idx.val) elem alignment metadata =
            some (nestedStateView pair) := hv.symm
        obtain ⟨hvalid, heq, hfit⟩ := NestedReference.checkedState_some
          (leading.val.drop idx.val) elem alignment metadata (nestedStateView pair) heq
        have hpower : pair.2.val.isPowerOfTwo := by
          have hp := NestedReference.state_alignment_power (leading.val.drop idx.val)
            elem alignment metadata hvalid
          rw [heq] at hp
          exact hp
        rcases pair with ⟨size, currentAlignment⟩
        step with nested_apply_layer_spec layer size currentAlignment hpower as ⟨next, hnext⟩
        have hview : next.map nestedStateView =
            NestedReference.checkedState (leading.val.drop j.val) elem alignment metadata := by
          rw [hmath, ← hv]
          exact hnext
        exact ⟨by omega, hview, by omega⟩
    · rename_i hz
      have heq : idx.val = 0 := by
        have h : idx = 0#usize := not_ne_iff.mp hz
        simpa using congrArg UScalar.val h
      simpa only [heq, List.drop_zero, WP.spec_ok] using hv
  · exact ⟨hi, hv⟩

theorem nested_reference_size_spec
    (leading : Slice layout.nested_reference.NestedLayer) (elem_size leaf_align elems : Usize) :
    layout.nested_reference.size_for_metadata leading elem_size leaf_align elems
      ⦃ result => result.map UScalar.val =
        NestedReference.checkedSize leading.val elem_size.val leaf_align.val elems.val ⦄ := by
  classical
  unfold layout.nested_reference.size_for_metadata
  step as ⟨leafPow, hp⟩
  cases leafPow with
  | false =>
    have hn : ¬leaf_align.val.isPowerOfTwo := by
      intro h
      have := (Iff.of_eq hp).mpr h
      contradiction
    have hv : ¬NestedReference.valid leading.val elem_size.val leaf_align.val := by
      intro h
      exact hn h.1
    simp only [Bool.false_eq_true, if_false, WP.spec_ok, Option.map_none,
      NestedReference.checkedSize, hv, if_false]
  | true =>
    have hpow : leaf_align.val.isPowerOfTwo := (Iff.of_eq hp).mp rfl
    have hpos := Nat.pos_of_isPowerOfTwo hpow
    simp only [if_true]
    step with Usize.rem_spec elem_size (y := leaf_align) (by omega) as ⟨remainder, hr⟩
    simp only [bne_iff_ne]
    split
    · rename_i hn
      have hv : ¬NestedReference.valid leading.val elem_size.val leaf_align.val := by
        intro h
        apply hn
        exact UScalar.eq_of_val_eq (by simpa only [hr, show (0#usize).val = 0 by simp] using h.2.1)
      simp only [WP.spec_ok, Option.map_none, NestedReference.checkedSize, hv, if_false]
    · rename_i hz
      have hzero : elem_size.val % leaf_align.val = 0 := by
        have h : remainder = 0#usize := not_ne_iff.mp hz
        simpa only [hr, show (0#usize).val = 0 by simp] using congrArg UScalar.val h
      step as ⟨product, hproduct⟩
      let start : Option (Usize × Usize) := match product with
        | none => none
        | some size => some (size, leaf_align)
      have hinit : start.map nestedStateView =
          NestedReference.checkedState (leading.val.drop (Slice.len leading).val)
            elem_size.val leaf_align.val elems.val := by
        have hvalid : NestedReference.valid [] elem_size.val leaf_align.val :=
          ⟨hpow, hzero, by simp⟩
        simp only [Slice.len_val, Slice.length, List.drop_length, NestedReference.checkedState,
          hvalid, if_true, NestedReference.state, List.foldr_nil]
        cases product with
        | none =>
          have hn : ¬elems.val * elem_size.val ≤ Usize.max := by
            simp only [] at hproduct
            rw [Nat.mul_comm]
            omega
          simp only [start, Option.map_none, hn, if_false]
        | some size =>
          have hv : size.val = elems.val * elem_size.val := by
            simp only [] at hproduct
            rw [Nat.mul_comm]
            exact hproduct.2.1
          have hf : elems.val * elem_size.val ≤ Usize.max := by
            simp only [] at hproduct
            rw [Nat.mul_comm]
            exact hproduct.1
          simp only [start, Option.map_some, nestedStateView, hv, hf, if_true]
      have hrun := nested_reference_loop_spec leading elem_size.val leaf_align.val elems.val
        start (Slice.len leading) (by simp only [Slice.len_val, Slice.length, le_refl]) hinit
      cases product <;> simp only [start] at hrun ⊢
      all_goals
        step with hrun as ⟨out, hout⟩
        have hfinal : (match out with | none => none | some pair => some pair.1).map UScalar.val =
            NestedReference.checkedSize leading.val elem_size.val leaf_align.val elems.val := by
          rw [NestedReference.checkedSize_eq_map, ← hout]
          cases out <;> rfl
        cases out with
        | none => simpa only [WP.spec_ok] using hfinal
        | some pair =>
          rcases pair with ⟨size, alignment⟩
          dsimp only
          exact WP.spec.ret hfinal

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

theorem nested_round_up_spec : Zerocopy.Specs.nested_round_up_spec := by
  intro size align sizeValue hsize alignValue halign
  apply WP.spec_mono (Raw.nested_round_up_spec size align)
  intro rounded hr
  refine ⟨rounded.map unsignedWord, ?_, hr⟩
  cases rounded <;> rfl
register_spec_step nested_round_up_spec

theorem nested_reference_size_spec : Zerocopy.Specs.nested_reference_size_spec := by
  intro leading elem_size leaf_align elems layers hl elemValue he alignmentValue ha metadataValue hn
  apply WP.spec_mono (Raw.nested_reference_size_spec leading elem_size leaf_align elems)
  intro result hr
  refine ⟨result.map unsignedWord, ?_, hr⟩
  cases result <;> rfl
register_spec_step nested_reference_size_spec

/-- No descriptor bit pattern is excluded by a hidden decoder guard. -/
theorem nested_layer_decoder_total (raw : layout.nested_reference.NestedLayer) :
    isValid raw := by
  refine ⟨⟨unsignedWord raw.packed, unsignedWord raw.min_align,
    unsignedWord raw.prefix_bytes⟩, ?_⟩
  rfl

theorem nested_layers_decoder_total (raw : Slice layout.nested_reference.NestedLayer) :
    isValid raw :=
  (slice_valid_iff raw).mpr (fun layer _ => nested_layer_decoder_total layer)

@[contract_simps] theorem nested_reference_size_spec_implies_required
    (leading : Slice layout.nested_reference.NestedLayer) (elem_size leaf_align elems : Usize)
    (run : Result (Option Usize))
    (provided : Zerocopy.Specs.nested_reference_size_spec_contract leading elem_size leaf_align elems run) :
    Zerocopy.Obligations.nested_reference_size_spec_contract leading elem_size leaf_align elems run := by
  obtain ⟨layers, hlayers⟩ := nested_layers_decoder_total leading
  have execution := provided layers hlayers (unsignedWord elem_size) rfl
    (unsignedWord leaf_align) rfl (unsignedWord elems) rfl
  apply WP.spec_mono execution
  rintro result ⟨decoded, hdecoded, hr⟩
  exact hr

@[contract_simps] theorem nested_round_up_spec_implies_required
    (size align : Usize) (run : Result (Option Usize))
    (provided : Zerocopy.Specs.nested_round_up_spec_contract size align run) :
    Zerocopy.Obligations.nested_round_up_spec_contract size align run := by
  have execution := provided (unsignedWord size) rfl (unsignedWord align) rfl
  apply WP.spec_mono execution
  rintro rounded ⟨decoded, hdecoded, hr⟩
  exact hr

end Zerocopy.Proofs
