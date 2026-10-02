/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Corollaries
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.NestedReference
open LayoutMath

def prefixValue (bytes : Nat) : LayoutValue := ⟨1, .fixed bytes, true⟩

def layerFragment (inner : LayoutValue) (minimum packing bytes : Nat) : LayoutValue :=
  ((LayoutValue.initial minimum).extend (prefixValue bytes) packing).extend inner packing

theorem prefixValue_extend (minimum packing bytes : Nat)
    (hm : 0 < minimum) (hp : 0 < packing) :
    (LayoutValue.initial minimum).extend (prefixValue bytes) packing =
      ⟨minimum, .fixed bytes, true⟩ := by
  have hmin : min 1 packing = 1 := Nat.min_eq_left (by omega)
  have hmax : max minimum 1 = minimum := Nat.max_eq_left (by omega)
  simp [LayoutValue.initial, LayoutValue.extend, prefixValue, hmin, hmax, roundUp]

theorem layerFragment_align (inner : LayoutValue) (minimum packing bytes : Nat)
    (hm : 0 < minimum) (hp : 0 < packing) :
    (layerFragment inner minimum packing bytes).align = max minimum (min inner.align packing) := by
  rw [layerFragment, prefixValue_extend minimum packing bytes hm hp]
  rfl

theorem layerFragment_size (inner : LayoutValue) (minimum packing bytes n : Nat)
    (hm : 0 < minimum) (hp : 0 < packing) :
    (layerFragment inner minimum packing bytes).size n =
      roundUp bytes (min inner.align packing) + inner.size n := by
  rw [layerFragment, prefixValue_extend minimum packing bytes hm hp]
  exact LayoutValue.extend_size _ _ _ _ _ rfl

theorem layerFragment_payload (inner : LayoutValue) (f : Formula)
    (minimum packing bytes : Nat) (hf : inner.payload = .trailing f)
    (hm : 0 < minimum) (hp : 0 < packing) :
    (layerFragment inner minimum packing bytes).payload =
      .trailing { f with base := roundUp bytes (min inner.align packing) + f.base, offset := roundUp bytes (min inner.align packing) + f.offset } := by
  rw [layerFragment, prefixValue_extend minimum packing bytes hm hp]
  simp only [LayoutValue.extend, hf]

theorem layerFragment_bounds (inner : LayoutValue) (f : Formula)
    (minimum packing bytes limit : Nat) (hf : inner.payload = .trailing f)
    (hm : 0 < minimum) (hp : 0 < packing) (hi : 0 < inner.align)
    (ho : f.offset ≤ inner.size 0)
    (hfit : roundUp (roundUp bytes (min inner.align packing) + inner.size 0)
      (max minimum (min inner.align packing)) ≤ limit) :
    bytes ≤ limit ∧ roundUp bytes (min inner.align packing) + f.offset ≤ limit ∧
      roundUp bytes (min inner.align packing) + f.base ≤ limit := by
  have hplace := (roundUp_properties bytes (min inner.align packing) (by omega)).1
  have houter := (roundUp_properties
    (roundUp bytes (min inner.align packing) + inner.size 0)
    (max minimum (min inner.align packing)) (by omega)).1
  have hbase : f.base ≤ inner.size 0 := by
    simp only [LayoutValue.size, hf, Formula.size, Formula.bytes, roundUp]
    omega
  omega

theorem layerFragment_padFits (inner : LayoutValue) (f : Formula)
    (minimum packing bytes limit : Nat) (hf : inner.payload = .trailing f)
    (hm : 0 < minimum) (hp : 0 < packing)
    (ha : f.align.isPowerOfTwo)
    (hout : (max minimum (min inner.align packing)).isPowerOfTwo)
    (hfit : roundUp (roundUp bytes (min inner.align packing) + inner.size 0)
      (max minimum (min inner.align packing)) ≤ limit) :
    (layerFragment inner minimum packing bytes).padFits limit := by
  let g : Formula := { f with base := roundUp bytes (min inner.align packing) + f.base, offset := roundUp bytes (min inner.align packing) + f.offset }
  have hv := layerFragment_payload inner f minimum packing bytes hf hm hp
  change (layerFragment inner minimum packing bytes).payload = .trailing g at hv
  apply LayoutValue.padFits_of_zero_size _ g limit hv
  · exact Nat.pos_of_isPowerOfTwo ha
  · rw [layerFragment_align inner minimum packing bytes hm hp]
    exact Nat.pos_of_isPowerOfTwo hout
  · rw [layerFragment_align inner minimum packing bytes hm hp]
    change if f.align < max minimum (min inner.align packing) then
      f.align ∣ max minimum (min inner.align packing) else
      max minimum (min inner.align packing) ∣ f.align
    split
    · exact Raw.power_dvd_of_le _ _ ha hout (by omega)
    · exact Raw.power_dvd_of_le _ _ hout ha (by omega)
  · rw [layerFragment_size inner minimum packing bytes 0 hm hp,
      layerFragment_align inner minimum packing bytes hm hp]
    exact hfit

theorem layerFragment_pad_size (inner : LayoutValue) (f : Formula)
    (minimum packing bytes n : Nat) (hf : inner.payload = .trailing f)
    (hm : 0 < minimum) (hp : 0 < packing)
    (ha : f.align.isPowerOfTwo)
    (hout : (max minimum (min inner.align packing)).isPowerOfTwo) :
    ((layerFragment inner minimum packing bytes).pad).size n =
      roundUp (roundUp bytes (min inner.align packing) + inner.size n)
        (max minimum (min inner.align packing)) := by
  let g : Formula := { f with base := roundUp bytes (min inner.align packing) + f.base, offset := roundUp bytes (min inner.align packing) + f.offset }
  have hv := layerFragment_payload inner f minimum packing bytes hf hm hp
  change (layerFragment inner minimum packing bytes).payload = .trailing g at hv
  have hd : if g.align < (layerFragment inner minimum packing bytes).align then
      g.align ∣ (layerFragment inner minimum packing bytes).align else
      (layerFragment inner minimum packing bytes).align ∣ g.align := by
    rw [layerFragment_align inner minimum packing bytes hm hp]
    change if f.align < max minimum (min inner.align packing) then
      f.align ∣ max minimum (min inner.align packing) else
      max minimum (min inner.align packing) ∣ f.align
    split
    · exact Raw.power_dvd_of_le _ _ ha hout (by omega)
    · exact Raw.power_dvd_of_le _ _ hout ha (by omega)
  have hpad := pad_size g n (layerFragment inner minimum packing bytes).align
    (Nat.pos_of_isPowerOfTwo ha)
    (by rw [layerFragment_align inner minimum packing bytes hm hp];
        exact Nat.pos_of_isPowerOfTwo hout) hd
  have hs : (layerFragment inner minimum packing bytes).size n = g.size n := by
    simp only [LayoutValue.size, hv]
  rw [← hs, layerFragment_size inner minimum packing bytes n hm hp,
    layerFragment_align inner minimum packing bytes hm hp] at hpad
  simpa only [LayoutValue.pad, hv, LayoutValue.size,
    layerFragment_align inner minimum packing bytes hm hp] using hpad

end Zerocopy.Proofs.NestedReference

namespace Zerocopy.Proofs.Raw
open LayoutMath NestedReference

def nestedPrefix (bytes : Usize) : layout.DstLayout :=
  { align := ⟨1#usize⟩, size_info := .Sized bytes, statically_shallow_unpadded := true }

theorem nested_prefix_value (bytes : Usize) :
    layoutValue (nestedPrefix bytes) = NestedReference.prefixValue bytes.val := rfl

/-- One recursive layer has the same exact static fit domain as the direct
reference. Its inner fragment retains the complete inner size for every count. -/
theorem nested_layer_constructor_spec (minimum packed : NonZeroUsize) (bytes : Usize)
    (inner : layout.DstLayout) (tail : layout.TrailingSliceLayout Usize)
    (fields : Slice layout.DstLayout) (hfields : fields.val = [nestedPrefix bytes, inner])
    (hm : alignmentDomain minimum.val.val) (hp : alignmentDomain packed.val.val)
    (hi : alignmentDomain inner.align.val.val) (hc : canonicalLayout inner)
    (hs : inner.size_info = .SliceDst tail)
    (ho : tail.offset.val ≤ (layoutValue inner).size 0)
    (hfit : roundUp (roundUp bytes.val (min inner.align.val.val packed.val.val) +
      (layoutValue inner).size 0) (max minimum.val.val (min inner.align.val.val packed.val.val)) ≤ Usize.max) :
    layout.DstLayout.for_repr_c_struct (some minimum) (some packed) fields
      ⦃ r => canonicalLayout r ∧
        r.align.val.val = max minimum.val.val (min inner.align.val.val packed.val.val) ∧
        (∀ n : Nat, (layoutValue r).size n =
          roundUp (roundUp bytes.val (min inner.align.val.val packed.val.val) +
            (layoutValue inner).size n)
            (max minimum.val.val (min inner.align.val.val packed.val.val))) ∧
        ∃ out, r.size_info = .SliceDst out ∧ out.offset.val ≤ (layoutValue r).size 0 ⦄ := by
  have hmpos := Nat.pos_of_isPowerOfTwo hm.1
  have hppos := Nat.pos_of_isPowerOfTwo hp.1
  have hipos := Nat.pos_of_isPowerOfTwo hi.1
  have hplacePow : (min inner.align.val.val packed.val.val).isPowerOfTwo := by
    by_cases h : inner.align.val.val ≤ packed.val.val
    · simpa only [Nat.min_eq_left h] using hi.1
    · simpa only [Nat.min_eq_right (by omega : packed.val.val ≤ inner.align.val.val)] using hp.1
  have houtPow : (max minimum.val.val (min inner.align.val.val packed.val.val)).isPowerOfTwo := by
    by_cases h : minimum.val.val ≤ min inner.align.val.val packed.val.val
    · simpa only [Nat.max_eq_right h] using hplacePow
    · simpa only [Nat.max_eq_left (by omega : min inner.align.val.val packed.val.val ≤ minimum.val.val)] using hm.1
  have hout : alignmentDomain (max minimum.val.val (min inner.align.val.val packed.val.val)) :=
    ⟨houtPow, max_le hm.2 (le_trans (Nat.min_le_left _ _) hi.2)⟩
  have hf : (layoutValue inner).payload = .trailing (trailingFormula tail) := by
    simp only [layoutValue, hs]
  have hformulaPow : (trailingFormula tail).align.isPowerOfTwo := by
    exact ⟨_, rfl⟩
  have bounds := layerFragment_bounds (layoutValue inner) (trailingFormula tail)
    minimum.val.val packed.val.val bytes.val Usize.max hf hmpos hppos hipos ho hfit
  have hprefix : constructionPrefix fields (LayoutValue.initial (initialAlignment (some minimum)))
      (some packed) 1 = ⟨minimum.val.val, .fixed bytes.val, true⟩ := by
    simp only [constructionPrefix, hfields, List.map_cons, List.map_nil,
      LayoutValue.prefixValue, List.take_succ_cons, List.take_zero, List.foldl_cons,
      List.foldl_nil, nested_prefix_value, initialAlignment, packingValue,
      Option.map_some, Option.getD_some]
    exact prefixValue_extend _ _ _ hmpos hppos
  have hcomplete : constructionPrefix fields (LayoutValue.initial (initialAlignment (some minimum)))
      (some packed) fields.val.length =
      layerFragment (layoutValue inner) minimum.val.val packed.val.val bytes.val := by
    simp only [constructionPrefix, hfields, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, LayoutValue.prefixValue, List.take_succ_cons,
      List.take_zero, List.foldl_cons, List.foldl_nil, nested_prefix_value,
      initialAlignment, packingValue, Option.map_some, Option.getD_some]
    rfl
  have hd : constructionDomain fields (LayoutValue.initial (initialAlignment (some minimum)))
      (some packed) := by
    intro i hil
    have hil' : i < 2 := by simpa only [hfields, List.length_cons, List.length_nil] using hil
    have heither : i = 0 ∨ i = 1 := by omega
    rcases heither with rfl | rfl
    · simp only [constructionPrefix, LayoutValue.prefixValue, List.take_zero, List.foldl_nil,
        initialAlignment, Option.map_some, Option.getD_some, LayoutValue.initial,
        hfields, List.getElem_cons_zero, nestedPrefix, canonicalLayout, layoutValue,
        LayoutValue.extendFits, packingValue, show (1#usize).val = 1 by simp]
      have hmin : min 1 packed.val.val = 1 := Nat.min_eq_left (by omega)
      simpa only [hmin, roundUp, Nat.zero_mod, Nat.mod_self, Nat.zero_add] using
        (show alignmentDomain minimum.val.val ∧ alignmentDomain 1 ∧ True ∧ bytes.val ≤ Usize.max from
          ⟨hm, ⟨⟨0, rfl⟩, by decide⟩, trivial, bounds.1⟩)
    · rw [hprefix]
      simp only [hfields, List.getElem_cons_succ, List.getElem_cons_zero]
      refine ⟨hm, hi, hc, ?_⟩
      simp only [LayoutValue.extendFits, hf, packingValue, Option.map_some, Option.getD_some]
      exact bounds.2
  have hlast : alignmentDomain (constructionPrefix fields
      (LayoutValue.initial (initialAlignment (some minimum))) (some packed) fields.val.length).align := by
    rw [hcomplete, layerFragment_align _ _ _ _ hmpos hppos]
    exact hout
  have hpad : (constructionPrefix fields (LayoutValue.initial (initialAlignment (some minimum)))
      (some packed) fields.val.length).padFits Usize.max := by
    rw [hcomplete]
    exact layerFragment_padFits _ _ _ _ _ _ hf hmpos hppos hformulaPow houtPow hfit
  step with for_repr_c_struct_spec (some minimum) (some packed) fields
    (by intro a ha; cases ha; exact hm) (by intro a ha; cases ha; exact hp)
    hd hlast hpad as ⟨result, hr, hcanonical⟩
  rw [hcomplete] at hr
  have halign : result.align.val.val = max minimum.val.val (min inner.align.val.val packed.val.val) := by
    have h := congrArg LayoutValue.align hr
    simpa only [layoutValue, LayoutValue.pad, layerFragment_align _ _ _ _ hmpos hppos] using h
  have hsize : ∀ n : Nat, (layoutValue result).size n =
      roundUp (roundUp bytes.val (min inner.align.val.val packed.val.val) +
        (layoutValue inner).size n) (max minimum.val.val (min inner.align.val.val packed.val.val)) := by
    intro n
    rw [hr]
    exact layerFragment_pad_size _ _ _ _ _ _ hf hmpos hppos hformulaPow houtPow
  have hpayload := congrArg LayoutValue.payload hr
  have hfragment := layerFragment_payload (layoutValue inner) (trailingFormula tail)
    minimum.val.val packed.val.val bytes.val hf hmpos hppos
  simp only [LayoutValue.pad, hfragment] at hpayload
  cases hresult : result.size_info with
  | Sized size => simp only [layoutValue, hresult] at hpayload; contradiction
  | SliceDst out =>
    have hformula : trailingFormula out =
        ({ trailingFormula tail with base := roundUp bytes.val (min inner.align.val.val packed.val.val) + (trailingFormula tail).base, offset := roundUp bytes.val (min inner.align.val.val packed.val.val) + (trailingFormula tail).offset }).pad
          (layerFragment (layoutValue inner) minimum.val.val packed.val.val bytes.val).align := by
      simpa only [layoutValue, hresult, Payload.trailing.injEq] using hpayload
    have hoffset := congrArg Formula.offset hformula
    simp only [trailingFormula, byteFormula, Formula.pad] at hoffset
    split at hoffset <;> simp only at hoffset
    all_goals
      refine ⟨hcanonical, halign, hsize, out, rfl, ?_⟩
      rw [hsize 0, hoffset]
      have houter := (roundUp_properties
        (roundUp bytes.val (min inner.align.val.val packed.val.val) + (layoutValue inner).size 0)
        (max minimum.val.val (min inner.align.val.val packed.val.val))
        (Nat.pos_of_isPowerOfTwo houtPow)).1
      omega

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs.NestedReference

def runtime (layers : List layout.nested_reference.NestedLayer) (elem alignment : Nat)
    (inner : layout.DstLayout) : Prop :=
  canonicalLayout inner ∧
    (∀ n : Nat, ((layoutValue inner).size n, inner.align.val.val) = state layers elem alignment n) ∧
    ∃ tail, inner.size_info = .SliceDst tail ∧ tail.offset.val ≤ (layoutValue inner).size 0

def layerDomain (layer : layout.nested_reference.NestedLayer) : Prop :=
  layerValid layer ∧ layer.packed.val ≤ 2 ^ 29

end Zerocopy.Proofs.NestedReference

namespace Zerocopy.Proofs.Raw
open LayoutMath NestedReference

/-- Reverse construction terminates for any admitted descriptor length. Its
invariant keeps the physical tail offset and the complete per-metadata size. -/
theorem nested_construction_loop_spec
    (leading : Slice layout.nested_reference.NestedLayer) (elem alignment : Nat)
    (inner : layout.DstLayout) (i : Usize)
    (hvalid : NestedReference.valid leading.val elem alignment)
    (ha : alignment ≤ 2 ^ 29)
    (hb : ∀ layer ∈ leading.val, layer.packed.val ≤ 2 ^ 29)
    (hfit : (NestedReference.state leading.val elem alignment 0).1 ≤ Usize.max)
    (hi : i.val ≤ leading.val.length)
    (hv : NestedReference.runtime (leading.val.drop i.val) elem alignment inner) :
    layout.nested_reference.assert_matches_dst_layout_loop1 leading inner i
      ⦃ out => NestedReference.runtime leading.val elem alignment out ⦄ := by
  unfold layout.nested_reference.assert_matches_dst_layout_loop1
  apply loop.spec_decr_nat
    (fun s : layout.DstLayout × Usize => s.2.val)
    (fun s => s.2.val ≤ leading.val.length ∧
      NestedReference.runtime (leading.val.drop s.2.val) elem alignment s.1)
  · rintro ⟨inner, idx⟩ ⟨hi, hv⟩
    dsimp only at hi hv ⊢
    unfold layout.nested_reference.assert_matches_dst_layout_loop1.body
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
      have hlmem : layer ∈ leading.val := by rw [hlayer]; exact List.getElem_mem hjlt
      have hl := hvalid.2.2 layer hlmem
      have hpacknz : layer.packed ≠ 0#usize := by
        intro h
        have hp := Nat.pos_of_isPowerOfTwo hl.1
        have hz := congrArg UScalar.val h
        simp only [show (0#usize).val = 0 by simp] at hz
        omega
      have hminnz : layer.min_align ≠ 0#usize := by
        intro h
        have hp := Nat.pos_of_isPowerOfTwo hl.2.1
        have hz := congrArg UScalar.val h
        simp only [show (0#usize).val = 0 by simp] at hz
        omega
      simp only [core.num.nonzero.NonZero.new, cast_eq, hpacknz, hminnz,
        ↓reduceDIte, ↓reduceIte, bind_ok, min_align_eq, lift]
      let fields := Array.to_slice (Array.make 2#usize [nestedPrefix layer.prefix_bytes, inner])
      have hfields : fields.val = [nestedPrefix layer.prefix_bytes, inner] := rfl
      have hinnerValid : NestedReference.valid (leading.val.drop idx.val) elem alignment :=
        ⟨hvalid.1, hvalid.2.1, fun layer hl => hvalid.2.2 layer (List.mem_of_mem_drop hl)⟩
      have halign : inner.align.val.val =
          (NestedReference.state (leading.val.drop idx.val) elem alignment 0).2 :=
        congrArg Prod.snd (hv.2.1 0)
      have hinnerDomain : alignmentDomain inner.align.val.val := by
        rw [halign]
        refine ⟨NestedReference.state_alignment_power _ _ _ _ hinnerValid, ?_⟩
        apply NestedReference.state_alignment_bound _ _ _ _ _ ha
        intro layer hlmem
        have hm := hvalid.2.2 layer (List.mem_of_mem_drop hlmem)
        exact le_trans hm.2.2 (hb layer (List.mem_of_mem_drop hlmem))
      have hminimum : alignmentDomain layer.min_align.val :=
        ⟨hl.2.1, le_trans hl.2.2 (hb layer hlmem)⟩
      have hpacking : alignmentDomain layer.packed.val := ⟨hl.1, hb layer hlmem⟩
      have hmath : ∀ n : Nat, NestedReference.state (leading.val.drop j.val) elem alignment n =
          NestedReference.step layer (NestedReference.state (leading.val.drop idx.val) elem alignment n) := by
        intro n
        rw [List.drop_eq_getElem_cons hjlt, NestedReference.state_cons, hj', ← hlayer]
      obtain ⟨tail, htail, hoffset⟩ := hv.2.2
      have houterFit : roundUp (roundUp layer.prefix_bytes.val
          (min inner.align.val.val layer.packed.val) + (layoutValue inner).size 0)
          (max layer.min_align.val (min inner.align.val.val layer.packed.val)) ≤ Usize.max := by
        have h := NestedReference.suffix_zero_size_fits leading.val elem alignment Usize.max j.val hfit
        rw [hmath 0, ← hv.2.1 0] at h
        exact h
      change layout.DstLayout.for_repr_c_struct (some ⟨layer.min_align⟩)
        (some ⟨layer.packed⟩) fields >>= _ ⦃ _ ⦄
      step with nested_layer_constructor_spec ⟨layer.min_align⟩ ⟨layer.packed⟩
        layer.prefix_bytes inner tail fields hfields hminimum hpacking hinnerDomain
        hv.1 htail hoffset houterFit as ⟨out, hc, houtalign, houtsize, outtail, hoout, hoffout⟩
      refine ⟨by omega, ⟨hc, ?_, outtail, hoout, hoffout⟩, by omega⟩
      intro n
      rw [hmath n, ← hv.2.1 n]
      simp only [NestedReference.step, houtalign, houtsize]
    · rename_i hz
      have heq : idx.val = 0 := by
        have h : idx = 0#usize := not_ne_iff.mp hz
        simpa using congrArg UScalar.val h
      simpa only [heq, List.drop_zero, WP.spec_ok] using hv
  · exact ⟨hi, hv⟩

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs.Raw
open NestedReference

theorem nested_guard_loop_spec (maximum : NonZeroUsize)
    (leading : Slice layout.nested_reference.NestedLayer) (i : Usize) (valid : Bool)
    (hmaximum : maximum.val.val = 2 ^ 29) (hi : i.val ≤ leading.val.length)
    (hv : valid = true → ∀ layer ∈ leading.val.take i.val, NestedReference.layerDomain layer) :
    layout.nested_reference.assert_matches_dst_layout_loop0 maximum leading i valid
      ⦃ out => out = true → ∀ layer ∈ leading.val, NestedReference.layerDomain layer ⦄ := by
  unfold layout.nested_reference.assert_matches_dst_layout_loop0
  apply loop.spec_decr_nat
    (fun s : Usize × Bool => leading.val.length - s.1.val)
    (fun s => s.1.val ≤ leading.val.length ∧
      (s.2 = true → ∀ layer ∈ leading.val.take s.1.val, NestedReference.layerDomain layer))
  · rintro ⟨idx, valid⟩ ⟨hi, hv⟩
    dsimp only at hi hv ⊢
    unfold layout.nested_reference.assert_matches_dst_layout_loop0.body
    simp only [Slice.len_val, Slice.length, UScalar.lt_equiv]
    split
    · rename_i hlt
      step with Slice.index_usize_spec leading idx hlt as ⟨layer, hlayer⟩
      step as ⟨packedPow, hpow⟩
      have hcheck : (if packedPow then do
          let b ← core.num.Usize.is_power_of_two layer.min_align
          if b then
            if layer.min_align > layer.packed then Result.ok false
            else do
              let bound ← core.num.nonzero.NonZero.get
                Usize.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroUsizeInner maximum
              if layer.packed > bound then Result.ok false else Result.ok valid
          else Result.ok false
        else Result.ok false)
          ⦃ next => next = true → valid = true ∧ NestedReference.layerDomain layer ⦄ := by
        cases packedPow with
        | false => simp
        | true =>
          have hp : layer.packed.val.isPowerOfTwo := (Iff.of_eq hpow).mp rfl
          simp only [if_true]
          step as ⟨minimumPow, hminimum⟩
          cases minimumPow with
          | false => simp
          | true =>
            have hm : layer.min_align.val.isPowerOfTwo := (Iff.of_eq hminimum).mp rfl
            simp only [if_true, core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
            split
            · simp
            · rename_i hmin
              split
              · simp
              · rename_i hpack
                apply WP.spec.ret
                intro hvalid
                exact ⟨hvalid, ⟨hp, hm, by omega⟩, by omega⟩
      step with hcheck as ⟨next, hnext⟩
      have hlen := Slice.property leading
      step with Usize.add_spec (x := idx) (y := 1#usize) (by simp; omega) as ⟨j, hj⟩
      change j.val = idx.val + 1 at hj
      refine ⟨by omega, ?_, by omega⟩
      intro htrue item hitem
      obtain ⟨hprevious, hl⟩ := hnext htrue
      rw [hj, List.take_succ_eq_append_getElem hlt] at hitem
      rcases List.mem_append.mp hitem with hleft | hright
      · exact hv hprevious item hleft
      · have heq : item = leading.val[idx.val] := List.mem_singleton.mp hright
        rw [heq, ← hlayer]
        exact hl
    · rename_i hdone
      have hend : idx.val = leading.val.length := by omega
      simpa only [hend, List.take_length, WP.spec_ok] using hv
  · exact ⟨hi, hv⟩

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs.Raw
open LayoutMath NestedReference

theorem nested_word_option_injective (a b : Option Usize)
    (h : a.map UScalar.val = b.map UScalar.val) : a = b := by
  cases a with
  | none => cases b <;> simp_all
  | some x =>
    cases b with
    | none => simp_all
    | some y =>
      have heq : x.val = y.val := by simpa only [Option.map_some, Option.some.injEq] using h
      exact congrArg some (UScalar.eq_of_val_eq heq)

/-- This ordinary assertion harness has no semantic precondition. Every invalid
descriptor returns successfully through a Rust guard, and every admitted
descriptor agrees with production sizing for every machine metadata count. -/
theorem nested_reference_matches_spec
    (leading : Slice layout.nested_reference.NestedLayer) (elem_size leaf_align elems : Usize) :
    layout.nested_reference.assert_matches_dst_layout leading elem_size leaf_align elems
      ⦃ _ => True ⦄ := by
  classical
  unfold layout.nested_reference.assert_matches_dst_layout
  step as ⟨leafPow, hleafPow⟩
  cases leafPow with
  | false => simp
  | true =>
    have hpow : leaf_align.val.isPowerOfTwo := (Iff.of_eq hleafPow).mp rfl
    have hpos := Nat.pos_of_isPowerOfTwo hpow
    simp only [if_true]
    step with current_max_align_spec as ⟨maximum, hmaximum⟩
    simp only [core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
    split
    · simp
    · rename_i hleafBound
      have hbound : leaf_align.val ≤ 2 ^ 29 := by omega
      step with Usize.rem_spec elem_size (y := leaf_align) (by omega) as ⟨remainder, hr⟩
      simp only [bne_iff_ne]
      split
      · simp
      · rename_i hremzero
        have hstride : elem_size.val % leaf_align.val = 0 := by
          have hz : remainder = 0#usize := not_ne_iff.mp hremzero
          simpa only [hr, show (0#usize).val = 0 by simp] using congrArg UScalar.val hz
        step with nested_guard_loop_spec maximum leading 0#usize true hmaximum
          (by simp) (by simp) as ⟨valid, hvalid⟩
        cases valid with
        | false => simp
        | true =>
          have domains := hvalid rfl
          have hv : NestedReference.valid leading.val elem_size.val leaf_align.val :=
            ⟨hpow, hstride, fun layer hl => (domains layer hl).1⟩
          have hb : ∀ layer ∈ leading.val, layer.packed.val ≤ 2 ^ 29 :=
            fun layer hl => (domains layer hl).2
          simp only [if_true]
          step with nested_reference_size_spec leading elem_size leaf_align 0#usize
            as ⟨initialSize, hsize0⟩
          cases initialSize with
          | none => simp
          | some zeroSize =>
            have hfit : (NestedReference.state leading.val elem_size.val leaf_align.val 0).1 ≤ Usize.max := by
              simp only [Option.map_some, NestedReference.checkedSize, hv, if_true] at hsize0
              split at hsize0
              · assumption
              · contradiction
            have hnz : leaf_align ≠ 0#usize := by
              intro h
              have hz := congrArg UScalar.val h
              simp only [show (0#usize).val = 0 by simp] at hz
              omega
            simp only [Option.isNone_some, Bool.false_eq_true,
              core.num.nonzero.NonZero.new, cast_eq, hnz, ↓reduceDIte, ↓reduceIte, bind_ok]
            step with encoding_new_spec ⟨leaf_align⟩ 0#usize hpow
              (by simpa only [show (0#usize).val = 0 by simp] using hpos) as ⟨encoding, hencoding⟩
            let tail : layout.TrailingSliceLayout Usize :=
              { offset := 0#usize, elem_size, size_base := 0#usize,
                size_rounding_align_and_phase := encoding }
            let leaf : layout.DstLayout :=
              { align := ⟨leaf_align⟩, size_info := .SliceDst tail, statically_shallow_unpadded := true }
            have hformula : trailingFormula tail = ⟨0, 0, leaf_align.val, elem_size.val, 0⟩ := by
              have h := trailing_view tail leaf_align.val 0 hpow hpos hencoding
              simpa only [tail, show (0#usize).val = 0 by simp] using h
            have hstart : NestedReference.runtime (leading.val.drop (Slice.len leading).val)
                elem_size.val leaf_align.val leaf := by
              simp only [Slice.len_val, Slice.length, List.drop_length, NestedReference.runtime]
              refine ⟨?_, ?_, tail, rfl, ?_⟩
              · simp only [canonicalLayout, leaf, tail]
                simp only [Nat.add_zero] at hencoding
                omega
              · intro n
                have haligned : n * elem_size.val % leaf_align.val = 0 := by
                  simp only [Nat.mul_mod, hstride, Nat.mul_zero, Nat.zero_mod]
                simp only [layoutValue, leaf, LayoutValue.size, hformula,
                  Formula.size, Formula.bytes, Nat.zero_add, NestedReference.state,
                  List.foldr_nil, roundUp_eq _ _ haligned]
              · simp only [tail, show (0#usize).val = 0 by simp]
                omega
            change layout.nested_reference.assert_matches_dst_layout_loop1 leading leaf
              (Slice.len leading) >>= _ ⦃ _ ⦄
            step with nested_construction_loop_spec leading elem_size.val leaf_align.val
              leaf (Slice.len leading) hv hbound hb hfit
              (by simp only [Slice.len_val, Slice.length, le_refl]) hstart
              as ⟨result, hruntime⟩
            obtain ⟨hcanonical, hsizes, resultTail, htail, hoffset⟩ := hruntime
            rw [htail]
            have htailPositive : 0 < resultTail.size_rounding_align_and_phase._0.val.val := by
              simpa only [canonicalLayout, htail] using hcanonical
            step with size_for_elems_spec resultTail elems htailPositive as ⟨actual, hactual⟩
            step with nested_reference_size_spec leading elem_size leaf_align elems as ⟨expected, hexpected⟩
            have hsize := congrArg Prod.fst (hsizes elems.val)
            simp only [layoutValue, htail, LayoutValue.size] at hsize
            have heq : actual = expected := by
              apply nested_word_option_injective
              rw [hactual, hexpected]
              simp only [Formula.checkedSize, NestedReference.checkedSize, hv, if_true, hsize]
            rw [← heq]
            cases actual <;> simp [massert]

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

theorem nested_reference_matches_spec : Zerocopy.Specs.nested_reference_matches_spec := by
  intro leading elem_size leaf_align elems layers hl elemValue he alignmentValue ha metadataValue hn
  apply WP.spec_mono (Raw.nested_reference_matches_spec leading elem_size leaf_align elems)
  intro result _
  cases result
  exact ⟨(), rfl, trivial⟩
register_spec_step nested_reference_matches_spec

end Zerocopy.Proofs

