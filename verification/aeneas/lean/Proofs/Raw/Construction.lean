/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Raw.Composition
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false
/- Lift detailed raw extension facts to the independent fragment operation. This
supplies the constructor loop's mathematical state transition.
-/
theorem extend_value_spec (self field : layout.DstLayout) (packed : Option NonZeroUsize)
    (hself : alignmentDomain self.align.val.val)
    (hfield : alignmentDomain field.align.val.val)
    (hpacked : ∀ a ∈ packed, alignmentDomain a.val.val)
    (hcanonical : canonicalLayout field)
    (hfit : (layoutValue self).extendFits (layoutValue field) (packingValue packed) Usize.max) :
    layout.DstLayout.extend self field packed
      ⦃ r => layoutValue r = (layoutValue self).extend (layoutValue field) (packingValue packed) ∧ canonicalLayout r ⦄ := by
  cases hs : self.size_info with
  | SliceDst tail => simp [layoutValue, hs, LayoutMath.LayoutValue.extendFits] at hfit
  | Sized size =>
    have hf : match field.size_info with
      | .Sized s => placement size field packed + s.val ≤ Usize.max
      | .SliceDst t => placement size field packed + t.offset.val ≤ Usize.max ∧
        placement size field packed + t.size_base.val ≤ Usize.max := by
      cases hfs : field.size_info <;>
        simpa only [layoutValue, hs, hfs, LayoutMath.LayoutValue.extendFits,
          placement, fieldAlignment, trailingFormula, byteFormula] using hfit
    apply WP.spec_mono (extend_spec self field packed size hs hself hfield hpacked hf)
    rintro r ⟨ha, hu, hr⟩
    cases hfs : field.size_info with
    | Sized s =>
      simp only [hfs] at hr
      obtain ⟨bytes, hb, hv⟩ := hr
      simp only [layoutValue, hb, hs, hfs, LayoutMath.LayoutValue.extend,
        canonicalLayout, ha, hu, hv, placement, fieldAlignment]
      exact ⟨rfl, trivial⟩
    | SliceDst t =>
      simp only [hfs] at hr
      simp only [canonicalLayout, hfs] at hcanonical
      obtain ⟨u, hsi, ho, hb, he, hc⟩ := hr
      simp only [layoutValue, hsi, hs, hfs, LayoutMath.LayoutValue.extend,
        canonicalLayout, ha, hu, trailingFormula, byteFormula, ho, hb, he, hc,
        placement, fieldAlignment]
      exact ⟨rfl, hcanonical⟩

attribute [step] extend_value_spec

/- Lift detailed raw padding facts to the fragment operation used after the
loop.
-/
theorem pad_value_spec (self : layout.DstLayout)
    (ha : self.align.val.val.isPowerOfTwo)
    (hc : canonicalLayout self)
    (hf : (layoutValue self).padFits Usize.max) :
    layout.DstLayout.pad_to_align self
      ⦃ r => layoutValue r = (layoutValue self).pad ∧ canonicalLayout r ⦄ := by
  have hfit : match self.size_info with
    | .Sized s => LayoutMath.roundUp s.val self.align.val.val ≤ Usize.max
    | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val ∧
      (if (trailingFormula t).align < self.align.val.val then
        LayoutMath.roundUp t.size_base.val (trailingFormula t).align +
          (trailingFormula t).phase ≤ Usize.max
       else LayoutMath.roundUp t.size_base.val self.align.val.val ≤ Usize.max) := by
    cases hs : self.size_info with
    | Sized s => simpa only [layoutValue, hs, LayoutMath.LayoutValue.padFits] using hf
    | SliceDst t =>
      simp only [canonicalLayout, hs] at hc
      simp only []
      refine ⟨hc, ?_⟩
      simpa only [layoutValue, hs, LayoutMath.LayoutValue.padFits,
        trailingFormula, byteFormula] using hf
  apply WP.spec_mono (pad_to_align_spec self ha hfit)
  rintro r ⟨hcanonical, hr, hp⟩
  refine ⟨?_, hcanonical⟩
  cases hs : self.size_info with
  | Sized s =>
    simp only [hs] at hp
    obtain ⟨p, hsi, hv, hu⟩ := hp
    simp only [layoutValue, hsi, hs, LayoutMath.LayoutValue.pad, hr, hv, hu]
  | SliceDst t =>
    simp only [hs] at hp
    obtain ⟨u, hsi, hv, hu⟩ := hp
    simp only [layoutValue, hsi, hs, LayoutMath.LayoutValue.pad, hr, hv, hu]

attribute [step] pad_value_spec

theorem construction_prefix_step (fields : Slice layout.DstLayout) (initial : LayoutMath.LayoutValue)
    (packed : Option NonZeroUsize) (i : Nat) (hi : i < fields.val.length) :
    constructionPrefix fields initial packed (i + 1) =
      (constructionPrefix fields initial packed i).extend (layoutValue fields.val[i]) (packingValue packed) := by
  unfold constructionPrefix
  rw [LayoutMath.LayoutValue.prefixValue_step _ _ _ _ (by simpa only [List.length_map] using hi)]
  simp only [List.getElem_map]

/- Relate each extracted loop state to the independently computed field prefix.
The shared indexed-loop adapter proves termination from the remaining field
count; each body step preserves the representation facts needed for the next.
-/
theorem constructor_loop_spec (packed : Option NonZeroUsize) (fields : Slice layout.DstLayout)
    (initial : LayoutMath.LayoutValue) (self : layout.DstLayout) (i : Usize)
    (hp : ∀ a ∈ packed, alignmentDomain a.val.val)
    (hd : constructionDomain fields initial packed)
    (hi : i.val ≤ fields.val.length)
    (hv : layoutValue self = constructionPrefix fields initial packed i.val)
    (hc : canonicalLayout self) :
    layout.DstLayout.for_repr_c_struct_loop packed fields self i
      ⦃ r => layoutValue r = constructionPrefix fields initial packed fields.val.length ∧ canonicalLayout r ⦄ := by
  unfold layout.DstLayout.for_repr_c_struct_loop
  apply AeneasContracts.indexed_loop_spec fields.val.length layoutValue
    (constructionPrefix fields initial packed) canonicalLayout
  · intro value idx hi hv hc
    unfold layout.DstLayout.for_repr_c_struct_loop.body
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]
    split
    · rename_i hlt
      have hlt' : idx.val < fields.val.length := hlt
      step with Slice.index_usize_spec fields idx hlt' as ⟨field, hf⟩
      obtain ⟨hself, hfield, hcanon, hfits⟩ := hd idx.val hlt'
      have hsa : alignmentDomain value.align.val.val := by
        have hh := congrArg LayoutMath.LayoutValue.align hv
        change value.align.val.val = _ at hh
        rw [hh]
        exact hself
      have hfa : alignmentDomain field.align.val.val := by rw [hf]; exact hfield
      have hca : canonicalLayout field := by rw [hf]; exact hcanon
      have hfit : (layoutValue value).extendFits (layoutValue field) (packingValue packed) Usize.max := by
        rw [hv, hf]
        exact hfits
      step as ⟨next, hnext, hcn⟩
      have hroom : idx.val + (1#usize).val ≤ Usize.max := by
        have := fields.property
        change idx.val + 1 ≤ Usize.max
        omega
      step with Usize.add_spec (x := idx) (y := 1#usize) hroom as ⟨j, hj⟩
      change j.val = idx.val + 1 at hj
      refine ⟨hlt', hj, ?_, hcn⟩
      rw [hj, construction_prefix_step fields initial packed idx.val hlt', hnext, hv, hf]
    · rename_i hdone
      have heq : idx.val = fields.val.length := by omega
      exact WP.spec.ret ⟨heq, hv, hc⟩
  · exact hi
  · exact hv
  · exact hc

/- Stitch together initialization, every field append, and final padding. The
requirements cover arbitrary field lists in the independent construction
domain, rather than assuming that the constructor already returned correctly.
-/
theorem for_repr_c_struct_spec :
  ∀ (repr_align repr_packed : Option NonZeroUsize) (fields : Slice layout.DstLayout), ∀ (ha : (∀ a ∈ repr_align, alignmentDomain a.val.val : Prop)), ∀ (hp : (∀ a ∈ repr_packed, alignmentDomain a.val.val : Prop)), ∀ (hd : (constructionDomain fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) repr_packed : Prop)), ∀ (hlast : (alignmentDomain
    (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) repr_packed fields.val.length).align : Prop)), ∀ (hfit : ((constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align))
    repr_packed fields.val.length).padFits Usize.max : Prop)),
    @Zerocopy.layout.DstLayout.for_repr_c_struct repr_align repr_packed fields ⦃ r => layoutValue r =
    (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) repr_packed fields.val.length).pad ∧ canonicalLayout r ⦄ := by
  intro repr_align packed fields ha hp hd hlast hfit
  unfold layout.DstLayout.for_repr_c_struct
  step with new_zst_spec repr_align (fun a h => (ha a h).1) as ⟨start, halign, hsize, hunpadded⟩
  have hv : layoutValue start = constructionPrefix fields
      (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed (0#usize).val := by
    simp only [constructionPrefix, LayoutMath.LayoutValue.prefixValue, show (0#usize).val = 0 by simp,
      List.take_zero, List.foldl_nil, layoutValue, hsize, hunpadded, halign,
      initialAlignment, LayoutMath.LayoutValue.initial]
    cases repr_align <;> rfl
  have hc : canonicalLayout start := by simp only [canonicalLayout, hsize]
  step with constructor_loop_spec packed fields _ start 0#usize hp hd (by simp) hv hc as ⟨complete, hv, hc⟩
  step with pad_value_spec complete (by
    have hh := congrArg LayoutMath.LayoutValue.align hv
    change complete.align.val.val = _ at hh
    rw [hh]
    exact hlast.1) hc (by rw [hv]; exact hfit) as ⟨result, hr, hcanonical⟩
  exact ⟨by rw [hr, hv], hcanonical⟩

end Zerocopy.Proofs.Raw
