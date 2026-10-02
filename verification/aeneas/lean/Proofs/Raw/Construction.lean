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

end Zerocopy.Proofs.Raw
