/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
public import RepresentationLaws
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

theorem byteFormula_decode {E : Type} [RustModel E]
    (raw : layout.TrailingSliceLayout E) (value : layout.TrailingSliceLayout.Fields (ModelOf E))
    (h : layout.TrailingSliceLayout.decode E raw = some value) :
    ModelViews.byteFormula value = byteFormula raw := by
  have fields := (layout.TrailingSliceLayout.decode_decompose E raw value).mp h
  simp only [layout.TrailingSliceLayout.decodeFields, decodeUScalar,
    Option.some.injEq] at fields
  rcases fields with ⟨offset, rfl, elem, _, base, rfl, rounding, hr, rfl⟩
  obtain ⟨ha, hp⟩ := rounding_decode_components raw.size_rounding_align_and_phase rounding hr
  simp only [ModelViews.byteFormula, byteFormula, unsignedWord_value, ha, hp]

theorem trailingFormula_decode (raw : layout.TrailingSliceLayout Usize)
    (value : layout.TrailingSliceLayout.Fields (UnsignedWord .Usize))
    (h : layout.TrailingSliceLayout.decode Usize raw = some value) :
    ModelViews.trailingFormula value = trailingFormula raw := by
  have hb := byteFormula_decode raw value h
  have fields := (layout.TrailingSliceLayout.decode_decompose Usize raw value).mp h
  simp only [layout.TrailingSliceLayout.decodeFields, decodeUScalar,
    Option.some.injEq] at fields
  rcases fields with ⟨offset, rfl, elem, rfl, base, rfl, rounding, _, rfl⟩
  simp only [ModelViews.trailingFormula, trailingFormula, hb, unsignedWord_value]

theorem layoutValue_decode (raw : layout.DstLayout) (value : layout.DstLayout.Fields)
    (h : layout.DstLayout.decode raw = some value) :
    ModelViews.layoutValue value = layoutValue raw := by
  have fields := (layout.DstLayout.decode_decompose raw value).mp h
  simp only [layout.DstLayout.decodeFields, Option.some.injEq] at fields
  rcases fields with ⟨align, ha, info, hi, flag, hf, rfl⟩
  have hva := (decodeNonZeroUScalar_iff raw.align align).mp ha
  change some raw.statically_shallow_unpadded = some flag at hf
  cases Option.some.inj hf
  have infoFields := (layout.SizeInfo.decode_decompose Usize raw.size_info info).mp hi
  cases hs : raw.size_info with
  | Sized size =>
    simp only [hs, layout.SizeInfo.decodeFields, decodeUScalar,
      Option.some.injEq] at infoFields
    rcases infoFields with ⟨size, rfl, rfl⟩
    simp only [ModelViews.layoutValue, layoutValue, hs, unsignedWord_value, hva]
  | SliceDst tail =>
    simp only [hs, layout.SizeInfo.decodeFields, decodeUScalar,
      Option.some.injEq] at infoFields
    rcases infoFields with ⟨tailValue, ht, rfl⟩
    simp only [ModelViews.layoutValue, layoutValue, hs, hva,
      trailingFormula_decode tail tailValue ht]

/-- Optional machine sizes retain both absence and the exact numeric payload. -/
theorem optionalSize_decode (raw : Option Usize) (value : Option (UnsignedWord .Usize))
    (h : RustModel.decode raw = some value) :
    value.map (fun size => (size : Nat)) = raw.map UScalar.val := by
  cases raw <;>
    simp only [RustModel.decode, Option.map_some,
      Option.some.injEq] at h <;>
    cases h <;> rfl

/-- Padding's existing view retains every exact field observation required by
its raw contract, including the size variant and the unpadded flag. -/
theorem layout_pad_iff (self result : layout.DstLayout) :
    layoutValue result = (layoutValue self).pad ↔
      result.align = self.align ∧ match self.size_info with
      | .Sized bytes => ∃ padded, result.size_info = .Sized padded ∧
          padded.val = LayoutMath.roundUp bytes.val self.align.val.val ∧
          result.statically_shallow_unpadded =
            (self.statically_shallow_unpadded && decide (bytes.val % self.align.val.val = 0))
      | .SliceDst tail => ∃ next, result.size_info = .SliceDst next ∧
          trailingFormula next = (trailingFormula tail).pad self.align.val.val ∧
          result.statically_shallow_unpadded = self.statically_shallow_unpadded := by
  constructor
  · intro h
    have ha := congrArg LayoutMath.LayoutValue.align h
    have hp := congrArg LayoutMath.LayoutValue.payload h
    have hu := congrArg LayoutMath.LayoutValue.unpadded h
    have align : result.align = self.align := by
      have hv : result.align.val = self.align.val := UScalar.eq_of_val_eq ha
      have ext : ∀ a b : NonZeroUsize, a.val = b.val → a = b := by
        rintro ⟨a⟩ ⟨b⟩ h
        cases h
        rfl
      exact ext result.align self.align hv
    refine ⟨align, ?_⟩
    cases hs : self.size_info <;> cases hr : result.size_info <;>
      simp only [layoutValue, LayoutMath.LayoutValue.pad, hs, hr,
        LayoutMath.Payload.fixed.injEq, LayoutMath.Payload.trailing.injEq,
        reduceCtorEq] at hp hu ⊢
    all_goals exact ⟨_, rfl, hp, hu⟩
  · rintro ⟨ha, h⟩
    cases hs : self.size_info with
    | Sized bytes =>
      simp only [hs] at h
      rcases h with ⟨padded, hr, hp, hu⟩
      simp only [layoutValue, LayoutMath.LayoutValue.pad, hs, hr, ha, hp, hu]
    | SliceDst tail =>
      simp only [hs] at h
      rcases h with ⟨next, hr, hp, hu⟩
      simp only [layoutValue, LayoutMath.LayoutValue.pad, hs, hr, ha, hp, hu]

/-- Exact physical offset and stride remain observable through the padding view;
equality of bounded words follows from equality of their numeric projections. -/
theorem layout_pad_trailing_fields (self result : layout.DstLayout)
    (tail : layout.TrailingSliceLayout Usize)
    (hs : self.size_info = .SliceDst tail)
    (h : layoutValue result = (layoutValue self).pad) :
    ∃ next, result.size_info = .SliceDst next ∧
      next.offset = tail.offset ∧ next.elem_size = tail.elem_size := by
  have facts := (layout_pad_iff self result).mp h
  simp only [hs] at facts
  obtain ⟨next, hn, hf, _⟩ := facts.2
  refine ⟨next, hn, UScalar.eq_of_val_eq ?_, UScalar.eq_of_val_eq ?_⟩
  · have ho := congrArg LayoutMath.Formula.offset hf
    dsimp only [LayoutMath.Formula.pad] at ho
    split at ho <;> exact ho
  · have he := congrArg LayoutMath.Formula.elem hf
    dsimp only [LayoutMath.Formula.pad] at he
    split at he <;> exact he

end Zerocopy.Proofs
