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

end Zerocopy.Proofs
