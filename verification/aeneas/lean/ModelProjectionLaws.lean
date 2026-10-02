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
    (raw : layout.TrailingSliceLayout E) (value : layout.TrailingSliceLayout.Fields E)
    (h : layout.TrailingSliceLayout.decode E raw = some value) :
    ModelViews.byteFormula value = byteFormula raw := by
  simp only [layout.TrailingSliceLayout.decode, layout.TrailingSliceLayout.decodeFields,
    decodeUScalar, Option.bind_eq_some_iff, Option.some.injEq] at h
  rcases h with ⟨offset, rfl, elem, _, base, rfl, rounding, hr, rfl⟩
  obtain ⟨ha, hp⟩ := rounding_decode_components raw.size_rounding_align_and_phase rounding hr
  simp only [ModelViews.byteFormula, byteFormula, unsignedWord_value, ha, hp]

theorem trailingFormula_decode (raw : layout.TrailingSliceLayout Usize)
    (value : layout.TrailingSliceLayout.Fields Usize)
    (h : layout.TrailingSliceLayout.decode Usize raw = some value) :
    ModelViews.trailingFormula value = trailingFormula raw := by
  have hb := byteFormula_decode raw value h
  simp only [layout.TrailingSliceLayout.decode, layout.TrailingSliceLayout.decodeFields,
    decodeUScalar, Option.bind_eq_some_iff, Option.some.injEq] at h
  rcases h with ⟨offset, rfl, elem, rfl, base, rfl, rounding, _, rfl⟩
  simp only [ModelViews.trailingFormula, trailingFormula, hb, unsignedWord_value]

theorem layoutValue_decode (raw : layout.DstLayout) (value : layout.DstLayout.Fields)
    (h : layout.DstLayout.decode raw = some value) :
    ModelViews.layoutValue value = layoutValue raw := by
  simp only [layout.DstLayout.decode, layout.DstLayout.decodeFields,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  rcases h with ⟨align, ha, info, hi, flag, hf, rfl⟩
  have hva := (decodeNonZeroUScalar_iff raw.align align).mp ha
  change some raw.statically_shallow_unpadded = some flag at hf
  cases Option.some.inj hf
  cases hs : raw.size_info with
  | Sized size =>
    simp only [hs, RustModel.decode, layout.SizeInfo.decode,
      layout.SizeInfo.decodeFields, Option.bind_eq_some_iff, Option.some.injEq] at hi
    rcases hi with ⟨size, rfl, rfl⟩
    simp only [ModelViews.layoutValue, layoutValue, hs, unsignedWord_value, hva]
  | SliceDst tail =>
    simp only [hs, RustModel.decode, layout.SizeInfo.decode,
      layout.SizeInfo.decodeFields, Option.bind_eq_some_iff, Option.some.injEq] at hi
    rcases hi with ⟨tailValue, ht, rfl⟩
    simp only [ModelViews.layoutValue, layoutValue, hs, hva,
      trailingFormula_decode tail tailValue ht]

end Zerocopy.Proofs
