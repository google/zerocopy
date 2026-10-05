/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Obligations.CastPlan
public import RequiredModelContracts
@[expose] public section

/-!
These adapters consume the generated contract for the same arbitrary outcome.
They construct every automatic decoded-input witness from the broad raw
premises and retain the independent output observations. They do not prove an
extracted call or use a canonical operation theorem as a substitute premise.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

theorem cast_plan_admitted (self : layout.cast_from.CastPlan) :
    ∃ value, RustModel.decode self = some value := by
  cases self <;> exact ⟨_, rfl⟩

theorem layout_admitted_of_canonical (self : layout.DstLayout)
    (positive : 0 < self.align.val.val) (canonical : canonicalLayout self) :
    ∃ value, RustModel.decode self = some value := by
  apply (layout_admitted_iff self).mpr
  refine ⟨positive, ?_⟩
  cases info : self.size_info with
  | Sized size => simp only [sizeInfoValid]
  | SliceDst tail =>
      simpa only [sizeInfoValid, trailingValid, scalar_valid_iff, true_and,
        encodingValid, canonicalLayout, info] using canonical

@[contract_simps] theorem required_cast_size_sequences
    (src dst : layout.TrailingSliceLayout Usize) (dst_base : Usize) (run : Result Bool)
    (provided : Specs.cast_size_sequences_spec_contract src dst dst_base run) :
    Obligations.cast_size_sequences_spec_contract src dst dst_base run := by
  intro srcPositive dstPositive dstElemPositive divides
  obtain ⟨srcValue, srcDecoded⟩ := (trailing_usize_admitted_iff src).mpr srcPositive
  obtain ⟨dstValue, dstDecoded⟩ := (trailing_usize_admitted_iff dst).mpr dstPositive
  apply WP.spec_mono (provided srcValue srcDecoded dstValue dstDecoded
    (unsignedWord dst_base) rfl dstElemPositive divides)
  rintro same ⟨_value, _decoded, facts⟩
  exact facts

@[contract_simps] theorem required_cast_plan (src dst : layout.DstLayout)
    (run : Result (Option layout.cast_from.CastPlan))
    (provided : Specs.cast_plan_spec_contract src dst run) :
    Obligations.cast_plan_spec_contract src dst run := by
  intro srcPositive dstPositive srcCanonical dstCanonical
  obtain ⟨srcValue, srcDecoded⟩ := layout_admitted_of_canonical src srcPositive srcCanonical
  obtain ⟨dstValue, dstDecoded⟩ := layout_admitted_of_canonical dst dstPositive dstCanonical
  apply WP.spec_mono (provided srcValue srcDecoded dstValue dstDecoded)
  rintro result ⟨_value, _decoded, facts⟩
  exact facts

@[contract_simps] theorem required_cast_metadata (self : layout.cast_from.CastPlan)
    (src_meta : Usize) (run : Result Usize)
    (provided : Specs.cast_metadata_spec_contract self src_meta run) :
    Obligations.cast_metadata_spec_contract self src_meta run := by
  intro fits
  obtain ⟨value, decoded⟩ := cast_plan_admitted self
  apply WP.spec_mono (provided value decoded (unsignedWord src_meta) rfl fits)
  rintro metadata ⟨_value, _decoded, facts⟩
  exact facts

@[contract_simps] theorem required_add_scaled_metadata (base metadata multiple : Usize)
    (run : Result Usize)
    (provided : Specs.add_scaled_metadata_spec_contract base metadata multiple run) :
    Obligations.add_scaled_metadata_spec_contract base metadata multiple run := by
  intro fits
  apply WP.spec_mono (provided (unsignedWord base) rfl (unsignedWord metadata) rfl
    (unsignedWord multiple) rfl fits)
  rintro result ⟨_value, _decoded, facts⟩
  exact facts

end Zerocopy.Proofs
