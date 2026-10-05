/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import Obligations.CastUnsized
public import RequiredModelContracts
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[contract_simps] theorem required_cast_unsized_layouts_match (src dst : layout.DstLayout)
    (run : Result Bool)
    (provided : Specs.cast_unsized_layouts_match_spec_contract src dst run) :
    Obligations.cast_unsized_layouts_match_spec_contract src dst run := by
  intro src_valid dst_valid
  obtain ⟨src_value, src_decoded⟩ := (layout_valid_iff src).mpr src_valid
  obtain ⟨dst_value, dst_decoded⟩ := (layout_valid_iff dst).mpr dst_valid
  apply WP.spec_mono (provided src_value src_decoded dst_value dst_decoded)
  rintro accepted ⟨_value, _decoded, facts⟩
  cases src_info : src.size_info <;> cases dst_info : dst.size_info
  · simpa only [src_info, dst_info, UScalar.eq_equiv] using facts
  · simpa only [src_info, dst_info] using facts
  · simpa only [src_info, dst_info] using facts
  · simp only [src_info, dst_info] at facts ⊢
    intro yes
    obtain ⟨align_same, offset_same, size_same⟩ := facts yes
    refine ⟨congrArg (fun (a : NonZeroUsize) => a.val.val) align_same,
      congrArg UScalar.val offset_same, ?_⟩
    intro count
    exact ⟨size_same count, by rw [size_same count]⟩

@[contract_simps] theorem required_cast_unsized_check (src dst : layout.DstLayout)
    (src_align : NonZeroUsize) (src_phase : Usize) (dst_align : NonZeroUsize)
    (dst_phase metadata : Usize) (run : Result Unit)
    (provided : Specs.cast_unsized_check_spec_contract
      src dst src_align src_phase dst_align dst_phase metadata run) :
    Obligations.cast_unsized_check_spec_contract
      src dst src_align src_phase dst_align dst_phase metadata run := by
  intro src_valid dst_valid src_positive dst_positive
  obtain ⟨src_value, src_decoded⟩ := (layout_valid_iff src).mpr src_valid
  obtain ⟨dst_value, dst_decoded⟩ := (layout_valid_iff dst).mpr dst_valid
  let src_align_value : NonZeroUsizeValue := ⟨unsignedWord src_align.val, src_positive⟩
  let dst_align_value : NonZeroUsizeValue := ⟨unsignedWord dst_align.val, dst_positive⟩
  have src_align_decoded := (decodeNonZeroUScalar_iff src_align src_align_value).mpr rfl
  have dst_align_decoded := (decodeNonZeroUScalar_iff dst_align dst_align_value).mpr rfl
  apply WP.spec_mono (provided src_value src_decoded dst_value dst_decoded
    src_align_value src_align_decoded (unsignedWord src_phase) rfl
    dst_align_value dst_align_decoded (unsignedWord dst_phase) rfl (unsignedWord metadata) rfl)
  rintro result ⟨_value, _decoded, _facts⟩
  trivial

end Zerocopy.Proofs
