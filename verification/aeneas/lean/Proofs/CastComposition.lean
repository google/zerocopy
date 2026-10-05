/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.CastSelection
public import Proofs.CastArithmetic
public import Proofs.CastSafety
public import Proofs.TailTransformReference
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.CastComposition
open TailChecks

/- The layout guard is total and exposes the witness only when it succeeds.
Sized layouts intentionally ignore both witness values.
-/
theorem witness_matches (self : layout.DstLayout) (align : NonZeroUsize) (phase : Usize) :
    layout.cast_from.checks.witness_matches self align phase
      ⦃ b => b = true → witnessMatches self align phase ⦄ := by
  unfold layout.cast_from.checks.witness_matches
  cases hs : self.size_info with
  | Sized size => simp [witnessMatches, hs, WP.spec_ok]
  | SliceDst tail =>
    simpa only [witnessMatches, hs] using TailTransforms.witness_matches tail align phase

/- The independent remainder-based reference computes the mathematical
complete size, including overflow. Guarded witnesses identify its formula.
-/
theorem reference_size (self : layout.DstLayout) (align : NonZeroUsize)
    (phase elems : Usize) (positive : 0 < align.val.val)
    (witness : witnessMatches self align phase) :
    layout.cast_from.checks.reference_size self align phase elems
      ⦃ result => result.map UScalar.val = checkedNat (completeLayoutSize self elems.val) ⦄ := by
  unfold layout.cast_from.checks.reference_size
  cases hs : self.size_info with
  | Sized size =>
    have fits : size.val ≤ Usize.max := by scalar_tac
    simp only [WP.spec_ok, Option.map_some, completeLayoutSize, hs, checkedNat, fits, if_true]
  | SliceDst tail =>
    simp only [witnessMatches, hs] at witness
    have view := witness_view tail align phase witness.1 witness.2.1 witness.2.2
    apply WP.spec_mono (TailChecks.reference_size tail align phase elems positive)
    intro result facts
    simpa only [completeLayoutSize, hs, view, LayoutMath.Formula.checkedSize, checkedNat]
      using facts

/- This independent checked implementation returns precisely the natural
metadata map when it fits, and none otherwise. Its intermediate product
cannot overflow while its nonnegative final sum fits.
-/
theorem checked_metadata (plan : layout.cast_from.CastPlan) (src_meta : Usize) :
    layout.cast_from.checks.checked_metadata plan src_meta
      ⦃ result => result.map UScalar.val = checkedNat (castPlanMetadata plan src_meta.val) ⦄ := by
  unfold layout.cast_from.checks.checked_metadata
  cases plan with
  | UnsizedToUnsized base multiple =>
    step as ⟨product, product_facts⟩
    cases product with
    | none =>
      simp only [] at product_facts
      have overflow : ¬base.val + src_meta.val * multiple.val ≤ Usize.max := by omega
      simp [castPlanMetadata, checkedNat, overflow, WP.spec_ok]
    | some product =>
      simp only [] at product_facts
      have product_value : product.val = src_meta.val * multiple.val := by omega
      simp only [WP.spec_ok, checked_add_value, castPlanMetadata, product_value]
  | SizedToUnsized metadata =>
    have fits : metadata.val ≤ Usize.max := by scalar_tac
    simp only [WP.spec_ok, Option.map_some, castPlanMetadata, checkedNat, fits, if_true]
  | SizedToSized =>
    simp only [WP.spec_ok, Option.map_some, castPlanMetadata, checkedNat, Nat.zero_le, if_true]
    rfl

/- The root accepts arbitrary metadata and witness phases. Witness failures,
rejected plans and source-size overflow return normally. Once selection and
source sizing succeed, the certificate itself supplies the metadata bound;
metadata overflow is then impossible, and both final assertions follow.
-/
theorem assert_cast_preserves_size (src dst : layout.DstLayout)
    (src_align : NonZeroUsize) (src_phase : Usize)
    (dst_align : NonZeroUsize) (dst_phase src_meta : Usize)
    (hsa : 0 < src.align.val.val) (hda : 0 < dst.align.val.val)
    (hsc : canonicalLayout src) (hdc : canonicalLayout dst)
    (hsrc_align : 0 < src_align.val.val) (hdst_align : 0 < dst_align.val.val) :
    layout.cast_from.checks.assert_cast_preserves_size
      src dst src_align src_phase dst_align dst_phase src_meta ⦃ _ => True ⦄ := by
  unfold layout.cast_from.checks.assert_cast_preserves_size
  step with witness_matches src src_align src_phase as ⟨src_matches, src_witness⟩
  split
  · rename_i src_matches_true
    have src_witness := src_witness src_matches_true
    step with witness_matches dst dst_align dst_phase as ⟨dst_matches, dst_witness⟩
    split
    · rename_i dst_matches_true
      have dst_witness := dst_witness dst_matches_true
      step with Raw.cast_plan_spec src dst hsa hda hsc hdc as ⟨selected, selected_facts⟩
      cases selected with
      | none => simp only [WP.spec_ok]
      | some plan =>
        step with reference_size src src_align src_phase src_meta hsrc_align src_witness
          as ⟨src_size, src_size_facts⟩
        cases src_size with
        | none => simp only [WP.spec_ok]
        | some src_size =>
          simp only [Option.map_some] at src_size_facts
          have source := (checkedNat_some _ _).mp src_size_facts.symm
          have fits := castPlanSpec_metadata_fits src dst plan selected_facts src_meta.val source.1
          have alignment := castPlanSpec_alignment src dst plan selected_facts
          have alignment_raw : src.align.val ≥ dst.align.val := by scalar_tac
          simp only [core.num.nonzero.NonZero.get, bind_ok, alignment_raw,
            massert, if_true]
          step with checked_metadata plan src_meta as ⟨expected, expected_facts⟩
          cases expected with
          | none =>
            simp only [Option.map_none] at expected_facts
            have overflow := (checkedNat_none _).mp expected_facts.symm
            unfold castMetadataFits at fits
            omega
          | some expected =>
            simp only [Option.map_some] at expected_facts
            have expected_value := (checkedNat_some _ _).mp expected_facts.symm
            step with Raw.cast_metadata_spec plan src_meta fits as ⟨dst_meta, dst_meta_value⟩
            have metadata_same : dst_meta = expected :=
              UScalar.eq_of_val_eq (dst_meta_value.trans expected_value.2)
            simp only [metadata_same, if_true, bind_ok]
            step with reference_size dst dst_align dst_phase expected hdst_align dst_witness
              as ⟨dst_size, dst_size_facts⟩
            have same_size := castPlanSpec_size src dst plan selected_facts src_meta.val
            rw [expected_value.2] at same_size
            have same : dst_size = some src_size := by
              apply optional_value_injective
              rw [dst_size_facts, ← same_size]
              exact src_size_facts.symm
            step with same_optional_usize dst_size (some src_size) as ⟨same_result, same_iff⟩
            simp [same_iff.mpr same, WP.spec_ok]
    · simp only [WP.spec_ok]
  · simp only [WP.spec_ok]

end Zerocopy.Proofs.Raw.CastComposition

namespace Zerocopy.Proofs
open AeneasSpecs

/- The canonical contract exposes exactly the automatic decoder domain. It
adds no source-size, metadata-fit, phase-range, or size-equality requirement.
-/
theorem cast_composition_check_spec : Specs.cast_composition_check_spec := by
  unfold Specs.cast_composition_check_spec
  representation_simps
  intro src dst src_align src_phase dst_align dst_phase src_meta hsrc hdst hsrc_align hdst_align
  have hcsrc : canonicalLayout src := by
    cases hs : src.size_info with
    | Sized _ => simp only [canonicalLayout, hs]
    | SliceDst _ => simpa only [canonicalLayout, hs] using hsrc.2
  have hcdst : canonicalLayout dst := by
    cases hs : dst.size_info with
    | Sized _ => simp only [canonicalLayout, hs]
    | SliceDst _ => simpa only [canonicalLayout, hs] using hdst.2
  apply WP.spec_mono (Raw.CastComposition.assert_cast_preserves_size src dst src_align src_phase
    dst_align dst_phase src_meta hsrc.1 hdst.1 hcsrc hcdst hsrc_align hdst_align)
  intro result _facts
  exact ⟨(), rfl⟩
register_spec_step cast_composition_check_spec

end Zerocopy.Proofs
