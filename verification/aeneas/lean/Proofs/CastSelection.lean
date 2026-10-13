/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.CastSequence
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw
set_option linter.unusedVariables false

/- Both candidate-selection paths finish with the same complete-sequence
check. Keep this final arithmetic obligation independent of candidate choice.
-/
theorem cast_plan_accept
    (src_layout dst_layout : layout.DstLayout)
    (src dst : layout.TrailingSliceLayout Usize) (base multiple : Usize)
    (hs : src_layout.size_info = .SliceDst src)
    (hd : dst_layout.size_info = .SliceDst dst)
    (ha : dst_layout.align.val.val ≤ src_layout.align.val.val)
    (hp : 0 < dst.elem_size.val)
    (hm : multiple.val = src.elem_size.val / dst.elem_size.val)
    (hr : src.elem_size.val = multiple.val * dst.elem_size.val)
    (same : ∀ n : Nat, (trailingFormula src).size n =
      (trailingFormula dst).size
        (base.val + n * (src.elem_size.val / dst.elem_size.val))) :
    castPlanSpec src_layout dst_layout (some (.UnsizedToUnsized base multiple)) := by
  simp only [castPlanSpec, hs, hd]
  exact ⟨ha, hp, hr, by simpa only [hm] using same⟩

/- The fallback chooses exact metadata for the zero-count source size, then
checks the entire sequence. A rejected candidate has no completeness promise.
-/
theorem cast_plan_fallback_spec
    (src_layout dst_layout : layout.DstLayout)
    (src dst : layout.TrailingSliceLayout Usize) (multiple : Usize)
    (hs : src_layout.size_info = .SliceDst src)
    (hd : dst_layout.size_info = .SliceDst dst)
    (ha : dst_layout.align.val.val ≤ src_layout.align.val.val)
    (hda : 0 < dst_layout.align.val.val)
    (hsrc : 0 < src.size_rounding_align_and_phase._0.val.val)
    (hdst : 0 < dst.size_rounding_align_and_phase._0.val.val)
    (hp : 0 < dst.elem_size.val)
    (hm : multiple.val = src.elem_size.val / dst.elem_size.val)
    (hr : src.elem_size.val = multiple.val * dst.elem_size.val)
    (hdiv : src.elem_size.val % dst.elem_size.val = 0) :
    (do
      let zeroSize ← layout.TrailingSliceLayoutUsize.size_for_elems src 0#usize
      match zeroSize with
      | none => Result.ok none
      | some size =>
        let metadata ← layout.DstLayout.metadata_for_exact_size dst_layout size
        match metadata with
        | none => Result.ok none
        | some elems =>
          let same ← layout.cast_from.CastPlan.size_sequences_match src dst elems
          if same then
            Result.ok (some (layout.cast_from.CastPlan.UnsizedToUnsized elems multiple))
          else Result.ok none)
      ⦃ plan => castPlanSpec src_layout dst_layout plan ⦄ := by
  step with size_for_elems_spec src 0#usize hsrc as ⟨zeroSize, _⟩
  cases zeroSize with
  | none => simp only [WP.spec_ok, castPlanSpec]
  | some size =>
    step with metadata_exact_spec dst_layout size hda
      (by simp only [hd]; exact fun _ => hdst) as ⟨metadata, _⟩
    cases metadata with
    | none => simp only [WP.spec_ok, castPlanSpec]
    | some elems =>
      step with cast_size_sequences_spec src dst elems hsrc hdst hp hdiv as ⟨same, hsame⟩
      split
      · rename_i htrue
        apply WP.spec.ret
        exact cast_plan_accept src_layout dst_layout src dst elems multiple
          hs hd ha hp hm hr (hsame htrue)
      · simp only [WP.spec_ok, castPlanSpec]

/- Accepted plans preserve complete size for all natural metadata values.
The only raw admission conditions are positive alignments and canonical
rounding encodings; all stride requirements follow from executed guards.
-/
theorem cast_plan_spec
    (src_layout dst_layout : layout.DstLayout)
    (hsa : 0 < src_layout.align.val.val)
    (hda : 0 < dst_layout.align.val.val)
    (hsc : canonicalLayout src_layout)
    (hdc : canonicalLayout dst_layout) :
    layout.cast_from.CastPlan.try_compute src_layout dst_layout
      ⦃ plan => castPlanSpec src_layout dst_layout plan ⦄ := by
  unfold layout.cast_from.CastPlan.try_compute
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  split
  · simp only [WP.spec_ok, castPlanSpec]
  · rename_i halign
    have ha : dst_layout.align.val.val ≤ src_layout.align.val.val := by
      simpa only [UScalar.lt_equiv, Nat.not_lt] using halign
    cases hs : src_layout.size_info with
    | Sized srcSize =>
      simp only []
      cases hd : dst_layout.size_info with
      | Sized dstSize =>
        simp only []
        split
        · simp only [WP.spec_ok, castPlanSpec]
        · rename_i heq
          apply WP.spec.ret
          simp only [castPlanSpec, hs, hd]
          exact ⟨ha, (UScalar.eq_equiv _ _).mpr (by simpa using heq)⟩
      | SliceDst dst =>
        simp only []
        have hdst : 0 < dst.size_rounding_align_and_phase._0.val.val := by
          simpa only [canonicalLayout, hd] using hdc
        step with metadata_exact_spec dst_layout srcSize hda
          (by simp only [hd]; exact fun _ => hdst) as ⟨metadata, hmeta⟩
        cases metadata with
        | none => simp only [WP.spec_ok, castPlanSpec]
        | some elems =>
          simp only [metadataSpec, hd] at hmeta
          split at hmeta
          · contradiction
          · rename_i hn
            apply WP.spec.ret
            simp only [castPlanSpec, hs, hd]
            exact ⟨ha, by omega, hmeta.1⟩
    | SliceDst src =>
      simp only []
      cases hd : dst_layout.size_info with
      | Sized _ => simp only [hd, WP.spec_ok, castPlanSpec]
      | SliceDst dst =>
        simp only []
        have hsrc : 0 < src.size_rounding_align_and_phase._0.val.val := by
          simpa only [canonicalLayout, hs] using hsc
        have hdst : 0 < dst.size_rounding_align_and_phase._0.val.val := by
          simpa only [canonicalLayout, hd] using hdc
        by_cases hz : dst.elem_size = 0#usize
        · simp only [core.num.nonzero.NonZero.new, cast_eq, hz,
            ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok, castPlanSpec]
        · simp only [core.num.nonzero.NonZero.new, cast_eq, hz,
            ↓reduceDIte, ↓reduceIte, bind_ok]
          have hp : 0 < dst.elem_size.val := by
            have hn : dst.elem_size.val ≠ 0 := by
              intro he
              apply hz
              exact (UScalar.eq_equiv _ _).mpr he
            omega
          split
          · simp only [WP.spec_ok, castPlanSpec]
          · step with max_elems_for_bytes_spec src.elem_size ⟨dst.elem_size⟩ hp as
              ⟨multiple, described, hm, hused, _, _, _⟩
            split
            · simp only [WP.spec_ok, castPlanSpec]
            · rename_i hexact
              have heq : described = src.elem_size :=
                (UScalar.eq_equiv _ _).mpr (by simpa using hexact)
              have hr : src.elem_size.val = multiple.val * dst.elem_size.val := by
                simpa only [heq] using hused
              have hdiv : src.elem_size.val % dst.elem_size.val = 0 := by
                rw [hr, Nat.mul_mod_left]
              have fallback := cast_plan_fallback_spec src_layout dst_layout src dst
                multiple hs hd ha hda hsrc hdst hp hm hr hdiv
              step with size_offset_spec src hsrc as ⟨srcOffset, _⟩
              step with size_offset_spec dst hdst as ⟨dstOffset, _⟩
              step as ⟨delta, _⟩
              cases delta with
              | none =>
                simp only [bind_ok]
                exact fallback
              | some delta =>
                step with max_elems_for_bytes_spec delta ⟨dst.elem_size⟩ hp as
                  ⟨pair, _, _, _, _, _⟩
                rcases pair with ⟨elems, describedDelta⟩
                change (Std.bind
                  (if describedDelta = delta then Result.ok (some elems) else Result.ok none) _)
                    ⦃ plan => castPlanSpec src_layout dst_layout plan ⦄
                split
                · simp only [bind_ok]
                  step with cast_size_sequences_spec src dst elems hsrc hdst hp hdiv as
                    ⟨same, hsame⟩
                  split
                  · rename_i htrue
                    apply WP.spec.ret
                    exact cast_plan_accept src_layout dst_layout src dst elems multiple
                      hs hd ha hp hm hr (hsame htrue)
                  · exact fallback
                · simp only [bind_ok]
                  exact fallback

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

theorem cast_plan_spec : Zerocopy.Specs.cast_plan_spec := by
  unfold Zerocopy.Specs.cast_plan_spec
  representation_simps
  intro src dst hsrc hdst
  have hcsrc : canonicalLayout src := by
    cases hs : src.size_info with
    | Sized _ => simp only [canonicalLayout, hs]
    | SliceDst _ => simpa only [canonicalLayout, hs] using hsrc.2
  have hcdst : canonicalLayout dst := by
    cases hs : dst.size_info with
    | Sized _ => simp only [canonicalLayout, hs]
    | SliceDst _ => simpa only [canonicalLayout, hs] using hdst.2
  apply WP.spec_mono (Raw.cast_plan_spec src dst hsrc.1 hdst.1 hcsrc hcdst)
  intro result facts
  refine ⟨?_, facts⟩
  change isValid result
  cases result with
  | none => simp
  | some plan =>
    cases plan <;> simp [isValid, RustModel.decode,
      layout.cast_from.CastPlan.decode, layout.cast_from.CastPlan.decodeFields]
register_spec_step cast_plan_spec

end Zerocopy.Proofs
