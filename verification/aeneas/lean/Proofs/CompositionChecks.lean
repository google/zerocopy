/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import CompositionConstructor
@[expose] public section

/-!
The roots below prove successful execution of ordinary Rust assertion harnesses.
The checked independent reference supplies the precise production arithmetic
domain. The existing raw operation proofs produce the actual layout, and the
reference matcher checks every stored observation before the assertion succeeds.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw
set_option linter.unusedSimpArgs false
open Zerocopy.CompositionReference

theorem composition_pad_checks (runtime_layout : layout.DstLayout) (reference : ReferenceLayout) :
    layout.composition_checks.check_pad runtime_layout reference ⦃ _ => True ⦄ := by
  unfold layout.composition_checks.check_pad
  step with composition_matches_spec runtime_layout reference as ⟨matching, hm⟩
  split
  · rename_i yes
    have matched := hm.mp yes
    obtain ⟨validity, canonical, view⟩ := matches_value runtime_layout reference matched
    have align_view := congrArg LayoutMath.LayoutValue.align view
    change runtime_layout.align.val.val = reference.align.val at align_view
    step with composition_reference_pad_spec reference as ⟨expected, he⟩
    cases expected with
    | none => simp
    | some expected =>
      obtain ⟨power, fits, expected_view, expected_validity⟩ := he expected rfl
      step with pad_value_spec runtime_layout
        (by simpa only [align_view] using power) canonical (by simpa only [view] using fits)
        as ⟨actual, actual_view, actual_canonical⟩
      have same : layoutValue actual = value expected := by
        rw [actual_view, view, expected_view]
      have matched_result := matches_of_value actual expected actual_canonical expected_validity same
      step with composition_matches_spec actual expected as ⟨checked, hc⟩
      have yes : checked = true := hc.mpr matched_result
      simp [yes, massert]
  · simp

theorem composition_extend_checks (preceding field : layout.DstLayout)
    (packed : Option NonZeroUsize) (preceding_reference field_reference : ReferenceLayout) :
    layout.composition_checks.check_extend preceding field packed preceding_reference field_reference
      ⦃ _ => True ⦄ := by
  unfold layout.composition_checks.check_extend
  step with composition_matches_spec preceding preceding_reference as ⟨preceding_matches, hp⟩
  split
  · rename_i py
    obtain ⟨preceding_valid, _, preceding_view⟩ := matches_value preceding preceding_reference (hp.mp py)
    have preceding_align := congrArg LayoutMath.LayoutValue.align preceding_view
    change preceding.align.val.val = preceding_reference.align.val at preceding_align
    step with composition_matches_spec field field_reference as ⟨field_matches, hf⟩
    split
    · rename_i fy
      obtain ⟨field_valid, field_canonical, field_view⟩ := matches_value field field_reference (hf.mp fy)
      have field_align := congrArg LayoutMath.LayoutValue.align field_view
      change field.align.val.val = field_reference.align.val at field_align
      step with composition_reference_extend_spec preceding_reference field_reference packed as ⟨expected, he⟩
      cases expected with
      | none => simp
      | some expected =>
        obtain ⟨preceding_domain, field_domain, packed_domain, fits, expected_view, validity⟩ := he expected rfl
        step with extend_value_spec preceding field packed
          (by simpa only [preceding_align] using preceding_domain)
          (by simpa only [field_align] using field_domain) packed_domain field_canonical
          (by simpa only [preceding_view, field_view] using fits)
          as ⟨actual, actual_view, actual_canonical⟩
        have same : layoutValue actual = value expected := by
          rw [actual_view, preceding_view, field_view, expected_view]
        have matched_result := matches_of_value actual expected actual_canonical (validity field_valid) same
        step with composition_matches_spec actual expected as ⟨checked, hc⟩
        have yes : checked = true := hc.mpr matched_result
        simp [yes, massert]
    · simp
  · simp

theorem composition_constructor_checks (repr_align packed : Option NonZeroUsize)
    (fields : Slice layout.DstLayout) (references : Slice ReferenceLayout) :
    layout.composition_checks.check_constructor repr_align packed fields references ⦃ _ => True ⦄ := by
  unfold layout.composition_checks.check_constructor
  simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, Slice.len_val, Slice.length]
  split
  · simp
  · rename_i equal_length
    have lengths : fields.val.length = references.val.length := by omega
    have initial_matching : (true = true) = fieldsMatchThrough fields references (0#usize).val := by
      apply propext
      simp [fieldsMatchThrough]
    step with composition_matching_loop_spec fields references lengths true 0#usize
      (by simp) initial_matching as ⟨matching, hm⟩
    split
    · rename_i yes
      have all_matching := Eq.mp hm yes
      have matched (j : Nat) (hj : j < fields.val.length) (hr : j < references.val.length) :
          Matches fields.val[j] references.val[j] := all_matching j hj hr hj
      have fields_valid : ∀ j (hr : j < references.val.length), valid references.val[j] := by
        intro j hr
        have hj : j < fields.val.length := by omega
        exact (matches_value _ _ (matched j hj hr)).1
      have field_views : fields.val.map layoutValue = references.val.map value := by
        apply List.ext_getElem
        · simpa only [List.length_map] using lengths
        · intro j hj hr
          have hj' : j < fields.val.length := by simpa only [List.length_map] using hj
          have hr' : j < references.val.length := by simpa only [List.length_map] using hr
          simpa only [List.getElem_map] using (matches_value _ _ (matched j hj' hr')).2.2
      have prefixes (j : Nat) : constructionPrefix fields
          (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed j =
          referencePrefix references (initialAlignment repr_align) packed j := by
        simp only [constructionPrefix, referencePrefix, field_views]
      step with composition_reference_constructor_spec repr_align packed references fields_valid as ⟨expected, he⟩
      cases expected with
      | none => simp
      | some expected =>
        obtain ⟨initial_domain, packed_domain, history, final_domain, fits, expected_view, expected_validity⟩ := he expected rfl
        have construction : constructionDomain fields
            (LayoutMath.LayoutValue.initial (initialAlignment repr_align)) packed := by
          intro j hj
          have hr : j < references.val.length := by omega
          obtain ⟨previous_domain, field_domain, _, field_fit⟩ := history j hr hr
          obtain ⟨_, field_canonical, view⟩ := matches_value _ _ (matched j hj hr)
          have alignment := congrArg LayoutMath.LayoutValue.align view
          change fields.val[j].align.val.val = references.val[j].align.val at alignment
          refine ⟨?_, ?_, field_canonical, ?_⟩
          · simpa only [prefixes] using previous_domain
          · simpa only [alignment] using field_domain
          · simpa only [prefixes, view] using field_fit
        step with composition_production_constructor_spec repr_align packed fields initial_domain
          (by simpa only [lengths] using packed_domain) construction
          (by simpa only [prefixes, lengths] using final_domain)
          (by simpa only [prefixes, lengths] using fits)
          as ⟨actual, actual_view, actual_canonical⟩
        have same : layoutValue actual = value expected := by
          rw [actual_view, prefixes, lengths, expected_view]
        have matched_result := matches_of_value actual expected actual_canonical expected_validity same
        step with composition_matches_spec actual expected as ⟨checked, hc⟩
        have yes : checked = true := hc.mpr matched_result
        simp [yes, massert]
    · simp

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs

theorem composition_pad_checks_spec : Specs.composition_pad_checks_spec := by
  intro runtime_layout reference
  repeat intro
  apply WP.spec_mono (Raw.composition_pad_checks runtime_layout reference)
  intro _ _
  exact ⟨(), rfl, trivial⟩

theorem composition_extend_checks_spec : Specs.composition_extend_checks_spec := by
  intro preceding field packed preceding_reference field_reference
  repeat intro
  apply WP.spec_mono (Raw.composition_extend_checks preceding field packed preceding_reference field_reference)
  intro _ _
  exact ⟨(), rfl, trivial⟩

theorem composition_constructor_checks_spec : Specs.composition_constructor_checks_spec := by
  intro repr_align packed fields references
  repeat intro
  apply WP.spec_mono (Raw.composition_constructor_checks repr_align packed fields references)
  intro _ _
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
