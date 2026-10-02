/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
@[expose] public section

/-!
The Rust reference stores independent numeric alignment and phase witnesses.
These observations connect those witnesses to the mathematical fragment model.
The raw helper proofs check the extracted remainder and checked arithmetic;
they do not substitute a mathematical algorithm for an extracted computation.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.CompositionReference
open Zerocopy.Proofs
set_option linter.unusedSimpArgs false

abbrev ReferenceLayout := layout.composition_checks.ReferenceLayout
abbrev ReferenceTail := layout.composition_checks.ReferenceTail
abbrev ReferenceSize := layout.composition_checks.ReferenceSize

def tailValue (tail : ReferenceTail) : LayoutMath.Formula :=
  ⟨tail.base.val, tail.phase.val, tail.round_align.val, tail.elem_size.val, tail.offset.val⟩

def value (reference : ReferenceLayout) : LayoutMath.LayoutValue :=
  ⟨reference.align.val,
    match reference.size with
    | .Fixed bytes => .fixed bytes.val
    | .Tail tail => .trailing (tailValue tail),
    reference.unpadded⟩

def valid (reference : ReferenceLayout) : Prop :=
  match reference.size with
  | .Fixed _ => True
  | .Tail tail => tail.round_align.val.isPowerOfTwo ∧ tail.phase.val < tail.round_align.val

def Matches (runtime_layout : layout.DstLayout) (reference : ReferenceLayout) : Prop :=
  runtime_layout.align.val = reference.align ∧
  runtime_layout.statically_shallow_unpadded = reference.unpadded ∧
  match runtime_layout.size_info, reference.size with
  | .Sized bytes, .Fixed expected => bytes = expected
  | .SliceDst actual, .Tail expected =>
    expected.round_align.val.isPowerOfTwo ∧ expected.phase < expected.round_align ∧
    actual.offset = expected.offset ∧ actual.elem_size = expected.elem_size ∧
    actual.size_base = expected.base ∧
    Usize.checked_add expected.round_align expected.phase =
      some actual.size_rounding_align_and_phase._0.val
  | _, _ => False

theorem checked_encoding (tail : ReferenceTail) (encoded : Usize)
    (h : Usize.checked_add tail.round_align tail.phase = some encoded) :
    encoded.val = tail.round_align.val + tail.phase.val := by
  have facts := Usize.checked_add_bv_spec tail.round_align tail.phase
  rw [h] at facts
  exact facts.2.1

theorem matches_value (runtime_layout : layout.DstLayout) (reference : ReferenceLayout)
    (h : Matches runtime_layout reference) :
    valid reference ∧ canonicalLayout runtime_layout ∧ layoutValue runtime_layout = value reference := by
  obtain ⟨ha, hu, h⟩ := h
  cases hr : runtime_layout.size_info <;> cases hs : reference.size <;>
    simp only [hr, hs] at h
  case Sized.Fixed bytes expected =>
    subst expected
    exact ⟨by simp [valid, hs], by simp [canonicalLayout, hr], by simp [layoutValue, value, hr, hs, ha, hu]⟩
  case SliceDst.Tail actual expected =>
    obtain ⟨hp, hphase, ho, he, hb, hc⟩ := h
    have hl := (UScalar.lt_equiv _ _).mp hphase
    have hn := checked_encoding expected _ hc
    have hv := Raw.trailing_view actual expected.round_align.val expected.phase.val hp hl hn
    have positive := Nat.pos_of_isPowerOfTwo hp
    refine ⟨by simpa only [valid, hs] using And.intro hp hl, ?_, ?_⟩
    · simp only [canonicalLayout, hr]
      omega
    · simp only [layoutValue, value, hr, hs, hv, tailValue, ha, hu, ho, he, hb]

/- A checked sum succeeds exactly when its expected stored word is the sum.
This lemma also recovers the guard's machine-overflow bound. -/
theorem checked_add_of_value (a b encoded : Usize)
    (sum : encoded.val = a.val + b.val) : Usize.checked_add a b = some encoded := by
  have facts := Usize.checked_add_bv_spec a b
  have bound : encoded.val ≤ Usize.max := by scalar_tac
  cases hc : Usize.checked_add a b with
  | none => rw [hc] at facts; omega
  | some result =>
    rw [hc] at facts
    have same : result = encoded := UScalar.eq_of_val_eq (by omega)
    simp only [same]

theorem matches_of_value (runtime_layout : layout.DstLayout) (reference : ReferenceLayout)
    (hrc : canonicalLayout runtime_layout) (hrv : valid reference)
    (hv : layoutValue runtime_layout = value reference) : Matches runtime_layout reference := by
  have ha := congrArg LayoutMath.LayoutValue.align hv
  have hu := congrArg LayoutMath.LayoutValue.unpadded hv
  have hp := congrArg LayoutMath.LayoutValue.payload hv
  refine ⟨UScalar.eq_of_val_eq ha, hu, ?_⟩
  cases hr : runtime_layout.size_info <;> cases hs : reference.size <;>
    simp only [layoutValue, value, hr, hs] at hp ⊢
  case Sized.Fixed bytes expected =>
    injection hp with he
    exact UScalar.eq_of_val_eq he
  case Sized.Tail => cases hp
  case SliceDst.Fixed => cases hp
  case SliceDst.Tail actual expected =>
    injection hp with formula
    have hb := congrArg LayoutMath.Formula.base formula
    have hphase := congrArg LayoutMath.Formula.phase formula
    have hround := congrArg LayoutMath.Formula.align formula
    have he := congrArg LayoutMath.Formula.elem formula
    have ho := congrArg LayoutMath.Formula.offset formula
    simp only [tailValue, trailingFormula, byteFormula] at hb hphase hround he ho
    obtain ⟨pow2, phase_lt⟩ := (show expected.round_align.val.isPowerOfTwo ∧
      expected.phase.val < expected.round_align.val by simpa only [valid, hs] using hrv)
    have positive : 0 < actual.size_rounding_align_and_phase._0.val.val := by
      simpa only [canonicalLayout, hr] using hrc
    have reconstruct := RoundingFacts.reconstruction _ positive
    refine ⟨pow2, (UScalar.lt_equiv _ _).mpr phase_lt,
      UScalar.eq_of_val_eq ho, UScalar.eq_of_val_eq he, UScalar.eq_of_val_eq hb, ?_⟩
    apply checked_add_of_value
    omega

/- Every canonical raw representation has a numeric witness. In particular,
this covers every nonzero rounding encoding, not just constructor outputs. -/
theorem witness_exists (runtime_layout : layout.DstLayout) (hc : canonicalLayout runtime_layout) :
    ∃ reference : ReferenceLayout, Matches runtime_layout reference := by
  cases hs : runtime_layout.size_info with
  | Sized bytes =>
    exact ⟨⟨runtime_layout.align.val, .Fixed bytes, runtime_layout.statically_shallow_unpadded⟩,
      by simp [Matches, hs]⟩
  | SliceDst tail =>
    have positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by
      simpa only [canonicalLayout, hs] using hc
    obtain ⟨⟨align, phase⟩, _, pow2, phase_lt, encoding, _, _⟩ :=
      WP.spec_imp_exists (Raw.encoding_components_spec tail.size_rounding_align_and_phase positive)
    refine ⟨⟨runtime_layout.align.val,
      .Tail ⟨tail.offset, tail.elem_size, tail.size_base, align.val, phase⟩,
      runtime_layout.statically_shallow_unpadded⟩, ?_⟩
    refine ⟨rfl, rfl, ?_⟩
    simp only [hs]
    exact ⟨pow2, (UScalar.lt_equiv _ _).mpr phase_lt, trivial, trivial, trivial,
      checked_add_of_value _ _ _ encoding.symm⟩

theorem no_rounding_padding (bytes align rounded : Usize) (positive : 0 < align.val)
    (hr : rounded.val = LayoutMath.roundUp bytes.val align.val) :
    (rounded = bytes) ↔ bytes.val % align.val = 0 := by
  constructor
  · intro same
    have aligned := (LayoutMath.roundUp_properties bytes.val align.val positive).2.2
    rw [← hr, same] at aligned
    exact aligned
  · intro zero
    apply UScalar.eq_of_val_eq
    rw [hr, LayoutMath.roundUp_eq bytes.val align.val zero]

theorem scalar_max_value (a b : Usize) :
    max a.val b.val = (if a > b then a else b).val := by
  split <;> rename_i comparison
  · exact max_eq_left (by scalar_tac)
  · exact max_eq_right (by scalar_tac)

end Zerocopy.CompositionReference

namespace Zerocopy.Proofs.Raw
open Zerocopy.CompositionReference
set_option linter.unusedSimpArgs false

theorem composition_matches_spec (runtime_layout : layout.DstLayout) (reference : ReferenceLayout) :
    layout.composition_checks.matches_reference runtime_layout reference
      ⦃ b => (b = true ↔ Matches runtime_layout reference) ⦄ := by
  unfold layout.composition_checks.matches_reference
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  split
  · rename_i ha
    split
    · rename_i hu
      cases hr : runtime_layout.size_info <;> cases hs : reference.size <;>
        simp only [bind_ok, WP.spec_ok]
      case Sized.Fixed bytes expected => simp [Matches, hr, hs, ha, hu]
      case Sized.Tail bytes expected => simp [Matches, hr, hs]
      case SliceDst.Fixed actual expected => simp [Matches, hr, hs]
      case SliceDst.Tail actual expected =>
        step as ⟨enabled, he⟩
        split
        · rename_i hp
          have pow2 := Eq.mp he hp
          split
          · rename_i hphase
            split
            · rename_i ho
              split
              · rename_i hel
                split
                · rename_i hb
                  simp only [lift, bind_ok]
                  cases hc : Usize.checked_add expected.round_align expected.phase with
                  | none => simp [Matches, hr, hs, ha, hu, pow2, hphase, ho, hel, hb, hc]
                  | some encoded =>
                    simp [core.num.nonzero.NonZero.get, bind_ok, WP.spec_ok,
                      Matches, hr, hs, ha, hu, pow2, hphase, ho, hel, hb, hc, eq_comm]
                · simp [Matches, hr, hs, ha, hu, pow2, hphase, ho, hel, *]
              · simp [Matches, hr, hs, ha, hu, pow2, hphase, ho, *]
            · simp [Matches, hr, hs, ha, hu, pow2, hphase, *]
          · simp [Matches, hr, hs, ha, hu, *]
        · have np : ¬expected.round_align.val.isPowerOfTwo := by
            intro h
            have yes : enabled = true := Eq.mpr he h
            contradiction
          simp [Matches, hr, hs, ha, hu, np]
    · simp [Matches, *]
  · simp [Matches, *]

theorem composition_round_up_spec (bytes align : Usize) :
    layout.composition_checks.reference_round_up bytes align
      ⦃ result => if align.val = 0 then result = none else
        match result with
        | none => Usize.max < LayoutMath.roundUp bytes.val align.val
        | some rounded => rounded.val = LayoutMath.roundUp bytes.val align.val ⦄ := by
  unfold layout.composition_checks.reference_round_up
  split
  · rename_i hz
    simp [hz, UScalar.val]
  · rename_i hn
    have positive : 0 < align.val := by
      have : align.val ≠ 0 := by simpa only [UScalar.eq_equiv, show (0#usize).val = 0 by simp] using hn
      omega
    step as ⟨remainder, hr⟩
    step with Usize.sub_spec (show remainder.val ≤ align.val by
      have := Nat.mod_lt bytes.val positive
      omega) as ⟨gap, hg, _⟩
    step as ⟨padding, hp⟩
    simp only [WP.spec_ok, show ¬align.val = 0 by omega, if_false]
    have padding_value : padding.val = (align.val - bytes.val % align.val) % align.val := by
      rw [hp, hg, hr]
    have hc := Usize.checked_add_bv_spec bytes padding
    rw [padding_value] at hc
    cases hresult : Usize.checked_add bytes padding with
    | none =>
      rw [hresult] at hc
      unfold LayoutMath.roundUp
      omega
    | some rounded =>
      rw [hresult] at hc
      unfold LayoutMath.roundUp
      omega

theorem composition_alignment_spec (align : Usize) :
    layout.composition_checks.extension_alignment align
      ⦃ b => (b = true ↔ alignmentDomain align.val) ⦄ := by
  unfold layout.composition_checks.extension_alignment
  step as ⟨enabled, he⟩
  split
  · rename_i yes
    have power := Eq.mp he yes
    step as ⟨bound, hb⟩
    · rcases System.Platform.numBits_eq with h | h <;> simp [h]
    have bv : bound.val = 2 ^ 29 := by
      rw [hb]
      rcases System.Platform.numBits_eq with h | h <;> simp [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq, h]
    simp only [WP.spec_ok, alignmentDomain, power, true_and, decide_eq_true_eq,
      UScalar.le_equiv, bv]
  · rename_i no
    have np : ¬align.val.isPowerOfTwo := by
      intro h
      exact no (Eq.mpr he h)
    simp [alignmentDomain, np]

/- Successful independent padding exposes exactly the production fit predicate
and the complete stored result. Failed intermediate sums stay outside that
success domain; no metadata or isize bound is added. -/
theorem composition_reference_pad_spec (reference : ReferenceLayout) :
    layout.composition_checks.reference_pad reference
      ⦃ result => ∀ expected, result = some expected →
        reference.align.val.isPowerOfTwo ∧ (value reference).padFits Usize.max ∧
        value expected = (value reference).pad ∧ valid expected ⦄ := by
  unfold layout.composition_checks.reference_pad
  step as ⟨enabled, he⟩
  split
  · rename_i yes
    have power := Eq.mp he yes
    have positive := Nat.pos_of_isPowerOfTwo power
    cases hs : reference.size with
    | Fixed bytes =>
      step with composition_round_up_spec bytes reference.align as ⟨rounded, hr⟩
      simp only [show ¬reference.align.val = 0 by omega, if_false] at hr
      cases rounded with
      | none => simp
      | some rounded =>
        have bound : rounded.val ≤ Usize.max := by scalar_tac
        have no_padding : (rounded = bytes) ↔ bytes.val % reference.align.val = 0 := by
          constructor
          · intro same
            have aligned := (LayoutMath.roundUp_properties bytes.val reference.align.val positive).2.2
            rw [← hr, same] at aligned
            exact aligned
          · intro zero
            apply UScalar.eq_of_val_eq
            rw [hr, LayoutMath.roundUp_eq bytes.val reference.align.val zero]
        simp only [WP.spec_ok]
        intro expected same
        cases same
        refine ⟨power, ?_, ?_, by simp [valid]⟩
        · simpa only [value, hs, LayoutMath.LayoutValue.padFits, ← hr] using bound
        · simp [value, hs, LayoutMath.LayoutValue.pad, hr, no_padding]
    | Tail tail =>
      step as ⟨tail_enabled, hte⟩
      split
      · rename_i ty
        have tail_power := Eq.mp hte ty
        split
        · simp
        · rename_i phase_small
          have phase_lt : tail.phase.val < tail.round_align.val := by scalar_tac
          split
          · rename_i inner_large
            have nlt : ¬tail.round_align.val < reference.align.val := by scalar_tac
            step with composition_round_up_spec tail.base reference.align as ⟨base, hb⟩
            simp only [show ¬reference.align.val = 0 by omega, if_false] at hb
            cases base with
            | none => simp
            | some base =>
              have bound : base.val ≤ Usize.max := by scalar_tac
              simp only [WP.spec_ok]
              intro expected same
              cases same
              refine ⟨power, ?_, ?_, ?_⟩
              · simpa only [value, hs, tailValue, LayoutMath.LayoutValue.padFits,
                  nlt, if_false, ← hb] using bound
              · simp [value, hs, tailValue, LayoutMath.LayoutValue.pad,
                  LayoutMath.Formula.pad, nlt, hb]
              · simpa only [valid] using And.intro tail_power phase_lt
          · rename_i outer_large
            have lt : tail.round_align.val < reference.align.val := by scalar_tac
            have tail_positive := Nat.pos_of_isPowerOfTwo tail_power
            step with composition_round_up_spec tail.base tail.round_align as ⟨base, hb⟩
            simp only [show ¬tail.round_align.val = 0 by omega, if_false] at hb
            cases base with
            | none => simp
            | some base =>
              step as ⟨fixed, hf⟩
              cases fixed with
              | none => simp
              | some fixed =>
                simp only [] at hf
                step as ⟨phase, hp⟩
                step with Usize.sub_spec (show phase.val ≤ fixed.val by
                  rw [hp]; exact Nat.mod_le _ _) as ⟨newbase, hn, _⟩
                have small : phase.val < reference.align.val := by
                  rw [hp]; exact Nat.mod_lt _ positive
                intro expected same
                cases same
                refine ⟨power, ?_, ?_, by simpa only [valid] using And.intro power small⟩
                · simp only [value, hs, tailValue, LayoutMath.LayoutValue.padFits,
                    lt, if_true]
                  omega
                · have fixed_value : fixed.val = LayoutMath.roundUp tail.base.val tail.round_align.val + tail.phase.val := by omega
                  simp [value, hs, tailValue, LayoutMath.LayoutValue.pad,
                    LayoutMath.Formula.pad, lt, hn, hp, fixed_value]
      · simp
  · simp

theorem composition_reference_extend_at_spec (preceding field : ReferenceLayout)
    (field_align : Usize) (positive : 0 < field_align.val)
    (minimum : field_align.val ≤ field.align.val) :
    layout.composition_checks.reference_extend_at preceding field field_align
      ⦃ result => ∀ expected, result = some expected →
        (value preceding).extendFits (value field) field_align.val Usize.max ∧
        value expected = (value preceding).extend (value field) field_align.val ∧
        (valid field → valid expected) ⦄ := by
  unfold layout.composition_checks.reference_extend_at
  have min_eq : min field.align.val field_align.val = field_align.val := min_eq_right minimum
  cases hs : preceding.size with
  | Tail tail => simp
  | Fixed bytes =>
    step with composition_round_up_spec bytes field_align as ⟨offset, ho⟩
    simp only [show ¬field_align.val = 0 by omega, if_false] at ho
    cases offset with
    | none => simp
    | some offset =>
      have no_padding := no_rounding_padding bytes field_align offset positive ho
      cases hf : field.size with
      | Fixed fieldbytes =>
        step as ⟨total, ht⟩
        cases total with
        | none => simp
        | some total =>
          simp only [] at ht
          by_cases comparison : preceding.align > field_align
          all_goals
            simp only [comparison, if_true, if_false, bind_ok, WP.spec_ok]
            intro expected same
            cases same
            refine ⟨?_, ?_, ?_⟩
            · simp only [value, hs, hf, LayoutMath.LayoutValue.extendFits, min_eq]
              omega
            · simp only [value, hs, hf, LayoutMath.LayoutValue.extend, min_eq]
              have total_value : total.val = LayoutMath.roundUp bytes.val field_align.val + fieldbytes.val := by omega
              simp [total_value, ho, no_padding, scalar_max_value, comparison]
            · simp [valid]
      | Tail tail =>
        step as ⟨slice_offset, ht⟩
        cases slice_offset with
        | none => simp
        | some slice_offset =>
          simp only [] at ht
          step as ⟨base, hb⟩
          cases base with
          | none => simp
          | some base =>
            simp only [] at hb
            by_cases comparison : preceding.align > field_align
            all_goals
              simp only [comparison, if_true, if_false, bind_ok, WP.spec_ok]
              intro expected same
              cases same
              refine ⟨?_, ?_, ?_⟩
              · simp only [value, hs, hf, tailValue, LayoutMath.LayoutValue.extendFits, min_eq]
                constructor <;> omega
              · simp only [value, hs, hf, tailValue, LayoutMath.LayoutValue.extend, min_eq]
                have offset_value : slice_offset.val = LayoutMath.roundUp bytes.val field_align.val + tail.offset.val := by omega
                have base_value : base.val = LayoutMath.roundUp bytes.val field_align.val + tail.base.val := by omega
                simp [offset_value, base_value, ho, no_padding, scalar_max_value, comparison]
              · intro validity
                simpa only [valid, hf] using validity

theorem composition_reference_extend_spec (preceding field : ReferenceLayout)
    (packed : Option NonZeroUsize) :
    layout.composition_checks.reference_extend preceding field packed
      ⦃ result => ∀ expected, result = some expected →
        alignmentDomain preceding.align.val ∧ alignmentDomain field.align.val ∧
        (∀ a ∈ packed, alignmentDomain a.val.val) ∧
        (value preceding).extendFits (value field) (packingValue packed) Usize.max ∧
        value expected = (value preceding).extend (value field) (packingValue packed) ∧
        (valid field → valid expected) ⦄ := by
  unfold layout.composition_checks.reference_extend
  step with composition_alignment_spec preceding.align as ⟨preceding_ok, hp⟩
  split
  · rename_i py
    have preceding_domain := hp.mp py
    step with composition_alignment_spec field.align as ⟨field_ok, hf⟩
    split
    · rename_i fy
      have field_domain := hf.mp fy
      cases packed with
      | none =>
        have limit : 2 ^ 29 ≤ packingValue none := by
          rcases System.Platform.numBits_eq with h | h <;> simp [packingValue, h]
        have field_bound := field_domain.2
        have minimum : min field.align.val (packingValue none) = field.align.val :=
          min_eq_left (by omega)
        apply WP.spec_mono (composition_reference_extend_at_spec preceding field field.align
          (Nat.pos_of_isPowerOfTwo field_domain.1) le_rfl)
        intro result facts expected same
        obtain ⟨fits, output, validity⟩ := facts expected same
        refine ⟨preceding_domain, field_domain, by simp, ?_, ?_, validity⟩
        · simpa only [LayoutMath.LayoutValue.extendFits, minimum,
            show (value field).align = field.align.val from rfl, min_self] using fits
        · simpa only [LayoutMath.LayoutValue.extend, minimum,
            show (value field).align = field.align.val from rfl, min_self] using output
      | some cap =>
        simp only [core.num.nonzero.NonZero.get, bind_ok]
        step with composition_alignment_spec cap.val as ⟨cap_ok, hc⟩
        split
        · rename_i cy
          have cap_domain := hc.mp cy
          have choice : (if field.align < cap.val then Result.ok field.align else Result.ok cap.val)
              ⦃ effective => effective.val = min field.align.val cap.val.val ∧ 0 < effective.val ⦄ := by
            by_cases cmp : field.align < cap.val
            · simp only [cmp, if_true, WP.spec_ok]
              exact ⟨(min_eq_left (by scalar_tac)).symm, Nat.pos_of_isPowerOfTwo field_domain.1⟩
            · simp only [cmp, if_false, WP.spec_ok]
              exact ⟨(min_eq_right (by scalar_tac)).symm, Nat.pos_of_isPowerOfTwo cap_domain.1⟩
          step with choice as ⟨effective, he, positive⟩
          apply WP.spec_mono (composition_reference_extend_at_spec preceding field effective positive
            (by rw [he]; exact min_le_left _ _))
          intro result facts expected same
          obtain ⟨fits, output, validity⟩ := facts expected same
          refine ⟨preceding_domain, field_domain, ?_, ?_, ?_, validity⟩
          · intro a member
            have same : a = cap := by simpa [eq_comm] using member
            subst a
            exact cap_domain
          · simpa only [LayoutMath.LayoutValue.extendFits, packingValue, Option.map_some,
              Option.getD_some, show (value field).align = field.align.val from rfl,
              min_eq_right (show effective.val ≤ field.align.val by rw [he]; exact min_le_left _ _), he,
              min_eq_right (min_le_left field.align.val cap.val.val)] using fits
          · simpa only [LayoutMath.LayoutValue.extend, packingValue, Option.map_some,
              Option.getD_some, show (value field).align = field.align.val from rfl,
              min_eq_right (show effective.val ≤ field.align.val by rw [he]; exact min_le_left _ _), he,
              min_eq_right (min_le_left field.align.val cap.val.val)] using output
        · simp
    · simp
  · simp

end Zerocopy.Proofs.Raw
