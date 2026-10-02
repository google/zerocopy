/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredModelContracts.Util
public import RepresentationLaws
public import ModelProjectionLaws
@[expose] public section

/-!
These adapters prove that mathematical inline promises retain independently
stated raw behavior and input coverage. Each receives provided, a proof about
an arbitrary run, and derives the matching Obligations proposition for that
same run. It never executes or independently proves the function to bypass a
weak authored spec.

Constructing mathematical input witnesses from raw premises checks the
promised domain. Recovering raw facts from the decoded result checks the
promised observations. The contract_simps attribute makes these ordinary
proved implications available to check_contract's bounded normalization.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

attribute [contract_simps] encoding_decoder_admitted_iff trailing_decoder_admitted_iff
  size_info_decoder_admitted_iff layout_decoder_admitted_iff

@[contract_simps] theorem required_encoding_new (align : NonZeroUsize) (phase : Usize)
    (run : Result layout.RoundingAlignAndPhase)
    (provided : Specs.encoding_new_spec_contract align phase run) :
    Obligations.encoding_new_spec_contract align phase run := by
  intro positive pow2 below
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have admitted := (decodeNonZeroUScalar_iff align av).mpr rfl
  have result := provided av admitted (unsignedWord phase) rfl pow2 below
  simp only [WP.spec_equiv_exists] at result
  obtain ⟨raw, call, value, decoded, ha, hp⟩ := result
  refine ⟨raw, call, ?_, ?_⟩
  · exact (encoding_valid_iff raw).mp ⟨value, decoded⟩
  · have represents := (rounding_decode_iff raw value).mp decoded
    simpa only [roundingRepresents, ha, hp, av, unsignedWord] using represents

@[contract_simps] theorem required_encoding_align (raw : layout.RoundingAlignAndPhase)
    (run : Result NonZeroUsize)
    (provided : Specs.encoding_align_spec_contract raw run) :
    Obligations.encoding_align_spec_contract raw run := by
  intro positive
  obtain ⟨value, decoded⟩ := rounding_decode_positive raw positive
  have result := provided value decoded
  simp only [WP.spec_equiv_exists] at result
  obtain ⟨align, call, av, admitted, facts⟩ := result
  have same := (decodeNonZeroUScalar_iff align av).mp admitted
  exact ⟨align, call, by rw [same]; exact av.positive,
    same.trans (facts.trans (rounding_decode_components raw value decoded).1)⟩

@[contract_simps] theorem required_encoding_components (raw : layout.RoundingAlignAndPhase)
    (run : Result (NonZeroUsize × Usize))
    (provided : Specs.encoding_components_spec_contract raw run) :
    Obligations.encoding_components_spec_contract raw run := by
  intro positive
  obtain ⟨value, decoded⟩ := rounding_decode_positive raw positive
  apply WP.spec_mono (provided value decoded)
  rintro ⟨align, phase⟩ ⟨pair, admitted, ha, hp⟩
  have positiveAlign : 0 < align.val.val :=
    (nonzero_valid_iff align).mp ((prod_valid_iff (align, phase)).mp ⟨pair, admitted⟩).1
  have pairEq : ((⟨unsignedWord align.val, positiveAlign⟩ : NonZeroUsizeValue),
      unsignedWord phase) = pair := by
    simpa only [RustModel.decode, dif_pos positiveAlign, Option.some.injEq] using admitted
  cases pairEq
  dsimp only [unsignedWord] at ha hp
  have hraw := (rounding_decode_iff raw value).mp decoded
  have hcanonical := rounding_decode_components raw value decoded
  change 0 < align.val.val ∧ align.val.val.isPowerOfTwo ∧
    phase.val < align.val.val ∧ align.val.val + phase.val = raw._0.val.val ∧
    align.val.val = 2 ^ raw._0.val.val.log2 ∧
    phase.val = raw._0.val.val - 2 ^ raw._0.val.val.log2
  rw [ha, hp]
  exact ⟨Nat.pos_of_isPowerOfTwo value.align_pow2, value.align_pow2, value.phase_lt,
    hraw.symm, hcanonical.1, hcanonical.2⟩

@[contract_simps] theorem required_extend (self field : layout.DstLayout)
    (packed : Option NonZeroUsize) (run : Result layout.DstLayout)
    (provided : Specs.extend_spec_contract self field packed run) :
    Obligations.extend_spec_contract self field packed run := by
  intro size selfValid fieldValid packedValid hs ha hf hp fits
  obtain ⟨selfModel, selfDecoded⟩ := (layout_decoder_admitted_iff self).mpr selfValid
  obtain ⟨fieldModel, fieldDecoded⟩ := (layout_decoder_admitted_iff field).mpr fieldValid
  have packedAccepted : isValid packed := by simpa using packedValid
  obtain ⟨packedModel, packedDecoded⟩ := packedAccepted
  have selfView := layoutValue_decode self selfModel selfDecoded
  have fieldView := layoutValue_decode field fieldModel fieldDecoded
  have packedView := packingValue_decode packed packedModel packedDecoded
  have selfAlign : selfModel.align.value = self.align.val.val :=
    congrArg LayoutMath.LayoutValue.align selfView
  have fieldAlign : fieldModel.align.value = field.align.val.val :=
    congrArg LayoutMath.LayoutValue.align fieldView
  have modelPacked : ∀ a ∈ packedModel, alignmentDomain a.value :=
    (packing_alignment_decode packed packedModel packedDecoded).mpr hp
  have modelFits : (ModelViews.layoutValue selfModel).extendFits
      (ModelViews.layoutValue fieldModel) (ModelViews.packingValue packedModel) Usize.max := by
    rw [selfView, fieldView, packedView]
    exact (layout_extendFits_iff self field packed size hs).mpr fits
  have fieldCanonical : canonicalLayout field := by
    cases info : field.size_info with
    | Sized _ => simp only [canonicalLayout, info]
    | SliceDst _ =>
      simpa only [sizeInfoValid, trailingValid, encodingValid,
        scalar_valid_iff, true_and, canonicalLayout, info] using fieldValid.2
  apply WP.spec_mono (provided selfModel selfDecoded fieldModel fieldDecoded
    packedModel packedDecoded (by simpa only [selfAlign] using ha)
    (by simpa only [fieldAlign] using hf) modelPacked modelFits)
  rintro result ⟨value, decoded, facts⟩
  have valid := (layout_decoder_admitted_iff result).mp ⟨value, decoded⟩
  have resultCanonical : canonicalLayout result := by
    cases info : result.size_info with
    | Sized _ => simp only [canonicalLayout, info]
    | SliceDst _ =>
      simpa only [sizeInfoValid, trailingValid, encodingValid,
        scalar_valid_iff, true_and, canonicalLayout, info] using valid.2
  refine ⟨valid, ?_⟩
  change ModelViews.layoutValue value =
    (ModelViews.layoutValue selfModel).extend
      (ModelViews.layoutValue fieldModel) (ModelViews.packingValue packedModel) at facts
  rw [layoutValue_decode result value decoded, selfView, fieldView, packedView] at facts
  exact (layout_extend_iff self field result packed size hs
    fieldCanonical resultCanonical).mp facts

@[contract_simps] theorem required_try_nonzero (self : layout.SizeInfo Usize)
    (run : Result (Option (layout.SizeInfo NonZeroUsize)))
    (provided : Specs.try_nonzero_spec_contract self run) :
    Obligations.try_nonzero_spec_contract self run := by
  intro accepted
  obtain ⟨value, decoded⟩ := (size_info_valid_iff self).mpr accepted
  apply WP.spec_mono (provided value decoded)
  rintro result ⟨resultValue, resultDecoded, facts⟩
  refine ⟨?_, ?_⟩
  · have valid : isValid result := ⟨resultValue, resultDecoded⟩
    simpa only [option_valid_iff, size_info_valid_iff] using valid
  · cases self <;> simpa only using facts

end Zerocopy.Proofs
