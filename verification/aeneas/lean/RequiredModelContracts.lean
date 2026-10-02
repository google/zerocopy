/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredModelContracts.Util
public import RepresentationLaws
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

attribute [contract_simps] encoding_decoder_admitted_iff trailing_decoder_admitted_iff
  size_info_decoder_admitted_iff layout_decoder_admitted_iff

@[contract_simps] theorem required_encoding_new (provided : Specs.encoding_new_spec) :
    Obligations.encoding_new_spec := by
  intro align phase positive pow2 below
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have admitted := (decodeNonZeroUScalar_iff align av).mpr rfl
  have result := provided align phase av admitted (unsignedWord phase) rfl pow2 below
  simp only [WP.spec_equiv_exists] at result
  obtain ⟨raw, call, value, decoded, ha, hp⟩ := result
  refine ⟨raw, call, ?_, ?_⟩
  · exact (encoding_valid_iff raw).mp ⟨value, decoded⟩
  · have represents := (rounding_decode_iff raw value).mp decoded
    simpa only [roundingRepresents, ha, hp, av, unsignedWord] using represents

@[contract_simps] theorem required_encoding_align (provided : Specs.encoding_align_spec) :
    Obligations.encoding_align_spec := by
  intro raw positive
  obtain ⟨value, decoded⟩ := rounding_decode_positive raw positive
  have result := provided raw value decoded
  simp only [WP.spec_equiv_exists] at result
  obtain ⟨align, call, av, admitted, facts⟩ := result
  have same := (decodeNonZeroUScalar_iff align av).mp admitted
  exact ⟨align, call, by rw [same]; exact av.positive,
    same.trans (facts.trans (rounding_decode_components raw value decoded).1)⟩

@[contract_simps] theorem required_encoding_components (provided : Specs.encoding_components_spec) :
    Obligations.encoding_components_spec := by
  intro raw positive
  obtain ⟨value, decoded⟩ := rounding_decode_positive raw positive
  apply WP.spec_mono (provided raw value decoded)
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

@[contract_simps] theorem required_extend (provided : Specs.extend_spec) :
    Obligations.extend_spec := by
  intro self field packed size selfValid fieldValid packedValid hs ha hf hp fits
  obtain ⟨selfModel, selfDecoded⟩ := (layout_valid_iff self).mpr selfValid
  obtain ⟨fieldModel, fieldDecoded⟩ := (layout_valid_iff field).mpr fieldValid
  have packedAccepted : isValid packed := by simpa using packedValid
  obtain ⟨packedModel, packedDecoded⟩ := packedAccepted
  apply WP.spec_mono (provided self field packed selfModel selfDecoded
    fieldModel fieldDecoded packedModel packedDecoded size hs ha hf hp fits)
  rintro result ⟨value, decoded, facts⟩
  exact ⟨(layout_valid_iff result).mp ⟨value, decoded⟩, facts⟩

@[contract_simps] theorem required_try_nonzero (provided : Specs.try_nonzero_spec) :
    Obligations.try_nonzero_spec := by
  intro self accepted
  obtain ⟨value, decoded⟩ := (size_info_valid_iff self).mpr accepted
  apply WP.spec_mono (provided self value decoded)
  rintro result ⟨resultValue, resultDecoded, facts⟩
  refine ⟨?_, ?_⟩
  · have valid : isValid result := ⟨resultValue, resultDecoded⟩
    simpa only [option_valid_iff, size_info_valid_iff] using valid
  · cases self <;> simpa only using facts

end Zerocopy.Proofs
