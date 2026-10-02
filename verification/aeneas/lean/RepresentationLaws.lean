/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import MathViews
public import ModelSupport
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

/-- The stored word represents exactly the sum of the observed pair. -/
def roundingRepresents (raw : layout.RoundingAlignAndPhase)
    (value : layout.RoundingAlignAndPhase.RoundingValue) : Prop :=
  raw._0.val.val = value.align + value.phase

theorem rounding_decode_positive (raw : layout.RoundingAlignAndPhase)
    (positive : 0 < raw._0.val.val) :
    ∃ value, layout.RoundingAlignAndPhase.decode raw = some value :=
  (encoding_valid_iff raw).mpr positive

theorem rounding_decode_components (raw : layout.RoundingAlignAndPhase)
    (value : layout.RoundingAlignAndPhase.RoundingValue)
    (h : layout.RoundingAlignAndPhase.decode raw = some value) :
    value.align = 2 ^ Nat.log2 raw._0.val.val ∧
      value.phase = raw._0.val.val - 2 ^ Nat.log2 raw._0.val.val := by
  have positive : 0 < raw._0.val.val :=
    (encoding_valid_iff raw).mp ⟨value, h⟩
  simp [layout.RoundingAlignAndPhase.decode, layout.RoundingAlignAndPhase.decodeFields,
    RustModel.decode, positive, unsignedWord] at h
  cases h
  exact ⟨rfl, rfl⟩

theorem rounding_decode_iff (raw : layout.RoundingAlignAndPhase)
    (value : layout.RoundingAlignAndPhase.RoundingValue) :
    layout.RoundingAlignAndPhase.decode raw = some value ↔ roundingRepresents raw value := by
  constructor
  · intro h
    obtain ⟨ha, hp⟩ := rounding_decode_components raw value h
    have positive := (encoding_valid_iff raw).mp ⟨value, h⟩
    unfold roundingRepresents
    rw [ha, hp]
    exact (RoundingFacts.reconstruction _ positive).symm
  · intro h
    have positive : 0 < raw._0.val.val := by
      have := Nat.pos_of_isPowerOfTwo value.align_pow2
      unfold roundingRepresents at h
      omega
    obtain ⟨actual, decoded⟩ := rounding_decode_positive raw positive
    obtain ⟨ha, hp⟩ := rounding_decode_components raw actual decoded
    have unique := RoundingFacts.components_unique raw._0.val.val value.align value.phase
      value.align_pow2 value.phase_lt h
    have equal : actual = value := RoundingFacts.value_ext
      (ha.trans unique.1.symm) (hp.trans unique.2.symm)
    simpa only [equal] using decoded

end Zerocopy.Proofs
