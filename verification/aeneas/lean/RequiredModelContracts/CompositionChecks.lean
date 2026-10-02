/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredModelContracts
public import Obligations.CompositionChecks
@[expose] public section

/-!
These adapters recover the independent successful-execution expectations from
an arbitrary supplied specification outcome. Every numeric reference value
decodes; its runtime admission guard belongs to the Rust harness itself.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

/- Structural decoding imposes no hidden restriction on the numeric witnesses. -/
theorem composition_reference_admitted (reference : layout.composition_checks.ReferenceLayout) :
    isValid reference := by
  cases reference with
  | mk align size unpadded =>
    cases size with
    | Fixed bytes =>
      exact ⟨⟨unsignedWord align, .Fixed (unsignedWord bytes), unpadded⟩, rfl⟩
    | Tail tail =>
      exact ⟨⟨unsignedWord align,
        .Tail ⟨unsignedWord tail.offset, unsignedWord tail.elem_size, unsignedWord tail.base,
          unsignedWord tail.round_align, unsignedWord tail.phase⟩, unpadded⟩, rfl⟩

theorem composition_options_admitted (words : Option NonZeroUsize)
    (positive : ∀ a ∈ words, 0 < a.val.val) : isValid words := by
  rw [option_valid_iff]
  intro a member
  exact (nonzero_valid_iff a).mpr (positive a member)

@[contract_simps] theorem required_composition_pad_checks (runtime_layout : layout.DstLayout)
    (reference : layout.composition_checks.ReferenceLayout) (run : Result Unit)
    (provided : Specs.composition_pad_checks_spec_contract runtime_layout reference run) :
    Obligations.composition_pad_checks_spec_contract runtime_layout reference run := by
  intro validity
  obtain ⟨runtime_value, runtime_decode⟩ := (layout_decoder_admitted_iff runtime_layout).mpr validity
  obtain ⟨reference_value, reference_decode⟩ := composition_reference_admitted reference
  apply WP.spec_mono (provided runtime_value runtime_decode reference_value reference_decode)
  intro _ _
  trivial

@[contract_simps] theorem required_composition_extend_checks (preceding field : layout.DstLayout)
    (packed : Option NonZeroUsize)
    (preceding_reference field_reference : layout.composition_checks.ReferenceLayout)
    (run : Result Unit) (provided : Specs.composition_extend_checks_spec_contract preceding field packed
      preceding_reference field_reference run) :
    Obligations.composition_extend_checks_spec_contract preceding field packed
      preceding_reference field_reference run := by
  intro preceding_valid field_valid packed_positive
  obtain ⟨preceding_value, preceding_decode⟩ := (layout_decoder_admitted_iff preceding).mpr preceding_valid
  obtain ⟨field_value, field_decode⟩ := (layout_decoder_admitted_iff field).mpr field_valid
  obtain ⟨packed_value, packed_decode⟩ := composition_options_admitted packed packed_positive
  obtain ⟨preceding_reference_value, preceding_reference_decode⟩ := composition_reference_admitted preceding_reference
  obtain ⟨field_reference_value, field_reference_decode⟩ := composition_reference_admitted field_reference
  apply WP.spec_mono (provided preceding_value preceding_decode field_value field_decode packed_value packed_decode
    preceding_reference_value preceding_reference_decode field_reference_value field_reference_decode)
  intro _ _
  trivial

end Zerocopy.Proofs
