/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.TailTransforms
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs
set_option linter.unusedVariables false

@[contract_simps] theorem required_tail_transformations_check
    (tail : layout.TrailingSliceLayout Usize) (align : NonZeroUsize)
    (phase bytes replacement_stride elems : Usize) (run : Result Unit)
    (provided : Specs.tail_transformations_check_spec_contract
      tail align phase bytes replacement_stride elems run) :
    Obligations.tail_transformations_check_spec_contract
      tail align phase bytes replacement_stride elems run := by
  intro positive align_positive
  obtain ⟨tail_value, decoded_tail⟩ :=
    (trailing_valid_iff tail).mpr ⟨by simp, positive⟩
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, align_positive⟩
  have decoded_align := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided tail_value decoded_tail av decoded_align
    (unsignedWord phase) rfl (unsignedWord bytes) rfl
    (unsignedWord replacement_stride) rfl (unsignedWord elems) rfl)
  rintro result ⟨value, decoded, facts⟩
  trivial

@[contract_simps] theorem required_tail_size_sequence_check
    (left right : layout.TrailingSliceLayout Usize)
    (left_align : NonZeroUsize) (left_phase : Usize)
    (right_align : NonZeroUsize) (right_phase elems : Usize) (run : Result Unit)
    (provided : Specs.tail_size_sequence_check_spec_contract
      left right left_align left_phase right_align right_phase elems run) :
    Obligations.tail_size_sequence_check_spec_contract
      left right left_align left_phase right_align right_phase elems run := by
  intro left_positive right_positive left_align_positive right_align_positive
  obtain ⟨left_value, decoded_left⟩ :=
    (trailing_valid_iff left).mpr ⟨by simp, left_positive⟩
  obtain ⟨right_value, decoded_right⟩ :=
    (trailing_valid_iff right).mpr ⟨by simp, right_positive⟩
  let av : NonZeroUsizeValue := ⟨unsignedWord left_align.val, left_align_positive⟩
  let bv : NonZeroUsizeValue := ⟨unsignedWord right_align.val, right_align_positive⟩
  have decoded_a := (decodeNonZeroUScalar_iff left_align av).mpr rfl
  have decoded_b := (decodeNonZeroUScalar_iff right_align bv).mpr rfl
  apply WP.spec_mono (provided left_value decoded_left right_value decoded_right
    av decoded_a (unsignedWord left_phase) rfl bv decoded_b
    (unsignedWord right_phase) rfl (unsignedWord elems) rfl)
  rintro result ⟨value, decoded, facts⟩
  trivial

@[contract_simps] theorem required_tail_dynamic_padding_check
    (runtime_layout : layout.DstLayout) (align : NonZeroUsize) (phase : Usize)
    (run : Result Unit)
    (provided : Specs.tail_dynamic_padding_check_spec_contract runtime_layout align phase run) :
    Obligations.tail_dynamic_padding_check_spec_contract runtime_layout align phase run := by
  intro valid_runtime align_positive
  obtain ⟨layout_value, decoded_layout⟩ := (layout_valid_iff runtime_layout).mpr valid_runtime
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, align_positive⟩
  have decoded_align := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided layout_value decoded_layout av decoded_align (unsignedWord phase) rfl)
  rintro result ⟨value, decoded, facts⟩
  trivial

end Zerocopy.Proofs
