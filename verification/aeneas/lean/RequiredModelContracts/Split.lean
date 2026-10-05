/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.Split
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[contract_simps] theorem required_split_right_len (total left : Usize) (run : Result Usize)
    (provided : Specs.split_right_len_spec_contract total left run) :
    Obligations.split_right_len_spec_contract total left run := by
  intro index
  apply WP.spec_mono (provided (unsignedWord total) rfl (unsignedWord left) rfl index)
  rintro right ⟨value, decoded, count, bound⟩
  have same := (decodeUScalar_iff right value).mp decoded
  change value.value + left.val = total.val at count
  change value.value ≤ total.val at bound
  rw [← same] at count bound
  exact ⟨by omega, count, bound⟩

@[contract_simps] theorem required_split_zero_padding (padding : Usize) (run : Result Bool)
    (provided : Specs.split_zero_padding_spec_contract padding run) :
    Obligations.split_zero_padding_spec_contract padding run := by
  apply WP.spec_mono (provided (unsignedWord padding) rfl)
  rintro accepted ⟨value, decoded, fact⟩
  have same : value = accepted := by
    symm
    simpa only [RustModel.decode, modelBool, Option.some.injEq] using decoded
  simpa only [same, unsignedWord] using fact

@[contract_simps] theorem required_split_geometry_check (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase total left : Usize) (run : Result Unit)
    (provided : Specs.split_geometry_check_spec_contract tail align phase total left run) :
    Obligations.split_geometry_check_spec_contract tail align phase total left run := by
  intro positive alignPositive
  obtain ⟨tailValue, tailDecoded⟩ := (trailing_valid_iff tail).mpr ⟨by simp, positive⟩
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, alignPositive⟩
  have alignDecoded := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided tailValue tailDecoded av alignDecoded
    (unsignedWord phase) rfl (unsignedWord total) rfl (unsignedWord left) rfl)
  intro result facts
  trivial

end Zerocopy.Proofs
