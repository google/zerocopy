/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Obligations
public import Specs
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- These bridges consume the supplied weak-stage model contract and recover
-- the unchanged independent c85 propositions. No raw function proof is used.
@[contract_simps] theorem required_padding (len : Usize) (align : NonZeroUsize)
    (run : Result Usize) (provided : Specs.padding_lt_alignment_contract len align run) :
    Obligations.padding_lt_alignment_contract len align run := by
  intro positive
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have admitted := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided (unsignedWord len) rfl av admitted)
  rintro output ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff output value).mp decoded
  simpa only [unsignedWord, av, ← same] using facts

@[contract_simps] theorem required_round_down (n : Usize) (align : NonZeroUsize)
    (run : Result Usize) (provided : Specs.round_down_spec_contract n align run) :
    Obligations.round_down_spec_contract n align run := by
  intro positive pow2
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have admitted := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided (unsignedWord n) rfl av admitted pow2)
  rintro output ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff output value).mp decoded
  simpa only [unsignedWord, av, ← same] using facts

@[contract_simps] theorem required_max (a b : NonZeroUsize) (run : Result NonZeroUsize)
    (provided : Specs.max_spec_contract a b run) :
    Obligations.max_spec_contract a b run := by
  intro pa pb
  let av : NonZeroUsizeValue := ⟨unsignedWord a.val, pa⟩
  let bv : NonZeroUsizeValue := ⟨unsignedWord b.val, pb⟩
  have da := (decodeNonZeroUScalar_iff a av).mpr rfl
  have db := (decodeNonZeroUScalar_iff b bv).mpr rfl
  have result := provided av da bv db
  simp only [WP.spec_equiv_exists] at result
  obtain ⟨output, call, value, decoded, facts⟩ := result
  have same := (decodeNonZeroUScalar_iff output value).mp decoded
  refine ⟨output, call, ?_, ?_⟩
  · rw [same]; exact value.positive
  · simpa only [av, bv, unsignedWord, ← same] using facts

@[contract_simps] theorem required_min (a b : NonZeroUsize) (run : Result NonZeroUsize)
    (provided : Specs.min_spec_contract a b run) :
    Obligations.min_spec_contract a b run := by
  intro pa pb
  let av : NonZeroUsizeValue := ⟨unsignedWord a.val, pa⟩
  let bv : NonZeroUsizeValue := ⟨unsignedWord b.val, pb⟩
  have da := (decodeNonZeroUScalar_iff a av).mpr rfl
  have db := (decodeNonZeroUScalar_iff b bv).mpr rfl
  have result := provided av da bv db
  simp only [WP.spec_equiv_exists] at result
  obtain ⟨output, call, value, decoded, facts⟩ := result
  have same := (decodeNonZeroUScalar_iff output value).mp decoded
  refine ⟨output, call, ?_, ?_⟩
  · rw [same]; exact value.positive
  · simpa only [av, bv, unsignedWord, ← same] using facts
end Zerocopy.Proofs
