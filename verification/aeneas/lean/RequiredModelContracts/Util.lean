/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Obligations
public import Specs
public import MathViews
@[expose] public section

/-!
The arithmetic inline specs use bounded mathematical words; the independent
expectations retain raw machine-word observations. These adapters bridge
those descriptions for an arbitrary execution outcome, using only the
supplied spec. They must construct decoded inputs from the independent raw
domain and recover raw output facts from successful decoding. Proving the
implementation again would not establish that the inline promise itself is
strong enough.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

attribute [contract_simps] option_admitted_explicit_iff admitted_some admitted_none
  admitted_dite

-- These implications consume a supplied model contract and recover the
-- separately authored representation observations. They do not prove or
-- select a function contract themselves.
@[contract_simps] theorem required_padding (len : Usize) (align : NonZeroUsize)
    (run : Result Usize) (provided : Specs.padding_lt_alignment_contract len align run) :
    Obligations.padding_lt_alignment_contract len align run := by
  intro positive pow2
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, positive⟩
  have admitted := (decodeNonZeroUScalar_iff align av).mpr rfl
  apply WP.spec_mono (provided (unsignedWord len) rfl av admitted pow2)
  rintro p ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff p value).mp decoded
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

theorem nonzero_raw_eq_of_value_eq (a b : NonZeroUsize)
    (same : a.val.val = b.val.val) : a = b := by
  have hs := UScalar.eq_of_val_eq same
  cases a; cases b
  congr

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
  obtain ⟨r, call, value, decoded, facts⟩ := result
  have same := (decodeNonZeroUScalar_iff r value).mp decoded
  refine ⟨r, call, ?_, ?_, ?_, ?_, ?_⟩
  · rw [same]; exact value.positive
  · simpa only [av, bv, unsignedWord, ← same] using facts.1
  · rcases facts.2.1 with h | h
    · left; apply nonzero_raw_eq_of_value_eq; simp only [same, h, av, unsignedWord]
    · right; apply nonzero_raw_eq_of_value_eq; simp only [same, h, bv, unsignedWord]
  · simpa only [av, unsignedWord, ← same] using facts.2.2.1
  · simpa only [bv, unsignedWord, ← same] using facts.2.2.2

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
  obtain ⟨r, call, value, decoded, facts⟩ := result
  have same := (decodeNonZeroUScalar_iff r value).mp decoded
  refine ⟨r, call, ?_, ?_, ?_, ?_, ?_⟩
  · rw [same]; exact value.positive
  · simpa only [av, bv, unsignedWord, ← same] using facts.1
  · rcases facts.2.1 with h | h
    · left; apply nonzero_raw_eq_of_value_eq; simp only [same, h, av, unsignedWord]
    · right; apply nonzero_raw_eq_of_value_eq; simp only [same, h, bv, unsignedWord]
  · simpa only [av, unsignedWord, ← same] using facts.2.2.1
  · simpa only [bv, unsignedWord, ← same] using facts.2.2.2

end Zerocopy.Proofs
