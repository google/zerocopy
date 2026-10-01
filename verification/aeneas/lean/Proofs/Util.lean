/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
import all Init.Data.Nat.Power2.Basic
@[expose] public section

/-!
These four arithmetic helpers show the proof pattern used by the integration.
Raw lemmas unfold the actual extracted computation and prove precise numeric
facts. Canonical theorems then lift those facts to the generated inline
specs, including successful input and result decoding.

The notation computation ⦃ result => property ⦄ means that execution
terminates successfully and its returned value satisfies property. Aeneas's
step tactic uses a registered callee specification, generating its
preconditions as proof goals. These proofs connect numeric facts to the
specific zerocopy implementations.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false

theorem padding_lt_alignment :
  ∀ (len : Usize) (align : NonZeroUsize), ∀ (h : (0 < align.val.val : Prop)),
    @Zerocopy.util.padding_needed_for len align ⦃ p => p.val < align.val.val ⦄ := by
  intro len align h
  unfold util.padding_needed_for
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step
  simp only [lift, bind_ok, WP.spec_ok, UScalar.val_and]
  have hbound :
      (~~~(core.num.Usize.wrapping_sub len 1#usize)).val &&& mask.val ≤ mask.val :=
    Nat.and_le_right
  omega

theorem round_down_spec :
  ∀ (n : Usize) (align : NonZeroUsize), ∀ (hpos : (0 < align.val.val : Prop)), ∀ (h : (align.val.val.isPowerOfTwo : Prop)),
    @Zerocopy.util.round_down_to_next_multiple_of_alignment n align ⦃ m => m.val ≤ n.val ∧ m.val % align.val.val = 0 ⦄ := by
  intro n align hpos h
  unfold util.round_down_to_next_multiple_of_alignment
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step
  step
  step with UScalar.sub_bv_spec as ⟨mask, hval, hle, hbv⟩
  simp only [lift, bind_ok, WP.spec_ok]
  constructor
  · simp only [UScalar.val_and]
    exact Nat.and_le_left
  · have clear : (n &&& ~~~mask).val &&& mask.val = 0 := by
      rw [← UScalar.val_and]
      change ((n.bv &&& ~~~mask.bv) &&& mask.bv).toNat = 0
      simp [BitVec.and_assoc]
    unfold Nat.isPowerOfTwo at h
    rcases h with ⟨k, hk⟩
    rw [hval, hk, Nat.and_two_pow_sub_one_eq_mod] at clear
    simpa only [hk] using clear

theorem max_spec :
  ∀ (a b : NonZeroUsize),
    @Zerocopy.util.max a b ⦃ r => r.val.val = Nat.max a.val.val b.val.val ⦄ := by
  intro a b
  apply WP.exists_imp_spec
  simp only [util.max, core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
  split
  · rename_i h
    exact ⟨b, rfl, (Nat.max_eq_right (by omega)).symm⟩
  · rename_i h
    exact ⟨a, rfl, (Nat.max_eq_left (by omega)).symm⟩

theorem min_spec :
  ∀ (a b : NonZeroUsize),
    @Zerocopy.util.min a b ⦃ r => r.val.val = Nat.min a.val.val b.val.val ⦄ := by
  intro a b
  apply WP.exists_imp_spec
  simp only [util.min, core.num.nonzero.NonZero.get, bind_ok, UScalar.lt_equiv]
  split
  · rename_i h
    exact ⟨b, rfl, (Nat.min_eq_right (by omega)).symm⟩
  · rename_i h
    exact ⟨a, rfl, (Nat.min_eq_left (by omega)).symm⟩

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by
  intro len align _lenValue _hlen alignValue halign
  have ha := (decodeNonZeroUScalar_iff align alignValue).mp halign
  have positive : 0 < align.val.val := by rw [ha]; exact alignValue.positive
  apply WP.spec_mono (Raw.padding_lt_alignment len align positive)
  intro output facts
  refine ⟨unsignedWord output, rfl, ?_⟩
  dsimp only
  rw [← ha]
  exact facts
register_spec_step padding_lt_alignment

theorem round_down_spec : Zerocopy.Specs.round_down_spec := by
  intro n align nValue hn alignValue halign pow2
  have hnv := (decodeUScalar_iff n nValue).mp hn
  have ha := (decodeNonZeroUScalar_iff align alignValue).mp halign
  have positive : 0 < align.val.val := by rw [ha]; exact alignValue.positive
  apply WP.spec_mono (Raw.round_down_spec n align positive (by simpa only [ha] using pow2))
  intro output facts
  refine ⟨unsignedWord output, rfl, ?_⟩
  dsimp only
  rw [← hnv, ← ha]
  exact facts
register_spec_step round_down_spec

theorem max_spec : Zerocopy.Specs.max_spec := by
  intro a b av ha bv hb
  have hav := (decodeNonZeroUScalar_iff a av).mp ha
  have hbv := (decodeNonZeroUScalar_iff b bv).mp hb
  apply WP.spec_mono (Raw.max_spec a b)
  intro output facts
  have positive : 0 < output.val.val := by
    rw [facts, hav, hbv]
    exact lt_of_lt_of_le av.positive (Nat.le_max_left _ _)
  let value : NonZeroUsizeValue := ⟨unsignedWord output.val, positive⟩
  refine ⟨value, (decodeNonZeroUScalar_iff output value).mpr rfl, ?_⟩
  simpa only [value, unsignedWord, hav, hbv] using facts
register_spec_step max_spec

theorem min_spec : Zerocopy.Specs.min_spec := by
  intro a b av ha bv hb
  have hav := (decodeNonZeroUScalar_iff a av).mp ha
  have hbv := (decodeNonZeroUScalar_iff b bv).mp hb
  apply WP.spec_mono (Raw.min_spec a b)
  intro output facts
  have positive : 0 < output.val.val := by
    rw [facts, hav, hbv]
    exact lt_min av.positive bv.positive
  let value : NonZeroUsizeValue := ⟨unsignedWord output.val, positive⟩
  refine ⟨value, (decodeNonZeroUScalar_iff output value).mpr rfl, ?_⟩
  simpa only [value, unsignedWord, hav, hbv] using facts
register_spec_step min_spec

end Zerocopy.Proofs
