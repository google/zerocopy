/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelShapes
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs

namespace Zerocopy.RoundingFacts

/-- A positive word has a unique highest power-of-two bit. -/
theorem bounds (word : Nat) (positive : 0 < word) :
    2 ^ Nat.log2 word ≤ word ∧ word < 2 ^ (Nat.log2 word + 1) :=
  (Nat.log2_eq_iff (by omega)).mp rfl

theorem power_of_two (word : Nat) : (2 ^ Nat.log2 word).isPowerOfTwo :=
  ⟨Nat.log2 word, rfl⟩

theorem phase_bound (word : Nat) (positive : 0 < word) :
    word - 2 ^ Nat.log2 word < 2 ^ Nat.log2 word := by
  have := bounds word positive
  rw [Nat.pow_succ] at this
  omega

theorem reconstruction (word : Nat) (positive : 0 < word) :
    2 ^ Nat.log2 word + (word - 2 ^ Nat.log2 word) = word := by
  have := bounds word positive
  omega

theorem fits (word maximum : Nat) (positive : 0 < word)
    (bounded : word ≤ maximum) :
    2 ^ Nat.log2 word + (word - 2 ^ Nat.log2 word) ≤ maximum := by
  rw [reconstruction word positive]
  exact bounded

/-- These are the exact components of every positive encoding, not a restricted
constructor-only subset of the representation domain. -/
theorem components_unique (word align phase : Nat)
    (pow2 : align.isPowerOfTwo) (phase_lt : phase < align)
    (encoding : word = align + phase) :
    align = 2 ^ Nat.log2 word ∧ phase = word - 2 ^ Nat.log2 word := by
  obtain ⟨k, rfl⟩ := pow2
  have positive : 0 < word := by have := Nat.two_pow_pos k; omega
  have hk : Nat.log2 word = k :=
    (Nat.log2_eq_iff (by omega)).mpr (by rw [Nat.pow_succ]; omega)
  rw [hk]
  omega

/-- Proof irrelevance makes equality depend only on the observed pair. -/
@[ext] theorem value_ext
    {a b : layout.RoundingAlignAndPhase.RoundingValue}
    (ha : a.align = b.align) (hp : a.phase = b.phase) : a = b := by
  cases a; cases b; simp_all

theorem word_bound (word : NonZeroUsizeValue) : word.value ≤ Usize.max := by
  simpa only [UScalar.max, Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq] using word.bound

end Zerocopy.RoundingFacts
