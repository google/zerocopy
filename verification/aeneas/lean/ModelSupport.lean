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

/-!
The inline rounding decoder constructs a constrained alignment/phase pair.
These ordinary arithmetic lemmas explain why a positive word has the required
components, and why those components are unique. This module imports model
shapes rather than full providers, so it can be available while decoders are
being elaborated. It supplies reusable facts, not a separate certification
duty that every mathematical model must satisfy.
-/
open Aeneas Aeneas.Std AeneasSpecs

namespace Zerocopy.RoundingFacts

/-- A positive word has a unique highest power-of-two bit. -/
theorem bounds (word : Nat) (positive : 0 < word) :
    2 ^ Nat.log2 word ≤ word ∧ word < 2 ^ (Nat.log2 word + 1) :=
  (Nat.log2_eq_iff (by omega)).mp rfl

theorem reconstruction (word : Nat) (positive : 0 < word) :
    2 ^ Nat.log2 word + (word - 2 ^ Nat.log2 word) = word := by
  have := bounds word positive
  omega

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

end Zerocopy.RoundingFacts
