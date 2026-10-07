/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Std.Tactic
@[expose] public section

/-!
Natural-number alignment facts, independent of machine words and backends.
Bounded-word implementations can use these laws after separately proving their
numerical results. A positive alignment and exact padding or round-down result
are explicit hypotheses; these laws add no Rust or machine-layout assumptions.
-/

namespace Rust.Arithmetic

/-- The unique bounded padding that makes the sum divisible by alignment. -/
theorem padding_unique (len align p : Nat) (hpos : 0 < align)
    (hlt : p < align) (haligned : (len + p) % align = 0) :
    p = (align - len % align) % align := by
  have hr := Nat.mod_lt len hpos
  have hsum : (len % align + p) % align = 0 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hlt] at haligned
    exact haligned
  by_cases hzero : len % align = 0
  · simpa only [hzero, Nat.zero_add, Nat.mod_eq_of_lt hlt,
      Nat.sub_zero, Nat.mod_self] using hsum
  · have hge : align ≤ len % align + p := by
      by_cases h : align ≤ len % align + p
      · exact h
      · rw [Nat.mod_eq_of_lt (by omega)] at hsum
        omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hsum
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Exact padding also gives minimality and the zero-padding criterion. -/
theorem padding_properties (len align p : Nat) (hpos : 0 < align)
    (hlt : p < align) (haligned : (len + p) % align = 0) :
    p = (align - len % align) % align ∧
    (∀ q : Nat, (len + q) % align = 0 → p ≤ q) ∧
    (p = 0 ↔ len % align = 0) := by
  refine ⟨padding_unique len align p hpos hlt haligned, ?_, ?_⟩
  · intro q hq
    have hqm : (len + q % align) % align = 0 := by
      rw [Nat.add_mod] at hq
      rw [Nat.add_mod, Nat.mod_mod]
      exact hq
    have heq := padding_unique len align (q % align) hpos
      (Nat.mod_lt q hpos) hqm
    have hp := padding_unique len align p hpos hlt haligned
    have := Nat.mod_le q align
    omega
  · constructor
    · intro hp
      simpa only [hp, Nat.add_zero] using haligned
    · intro hl
      have hp := padding_unique len align p hpos hlt haligned
      simpa only [hl, Nat.sub_zero, Nat.mod_self] using hp

/-- An exact round-down result is aligned and the greatest such lower bound. -/
theorem round_down_properties (n align m : Nat) (hpos : 0 < align)
    (hm : m = n - n % align) :
    m ≤ n ∧ m % align = 0 ∧ n < m + align ∧
    (∀ q : Nat, q ≤ n → q % align = 0 → q ≤ m) := by
  have hr := Nat.mod_lt n hpos
  have hrle := Nat.mod_le n align
  have hmul : m = (n / align) * align := by
    rw [Nat.div_mul_self_eq_mod_sub_self, hm]
  refine ⟨by omega, ?_, by omega, ?_⟩
  · rw [hmul, Nat.mul_mod_left]
  · intro q hqn hqa
    have hdiv := Nat.div_le_div_right (c := align) hqn
    have hle := Nat.mul_le_mul_right align hdiv
    rw [Nat.div_mul_self_eq_mod_sub_self, Nat.div_mul_self_eq_mod_sub_self,
      hqa, Nat.sub_zero, ← hm] at hle
    exact hle

end Rust.Arithmetic
