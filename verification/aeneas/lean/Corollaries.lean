/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.Result
namespace Zerocopy.Corollaries
open Proofs

/- Selecting either input preserves any predicate shared by both inputs. -/
contract max_preserves (a b : NonZeroUsize) (P : NonZeroUsize → Prop)
  for util.max a b
  requires ha : P a
  requires hb : P b
  ensures r => P r
  proof:
    step with max_spec a b as ⟨r, _, hchoice, _, _⟩
    rcases hchoice with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb

contract min_preserves (a b : NonZeroUsize) (P : NonZeroUsize → Prop)
  for util.min a b
  requires ha : P a
  requires hb : P b
  ensures r => P r
  proof:
    step with min_spec a b as ⟨r, _, hchoice, _, _⟩
    rcases hchoice with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb

/-- Aligned inputs are fixed points of round-down. -/
theorem round_down_aligned (n : Usize) (align : NonZeroUsize)
    (hpow : (align.val : Nat).isPowerOfTwo)
    (haligned : (n : Nat) % (align.val : Nat) = 0) :
    util.round_down_to_next_multiple_of_alignment n align = .ok n := by
  obtain ⟨m, hm, _, hexact, _, _, _⟩ :=
    WP.spec_imp_exists (round_down_spec n align hpow)
  have heq : m = n := UScalar.eq_of_val_eq (by
    simpa only [haligned, Nat.sub_zero] using hexact)
  simpa only [heq] using hm

contract round_down_idempotent (n : Usize) (align : NonZeroUsize)
  for (do
    let m ← util.round_down_to_next_multiple_of_alignment n align
    let m' ← util.round_down_to_next_multiple_of_alignment m align
    ok (m, m'))
  requires hpow : (align.val : Nat).isPowerOfTwo
  ensures m m' => m' = m
  proof:
    step with round_down_spec n align hpow as ⟨m, _, _, haligned, _, _⟩
    rw [round_down_aligned m align hpow haligned]
    simp only [bind_ok, WP.spec_ok, WP.uncurry'_pair]

contract round_down_monotone (a b : Usize) (align : NonZeroUsize)
  for (do
    let m ← util.round_down_to_next_multiple_of_alignment a align
    let m' ← util.round_down_to_next_multiple_of_alignment b align
    ok (m, m'))
  requires hab : a ≤ b
  requires hpow : (align.val : Nat).isPowerOfTwo
  ensures m m' => m ≤ m'
  proof:
    step with round_down_spec a align hpow as ⟨m, hbound, _, haligned, _, _⟩
    step with round_down_spec b align hpow as ⟨m', _, _, _, _, hgreatest⟩
    apply (UScalar.le_equiv _ _).mpr
    exact hgreatest m.val ((UScalar.le_equiv _ _).mp (le_trans hbound hab)) haligned

end Zerocopy.Corollaries
