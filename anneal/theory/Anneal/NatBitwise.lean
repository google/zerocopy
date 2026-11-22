-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Div.Basic

namespace Anneal.NatBitwise

/-!
# Shared Foundation `Nat.bitwise` Lemmas (`Anneal.NatBitwise`)

Centralizes `Nat.bitwise.eq_def` unfolding and width bounds (`lt_two_pow`) in
one small module so sibling theory modules (`Anneal.BitVec`,
`Anneal.BitVecArith`) can unfold `Nat.bitwise` without emitting duplicate
`Nat.bitwise.eq_def` declarations.
-/

private theorem ite_prop_true {α : Type} {p : Prop} [hdec : Decidable p]
    (h : p) {a b : α} : (if p then a else b) = a := by
  cases hdec with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp h)

private theorem ite_prop_false {α : Type} {p : Prop} [hdec : Decidable p]
    (h : ¬ p) {a b : α} : (if p then a else b) = b := by
  cases hdec with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem ite_bool_true {α : Type} {a b : α} :
    (if true = true then a else b) = a :=
  rfl

private theorem ite_bool_false {α : Type} {a b : α} :
    (if false = true then a else b) = b :=
  rfl

/-- One-step unfolding equation for `Nat.bitwise`. -/
theorem unfold_eq (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m =
      if n = 0 then
        if f false true then m else 0
      else if m = 0 then
        if f true false then n else 0
      else
        let r := Nat.bitwise f (Nat.div n 2) (Nat.div m 2)
        if f (decide (Nat.mod n 2 = 1)) (decide (Nat.mod m 2 = 1)) then
          r + r + 1
        else
          r + r :=
  Nat.bitwise.eq_def f n m

/-- Any bitwise combination of two `w`-bit naturals stays below `2 ^ w`. -/
theorem lt_two_pow (f : Bool → Bool → Bool) (w : Nat) :
    ∀ n m : Nat, n < Nat.pow 2 w → m < Nat.pow 2 w →
      Nat.bitwise f n m < Nat.pow 2 w := by
  induction w with
  | zero =>
    intro n m hn hm
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hm)
    subst hn0
    subst hm0
    rw [unfold_eq, ite_prop_true rfl]
    cases f false true <;> exact Nat.zero_lt_one
  | succ w ih =>
    intro n m hn hm
    rw [unfold_eq]
    cases n with
    | zero =>
      rw [ite_prop_true rfl]
      cases f false true with
      | false =>
        rw [ite_bool_false]
        exact Nat.two_pow_pos (w + 1)
      | true =>
        rw [ite_bool_true]
        exact hm
    | succ n' =>
      rw [ite_prop_false (fun h => nomatch h)]
      cases m with
      | zero =>
        rw [ite_prop_true rfl]
        cases f true false with
        | false =>
          rw [ite_bool_false]
          exact Nat.two_pow_pos (w + 1)
        | true =>
          rw [ite_bool_true]
          exact hn
      | succ m' =>
        rw [ite_prop_false (fun h => nomatch h)]
        dsimp only
        have hn2 : Nat.div (Nat.succ n') 2 < Nat.pow 2 w :=
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr hn
        have hm2 : Nat.div (Nat.succ m') 2 < Nat.pow 2 w :=
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr hm
        have hr : Nat.bitwise f (Nat.div (Nat.succ n') 2)
            (Nat.div (Nat.succ m') 2) < Nat.pow 2 w :=
          ih _ _ hn2 hm2
        have hpow_split : Nat.pow 2 (w + 1) = Nat.pow 2 w + Nat.pow 2 w := by
          change Nat.pow 2 w * 2 = Nat.pow 2 w + Nat.pow 2 w
          exact Nat.mul_two (Nat.pow 2 w)
        cases f (decide (Nat.mod (Nat.succ n') 2 = 1))
            (decide (Nat.mod (Nat.succ m') 2 = 1)) with
        | false =>
          rw [ite_bool_false, hpow_split]
          exact Nat.add_lt_add hr hr
        | true =>
          rw [ite_bool_true, hpow_split, Nat.add_assoc]
          exact Nat.lt_of_le_of_lt
            (Nat.add_le_add_left hr _)
            (Nat.add_lt_add_right hr (Nat.pow 2 w))

end Anneal.NatBitwise
