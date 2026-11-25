-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Fin.Basic
public import Anneal.NatBitwise

public section

namespace Anneal.BitVec

/-!
# Reusable 3-Axiom BitVector Proof Library (`Anneal.BitVec`)

Kernel-checked, width-parametric bit-vector algebra built strictly on Anneal's
51-module `foundation-lock.json` foundation (no `bv_decide`, no `omega`, no
`Std.*`, and no `Init.Data.BitVec.Lemmas`).

Every core operation in `Anneal.BitVec` (`allOnes`, `getLsbD`, `and`, `or`,
`xor`, `not`, `shl`, `ushr`, `setWidth`, `mul`, `udiv`) is definitionally equal
(`rfl`) to its counterpart in `Init.Data.BitVec.Basic`, so downstream target
proofs that import `Init.Data.BitVec.Basic` can apply these lemmas directly to
standard `&&&`, `|||`, `^^^`, `~~~`, `<<<`, `>>>`, `0#w`, `*`, and `/` goals
without casts or competing typeclass instances.

1. **Bitwise & `testBit`/`getLsbD` Extensionality Core:** arbitrary-width
   bit-extensionality, bit characterizations, and Boolean-algebra identities.
2. **Disjoint Bitfield Packing & Injectivity:** `disjoint_or_injective`,
   `lowMask`, and `aligned_or_bounded_injective`.
3. **Masked-Bit / Tnum Relational Algebra:** `MaskEq` equivalence, monotonicity,
   canonicalization, exact bitwise/shift transfer soundness, and bounds.
4. **Unsigned Interval / Range Arithmetic Soundness:** overflow-free `+`, `-`,
   `*`, and nonzero-divisor unsigned division (`udiv`) interval soundness.
5. **Common-Prefix Range-to-Tnum Tightening & `clz`:** leading-zero count
   `clz`, bounds, zero characterization, and range-to-tnum prefix tightening.
-/

/-! ## Part 0: Foundation-Only `Nat` Arithmetic and Bitwise Lemmas -/

private theorem nat_pow_zero (a : Nat) : Nat.pow a 0 = 1 := rfl

private theorem nat_pow_succ (a n : Nat) :
    Nat.pow a (n + 1) = Nat.pow a n * a :=
  Nat.pow_succ a n

theorem nat_two_pow_pos (n : Nat) : 0 < Nat.pow 2 n :=
  Nat.two_pow_pos n

private theorem nat_pow_add (a m n : Nat) :
    Nat.pow a (m + n) = Nat.pow a m * Nat.pow a n := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nat_pow_zero, Nat.mul_one]
  | succ n ih =>
    rw [Nat.add_succ, nat_pow_succ, nat_pow_succ, ih, Nat.mul_assoc]

theorem nat_pow_le_pow_right {i j : Nat} (h : i ≤ j) :
    Nat.pow 2 i ≤ Nat.pow 2 j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

private theorem nat_div_add_mod (m n : Nat) :
    n * Nat.div m n + Nat.mod m n = m :=
  Nat.div_add_mod m n

private theorem nat_div_zero (n : Nat) : Nat.div n 0 = 0 :=
  Nat.div_zero n

private theorem nat_zero_div (n : Nat) : Nat.div 0 n = 0 :=
  Nat.zero_div n

private theorem nat_div_one (n : Nat) : Nat.div n 1 = n :=
  Nat.div_one n

private theorem nat_zero_mod (n : Nat) : Nat.mod 0 n = 0 :=
  Nat.zero_mod n

private theorem nat_mod_lt (a : Nat) {b : Nat} (hb : 0 < b) :
    Nat.mod a b < b :=
  Nat.mod_lt a hb

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

theorem nat_div_le_self (a b : Nat) : Nat.div a b ≤ a :=
  Nat.div_le_self a b

private theorem nat_div_div_eq_div_mul (m n k : Nat) :
    Nat.div (Nat.div m n) k = Nat.div m (n * k) :=
  Nat.div_div_eq_div_mul m n k

private theorem nat_div_mul_le_self (m n : Nat) :
    Nat.div m n * n ≤ m :=
  Nat.div_mul_le_self m n

private theorem nat_le_div_iff_mul_le {x y k : Nat} (hk : 0 < k) :
    x ≤ Nat.div y k ↔ x * k ≤ y :=
  Nat.le_div_iff_mul_le hk

private theorem nat_div_lt_iff_lt_mul {x y k : Nat} (hk : 0 < k) :
    Nat.div x k < y ↔ x < y * k :=
  Nat.div_lt_iff_lt_mul hk

private theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

private theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_mul_add_mod_self_left (a b c : Nat) :
    Nat.mod (a * b + c) a = Nat.mod c a :=
  Nat.mul_add_mod_self_left a b c

private theorem nat_add_mod_left (x z : Nat) :
    Nat.mod (x + z) x = Nat.mod z x :=
  Nat.add_mod_left x z

private theorem nat_mul_mod_right (m n : Nat) :
    Nat.mod (m * n) m = 0 :=
  Nat.mul_mod_right m n

private theorem nat_mul_div_right (n : Nat) {m : Nat} (hm : 0 < m) :
    Nat.div (m * n) m = n :=
  Nat.mul_div_right n hm

private theorem nat_mul_div_left (m : Nat) {n : Nat} (hn : 0 < n) :
    Nat.div (m * n) n = m :=
  Nat.mul_div_left m hn

private theorem nat_mul_div_mul_right (n k : Nat) {m : Nat} (hm : 0 < m) :
    Nat.div (n * m) (k * m) = Nat.div n k :=
  Nat.mul_div_mul_right n k hm

private theorem nat_div_le_div_right {a b : Nat} (h : a ≤ b) (c : Nat) :
    Nat.div a c ≤ Nat.div b c := by
  cases c with
  | zero =>
    rw [nat_div_zero, nat_div_zero]
    exact Nat.le_refl 0
  | succ c =>
    have hc : 0 < Nat.succ c := Nat.zero_lt_succ c
    exact (nat_le_div_iff_mul_le hc).2
      (Nat.le_trans (nat_div_mul_le_self a (Nat.succ c)) h)

private theorem nat_div_le_div_left {a b c : Nat} (h : b ≤ c) (hb : 0 < b) :
    Nat.div a c ≤ Nat.div a b := by
  exact (nat_le_div_iff_mul_le hb).2
    (Nat.le_trans (Nat.mul_le_mul_left (Nat.div a c) h)
      (nat_div_mul_le_self a c))

private theorem nat_mod_two_cases (n : Nat) :
    Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hlt : Nat.mod n 2 < 2 := nat_mod_lt n (by decide)
  cases hm : Nat.mod n 2 with
  | zero => left; rfl
  | succ k =>
    cases k with
    | zero => right; rfl
    | succ k' =>
      rw [hm] at hlt
      exact False.elim (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k'))) hlt)

private theorem ite_prop_true {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : P) : (@ite α P inst t e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem ite_prop_false {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : ¬ P) : (@ite α P inst t e) = e := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem ite_bool_true {α : Type} {t e : α} :
    (if true = true then t else e) = t := rfl

private theorem ite_bool_false {α : Type} {t e : α} :
    (if false = true then t else e) = e := rfl

private theorem dite_prop_true {α : Type} {P : Prop} {inst : Decidable P}
    {t : P → α} {e : ¬ P → α} (h : P) : (@dite α P inst t e) = t h := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem dite_prop_false {α : Type} {P : Prop} {inst : Decidable P}
    {t : P → α} {e : ¬ P → α} (h : ¬ P) : (@dite α P inst t e) = e h := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem nat_sub_le_sub {a b c d : Nat} (h1 : a ≤ b) (h2 : d ≤ c) :
    a - c ≤ b - d :=
  Nat.le_trans (Nat.sub_le_sub_right h1 c) (Nat.sub_le_sub_left h2 b)

private theorem nat_shiftRight_eq_div_pow (m k : Nat) :
    Nat.shiftRight m k = Nat.div m (Nat.pow 2 k) :=
  Nat.shiftRight_eq_div_pow m k

private theorem nat_two_mul_add_one_div_two (r : Nat) :
    Nat.div (r + r + 1) 2 = r := by
  have h2 : r + r = 2 * r := by
    rw [Nat.succ_mul 1 r, Nat.one_mul]
  have h12 : Nat.div 1 2 = 0 := by decide
  rw [h2, Nat.add_comm (2 * r) 1, nat_add_mul_div_left 1 r (by decide),
    h12, Nat.zero_add]

private theorem nat_two_mul_div_two (r : Nat) :
    Nat.div (r + r) 2 = r := by
  have h2 : r + r = 2 * r := by
    rw [Nat.succ_mul 1 r, Nat.one_mul]
  rw [h2]
  exact nat_mul_div_right r (by decide)

private theorem nat_two_mul_add_one_mod_two (r : Nat) :
    Nat.mod (r + r + 1) 2 = 1 := by
  have h2 : r + r = 2 * r := by
    rw [Nat.succ_mul 1 r, Nat.one_mul]
  rw [h2, nat_mul_add_mod_self_left]

private theorem nat_two_mul_mod_two (r : Nat) :
    Nat.mod (r + r) 2 = 0 := by
  have h2 : r + r = 2 * r := by
    rw [Nat.succ_mul 1 r, Nat.one_mul]
  rw [h2]
  exact nat_mul_mod_right 2 r

private theorem nat_eq_of_div_mod_eq {a b d : Nat}
    (hd : Nat.div a d = Nat.div b d) (hm : Nat.mod a d = Nat.mod b d) :
    a = b := by
  rw [← nat_div_add_mod a d, ← nat_div_add_mod b d, hd, hm]

private theorem nat_bitwise_unfold (f : Bool → Bool → Bool) (n m : Nat) :
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
  Anneal.NatBitwise.unfold_eq f n m

private theorem nat_land_one_eq (k : Nat) :
    Nat.land 1 k = if decide (Nat.mod k 2 = 1) then 1 else 0 := by
  rw [Anneal.NatBitwise.land_eq_bitwise, nat_bitwise_unfold]
  cases k with
  | zero => rfl
  | succ k' =>
    have hdiv1 : Nat.div 1 2 = 0 := by decide
    have hmod1 : decide (Nat.mod 1 2 = 1) = true := by decide
    have hbw0 : Nat.bitwise and 0 (Nat.div (Nat.succ k') 2) = 0 := by
      rw [nat_bitwise_unfold]
      rfl
    rw [ite_prop_false (by decide : ¬ (1 = 0)),
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [hdiv1, hbw0, hmod1]
    cases decide (Nat.mod (Nat.succ k') 2 = 1) <;> rfl

private theorem nat_testBit_eq (m i : Nat) :
    m.testBit i = decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) := by
  unfold Nat.testBit
  have hsr : Nat.shiftRight m i = Nat.div m (Nat.pow 2 i) :=
    Nat.shiftRight_eq_div_pow m i
  change (Nat.land 1 (Nat.shiftRight m i) != 0) = _
  rw [hsr, nat_land_one_eq]
  cases decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) <;> rfl

private theorem nat_testBit_zero_bit (m : Nat) :
    m.testBit 0 = decide (Nat.mod m 2 = 1) := by
  rw [nat_testBit_eq, nat_pow_zero, nat_div_one]

private theorem nat_testBit_succ (m i : Nat) :
    m.testBit (i + 1) = (Nat.div m 2).testBit i := by
  rw [nat_testBit_eq, nat_testBit_eq, nat_div_div_eq_div_mul,
    Nat.mul_comm 2 (Nat.pow 2 i), ← nat_pow_succ]

private theorem nat_testBit_zero (i : Nat) :
    (0 : Nat).testBit i = false := by
  rw [nat_testBit_eq, nat_zero_div, nat_zero_mod]
  rfl

private theorem nat_testBit_eq_false_of_lt {m i : Nat} (h : m < Nat.pow 2 i) :
    m.testBit i = false := by
  rw [nat_testBit_eq, nat_div_eq_of_lt h, nat_zero_mod]
  rfl

private theorem nat_testBit_two_pow_sub_one (k : Nat) :
    ∀ i : Nat, (Nat.pow 2 k - 1).testBit i = decide (i < k) := by
  induction k with
  | zero =>
    intro i
    change (0 : Nat).testBit i = decide (i < 0)
    rw [nat_testBit_zero]
    exact Eq.symm (decide_eq_false (Nat.not_lt_zero i))
  | succ k ih =>
    intro i
    have hpos : 0 < Nat.pow 2 k := nat_two_pow_pos k
    have hsplit : Nat.pow 2 (k + 1) - 1 =
        (Nat.pow 2 k - 1) + (Nat.pow 2 k - 1) + 1 := by
      rw [nat_pow_succ, Nat.mul_succ, Nat.mul_one]
      have hsub : Nat.pow 2 k = (Nat.pow 2 k - 1) + 1 :=
        Eq.symm (Nat.sub_add_cancel hpos)
      have hsum : Nat.pow 2 k + Nat.pow 2 k =
          ((Nat.pow 2 k - 1) + (Nat.pow 2 k - 1) + 1) + 1 := by
        have h1 :
            ((Nat.pow 2 k - 1) + 1) + ((Nat.pow 2 k - 1) + 1) =
            ((Nat.pow 2 k - 1) + (Nat.pow 2 k - 1) + 1) + 1 := by
          rw [Nat.add_assoc (Nat.pow 2 k - 1) 1,
            Nat.add_comm 1 ((Nat.pow 2 k - 1) + 1),
            ← Nat.add_assoc (Nat.pow 2 k - 1),
            ← Nat.add_assoc (Nat.pow 2 k - 1)]
        rw [← hsub] at h1
        exact h1
      rw [hsum, Nat.add_sub_cancel]
    cases i with
    | zero =>
      rw [nat_testBit_zero_bit, hsplit, nat_two_mul_add_one_mod_two]
      exact Eq.symm (decide_eq_true (Nat.zero_lt_succ k))
    | succ i =>
      rw [nat_testBit_succ, hsplit, nat_two_mul_add_one_div_two, ih i]
      cases Nat.lt_or_ge i k with
      | inl hlt =>
        rw [decide_eq_true hlt, decide_eq_true (Nat.succ_lt_succ hlt)]
      | inr hge =>
        rw [decide_eq_false (Nat.not_lt_of_ge hge),
          decide_eq_false (Nat.not_lt_of_ge (Nat.succ_le_succ hge))]

private theorem nat_testBit_mod_two_pow (m k i : Nat) :
    (Nat.mod m (Nat.pow 2 k)).testBit i = (decide (i < k) && m.testBit i) := by
  cases Nat.lt_or_ge i k with
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
    exact nat_testBit_eq_false_of_lt
      (Nat.lt_of_lt_of_le (nat_mod_lt m (nat_two_pow_pos k))
        (nat_pow_le_pow_right hge))
  | inl hlt =>
    rw [decide_eq_true hlt, Bool.true_and, nat_testBit_eq, nat_testBit_eq]
    have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hki_pos : 0 < k - i := Nat.zero_lt_sub_of_lt hlt
    have hki_eq : k - i = (k - i - 1) + 1 :=
      Eq.symm (Nat.sub_add_cancel hki_pos)
    have hpow_k : Nat.pow 2 k = Nat.pow 2 i * Nat.pow 2 (k - i) := by
      have h1 := congrArg (Nat.pow 2) hk
      rw [nat_pow_add] at h1
      exact h1
    have hdecomp : m = Nat.mod m (Nat.pow 2 k) +
        Nat.pow 2 i * (Nat.pow 2 (k - i) * Nat.div m (Nat.pow 2 k)) := by
      have h1 := nat_div_add_mod m (Nat.pow 2 k)
      have h2 : Nat.pow 2 k * Nat.div m (Nat.pow 2 k) =
          Nat.pow 2 i * (Nat.pow 2 (k - i) * Nat.div m (Nat.pow 2 k)) := by
        rw [hpow_k, Nat.mul_assoc]
      rw [h2, Nat.add_comm] at h1
      exact Eq.symm h1
    have hdiv : Nat.div m (Nat.pow 2 i) =
        Nat.div (Nat.mod m (Nat.pow 2 k)) (Nat.pow 2 i) +
        Nat.pow 2 (k - i) * Nat.div m (Nat.pow 2 k) := by
      have h1 := congrArg (fun z => Nat.div z (Nat.pow 2 i)) hdecomp
      rw [nat_add_mul_div_left _ _ (nat_two_pow_pos i)] at h1
      exact h1
    have hpow_even : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
      have h1 := congrArg (Nat.pow 2) hki_eq
      rw [nat_pow_succ, Nat.mul_comm] at h1
      exact h1
    rw [hdiv, hpow_even, Nat.mul_assoc, nat_add_mul_mod_self_left]

private theorem nat_testBit_shiftLeft (m k i : Nat) :
    (Nat.shiftLeft m k).testBit i = (decide (k ≤ i) && m.testBit (i - k)) := by
  have hsl : Nat.shiftLeft m k = m * Nat.pow 2 k := Nat.shiftLeft_eq m k
  rw [hsl]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, nat_testBit_eq]
    have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hki_pos : 0 < k - i := Nat.zero_lt_sub_of_lt hlt
    have hki_eq : k - i = (k - i - 1) + 1 :=
      Eq.symm (Nat.sub_add_cancel hki_pos)
    have hpow_k : Nat.pow 2 k = Nat.pow 2 (k - i) * Nat.pow 2 i := by
      have h1 := congrArg (Nat.pow 2) hk
      rw [nat_pow_add, Nat.mul_comm] at h1
      exact h1
    have hpow_even : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
      have h1 := congrArg (Nat.pow 2) hki_eq
      rw [nat_pow_succ, Nat.mul_comm] at h1
      exact h1
    rw [hpow_k, ← Nat.mul_assoc,
      nat_mul_div_left _ (nat_two_pow_pos i), hpow_even,
      Nat.mul_left_comm, nat_mul_mod_right]
    rfl
  | inr hge =>
    rw [decide_eq_true hge, Bool.true_and, nat_testBit_eq, nat_testBit_eq]
    have hi : i = (i - k) + k := Eq.symm (Nat.sub_add_cancel hge)
    have hpow_i : Nat.pow 2 i = Nat.pow 2 (i - k) * Nat.pow 2 k := by
      have h1 := congrArg (Nat.pow 2) hi
      rw [nat_pow_add] at h1
      exact h1
    rw [hpow_i, nat_mul_div_mul_right m (Nat.pow 2 (i - k)) (nat_two_pow_pos k)]

private theorem nat_testBit_shiftRight (m k i : Nat) :
    (Nat.shiftRight m k).testBit i = m.testBit (i + k) := by
  have hsr : Nat.shiftRight m k = Nat.div m (Nat.pow 2 k) :=
    Nat.shiftRight_eq_div_pow m k
  rw [hsr, nat_testBit_eq, nat_testBit_eq, nat_div_div_eq_div_mul,
    Nat.mul_comm (Nat.pow 2 k) (Nat.pow 2 i), ← nat_pow_add]

private theorem nat_testBit_bitwise {f : Bool → Bool → Bool}
    (hf : f false false = false) (i : Nat) :
    ∀ n m : Nat, (Nat.bitwise f n m).testBit i = f (n.testBit i) (m.testBit i) := by
  induction i with
  | zero =>
    intro n m
    rw [nat_bitwise_unfold]
    cases n with
    | zero =>
      rw [ite_prop_true rfl, nat_testBit_zero]
      cases hft : f false true with
      | false =>
        rw [ite_bool_false, nat_testBit_zero]
        cases m.testBit 0
        · exact Eq.symm hf
        · exact Eq.symm hft
      | true =>
        rw [ite_bool_true]
        cases m.testBit 0
        · exact Eq.symm hf
        · exact Eq.symm hft
    | succ n' =>
      rw [ite_prop_false (fun h => nomatch h)]
      cases m with
      | zero =>
        rw [ite_prop_true rfl, nat_testBit_zero]
        cases htf : f true false with
        | false =>
          rw [ite_bool_false, nat_testBit_zero]
          cases (Nat.succ n').testBit 0
          · exact Eq.symm hf
          · exact Eq.symm htf
        | true =>
          rw [ite_bool_true]
          cases (Nat.succ n').testBit 0
          · exact Eq.symm hf
          · exact Eq.symm htf
      | succ m' =>
        rw [ite_prop_false (fun h => nomatch h)]
        dsimp only
        rw [nat_testBit_zero_bit (Nat.succ n'),
          nat_testBit_zero_bit (Nat.succ m')]
        cases f (decide (Nat.mod (Nat.succ n') 2 = 1))
            (decide (Nat.mod (Nat.succ m') 2 = 1)) with
        | false =>
          rw [ite_bool_false, nat_testBit_zero_bit, nat_two_mul_mod_two]
          rfl
        | true =>
          rw [ite_bool_true, nat_testBit_zero_bit, nat_two_mul_add_one_mod_two]
          rfl
  | succ i ih =>
    intro n m
    rw [nat_bitwise_unfold]
    cases n with
    | zero =>
      rw [ite_prop_true rfl, nat_testBit_zero]
      cases hft : f false true with
      | false =>
        rw [ite_bool_false, nat_testBit_zero]
        cases m.testBit (i + 1)
        · exact Eq.symm hf
        · exact Eq.symm hft
      | true =>
        rw [ite_bool_true]
        cases m.testBit (i + 1)
        · exact Eq.symm hf
        · exact Eq.symm hft
    | succ n' =>
      rw [ite_prop_false (fun h => nomatch h)]
      cases m with
      | zero =>
        rw [ite_prop_true rfl, nat_testBit_zero]
        cases htf : f true false with
        | false =>
          rw [ite_bool_false, nat_testBit_zero]
          cases (Nat.succ n').testBit (i + 1)
          · exact Eq.symm hf
          · exact Eq.symm htf
        | true =>
          rw [ite_bool_true]
          cases (Nat.succ n').testBit (i + 1)
          · exact Eq.symm hf
          · exact Eq.symm htf
      | succ m' =>
        rw [ite_prop_false (fun h => nomatch h)]
        dsimp only
        rw [nat_testBit_succ (Nat.succ n') i, nat_testBit_succ (Nat.succ m') i]
        cases f (decide (Nat.mod (Nat.succ n') 2 = 1))
            (decide (Nat.mod (Nat.succ m') 2 = 1)) with
        | false =>
          rw [ite_bool_false, nat_testBit_succ, nat_two_mul_div_two]
          exact ih (Nat.div (Nat.succ n') 2) (Nat.div (Nat.succ m') 2)
        | true =>
          rw [ite_bool_true, nat_testBit_succ, nat_two_mul_add_one_div_two]
          exact ih (Nat.div (Nat.succ n') 2) (Nat.div (Nat.succ m') 2)

private theorem nat_bitwise_lt_two_pow {f : Bool → Bool → Bool} (w : Nat) :
    ∀ n m : Nat, n < Nat.pow 2 w → m < Nat.pow 2 w →
      Nat.bitwise f n m < Nat.pow 2 w :=
  Anneal.NatBitwise.lt_two_pow f w

theorem nat_land_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.land n m < Nat.pow 2 w :=
  Anneal.NatBitwise.land_lt_two_pow hn hm

theorem nat_lor_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.lor n m < Nat.pow 2 w :=
  Anneal.NatBitwise.lor_lt_two_pow hn hm

theorem nat_xor_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.xor n m < Nat.pow 2 w :=
  Anneal.NatBitwise.xor_lt_two_pow hn hm

private theorem nat_eq_of_testBit_eq_below (w : Nat) :
    ∀ a b : Nat, a < Nat.pow 2 w → b < Nat.pow 2 w →
      (∀ i, i < w → a.testBit i = b.testBit i) → a = b := by
  induction w with
  | zero =>
    intro a b ha hb _
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    rw [ha0, hb0]
  | succ w ih =>
    intro a b ha hb hbits
    have ha2 : Nat.div a 2 < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), ← nat_pow_succ]
      exact ha
    have hb2 : Nat.div b 2 < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), ← nat_pow_succ]
      exact hb
    have hdiv : Nat.div a 2 = Nat.div b 2 := by
      apply ih (Nat.div a 2) (Nat.div b 2) ha2 hb2
      intro i hi
      rw [← nat_testBit_succ a i, ← nat_testBit_succ b i]
      exact hbits (i + 1) (Nat.succ_lt_succ hi)
    have h0 : decide (Nat.mod a 2 = 1) = decide (Nat.mod b 2 = 1) := by
      rw [← nat_testBit_zero_bit a, ← nat_testBit_zero_bit b]
      exact hbits 0 (Nat.zero_lt_succ w)
    have hmod : Nat.mod a 2 = Nat.mod b 2 := by
      cases nat_mod_two_cases a with
      | inl ha0 =>
        cases nat_mod_two_cases b with
        | inl hb0 => rw [ha0, hb0]
        | inr hb1 =>
          rw [ha0, hb1] at h0
          nomatch h0
      | inr ha1 =>
        cases nat_mod_two_cases b with
        | inl hb0 =>
          rw [ha1, hb0] at h0
          nomatch h0
        | inr hb1 => rw [ha1, hb1]
    exact nat_eq_of_div_mod_eq hdiv hmod

private theorem nat_le_of_testBit_imp (w : Nat) :
    ∀ a b : Nat, a < Nat.pow 2 w → b < Nat.pow 2 w →
      (∀ i, i < w → a.testBit i = true → b.testBit i = true) → a ≤ b := by
  induction w with
  | zero =>
    intro a b ha hb _
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    rw [ha0, hb0]
    exact Nat.le_refl 0
  | succ w ih =>
    intro a b ha hb hbits
    have ha2 : Nat.div a 2 < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), ← nat_pow_succ]
      exact ha
    have hb2 : Nat.div b 2 < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), ← nat_pow_succ]
      exact hb
    have hdiv : Nat.div a 2 ≤ Nat.div b 2 := by
      apply ih (Nat.div a 2) (Nat.div b 2) ha2 hb2
      intro i hi hta
      rw [← nat_testBit_succ a i] at hta
      rw [← nat_testBit_succ b i]
      exact hbits (i + 1) (Nat.succ_lt_succ hi) hta
    have hmod : Nat.mod a 2 ≤ Nat.mod b 2 := by
      cases nat_mod_two_cases a with
      | inl ha0 =>
        rw [ha0]
        exact Nat.zero_le _
      | inr ha1 =>
        have hta : a.testBit 0 = true := by
          rw [nat_testBit_zero_bit, ha1]
          rfl
        have htb : b.testBit 0 = true := hbits 0 (Nat.zero_lt_succ w) hta
        rw [nat_testBit_zero_bit] at htb
        cases nat_mod_two_cases b with
        | inl hb0 =>
          rw [hb0] at htb
          nomatch htb
        | inr hb1 =>
          rw [ha1, hb1]
          exact Nat.le_refl 1
    rw [← nat_div_add_mod a 2, ← nat_div_add_mod b 2]
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 hdiv) hmod

/-! ## Part 1: Bitwise Operations, `getLsbD`/`testBit`, and Extensionality -/

/-- All-ones bitvector of width `w`, definitionally equal to `BitVec.allOnes w`.
-/
@[expose] def allOnes (w : Nat) : BitVec w :=
  BitVec.ofNatLT (Nat.pow 2 w - 1)
    (Nat.sub_lt (nat_two_pow_pos w) Nat.one_pos)

/-- Return the `i`-th least significant bit of `x` (or `false` for `i ≥ w`),
definitionally equal to `BitVec.getLsbD x i`. -/
@[expose] def getLsbD {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  x.toNat.testBit i

/-- Bitwise AND of two `w`-bit bitvectors, definitionally equal to `x &&& y`. -/
@[expose] def and {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNatLT (Nat.land x.toNat y.toNat) (nat_land_lt_two_pow x.isLt y.isLt)

/-- Bitwise OR of two `w`-bit bitvectors, definitionally equal to `x ||| y`. -/
@[expose] def or {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNatLT (Nat.lor x.toNat y.toNat) (nat_lor_lt_two_pow x.isLt y.isLt)

/-- Bitwise XOR of two `w`-bit bitvectors, definitionally equal to `x ^^^ y`. -/
@[expose] def xor {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNatLT (Nat.xor x.toNat y.toNat) (nat_xor_lt_two_pow x.isLt y.isLt)

/-- Bitwise complement of a `w`-bit bitvector, definitionally equal to `~~~x`.
-/
@[expose] def not {w : Nat} (x : BitVec w) : BitVec w :=
  xor (allOnes w) x

/-- Logical left shift by `k : Nat`, definitionally equal to `x <<< k`. -/
@[expose] def shl {w : Nat} (x : BitVec w) (k : Nat) : BitVec w :=
  BitVec.ofNat w (Nat.shiftLeft x.toNat k)

/-- Logical right shift by `k : Nat`, definitionally equal to `x >>> k`. -/
@[expose] def ushr {w : Nat} (x : BitVec w) (k : Nat) : BitVec w :=
  BitVec.ofNatLT (Nat.shiftRight x.toNat k)
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le x.toNat k) x.isLt)

/-- Zero-extend or truncate `x : BitVec w` to width `v`, definitionally equal
to `BitVec.setWidth v x`. -/
@[expose] def setWidth {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  if h : w ≤ v then
    BitVec.ofNatLT x.toNat
      (Nat.lt_of_lt_of_le x.isLt (nat_pow_le_pow_right h))
  else
    BitVec.ofNat v x.toNat

/-- Wrapping multiplication of two `w`-bit bitvectors, definitionally equal to
`x * y`. -/
@[expose] def mul {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat)

/-- Unsigned division of two `w`-bit bitvectors (division by zero returns zero),
definitionally equal to `x / y` (`BitVec.udiv`). -/
@[expose] def udiv {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNatLT (Nat.div x.toNat y.toNat)
    (Nat.lt_of_le_of_lt (nat_div_le_self x.toNat y.toNat) x.isLt)

/-- Extensionality of `BitVec w` via `.toNat`. -/
theorem eq_of_toNat_eq {w : Nat} {a b : BitVec w}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

/-- `toNat` characterization of `BitVec.ofNat`. -/
@[simp] theorem toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = Nat.mod n (Nat.pow 2 w) :=
  rfl

/-- `toNat` characterization of `BitVec.ofNatLT`. -/
@[simp] theorem toNat_ofNatLT {w : Nat} (n : Nat) (h : n < Nat.pow 2 w) :
    (BitVec.ofNatLT n h).toNat = n :=
  rfl

/-- `toNat` of the `w`-bit zero vector `0#w`. -/
@[simp] theorem toNat_zero (w : Nat) :
    (BitVec.ofNat w 0).toNat = 0 :=
  nat_zero_mod (Nat.pow 2 w)

/-- `toNat` of `allOnes w`. -/
@[simp] theorem toNat_allOnes (w : Nat) :
    (allOnes w).toNat = Nat.pow 2 w - 1 :=
  rfl

/-- `toNat` of `and a b`. -/
@[simp] theorem toNat_and {w : Nat} (a b : BitVec w) :
    (and a b).toNat = Nat.land a.toNat b.toNat :=
  rfl

/-- `toNat` of `or a b`. -/
@[simp] theorem toNat_or {w : Nat} (a b : BitVec w) :
    (or a b).toNat = Nat.lor a.toNat b.toNat :=
  rfl

/-- `toNat` of `xor a b`. -/
@[simp] theorem toNat_xor {w : Nat} (a b : BitVec w) :
    (xor a b).toNat = Nat.xor a.toNat b.toNat :=
  rfl

/-- `toNat` of `not a`. -/
@[simp] theorem toNat_not {w : Nat} (a : BitVec w) :
    (not a).toNat = Nat.xor (Nat.pow 2 w - 1) a.toNat :=
  rfl

/-- `toNat` of `shl a k`. -/
@[simp] theorem toNat_shl {w : Nat} (a : BitVec w) (k : Nat) :
    (shl a k).toNat = Nat.mod (Nat.shiftLeft a.toNat k) (Nat.pow 2 w) :=
  rfl

/-- `toNat` of `ushr a k`. -/
@[simp] theorem toNat_ushr {w : Nat} (a : BitVec w) (k : Nat) :
    (ushr a k).toNat = Nat.shiftRight a.toNat k :=
  rfl

/-- `toNat` of `setWidth v a`. -/
@[simp] theorem toNat_setWidth {w : Nat} (v : Nat) (a : BitVec w) :
    (setWidth v a).toNat = Nat.mod a.toNat (Nat.pow 2 v) := by
  unfold setWidth
  cases (inferInstance : Decidable (w ≤ v)) with
  | isTrue h =>
    rw [dite_prop_true h]
    exact Eq.symm (nat_mod_eq_of_lt
      (Nat.lt_of_lt_of_le a.isLt (nat_pow_le_pow_right h)))
  | isFalse h =>
    rw [dite_prop_false h]
    rfl

/-- `toNat` of `BitVec` addition `a + b`. -/
@[simp] theorem toNat_add {w : Nat} (a b : BitVec w) :
    (a + b).toNat = Nat.mod (a.toNat + b.toNat) (Nat.pow 2 w) :=
  rfl

/-- `toNat` of `BitVec` subtraction `a - b`. -/
@[simp] theorem toNat_sub {w : Nat} (a b : BitVec w) :
    (a - b).toNat =
      Nat.mod ((Nat.pow 2 w - b.toNat) + a.toNat) (Nat.pow 2 w) :=
  rfl

/-- Exact `toNat` of non-underflowing subtraction `a - b` when `b ≤ a`. -/
theorem toNat_sub_of_le {w : Nat} {a b : BitVec w} (h : b ≤ a) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [toNat_sub]
  have hle : b.toNat ≤ a.toNat := h
  have hsplit : (Nat.pow 2 w - b.toNat) + a.toNat =
      Nat.pow 2 w + (a.toNat - b.toNat) := by
    have ha : a.toNat = b.toNat + (a.toNat - b.toNat) :=
      Eq.symm (Nat.add_sub_of_le hle)
    have hsub : Nat.pow 2 w - b.toNat + b.toNat = Nat.pow 2 w :=
      Nat.sub_add_cancel (Nat.le_of_lt b.isLt)
    have h1 := congrArg (fun z => (Nat.pow 2 w - b.toNat) + z) ha
    rw [← Nat.add_assoc, hsub] at h1
    exact h1
  rw [hsplit, nat_add_mod_left]
  exact nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le a.toNat b.toNat) a.isLt)

/-- `toNat` of `mul a b`. -/
@[simp] theorem toNat_mul {w : Nat} (a b : BitVec w) :
    (mul a b).toNat = Nat.mod (a.toNat * b.toNat) (Nat.pow 2 w) :=
  rfl

/-- `toNat` of `udiv a b`. -/
@[simp] theorem toNat_udiv {w : Nat} (a b : BitVec w) :
    (udiv a b).toNat = Nat.div a.toNat b.toNat :=
  rfl

/-- Bitwise extensionality for `BitVec w` via `Nat.testBit`. -/
theorem eq_of_testBit_eq {w : Nat} {a b : BitVec w}
    (h : ∀ i, i < w → a.toNat.testBit i = b.toNat.testBit i) : a = b :=
  eq_of_toNat_eq (nat_eq_of_testBit_eq_below w a.toNat b.toNat a.isLt b.isLt h)

/-- Bitwise extensionality for `BitVec w` via `getLsbD`. -/
theorem eq_of_getLsbD_eq {w : Nat} {a b : BitVec w}
    (h : ∀ i, i < w → getLsbD a i = getLsbD b i) : a = b :=
  eq_of_testBit_eq h

/-- Any bit index `i ≥ w` of a `w`-bit bitvector is `false`. -/
theorem getLsbD_ge {w : Nat} (a : BitVec w) {i : Nat} (hi : w ≤ i) :
    getLsbD a i = false :=
  nat_testBit_eq_false_of_lt
    (Nat.lt_of_lt_of_le a.isLt (nat_pow_le_pow_right hi))

/-- `getLsbD` of `BitVec.ofNat w n`. -/
@[simp] theorem getLsbD_ofNat (w n i : Nat) :
    getLsbD (BitVec.ofNat w n) i = (decide (i < w) && n.testBit i) :=
  nat_testBit_mod_two_pow n w i

/-- `getLsbD` of `0#w`. -/
@[simp] theorem getLsbD_zero (w i : Nat) :
    getLsbD (BitVec.ofNat w 0) i = false := by
  unfold getLsbD
  rw [toNat_zero, nat_testBit_zero]

/-- `getLsbD` of `allOnes w`. -/
@[simp] theorem getLsbD_allOnes (w i : Nat) :
    getLsbD (allOnes w) i = decide (i < w) :=
  nat_testBit_two_pow_sub_one w i

/-- `getLsbD` of `and a b`. -/
@[simp] theorem getLsbD_and {w : Nat} (a b : BitVec w) (i : Nat) :
    getLsbD (and a b) i = (getLsbD a i && getLsbD b i) := by
  change (Nat.land a.toNat b.toNat).testBit i = (a.toNat.testBit i && b.toNat.testBit i)
  rw [Anneal.NatBitwise.land_eq_bitwise]
  exact nat_testBit_bitwise (f := Bool.and) rfl i a.toNat b.toNat

/-- `getLsbD` of `or a b`. -/
@[simp] theorem getLsbD_or {w : Nat} (a b : BitVec w) (i : Nat) :
    getLsbD (or a b) i = (getLsbD a i || getLsbD b i) := by
  change (Nat.lor a.toNat b.toNat).testBit i = (a.toNat.testBit i || b.toNat.testBit i)
  rw [Anneal.NatBitwise.lor_eq_bitwise]
  exact nat_testBit_bitwise (f := Bool.or) rfl i a.toNat b.toNat

/-- `getLsbD` of `xor a b`. -/
@[simp] theorem getLsbD_xor {w : Nat} (a b : BitVec w) (i : Nat) :
    getLsbD (xor a b) i = (getLsbD a i != getLsbD b i) := by
  change (Nat.xor a.toNat b.toNat).testBit i = (a.toNat.testBit i != b.toNat.testBit i)
  rw [Anneal.NatBitwise.xor_eq_bitwise]
  exact nat_testBit_bitwise (f := bne) rfl i a.toNat b.toNat

/-- `getLsbD` of `not a`. -/
@[simp] theorem getLsbD_not {w : Nat} (a : BitVec w) (i : Nat) :
    getLsbD (not a) i = (decide (i < w) && !getLsbD a i) := by
  unfold not
  rw [getLsbD_xor, getLsbD_allOnes]
  cases Nat.lt_or_ge i w with
  | inl hlt =>
    rw [decide_eq_true hlt]
    cases getLsbD a i <;> rfl
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), getLsbD_ge a hge]
    rfl

/-- `getLsbD` of `not a` at an in-bounds index `i < w`. -/
theorem getLsbD_not_of_lt {w : Nat} (a : BitVec w) {i : Nat} (hi : i < w) :
    getLsbD (not a) i = !getLsbD a i := by
  rw [getLsbD_not, decide_eq_true hi, Bool.true_and]

/-- `getLsbD` of `shl a k`. -/
@[simp] theorem getLsbD_shl {w : Nat} (a : BitVec w) (k i : Nat) :
    getLsbD (shl a k) i =
      (decide (i < w) && (decide (k ≤ i) && getLsbD a (i - k))) := by
  unfold shl
  rw [getLsbD_ofNat, nat_testBit_shiftLeft]
  rfl

/-- `getLsbD` of `ushr a k`. -/
@[simp] theorem getLsbD_ushr {w : Nat} (a : BitVec w) (k i : Nat) :
    getLsbD (ushr a k) i = getLsbD a (i + k) :=
  nat_testBit_shiftRight a.toNat k i

/-- `getLsbD` of `setWidth v a`. -/
@[simp] theorem getLsbD_setWidth {w : Nat} (v : Nat) (a : BitVec w) (i : Nat) :
    getLsbD (setWidth v a) i = (decide (i < v) && getLsbD a i) := by
  unfold getLsbD
  rw [toNat_setWidth]
  exact nat_testBit_mod_two_pow a.toNat v i

/-- `testBit` characterization of `0#w`. -/
theorem testBit_zero (w i : Nat) :
    (BitVec.ofNat w 0).toNat.testBit i = false :=
  getLsbD_zero w i

/-- `testBit` characterization of `allOnes w`. -/
theorem testBit_allOnes (w i : Nat) :
    (allOnes w).toNat.testBit i = decide (i < w) :=
  getLsbD_allOnes w i

/-- `testBit` characterization of `and a b`. -/
theorem testBit_and {w : Nat} (a b : BitVec w) (i : Nat) :
    (and a b).toNat.testBit i = (a.toNat.testBit i && b.toNat.testBit i) :=
  getLsbD_and a b i

/-- `testBit` characterization of `or a b`. -/
theorem testBit_or {w : Nat} (a b : BitVec w) (i : Nat) :
    (or a b).toNat.testBit i = (a.toNat.testBit i || b.toNat.testBit i) :=
  getLsbD_or a b i

/-- `testBit` characterization of `xor a b`. -/
theorem testBit_xor {w : Nat} (a b : BitVec w) (i : Nat) :
    (xor a b).toNat.testBit i = (a.toNat.testBit i != b.toNat.testBit i) :=
  getLsbD_xor a b i

/-- `testBit` characterization of `not a`. -/
theorem testBit_not {w : Nat} (a : BitVec w) (i : Nat) :
    (not a).toNat.testBit i = (decide (i < w) && !a.toNat.testBit i) :=
  getLsbD_not a i

/-- `testBit` characterization of `shl a k`. -/
theorem testBit_shl {w : Nat} (a : BitVec w) (k i : Nat) :
    (shl a k).toNat.testBit i =
      (decide (i < w) && (decide (k ≤ i) && a.toNat.testBit (i - k))) :=
  getLsbD_shl a k i

/-- `testBit` characterization of `ushr a k`. -/
theorem testBit_ushr {w : Nat} (a : BitVec w) (k i : Nat) :
    (ushr a k).toNat.testBit i = a.toNat.testBit (i + k) :=
  getLsbD_ushr a k i

/-- `testBit` characterization of `setWidth v a`. -/
theorem testBit_setWidth {w : Nat} (v : Nat) (a : BitVec w) (i : Nat) :
    (setWidth v a).toNat.testBit i = (decide (i < v) && a.toNat.testBit i) :=
  getLsbD_setWidth v a i

/-! ### Core Bitwise Boolean-Algebra Identities -/

/-- Complement of `0#w` is `allOnes w`. -/
@[simp] theorem not_zero_eq_allOnes (w : Nat) :
    not (BitVec.ofNat w 0) = allOnes w := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_not_of_lt _ hi, getLsbD_zero, getLsbD_allOnes, decide_eq_true hi]
  rfl

/-- Complement of `allOnes w` is `0#w`. -/
@[simp] theorem not_allOnes_eq_zero (w : Nat) :
    not (allOnes w) = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_not_of_lt _ hi, getLsbD_allOnes, decide_eq_true hi, getLsbD_zero]
  rfl

/-- Right identity of bitwise AND (`a &&& allOnes w = a`). -/
@[simp] theorem and_allOnes {w : Nat} (a : BitVec w) :
    and a (allOnes w) = a := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_allOnes, decide_eq_true hi, Bool.and_true]

/-- Left identity of bitwise AND (`allOnes w &&& a = a`). -/
@[simp] theorem allOnes_and {w : Nat} (a : BitVec w) :
    and (allOnes w) a = a := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_allOnes, decide_eq_true hi, Bool.true_and]

/-- Right absorbing element of bitwise AND (`a &&& 0#w = 0#w`). -/
@[simp] theorem and_zero {w : Nat} (a : BitVec w) :
    and a (BitVec.ofNat w 0) = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and, getLsbD_zero, Bool.and_false]

/-- Left absorbing element of bitwise AND (`0#w &&& a = 0#w`). -/
@[simp] theorem zero_and {w : Nat} (a : BitVec w) :
    and (BitVec.ofNat w 0) a = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and, getLsbD_zero, Bool.false_and]

/-- Right identity of bitwise OR (`a ||| 0#w = a`). -/
@[simp] theorem or_zero {w : Nat} (a : BitVec w) :
    or a (BitVec.ofNat w 0) = a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_or, getLsbD_zero, Bool.or_false]

/-- Left identity of bitwise OR (`0#w ||| a = a`). -/
@[simp] theorem zero_or {w : Nat} (a : BitVec w) :
    or (BitVec.ofNat w 0) a = a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_or, getLsbD_zero, Bool.false_or]

/-- Right identity of bitwise XOR (`a ^^^ 0#w = a`). -/
@[simp] theorem xor_zero {w : Nat} (a : BitVec w) :
    xor a (BitVec.ofNat w 0) = a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_xor, getLsbD_zero]
  cases getLsbD a i <;> rfl

/-- Left identity of bitwise XOR (`0#w ^^^ a = a`). -/
@[simp] theorem zero_xor {w : Nat} (a : BitVec w) :
    xor (BitVec.ofNat w 0) a = a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_xor, getLsbD_zero]
  cases getLsbD a i <;> rfl

/-- Self-cancellation of bitwise XOR (`a ^^^ a = 0#w`). -/
@[simp] theorem xor_self {w : Nat} (a : BitVec w) :
    xor a a = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_xor, getLsbD_zero]
  cases getLsbD a i <;> rfl

/-- Idempotence of bitwise AND (`a &&& a = a`). -/
@[simp] theorem and_self {w : Nat} (a : BitVec w) :
    and a a = a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and]
  cases getLsbD a i <;> rfl

/-- Idempotence of bitwise OR (`a ||| a = a`). -/
@[simp] theorem or_self {w : Nat} (a : BitVec w) :
    or a a = a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_or]
  cases getLsbD a i <;> rfl

/-- Complementarity under bitwise AND (`a &&& ~~~a = 0#w`). -/
@[simp] theorem and_not_self {w : Nat} (a : BitVec w) :
    and a (not a) = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_not_of_lt _ hi, getLsbD_zero]
  cases getLsbD a i <;> rfl

/-- Complementarity under bitwise OR (`a ||| ~~~a = allOnes w`). -/
@[simp] theorem or_not_self {w : Nat} (a : BitVec w) :
    or a (not a) = allOnes w := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_or, getLsbD_not_of_lt _ hi, getLsbD_allOnes, decide_eq_true hi]
  cases getLsbD a i <;> rfl

/-- Involution of bitwise complement (`~~~(~~~a) = a`). -/
@[simp] theorem not_not {w : Nat} (a : BitVec w) :
    not (not a) = a := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_not_of_lt _ hi, getLsbD_not_of_lt _ hi]
  cases getLsbD a i <;> rfl

/-- Commutativity of bitwise AND. -/
theorem and_comm {w : Nat} (a b : BitVec w) :
    and a b = and b a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and, getLsbD_and]
  cases getLsbD a i <;> cases getLsbD b i <;> rfl

/-- Commutativity of bitwise OR. -/
theorem or_comm {w : Nat} (a b : BitVec w) :
    or a b = or b a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_or, getLsbD_or]
  cases getLsbD a i <;> cases getLsbD b i <;> rfl

/-- Commutativity of bitwise XOR. -/
theorem xor_comm {w : Nat} (a b : BitVec w) :
    xor a b = xor b a := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_xor, getLsbD_xor]
  cases getLsbD a i <;> cases getLsbD b i <;> rfl

/-- Associativity of bitwise AND. -/
theorem and_assoc {w : Nat} (a b c : BitVec w) :
    and (and a b) c = and a (and b c) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and, getLsbD_and, getLsbD_and, getLsbD_and]
  cases getLsbD a i <;> cases getLsbD b i <;> cases getLsbD c i <;> rfl

/-- Associativity of bitwise OR. -/
theorem or_assoc {w : Nat} (a b c : BitVec w) :
    or (or a b) c = or a (or b c) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_or, getLsbD_or, getLsbD_or, getLsbD_or]
  cases getLsbD a i <;> cases getLsbD b i <;> cases getLsbD c i <;> rfl

/-- Associativity of bitwise XOR. -/
theorem xor_assoc {w : Nat} (a b c : BitVec w) :
    xor (xor a b) c = xor a (xor b c) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_xor, getLsbD_xor, getLsbD_xor, getLsbD_xor]
  cases getLsbD a i <;> cases getLsbD b i <;> cases getLsbD c i <;> rfl

/-- Left distributivity of bitwise AND over bitwise OR. -/
theorem and_or_distrib_left {w : Nat} (a b c : BitVec w) :
    and a (or b c) = or (and a b) (and a c) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and, getLsbD_or, getLsbD_or, getLsbD_and, getLsbD_and]
  cases getLsbD a i <;> cases getLsbD b i <;> cases getLsbD c i <;> rfl

/-- Left distributivity of bitwise OR over bitwise AND. -/
theorem or_and_distrib_left {w : Nat} (a b c : BitVec w) :
    or a (and b c) = and (or a b) (or a c) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_or, getLsbD_and, getLsbD_and, getLsbD_or, getLsbD_or]
  cases getLsbD a i <;> cases getLsbD b i <;> cases getLsbD c i <;> rfl

/-- De Morgan law for bitwise complement of AND. -/
theorem not_and {w : Nat} (a b : BitVec w) :
    not (and a b) = or (not a) (not b) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_not_of_lt _ hi, getLsbD_and, getLsbD_or,
    getLsbD_not_of_lt _ hi, getLsbD_not_of_lt _ hi]
  cases getLsbD a i <;> cases getLsbD b i <;> rfl

/-- De Morgan law for bitwise complement of OR. -/
theorem not_or {w : Nat} (a b : BitVec w) :
    not (or a b) = and (not a) (not b) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_not_of_lt _ hi, getLsbD_or, getLsbD_and,
    getLsbD_not_of_lt _ hi, getLsbD_not_of_lt _ hi]
  cases getLsbD a i <;> cases getLsbD b i <;> rfl

/-! ## Part 2: Disjoint Bitfield Packing and Injectivity -/

/-- Disjoint bitfield packing via bitwise OR is injective: if `a₁, a₂` live
strictly outside `mask` and `b₁, b₂` live strictly inside `mask`, then
`a₁ ||| b₁ = a₂ ||| b₂` forces `a₁ = a₂ ∧ b₁ = b₂`. -/
theorem disjoint_or_injective {w : Nat} {mask a₁ b₁ a₂ b₂ : BitVec w}
    (ha₁ : and a₁ mask = BitVec.ofNat w 0)
    (ha₂ : and a₂ mask = BitVec.ofNat w 0)
    (hb₁ : and b₁ (not mask) = BitVec.ofNat w 0)
    (hb₂ : and b₂ (not mask) = BitVec.ofNat w 0)
    (hor : or a₁ b₁ = or a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hbit : ∀ i, i < w →
      getLsbD a₁ i = getLsbD a₂ i ∧ getLsbD b₁ i = getLsbD b₂ i := by
    intro i hi
    have h1 := congrArg (fun x => getLsbD x i) ha₁
    have h2 := congrArg (fun x => getLsbD x i) ha₂
    have h3 := congrArg (fun x => getLsbD x i) hb₁
    have h4 := congrArg (fun x => getLsbD x i) hb₂
    have h5 := congrArg (fun x => getLsbD x i) hor
    rw [getLsbD_and, getLsbD_zero] at h1 h2
    rw [getLsbD_and, getLsbD_not_of_lt _ hi, getLsbD_zero] at h3 h4
    rw [getLsbD_or, getLsbD_or] at h5
    cases hm : getLsbD mask i with
    | false =>
      rw [hm] at h3 h4
      cases hb1v : getLsbD b₁ i <;> cases hb2v : getLsbD b₂ i
      · rw [hb1v, hb2v, Bool.or_false, Bool.or_false] at h5
        exact ⟨h5, rfl⟩
      · rw [hb2v] at h4; nomatch h4
      · rw [hb1v] at h3; nomatch h3
      · rw [hb1v] at h3; nomatch h3
    | true =>
      rw [hm] at h1 h2
      cases ha1v : getLsbD a₁ i <;> cases ha2v : getLsbD a₂ i
      · rw [ha1v, ha2v, Bool.false_or, Bool.false_or] at h5
        exact ⟨rfl, h5⟩
      · rw [ha2v] at h2; nomatch h2
      · rw [ha1v] at h1; nomatch h1
      · rw [ha1v] at h1; nomatch h1
  exact ⟨eq_of_getLsbD_eq (fun i hi => (hbit i hi).1),
    eq_of_getLsbD_eq (fun i hi => (hbit i hi).2)⟩

/-- Bitmask with the lowest `k` bits set to `1` in a `w`-bit bitvector. -/
@[expose] def lowMask (w k : Nat) : BitVec w :=
  BitVec.ofNat w (Nat.pow 2 k - 1)

/-- Bit characterization of `lowMask w k` at any in-bounds index `i < w`. -/
theorem getLsbD_lowMask {w k i : Nat} (hi : i < w) :
    getLsbD (lowMask w k) i = decide (i < k) := by
  unfold lowMask
  rw [getLsbD_ofNat, decide_eq_true hi, Bool.true_and]
  exact nat_testBit_two_pow_sub_one k i

/-- Any `w`-bit value strictly below `2^k` has no bits set outside
`lowMask w k`. -/
theorem lt_two_pow_and_not_lowMask {w k : Nat} {b : BitVec w}
    (hb : b.toNat < Nat.pow 2 k) :
    and b (not (lowMask w k)) = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_not_of_lt _ hi, getLsbD_lowMask hi, getLsbD_zero]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_true hlt]
    exact Bool.and_false _
  | inr hge =>
    have hb_bit : getLsbD b i = false :=
      nat_testBit_eq_false_of_lt
        (Nat.lt_of_lt_of_le hb (nat_pow_le_pow_right hge))
    rw [hb_bit]
    exact Bool.false_and _

/-- Any `w`-bit value aligned to `2^k` (`a.toNat % 2^k = 0`) has no bits set
inside `lowMask w k`. -/
theorem mod_two_pow_eq_zero_and_lowMask {w k : Nat} {a : BitVec w}
    (ha : Nat.mod a.toNat (Nat.pow 2 k) = 0) :
    and a (lowMask w k) = BitVec.ofNat w 0 := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_lowMask hi, getLsbD_zero]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    have hmod := nat_testBit_mod_two_pow a.toNat k i
    rw [ha, nat_testBit_zero, decide_eq_true hlt, Bool.true_and] at hmod
    have ha_bit : getLsbD a i = false := Eq.symm hmod
    rw [ha_bit, Bool.false_and]
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.and_false]

/-- Packing a `2^k`-aligned high field and a `< 2^k` low field with bitwise OR
is injective. -/
theorem aligned_or_bounded_injective {w k : Nat} {a₁ b₁ a₂ b₂ : BitVec w}
    (ha₁ : Nat.mod a₁.toNat (Nat.pow 2 k) = 0)
    (ha₂ : Nat.mod a₂.toNat (Nat.pow 2 k) = 0)
    (hb₁ : b₁.toNat < Nat.pow 2 k)
    (hb₂ : b₂.toNat < Nat.pow 2 k)
    (hor : or a₁ b₁ = or a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ :=
  disjoint_or_injective
    (mod_two_pow_eq_zero_and_lowMask ha₁)
    (mod_two_pow_eq_zero_and_lowMask ha₂)
    (lt_two_pow_and_not_lowMask hb₁)
    (lt_two_pow_and_not_lowMask hb₂)
    hor

/-! ## Part 3: Masked-Bit / Tnum Relational Algebra -/

/-- Tristate-number (tnum) equality modulo unknown-bit mask `mask`: `x` and `y`
agree on every known bit (`mask[i] = false`), i.e.,
`x &&& ~~~mask = y &&& ~~~mask`. -/
@[expose] def MaskEq {w : Nat} (mask x y : BitVec w) : Prop :=
  and x (not mask) = and y (not mask)

/-- Pointwise bit characterization of `MaskEq`. -/
theorem maskEq_iff_getLsbD {w : Nat} {mask x y : BitVec w} :
    MaskEq mask x y ↔
      ∀ i, i < w → getLsbD mask i = false → getLsbD x i = getLsbD y i := by
  constructor
  · intro h i hi hm
    have hb := congrArg (fun z => getLsbD z i) h
    rw [getLsbD_and, getLsbD_and, getLsbD_not_of_lt _ hi, hm] at hb
    rw [Bool.not_false, Bool.and_true, Bool.and_true] at hb
    exact hb
  · intro h
    apply eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_and, getLsbD_and, getLsbD_not_of_lt _ hi]
    cases hm : getLsbD mask i with
    | false =>
      rw [Bool.not_false, Bool.and_true, Bool.and_true]
      exact h i hi hm
    | true =>
      rw [Bool.not_true, Bool.and_false, Bool.and_false]

/-- Reflexivity of `MaskEq`. -/
theorem maskEq_refl {w : Nat} (m x : BitVec w) : MaskEq m x x :=
  rfl

/-- Symmetry of `MaskEq`. -/
theorem maskEq_symm {w : Nat} {m x y : BitVec w} (h : MaskEq m x y) :
    MaskEq m y x :=
  Eq.symm h

/-- Transitivity of `MaskEq`. -/
theorem maskEq_trans {w : Nat} {m x y z : BitVec w}
    (h₁ : MaskEq m x y) (h₂ : MaskEq m y z) : MaskEq m x z :=
  Eq.trans h₁ h₂

/-- Zero unknown-bit mask reduces `MaskEq` to exact equality. -/
theorem maskEq_zero_iff_eq {w : Nat} {x y : BitVec w} :
    MaskEq (BitVec.ofNat w 0) x y ↔ x = y := by
  unfold MaskEq
  rw [not_zero_eq_allOnes, and_allOnes, and_allOnes]

/-- All-ones unknown-bit mask relates every pair of bitvectors. -/
theorem maskEq_allOnes {w : Nat} (x y : BitVec w) :
    MaskEq (allOnes w) x y := by
  unfold MaskEq
  rw [not_allOnes_eq_zero, and_zero, and_zero]

/-- Monotonicity of `MaskEq` under mask weakening (`m₁ ⊆ m₂`). -/
theorem maskEq_mono {w : Nat} {m₁ m₂ x y : BitVec w}
    (hsub : and m₁ (not m₂) = BitVec.ofNat w 0)
    (h : MaskEq m₁ x y) :
    MaskEq m₂ x y := by
  rw [maskEq_iff_getLsbD]
  intro i hi hm₂
  have h1 := congrArg (fun z => getLsbD z i) hsub
  rw [getLsbD_and, getLsbD_not_of_lt _ hi, getLsbD_zero, hm₂,
    Bool.not_false, Bool.and_true] at h1
  exact maskEq_iff_getLsbD.1 h i hi h1

/-- Canonicalization of the reference value `v` by clearing its unknown bits. -/
theorem maskEq_canonical {w : Nat} {m x v : BitVec w} :
    MaskEq m x v ↔ MaskEq m x (and v (not m)) := by
  unfold MaskEq
  rw [and_assoc, and_self]

/-- Exact soundness of the tnum bitwise-AND abstract transfer function. -/
theorem tnum_and_sound {w : Nat} {m₁ m₂ x y v₁ v₂ : BitVec w}
    (h₁ : MaskEq m₁ x v₁) (h₂ : MaskEq m₂ y v₂) :
    MaskEq (or (or (and m₁ m₂) (and m₁ v₂)) (and v₁ m₂))
      (and x y) (and v₁ v₂) := by
  rw [maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_or, getLsbD_or, getLsbD_and, getLsbD_and, getLsbD_and] at hm
  rw [getLsbD_and, getLsbD_and]
  have h1 := maskEq_iff_getLsbD.1 h₁ i hi
  have h2 := maskEq_iff_getLsbD.1 h₂ i hi
  cases hm1 : getLsbD m₁ i with
  | false =>
    rw [h1 hm1]
    cases hm2 : getLsbD m₂ i with
    | false =>
      rw [h2 hm2]
    | true =>
      rw [hm1, hm2] at hm
      cases hv1 : getLsbD v₁ i with
      | false =>
        rw [Bool.false_and, Bool.false_and]
      | true =>
        rw [hv1] at hm
        nomatch hm
  | true =>
    cases hm2 : getLsbD m₂ i with
    | false =>
      rw [h2 hm2]
      rw [hm1, hm2] at hm
      cases hv2 : getLsbD v₂ i with
      | false =>
        rw [Bool.and_false, Bool.and_false]
      | true =>
        rw [hv2] at hm
        nomatch hm
    | true =>
      rw [hm1, hm2] at hm
      nomatch hm

/-- Exact soundness of the tnum bitwise-OR abstract transfer function. -/
theorem tnum_or_sound {w : Nat} {m₁ m₂ x y v₁ v₂ : BitVec w}
    (h₁ : MaskEq m₁ x v₁) (h₂ : MaskEq m₂ y v₂) :
    MaskEq (or (or (and m₁ m₂) (and m₁ (not v₂))) (and (not v₁) m₂))
      (or x y) (or v₁ v₂) := by
  rw [maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_or, getLsbD_or, getLsbD_and, getLsbD_and, getLsbD_and,
    getLsbD_not_of_lt _ hi, getLsbD_not_of_lt _ hi] at hm
  rw [getLsbD_or, getLsbD_or]
  have h1 := maskEq_iff_getLsbD.1 h₁ i hi
  have h2 := maskEq_iff_getLsbD.1 h₂ i hi
  cases hm1 : getLsbD m₁ i with
  | false =>
    rw [h1 hm1]
    cases hm2 : getLsbD m₂ i with
    | false =>
      rw [h2 hm2]
    | true =>
      rw [hm1, hm2] at hm
      cases hv1 : getLsbD v₁ i with
      | false =>
        rw [hv1] at hm
        nomatch hm
      | true =>
        rw [Bool.true_or, Bool.true_or]
  | true =>
    cases hm2 : getLsbD m₂ i with
    | false =>
      rw [h2 hm2]
      rw [hm1, hm2] at hm
      cases hv2 : getLsbD v₂ i with
      | false =>
        rw [hv2] at hm
        nomatch hm
      | true =>
        rw [Bool.or_true, Bool.or_true]
    | true =>
      rw [hm1, hm2] at hm
      nomatch hm

/-- Exact soundness of the tnum bitwise-XOR abstract transfer function. -/
theorem tnum_xor_sound {w : Nat} {m₁ m₂ x y v₁ v₂ : BitVec w}
    (h₁ : MaskEq m₁ x v₁) (h₂ : MaskEq m₂ y v₂) :
    MaskEq (or m₁ m₂) (xor x y) (xor v₁ v₂) := by
  rw [maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_or] at hm
  rw [getLsbD_xor, getLsbD_xor]
  cases hm1 : getLsbD m₁ i with
  | false =>
    cases hm2 : getLsbD m₂ i with
    | false =>
      rw [maskEq_iff_getLsbD.1 h₁ i hi hm1, maskEq_iff_getLsbD.1 h₂ i hi hm2]
    | true =>
      rw [hm1, hm2] at hm
      nomatch hm
  | true =>
    rw [hm1] at hm
    nomatch hm

/-- Exact soundness of the tnum bitwise-NOT abstract transfer function. -/
theorem tnum_not_sound {w : Nat} {m x v : BitVec w}
    (h : MaskEq m x v) :
    MaskEq m (not x) (not v) := by
  rw [maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_not_of_lt _ hi, getLsbD_not_of_lt _ hi,
    maskEq_iff_getLsbD.1 h i hi hm]

/-- Exact soundness of the tnum constant logical left-shift transfer function.
-/
theorem tnum_shl_sound {w : Nat} {m x v : BitVec w} (k : Nat)
    (h : MaskEq m x v) :
    MaskEq (shl m k) (shl x k) (shl v k) := by
  rw [maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_shl, decide_eq_true hi, Bool.true_and] at hm
  rw [getLsbD_shl, getLsbD_shl, decide_eq_true hi, Bool.true_and, Bool.true_and]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, Bool.false_and]
  | inr hge =>
    rw [decide_eq_true hge, Bool.true_and] at hm
    rw [decide_eq_true hge, Bool.true_and, Bool.true_and]
    exact maskEq_iff_getLsbD.1 h (i - k)
      (Nat.lt_of_le_of_lt (Nat.sub_le i k) hi) hm

/-- Exact soundness of the tnum constant logical right-shift transfer function.
-/
theorem tnum_ushr_sound {w : Nat} {m x v : BitVec w} (k : Nat)
    (h : MaskEq m x v) :
    MaskEq (ushr m k) (ushr x k) (ushr v k) := by
  rw [maskEq_iff_getLsbD]
  intro i _ hm
  rw [getLsbD_ushr] at hm
  rw [getLsbD_ushr, getLsbD_ushr]
  cases Nat.lt_or_ge (i + k) w with
  | inl hlt =>
    exact maskEq_iff_getLsbD.1 h (i + k) hlt hm
  | inr hge =>
    rw [getLsbD_ge x hge, getLsbD_ge v hge]

/-- Unsigned lower and upper bounds implied by a canonical tnum abstraction:
if `MaskEq m x v` and `v &&& m = 0#w`, then `v ≤ x ∧ x ≤ v ||| m`. -/
theorem tnum_and_bounds_sound {w : Nat} {m x v : BitVec w}
    (hEq : MaskEq m x v) (hDisj : and v m = BitVec.ofNat w 0) :
    v ≤ x ∧ x ≤ or v m := by
  constructor
  · apply nat_le_of_testBit_imp w v.toNat x.toNat v.isLt x.isLt
    intro i hi hv
    have hd := congrArg (fun z => getLsbD z i) hDisj
    rw [getLsbD_and, getLsbD_zero] at hd
    have hvi : getLsbD v i = true := hv
    rw [hvi, Bool.true_and] at hd
    have hxv := maskEq_iff_getLsbD.1 hEq i hi hd
    exact Eq.trans hxv hv
  · apply nat_le_of_testBit_imp w x.toNat (or v m).toNat x.isLt (or v m).isLt
    intro i hi hx
    change getLsbD (or v m) i = true
    rw [getLsbD_or]
    cases hm : getLsbD m i with
    | true =>
      exact Bool.or_true _
    | false =>
      have hxv := maskEq_iff_getLsbD.1 hEq i hi hm
      have hvi : getLsbD v i = true := Eq.trans (Eq.symm hxv) hx
      rw [hvi]
      rfl

/-! ## Part 4: Unsigned Interval / Range Arithmetic Soundness -/

/-- Soundness of unsigned interval addition when `a_hi + b_hi < 2^w`. -/
theorem range_add_no_overflow_sound {w : Nat}
    {a_lo x a_hi b_lo y b_hi : BitVec w}
    (ha_lo : a_lo ≤ x) (ha_hi : x ≤ a_hi)
    (hb_lo : b_lo ≤ y) (hb_hi : y ≤ b_hi)
    (hno_ovf : a_hi.toNat + b_hi.toNat < Nat.pow 2 w) :
    a_lo + b_lo ≤ x + y ∧ x + y ≤ a_hi + b_hi := by
  have h1 : a_lo.toNat + b_lo.toNat ≤ x.toNat + y.toNat :=
    Nat.add_le_add ha_lo hb_lo
  have h2 : x.toNat + y.toNat ≤ a_hi.toNat + b_hi.toNat :=
    Nat.add_le_add ha_hi hb_hi
  have hlt_xy : x.toNat + y.toNat < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h2 hno_ovf
  have hlt_lo : a_lo.toNat + b_lo.toNat < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h1 hlt_xy
  constructor
  · change (a_lo + b_lo).toNat ≤ (x + y).toNat
    rw [toNat_add, toNat_add, nat_mod_eq_of_lt hlt_lo, nat_mod_eq_of_lt hlt_xy]
    exact h1
  · change (x + y).toNat ≤ (a_hi + b_hi).toNat
    rw [toNat_add, toNat_add, nat_mod_eq_of_lt hlt_xy, nat_mod_eq_of_lt hno_ovf]
    exact h2

private theorem nat_lt_of_add_lt_add_left {k a b : Nat}
    (h : k + a < k + b) : a < b := by
  induction k with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | succ k ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.lt_of_succ_lt_succ h)

private theorem nat_mod_sub_of_ge_lt_two_mul {m n : Nat}
    (hge : m ≤ n) (hlt : n < m + m) :
    Nat.mod n m = n - m := by
  have hdecomp : n = m + (n - m) := Eq.symm (Nat.add_sub_of_le hge)
  have hsub_lt : n - m < m := by
    have h1 : m + (n - m) < m + m := by
      rw [← hdecomp]
      exact hlt
    exact nat_lt_of_add_lt_add_left h1
  have hmod : Nat.mod (m + (n - m)) m = n - m := by
    rw [nat_add_mod_left]
    exact nat_mod_eq_of_lt hsub_lt
  rw [← hdecomp] at hmod
  exact hmod

/-- Soundness of unsigned interval addition when both endpoint sums wrap
(`2^w ≤ a_lo.toNat + b_lo.toNat`). -/
theorem range_add_both_overflow_sound {w : Nat}
    {a_lo x a_hi b_lo y b_hi : BitVec w}
    (ha_lo : a_lo ≤ x) (ha_hi : x ≤ a_hi)
    (hb_lo : b_lo ≤ y) (hb_hi : y ≤ b_hi)
    (hboth_ovf : Nat.pow 2 w ≤ a_lo.toNat + b_lo.toNat) :
    a_lo + b_lo ≤ x + y ∧ x + y ≤ a_hi + b_hi := by
  have h1 : a_lo.toNat + b_lo.toNat ≤ x.toNat + y.toNat :=
    Nat.add_le_add ha_lo hb_lo
  have h2 : x.toNat + y.toNat ≤ a_hi.toNat + b_hi.toNat :=
    Nat.add_le_add ha_hi hb_hi
  have hge_xy : Nat.pow 2 w ≤ x.toNat + y.toNat :=
    Nat.le_trans hboth_ovf h1
  have hge_hi : Nat.pow 2 w ≤ a_hi.toNat + b_hi.toNat :=
    Nat.le_trans hge_xy h2
  have hlt_hi : a_hi.toNat + b_hi.toNat < Nat.pow 2 w + Nat.pow 2 w :=
    Nat.add_lt_add a_hi.isLt b_hi.isLt
  have hlt_xy : x.toNat + y.toNat < Nat.pow 2 w + Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h2 hlt_hi
  have hlt_lo : a_lo.toNat + b_lo.toNat < Nat.pow 2 w + Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h1 hlt_xy
  constructor
  · change (a_lo + b_lo).toNat ≤ (x + y).toNat
    rw [toNat_add, toNat_add,
      nat_mod_sub_of_ge_lt_two_mul hboth_ovf hlt_lo,
      nat_mod_sub_of_ge_lt_two_mul hge_xy hlt_xy]
    exact Nat.sub_le_sub_right h1 (Nat.pow 2 w)
  · change (x + y).toNat ≤ (a_hi + b_hi).toNat
    rw [toNat_add, toNat_add,
      nat_mod_sub_of_ge_lt_two_mul hge_xy hlt_xy,
      nat_mod_sub_of_ge_lt_two_mul hge_hi hlt_hi]
    exact Nat.sub_le_sub_right h2 (Nat.pow 2 w)

/-- Full soundness of unsigned wrapping interval addition: when lower- and
upper-endpoint overflow bits match, `x + y` stays within
`[a_lo + b_lo, a_hi + b_hi]`; when they differ, `[0, allOnes w]` encloses it.
-/
theorem range_add_sound {w : Nat}
    {a_lo x a_hi b_lo y b_hi : BitVec w}
    (ha_lo : a_lo ≤ x) (ha_hi : x ≤ a_hi)
    (hb_lo : b_lo ≤ y) (hb_hi : y ≤ b_hi) :
    let minOvf := decide (Nat.pow 2 w ≤ a_lo.toNat + b_lo.toNat)
    let maxOvf := decide (Nat.pow 2 w ≤ a_hi.toNat + b_hi.toNat)
    let resLo := if minOvf != maxOvf then BitVec.ofNat w 0 else a_lo + b_lo
    let resHi := if minOvf != maxOvf then allOnes w else a_hi + b_hi
    resLo ≤ x + y ∧ x + y ≤ resHi := by
  dsimp only
  cases Nat.lt_or_ge (a_hi.toNat + b_hi.toNat) (Nat.pow 2 w) with
  | inl hhi_lt =>
    have hlo_lt : a_lo.toNat + b_lo.toNat < Nat.pow 2 w :=
      Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_trans ha_lo ha_hi)
        (Nat.le_trans hb_lo hb_hi)) hhi_lt
    rw [decide_eq_false (Nat.not_le_of_gt hlo_lt),
      decide_eq_false (Nat.not_le_of_gt hhi_lt)]
    exact range_add_no_overflow_sound ha_lo ha_hi hb_lo hb_hi hhi_lt
  | inr hhi_ge =>
    rw [decide_eq_true hhi_ge]
    cases Nat.lt_or_ge (a_lo.toNat + b_lo.toNat) (Nat.pow 2 w) with
    | inl hlo_lt =>
      rw [decide_eq_false (Nat.not_le_of_gt hlo_lt)]
      constructor
      · change (BitVec.ofNat w 0).toNat ≤ (x + y).toNat
        rw [toNat_zero]
        exact Nat.zero_le _
      · change (x + y).toNat ≤ (allOnes w).toNat
        rw [toNat_allOnes]
        exact Nat.le_sub_one_of_lt (x + y).isLt
    | inr hlo_ge =>
      rw [decide_eq_true hlo_ge]
      exact range_add_both_overflow_sound ha_lo ha_hi hb_lo hb_hi hlo_ge

/-- Soundness of unsigned interval subtraction when `b_hi ≤ a_lo`. -/
theorem range_sub_no_underflow_sound {w : Nat}
    {a_lo x a_hi b_lo y b_hi : BitVec w}
    (ha_lo : a_lo ≤ x) (ha_hi : x ≤ a_hi)
    (hb_lo : b_lo ≤ y) (hb_hi : y ≤ b_hi)
    (hno_udf : b_hi ≤ a_lo) :
    a_lo - b_hi ≤ x - y ∧ x - y ≤ a_hi - b_lo := by
  have hyx : y ≤ x := Nat.le_trans hb_hi (Nat.le_trans hno_udf ha_lo)
  have hblo_ahi : b_lo ≤ a_hi :=
    Nat.le_trans hb_lo (Nat.le_trans hyx ha_hi)
  constructor
  · change (a_lo - b_hi).toNat ≤ (x - y).toNat
    rw [toNat_sub_of_le hno_udf, toNat_sub_of_le hyx]
    exact nat_sub_le_sub ha_lo hb_hi
  · change (x - y).toNat ≤ (a_hi - b_lo).toNat
    rw [toNat_sub_of_le hyx, toNat_sub_of_le hblo_ahi]
    exact nat_sub_le_sub ha_hi hb_lo

/-- Soundness of unsigned interval multiplication when `a_hi * b_hi < 2^w`. -/
theorem range_mul_no_overflow_sound {w : Nat}
    {a_lo x a_hi b_lo y b_hi : BitVec w}
    (ha_lo : a_lo ≤ x) (ha_hi : x ≤ a_hi)
    (hb_lo : b_lo ≤ y) (hb_hi : y ≤ b_hi)
    (hno_ovf : a_hi.toNat * b_hi.toNat < Nat.pow 2 w) :
    mul a_lo b_lo ≤ mul x y ∧ mul x y ≤ mul a_hi b_hi := by
  have h1 : a_lo.toNat * b_lo.toNat ≤ x.toNat * y.toNat :=
    Nat.mul_le_mul ha_lo hb_lo
  have h2 : x.toNat * y.toNat ≤ a_hi.toNat * b_hi.toNat :=
    Nat.mul_le_mul ha_hi hb_hi
  have hlt_xy : x.toNat * y.toNat < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h2 hno_ovf
  have hlt_lo : a_lo.toNat * b_lo.toNat < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h1 hlt_xy
  constructor
  · change (mul a_lo b_lo).toNat ≤ (mul x y).toNat
    rw [toNat_mul, toNat_mul, nat_mod_eq_of_lt hlt_lo, nat_mod_eq_of_lt hlt_xy]
    exact h1
  · change (mul x y).toNat ≤ (mul a_hi b_hi).toNat
    rw [toNat_mul, toNat_mul, nat_mod_eq_of_lt hlt_xy, nat_mod_eq_of_lt hno_ovf]
    exact h2

/-- Soundness of unsigned interval division when `0 < b_lo.toNat`. -/
theorem range_udiv_sound {w : Nat}
    {a_lo x a_hi b_lo y b_hi : BitVec w}
    (ha_lo : a_lo ≤ x) (ha_hi : x ≤ a_hi)
    (hb_lo : b_lo ≤ y) (hb_hi : y ≤ b_hi)
    (hpos : 0 < b_lo.toNat) :
    udiv a_lo b_hi ≤ udiv x y ∧ udiv x y ≤ udiv a_hi b_lo := by
  have hy_pos : 0 < y.toNat := Nat.lt_of_lt_of_le hpos hb_lo
  constructor
  · change Nat.div a_lo.toNat b_hi.toNat ≤ Nat.div x.toNat y.toNat
    exact Nat.le_trans
      (nat_div_le_div_left hb_hi hy_pos)
      (nat_div_le_div_right ha_lo y.toNat)
  · change Nat.div x.toNat y.toNat ≤ Nat.div a_hi.toNat b_lo.toNat
    exact Nat.le_trans
      (nat_div_le_div_right ha_hi y.toNat)
      (nat_div_le_div_left hb_lo hpos)

/-! ## Part 5: Common-Prefix Range-to-Tnum Tightening and `clz` -/

private theorem div_two_pow_eq_of_xor_not_lowMask_eq_zero {w k : Nat}
    {a b : BitVec w}
    (h : and (xor a b) (not (lowMask w k)) = BitVec.ofNat w 0) :
    Nat.div a.toNat (Nat.pow 2 k) = Nat.div b.toNat (Nat.pow 2 k) := by
  have ha_lt : Nat.div a.toNat (Nat.pow 2 k) < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt (nat_div_le_self a.toNat (Nat.pow 2 k)) a.isLt
  have hb_lt : Nat.div b.toNat (Nat.pow 2 k) < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt (nat_div_le_self b.toNat (Nat.pow 2 k)) b.isLt
  apply nat_eq_of_testBit_eq_below w _ _ ha_lt hb_lt
  intro j _
  have hsr_a : (Nat.div a.toNat (Nat.pow 2 k)).testBit j =
      a.toNat.testBit (j + k) := by
    rw [← nat_shiftRight_eq_div_pow a.toNat k]
    exact nat_testBit_shiftRight a.toNat k j
  have hsr_b : (Nat.div b.toNat (Nat.pow 2 k)).testBit j =
      b.toNat.testBit (j + k) := by
    rw [← nat_shiftRight_eq_div_pow b.toNat k]
    exact nat_testBit_shiftRight b.toNat k j
  rw [hsr_a, hsr_b]
  change getLsbD a (j + k) = getLsbD b (j + k)
  cases Nat.lt_or_ge (j + k) w with
  | inr hge =>
    rw [getLsbD_ge a hge, getLsbD_ge b hge]
  | inl hlt =>
    have hbit := congrArg (fun z => getLsbD z (j + k)) h
    have hnot_lt : ¬ (j + k < k) :=
      Nat.not_lt_of_ge (Nat.le_add_left k j)
    rw [getLsbD_and, getLsbD_xor, getLsbD_not_of_lt _ hlt,
      getLsbD_lowMask hlt, getLsbD_zero, decide_eq_false hnot_lt,
      Bool.not_false, Bool.and_true] at hbit
    cases ha_b : getLsbD a (j + k) <;> cases hb_b : getLsbD b (j + k)
    · rfl
    · rw [ha_b, hb_b] at hbit; nomatch hbit
    · rw [ha_b, hb_b] at hbit; nomatch hbit
    · rfl

/-- Common-prefix range-to-tnum tightening: if `umin ≤ x ≤ umax` and `umin`
agrees with `umax` on all bits `i ≥ k`, then `x` also agrees with `umin` on
all bits `i ≥ k`. -/
theorem common_prefix_of_bounds {w k : Nat} {umin x umax : BitVec w}
    (hlo : umin ≤ x) (hhi : x ≤ umax)
    (hpref : and (xor umin umax) (not (lowMask w k)) = BitVec.ofNat w 0) :
    and (xor x umin) (not (lowMask w k)) = BitVec.ofNat w 0 := by
  have hdiv_eq :
      Nat.div umin.toNat (Nat.pow 2 k) = Nat.div umax.toNat (Nat.pow 2 k) :=
    div_two_pow_eq_of_xor_not_lowMask_eq_zero hpref
  have hdiv_lo :
      Nat.div umin.toNat (Nat.pow 2 k) ≤ Nat.div x.toNat (Nat.pow 2 k) :=
    nat_div_le_div_right hlo (Nat.pow 2 k)
  have hdiv_hi :
      Nat.div x.toNat (Nat.pow 2 k) ≤ Nat.div umin.toNat (Nat.pow 2 k) := by
    rw [hdiv_eq]
    exact nat_div_le_div_right hhi (Nat.pow 2 k)
  have hdiv_x :
      Nat.div x.toNat (Nat.pow 2 k) = Nat.div umin.toNat (Nat.pow 2 k) :=
    Nat.le_antisymm hdiv_hi hdiv_lo
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_xor, getLsbD_not_of_lt _ hi,
    getLsbD_lowMask hi, getLsbD_zero]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_true hlt, Bool.not_true, Bool.and_false]
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.not_false, Bool.and_true]
    have hi_eq : i = (i - k) + k := Eq.symm (Nat.sub_add_cancel hge)
    have hbit_x : getLsbD x i =
        (Nat.div x.toNat (Nat.pow 2 k)).testBit (i - k) := by
      unfold getLsbD
      rw [← nat_shiftRight_eq_div_pow x.toNat k, nat_testBit_shiftRight, ← hi_eq]
    have hbit_u : getLsbD umin i =
        (Nat.div umin.toNat (Nat.pow 2 k)).testBit (i - k) := by
      unfold getLsbD
      rw [← nat_shiftRight_eq_div_pow umin.toNat k, nat_testBit_shiftRight, ← hi_eq]
    rw [hbit_x, hbit_u, hdiv_x]
    cases (Nat.div umin.toNat (Nat.pow 2 k)).testBit (i - k) <;> rfl

/-- `MaskEq` formulation of `common_prefix_of_bounds`: if `umin ≤ x ≤ umax` and
`umin ^^^ umax` vanishes outside `lowMask w k`, then
`MaskEq (lowMask w k) x umin`. -/
theorem maskEq_lowMask_of_bounds {w k : Nat} {umin x umax : BitVec w}
    (hlo : umin ≤ x) (hhi : x ≤ umax)
    (hpref : and (xor umin umax) (not (lowMask w k)) = BitVec.ofNat w 0) :
    MaskEq (lowMask w k) x umin := by
  have hx := common_prefix_of_bounds hlo hhi hpref
  rw [maskEq_iff_getLsbD]
  intro i hi hm
  have hbit := congrArg (fun z => getLsbD z i) hx
  rw [getLsbD_and, getLsbD_xor, getLsbD_not_of_lt _ hi, getLsbD_zero,
    hm, Bool.not_false, Bool.and_true] at hbit
  cases hxi : getLsbD x i <;> cases hui : getLsbD umin i
  · rfl
  · rw [hxi, hui] at hbit; nomatch hbit
  · rw [hxi, hui] at hbit; nomatch hbit
  · rfl

/-- Count consecutive leading zero bits of `x` across the low `n` bits (indices
`n - 1` down to `0`). Using `@Nat.rec` avoids compiler `_unsafe_rec`
auxiliaries while remaining `rfl`-reducible on `0` and `n + 1`. -/
@[expose] def clzAux {w : Nat} (x : BitVec w) (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih => if getLsbD x k then 0 else ih + 1)
    n

private theorem clzAux_succ {w : Nat} (x : BitVec w) (n : Nat) :
    clzAux x (n + 1) = if getLsbD x n then 0 else clzAux x n + 1 :=
  rfl

/-- Number of leading zero bits of a `w`-bit bitvector (`0 ≤ clz x ≤ w`). -/
@[expose] def clz {w : Nat} (x : BitVec w) : Nat :=
  clzAux x w

private theorem clzAux_le {w : Nat} (x : BitVec w) (n : Nat) :
    clzAux x n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [clzAux_succ]
    cases getLsbD x n with
    | true => exact Nat.zero_le (n + 1)
    | false => exact Nat.succ_le_succ ih

/-- Upper bound: the leading-zero count never exceeds the bit width `w`. -/
theorem clz_le {w : Nat} (x : BitVec w) : clz x ≤ w :=
  clzAux_le x w

private theorem clzAux_eq_iff {w : Nat} (x : BitVec w) (n : Nat) :
    clzAux x n = n ↔ ∀ i, i < n → getLsbD x i = false := by
  induction n with
  | zero =>
    constructor
    · intro _ i hi
      exact False.elim (Nat.not_lt_zero i hi)
    · intro _
      rfl
  | succ n ih =>
    rw [clzAux_succ]
    cases hb : getLsbD x n with
    | true =>
      constructor
      · intro h
        nomatch h
      · intro hall
        have hfalse := hall n (Nat.lt_succ_self n)
        rw [hb] at hfalse
        nomatch hfalse
    | false =>
      constructor
      · intro h i hi
        have hpred : clzAux x n = n := Nat.succ.inj h
        cases Nat.lt_or_ge i n with
        | inl hlt => exact ih.1 hpred i hlt
        | inr hge =>
          have heq : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
          rw [heq]
          exact hb
      · intro hall
        have hlow : ∀ i, i < n → getLsbD x i = false :=
          fun i hi => hall i (Nat.lt_succ_of_lt hi)
        exact congrArg Nat.succ (ih.2 hlow)

/-- A `w`-bit bitvector has `w` leading zeros if and only if it is `0#w`. -/
theorem clz_eq_width_iff {w : Nat} (x : BitVec w) :
    clz x = w ↔ x = BitVec.ofNat w 0 := by
  unfold clz
  rw [clzAux_eq_iff]
  constructor
  · intro hall
    apply eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_zero]
    exact hall i hi
  · intro hx i _
    rw [hx, getLsbD_zero]

private theorem getLsbD_eq_false_of_ge_sub_clzAux {w : Nat} (x : BitVec w)
    (n : Nat) :
    ∀ i, n - clzAux x n ≤ i → i < n → getLsbD x i = false := by
  induction n with
  | zero =>
    intro i _ hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hlo hi
    rw [clzAux_succ] at hlo
    cases hb : getLsbD x n with
    | true =>
      rw [hb, ite_bool_true, Nat.sub_zero] at hlo
      exact False.elim (Nat.not_lt_of_ge hlo hi)
    | false =>
      rw [hb, ite_bool_false, Nat.succ_sub_succ] at hlo
      cases Nat.lt_or_ge i n with
      | inl hlt => exact ih i hlo hlt
      | inr hge =>
        have heq : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
        rw [heq]
        exact hb

/-- Every bit at position `i ≥ w - clz x` of `x` is `false`. -/
theorem getLsbD_eq_false_of_ge_sub_clz {w : Nat} (x : BitVec w)
    {i : Nat} (hi : w - clz x ≤ i) :
    getLsbD x i = false := by
  cases Nat.lt_or_ge i w with
  | inl hlt => exact getLsbD_eq_false_of_ge_sub_clzAux x w i hi hlt
  | inr hge => exact getLsbD_ge x hge

private theorem getLsbD_sub_clzAux_sub_one {w : Nat} (x : BitVec w) (n : Nat) :
    clzAux x n < n → getLsbD x (n - clzAux x n - 1) = true := by
  induction n with
  | zero =>
    intro hlt
    exact False.elim (Nat.not_lt_zero _ hlt)
  | succ n ih =>
    intro hlt
    rw [clzAux_succ] at hlt
    rw [clzAux_succ]
    cases hb : getLsbD x n with
    | true =>
      rw [ite_bool_true, Nat.sub_zero, Nat.add_sub_cancel]
      exact hb
    | false =>
      rw [hb, ite_bool_false] at hlt
      rw [ite_bool_false, Nat.succ_sub_succ]
      exact ih (Nat.lt_of_succ_lt_succ hlt)

/-- Tightness of `clz`: for any nonzero `x : BitVec w`, bit `w - clz x - 1` is
set (`true`). -/
theorem getLsbD_sub_clz_sub_one {w : Nat} {x : BitVec w}
    (hne : x ≠ BitVec.ofNat w 0) :
    getLsbD x (w - clz x - 1) = true := by
  have hne_w : clz x ≠ w := fun heq => hne ((clz_eq_width_iff x).1 heq)
  have hlt : clz x < w := Nat.lt_of_le_of_ne (clz_le x) hne_w
  exact getLsbD_sub_clzAux_sub_one x w hlt

/-- Every `x : BitVec w` is strictly bounded by `2^(w - clz x)`. -/
theorem toNat_lt_two_pow_sub_clz {w : Nat} (x : BitVec w) :
    x.toNat < Nat.pow 2 (w - clz x) := by
  have hmod_lt : Nat.mod x.toNat (Nat.pow 2 (w - clz x)) < Nat.pow 2 w :=
    Nat.lt_of_lt_of_le
      (nat_mod_lt x.toNat (nat_two_pow_pos (w - clz x)))
      (nat_pow_le_pow_right (Nat.sub_le w (clz x)))
  have heq : x.toNat = Nat.mod x.toNat (Nat.pow 2 (w - clz x)) := by
    apply nat_eq_of_testBit_eq_below w _ _ x.isLt hmod_lt
    intro i _
    rw [nat_testBit_mod_two_pow]
    cases Nat.lt_or_ge i (w - clz x) with
    | inl hlt =>
      rw [decide_eq_true hlt, Bool.true_and]
    | inr hge =>
      rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
      exact getLsbD_eq_false_of_ge_sub_clz x hge
  rw [heq]
  exact nat_mod_lt x.toNat (nat_two_pow_pos (w - clz x))

/-- Exact `clz` bound on the XOR difference `umin ^^^ umax`. -/
theorem xor_lt_two_pow_sub_clz {w : Nat} (umin umax : BitVec w) :
    (xor umin umax).toNat < Nat.pow 2 (w - clz (xor umin umax)) :=
  toNat_lt_two_pow_sub_clz (xor umin umax)

/-- `umin ^^^ umax` has zero bits outside `lowMask w (w - clz (umin ^^^ umax))`.
-/
theorem xor_and_not_lowMask_sub_clz {w : Nat} (umin umax : BitVec w) :
    and (xor umin umax) (not (lowMask w (w - clz (xor umin umax)))) =
      BitVec.ofNat w 0 :=
  lt_two_pow_and_not_lowMask (xor_lt_two_pow_sub_clz umin umax)

/-- Common-prefix tightening directly parameterized by `clz (umin ^^^ umax)`. -/
theorem common_prefix_of_bounds_clz {w : Nat} {umin x umax : BitVec w}
    (hlo : umin ≤ x) (hhi : x ≤ umax) :
    and (xor x umin) (not (lowMask w (w - clz (xor umin umax)))) =
      BitVec.ofNat w 0 :=
  common_prefix_of_bounds hlo hhi (xor_and_not_lowMask_sub_clz umin umax)

/-- `MaskEq` range-to-tnum tightening directly parameterized by
`clz (umin ^^^ umax)`. -/
theorem maskEq_clz_of_bounds {w : Nat} {umin x umax : BitVec w}
    (hlo : umin ≤ x) (hhi : x ≤ umax) :
    MaskEq (lowMask w (w - clz (xor umin umax))) x umin :=
  maskEq_lowMask_of_bounds hlo hhi (xor_and_not_lowMask_sub_clz umin umax)

end Anneal.BitVec

end
