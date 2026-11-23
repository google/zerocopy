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
public import Anneal.BitVec

public section

namespace Anneal.BitVecArith

/-!
# Reusable 3-Axiom BitVector Arithmetic Library (`Anneal.BitVecArith`)

Kernel-checked, width-parametric signed arithmetic, tristate-number (tnum)
addition/subtraction soundness, unsigned and signed interval transfers,
bitfield extraction, and byte-swap involutions built strictly on Anneal's
51-module `foundation-lock.json` foundation and `Anneal.BitVec` (zero
`bv_decide`, zero `omega`, zero `Lean.ofReduceBool`).

Core operations shared with `Init.Data.BitVec.Basic` (`msb`, `neg`, `urem`)
are definitionally equal (`rfl`) to their standard-library counterparts, so
downstream target proofs importing `Init.Data.BitVec.Basic` can apply these
lemmas directly without casts.

1. **Two's-Complement Signed Bit-Vectors:** `msb`, `neg`, `signBit`,
   `signedKey`, `sle`, `slt`, `signExtend`, and `ashr`.
2. **Tnum / `MaskEq` Transfer Functions:** `setWidth`, `signExtend`, `ashr`,
   carry-propagation `tnum_add_sound`, and borrow-propagation `tnum_sub_sound`.
3. **Unsigned & Signed Interval Transfer Soundness:** `urem`, `shl`, `ushr`,
   `and`, `or`, `xor`, overflow-free signed addition, and branch refinement.
4. **Bitfield Extraction & Byte-Swap:** `extractBits` and involutive
   `bswap16`, `bswap32`, and `bswap64`.
-/

/-! ## Part 0: Foundation-Only `Nat` Arithmetic and Bitwise Helpers -/

private theorem nat_pow_zero (a : Nat) : Nat.pow a 0 = 1 := rfl

private theorem nat_pow_succ (a n : Nat) :
    Nat.pow a (n + 1) = Nat.pow a n * a :=
  Nat.pow_succ a n

private theorem nat_two_pow_pos (n : Nat) : 0 < Nat.pow 2 n :=
  Nat.two_pow_pos n

private theorem nat_pow_add (a m n : Nat) :
    Nat.pow a (m + n) = Nat.pow a m * Nat.pow a n := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nat_pow_zero, Nat.mul_one]
  | succ n ih =>
    rw [Nat.add_succ, nat_pow_succ, nat_pow_succ, ih, Nat.mul_assoc]

private theorem nat_pow_le_pow_right {i j : Nat} (h : i ≤ j) :
    Nat.pow 2 i ≤ Nat.pow 2 j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

private theorem nat_two_pow_split {w : Nat} (hw : 0 < w) :
    Nat.pow 2 w = Nat.pow 2 (w - 1) + Nat.pow 2 (w - 1) := by
  have hw_eq : w = (w - 1) + 1 := Eq.symm (Nat.sub_add_cancel hw)
  have h1 := congrArg (Nat.pow 2) hw_eq
  rw [nat_pow_succ, Nat.mul_two] at h1
  exact h1

private theorem nat_two_pow_sub_one_lt {w : Nat} (hw : 0 < w) :
    Nat.pow 2 (w - 1) < Nat.pow 2 w := by
  rw [nat_two_pow_split hw]
  exact Nat.lt_add_of_pos_right (nat_two_pow_pos (w - 1))

private theorem nat_div_add_mod (m n : Nat) :
    n * Nat.div m n + Nat.mod m n = m :=
  Nat.div_add_mod m n

private theorem nat_div_zero (n : Nat) : Nat.div n 0 = 0 :=
  Nat.div_zero n

private theorem nat_div_one (n : Nat) : Nat.div n 1 = n :=
  Nat.div_one n

private theorem nat_div_self {n : Nat} (hn : 0 < n) : Nat.div n n = 1 :=
  Nat.div_self hn

private theorem nat_zero_mod (n : Nat) : Nat.mod 0 n = 0 :=
  Nat.zero_mod n

private theorem nat_mod_self (n : Nat) : Nat.mod n n = 0 :=
  Nat.mod_self n

private theorem nat_mod_lt (a : Nat) {b : Nat} (hb : 0 < b) :
    Nat.mod a b < b :=
  Nat.mod_lt a hb

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

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

private theorem nat_add_mod_left (x z : Nat) :
    Nat.mod (x + z) x = Nat.mod z x :=
  Nat.add_mod_left x z

private theorem nat_mul_mod_right (m n : Nat) :
    Nat.mod (m * n) m = 0 :=
  Nat.mul_mod_right m n

private theorem nat_mul_div_right (n : Nat) {m : Nat} (hm : 0 < m) :
    Nat.div (m * n) m = n :=
  Nat.mul_div_right n hm

private theorem nat_shiftLeft_eq (m k : Nat) :
    Nat.shiftLeft m k = m * Nat.pow 2 k :=
  Nat.shiftLeft_eq m k

private theorem nat_shiftRight_eq_div_pow (m k : Nat) :
    Nat.shiftRight m k = Nat.div m (Nat.pow 2 k) :=
  Nat.shiftRight_eq_div_pow m k

private theorem nat_lt_of_add_lt_add_right {a b c : Nat}
    (h : a + c < b + c) : a < b := by
  have h1 : (a + 1) + c ≤ b + c := by
    rw [Nat.add_right_comm]
    exact h
  exact Nat.le_of_add_le_add_right h1

private theorem nat_sub_sub_self {a b : Nat} (h : a ≤ b) :
    b - (b - a) = a := by
  have h1 : (b - a) + a = b := Nat.sub_add_cancel h
  have h2 := congrArg (fun z => z - (b - a)) h1
  rw [Nat.add_comm (b - a) a, Nat.add_sub_cancel] at h2
  exact Eq.symm h2

private theorem nat_sub_add_comm {a b c : Nat} (h : b ≤ a) :
    a - b + c = a + c - b := by
  have h1 : (a - b + c) + b = a + c := by
    rw [Nat.add_right_comm, Nat.sub_add_cancel h]
  have h2 := congrArg (fun z => z - b) h1
  rw [Nat.add_sub_cancel] at h2
  exact h2

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

private theorem nat_mod_two_cases (n : Nat) :
    Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hlt : Nat.mod n 2 < 2 := Nat.mod_lt n (by decide)
  cases hm : Nat.mod n 2 with
  | zero => left; rfl
  | succ k =>
    cases k with
    | zero => right; rfl
    | succ k' =>
      rw [hm] at hlt
      exact False.elim
        (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k')))
          hlt)

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
    Nat.div a c ≤ Nat.div a b :=
  (nat_le_div_iff_mul_le hb).2
    (Nat.le_trans (Nat.mul_le_mul_left (Nat.div a c) h)
      (nat_div_mul_le_self a c))

private theorem nat_land_one_eq (k : Nat) :
    Nat.land 1 k = if decide (Nat.mod k 2 = 1) then 1 else 0 := by
  rw [Anneal.NatBitwise.land_eq_bitwise, Anneal.NatBitwise.unfold_eq]
  cases k with
  | zero => rfl
  | succ k' =>
    have hdiv1 : Nat.div 1 2 = 0 := by decide
    have hmod1 : decide (Nat.mod 1 2 = 1) = true := by decide
    have hbw0 : Nat.bitwise and 0 (Nat.div (Nat.succ k') 2) = 0 := by
      rw [Anneal.NatBitwise.unfold_eq]
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

private theorem nat_testBit_two_pow (k i : Nat) :
    (Nat.pow 2 k).testBit i = decide (i = k) := by
  rw [nat_testBit_eq]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    have hne : ¬ (i = k) := Nat.ne_of_lt hlt
    rw [decide_eq_false hne]
    have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hki_pos : 0 < k - i := Nat.zero_lt_sub_of_lt hlt
    have hki_eq : k - i = (k - i - 1) + 1 :=
      Eq.symm (Nat.sub_add_cancel hki_pos)
    have hpow : Nat.pow 2 k = Nat.pow 2 i * Nat.pow 2 (k - i) := by
      have h1 := congrArg (Nat.pow 2) hk
      rw [nat_pow_add] at h1
      exact h1
    have hpow2 : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
      have h1 := congrArg (Nat.pow 2) hki_eq
      rw [nat_pow_succ, Nat.mul_comm] at h1
      exact h1
    rw [hpow, nat_mul_div_right _ (nat_two_pow_pos i), hpow2, nat_mul_mod_right]
    rfl
  | inr hge =>
    cases Nat.lt_or_ge k i with
    | inl hlt =>
      have hne : ¬ (i = k) := Nat.ne_of_gt hlt
      rw [decide_eq_false hne]
      have hpow_lt : Nat.pow 2 k < Nat.pow 2 i := by
        have hle : k + 1 ≤ i := hlt
        have h1 : Nat.pow 2 (k + 1) ≤ Nat.pow 2 i := nat_pow_le_pow_right hle
        have h2 : Nat.pow 2 k < Nat.pow 2 (k + 1) := by
          rw [nat_pow_succ, Nat.mul_two]
          exact Nat.lt_add_of_pos_right (nat_two_pow_pos k)
        exact Nat.lt_of_lt_of_le h2 h1
      rw [nat_div_eq_of_lt hpow_lt, nat_zero_mod]
      rfl
    | inr hle =>
      have heq : i = k := Nat.le_antisymm hle hge
      subst heq
      rw [decide_eq_true rfl, nat_div_self (nat_two_pow_pos i)]
      rfl

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

private theorem nat_lor_add_land (w : Nat) :
    ∀ a b : Nat, a < Nat.pow 2 w → b < Nat.pow 2 w →
      Nat.lor a b + Nat.land a b = a + b := by
  induction w with
  | zero =>
    intro a b ha hb
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    subst ha0
    subst hb0
    rfl
  | succ w ih =>
    intro a b ha hb
    have ha2 : Nat.div a 2 < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), ← nat_pow_succ]
      exact ha
    have hb2 : Nat.div b 2 < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), ← nat_pow_succ]
      exact hb
    have hrec := ih (Nat.div a 2) (Nat.div b 2) ha2 hb2
    have hlor_div : Nat.div (Nat.lor a b) 2 = Nat.lor (Nat.div a 2) (Nat.div b 2) := by
      have hbv := Anneal.BitVec.eq_of_getLsbD_eq (w := w)
        (a := BitVec.ofNatLT (Nat.div (Nat.lor a b) 2)
          ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
            (Anneal.NatBitwise.lor_lt_two_pow ha hb)))
        (b := BitVec.ofNatLT (Nat.lor (Nat.div a 2) (Nat.div b 2))
          (Anneal.NatBitwise.lor_lt_two_pow ha2 hb2))
      have hEq :
          BitVec.ofNatLT (Nat.div (Nat.lor a b) 2)
            ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
              (Anneal.NatBitwise.lor_lt_two_pow ha hb)) =
          BitVec.ofNatLT (Nat.lor (Nat.div a 2) (Nat.div b 2))
            (Anneal.NatBitwise.lor_lt_two_pow ha2 hb2) := by
        apply hbv
        intro i _
        change (Nat.div (Nat.lor a b) 2).testBit i =
          (Nat.lor (Nat.div a 2) (Nat.div b 2)).testBit i
        rw [← nat_testBit_succ (Nat.lor a b) i]
        have h1 := Anneal.BitVec.testBit_or
          (BitVec.ofNatLT a ha) (BitVec.ofNatLT b hb) (i + 1)
        have h2 := Anneal.BitVec.testBit_or
          (BitVec.ofNatLT (Nat.div a 2) ha2)
          (BitVec.ofNatLT (Nat.div b 2) hb2) i
        change (Nat.lor a b).testBit (i + 1) =
          (a.testBit (i + 1) || b.testBit (i + 1)) at h1
        change (Nat.lor (Nat.div a 2) (Nat.div b 2)).testBit i =
          ((Nat.div a 2).testBit i || (Nat.div b 2).testBit i) at h2
        rw [h1, h2, nat_testBit_succ, nat_testBit_succ]
      exact congrArg BitVec.toNat hEq
    have hland_div :
        Nat.div (Nat.land a b) 2 = Nat.land (Nat.div a 2) (Nat.div b 2) := by
      have hEq :
          BitVec.ofNatLT (Nat.div (Nat.land a b) 2)
            ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
              (Anneal.NatBitwise.land_lt_two_pow ha hb)) =
          BitVec.ofNatLT (Nat.land (Nat.div a 2) (Nat.div b 2))
            (Anneal.NatBitwise.land_lt_two_pow ha2 hb2) := by
        apply Anneal.BitVec.eq_of_getLsbD_eq
        intro i _
        change (Nat.div (Nat.land a b) 2).testBit i =
          (Nat.land (Nat.div a 2) (Nat.div b 2)).testBit i
        rw [← nat_testBit_succ (Nat.land a b) i]
        have h1 := Anneal.BitVec.testBit_and
          (BitVec.ofNatLT a ha) (BitVec.ofNatLT b hb) (i + 1)
        have h2 := Anneal.BitVec.testBit_and
          (BitVec.ofNatLT (Nat.div a 2) ha2)
          (BitVec.ofNatLT (Nat.div b 2) hb2) i
        change (Nat.land a b).testBit (i + 1) =
          (a.testBit (i + 1) && b.testBit (i + 1)) at h1
        change (Nat.land (Nat.div a 2) (Nat.div b 2)).testBit i =
          ((Nat.div a 2).testBit i && (Nat.div b 2).testBit i) at h2
        rw [h1, h2, nat_testBit_succ, nat_testBit_succ]
      exact congrArg BitVec.toNat hEq
    have hmod_sum :
        Nat.mod (Nat.lor a b) 2 + Nat.mod (Nat.land a b) 2 =
          Nat.mod a 2 + Nat.mod b 2 := by
      have hor0 := Anneal.BitVec.testBit_or
        (BitVec.ofNatLT a ha) (BitVec.ofNatLT b hb) 0
      have hand0 := Anneal.BitVec.testBit_and
        (BitVec.ofNatLT a ha) (BitVec.ofNatLT b hb) 0
      change (Nat.lor a b).testBit 0 = (a.testBit 0 || b.testBit 0) at hor0
      change (Nat.land a b).testBit 0 = (a.testBit 0 && b.testBit 0) at hand0
      rw [nat_testBit_zero_bit, nat_testBit_zero_bit, nat_testBit_zero_bit]
        at hor0 hand0
      cases nat_mod_two_cases a with
      | inl ha0 =>
        cases nat_mod_two_cases b with
        | inl hb0 =>
          rw [ha0, hb0] at hor0 hand0
          cases nat_mod_two_cases (Nat.lor a b) with
          | inl ho0 =>
            cases nat_mod_two_cases (Nat.land a b) with
            | inl hn0 => rw [ha0, hb0, ho0, hn0]
            | inr hn1 => rw [hn1] at hand0; nomatch hand0
          | inr ho1 => rw [ho1] at hor0; nomatch hor0
        | inr hb1 =>
          rw [ha0, hb1] at hor0 hand0
          cases nat_mod_two_cases (Nat.lor a b) with
          | inl ho0 => rw [ho0] at hor0; nomatch hor0
          | inr ho1 =>
            cases nat_mod_two_cases (Nat.land a b) with
            | inl hn0 => rw [ha0, hb1, ho1, hn0]
            | inr hn1 => rw [hn1] at hand0; nomatch hand0
      | inr ha1 =>
        cases nat_mod_two_cases b with
        | inl hb0 =>
          rw [ha1, hb0] at hor0 hand0
          cases nat_mod_two_cases (Nat.lor a b) with
          | inl ho0 => rw [ho0] at hor0; nomatch hor0
          | inr ho1 =>
            cases nat_mod_two_cases (Nat.land a b) with
            | inl hn0 => rw [ha1, hb0, ho1, hn0]
            | inr hn1 => rw [hn1] at hand0; nomatch hand0
        | inr hb1 =>
          rw [ha1, hb1] at hor0 hand0
          cases nat_mod_two_cases (Nat.lor a b) with
          | inl ho0 => rw [ho0] at hor0; nomatch hor0
          | inr ho1 =>
            cases nat_mod_two_cases (Nat.land a b) with
            | inl hn0 => rw [hn0] at hand0; nomatch hand0
            | inr hn1 => rw [ha1, hb1, ho1, hn1]
    have hdecomp :
        Nat.lor a b + Nat.land a b =
          2 * (Nat.div (Nat.lor a b) 2 + Nat.div (Nat.land a b) 2) +
          (Nat.mod (Nat.lor a b) 2 + Nat.mod (Nat.land a b) 2) := by
      rw [Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm (2 * Nat.div (Nat.land a b) 2),
        ← Nat.add_assoc, nat_div_add_mod (Nat.lor a b) 2,
        nat_div_add_mod (Nat.land a b) 2]
    have hdecomp_ab :
        a + b =
          2 * (Nat.div a 2 + Nat.div b 2) + (Nat.mod a 2 + Nat.mod b 2) := by
      rw [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm (2 * Nat.div b 2),
        ← Nat.add_assoc, nat_div_add_mod a 2, nat_div_add_mod b 2]
    rw [hdecomp, hdecomp_ab, hlor_div, hland_div, hrec, hmod_sum]

private theorem toNat_or_add_and {w : Nat} (a b : BitVec w) :
    (Anneal.BitVec.or a b).toNat + (Anneal.BitVec.and a b).toNat =
      a.toNat + b.toNat :=
  nat_lor_add_land w a.toNat b.toNat a.isLt b.isLt

private theorem toNat_or_of_and_eq_zero {w : Nat} {a b : BitVec w}
    (h : Anneal.BitVec.and a b = BitVec.ofNat w 0) :
    (Anneal.BitVec.or a b).toNat = a.toNat + b.toNat := by
  have hsum := toNat_or_add_and a b
  rw [h, Anneal.BitVec.toNat_zero, Nat.add_zero] at hsum
  exact hsum

private theorem nat_add_mod_cancel_left (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  have h1 := nat_div_add_mod a m
  rw [Nat.add_comm (m * Nat.div a m) (Nat.mod a m)] at h1
  have h2 : a + b = (Nat.mod a m + b) + m * Nat.div a m := by
    have h3 := congrArg (fun z => z + b) (Eq.symm h1)
    rw [Nat.add_right_comm] at h3
    exact h3
  rw [h2, nat_add_mul_mod_self_left]

private theorem nat_add_mod_cancel_right (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm a (Nat.mod b m), nat_add_mod_cancel_left, Nat.add_comm]

private theorem nat_testBit_add_add_bit (a b : Nat) {c : Nat} (hc : c ≤ 1)
    (i : Nat) :
    (a + b + c).testBit i =
      if i = 0 then
        ((a.testBit 0 != b.testBit 0) != decide (c = 1))
      else
        ((a.testBit i != b.testBit i) !=
          decide (Nat.pow 2 i ≤
            Nat.mod a (Nat.pow 2 i) + Nat.mod b (Nat.pow 2 i) + c)) := by
  cases i with
  | zero =>
    rw [ite_prop_true rfl, nat_testBit_zero_bit, nat_testBit_zero_bit,
      nat_testBit_zero_bit]
    have hmod :
        Nat.mod (a + b + c) 2 = Nat.mod (Nat.mod a 2 + Nat.mod b 2 + c) 2 := by
      have h1 : Nat.mod (a + b + c) 2 = Nat.mod (Nat.mod (a + b) 2 + c) 2 :=
        Eq.symm (nat_add_mod_cancel_left (a + b) c 2)
      rw [← nat_add_mod_cancel_left a b 2,
        ← nat_add_mod_cancel_right (Nat.mod a 2) b 2,
        nat_add_mod_cancel_left] at h1
      exact h1
    rw [hmod]
    cases c with
    | zero =>
      cases nat_mod_two_cases a with
      | inl ha0 =>
        cases nat_mod_two_cases b with
        | inl hb0 => rw [ha0, hb0]; rfl
        | inr hb1 => rw [ha0, hb1]; rfl
      | inr ha1 =>
        cases nat_mod_two_cases b with
        | inl hb0 => rw [ha1, hb0]; rfl
        | inr hb1 => rw [ha1, hb1]; rfl
    | succ c' =>
      have hc0 : c' = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hc)
      subst hc0
      cases nat_mod_two_cases a with
      | inl ha0 =>
        cases nat_mod_two_cases b with
        | inl hb0 => rw [ha0, hb0]; rfl
        | inr hb1 => rw [ha0, hb1]; rfl
      | inr ha1 =>
        cases nat_mod_two_cases b with
        | inl hb0 => rw [ha1, hb0]; rfl
        | inr hb1 => rw [ha1, hb1]; rfl
  | succ i' =>
    rw [ite_prop_false (fun h => nomatch h)]
    let p := Nat.pow 2 (i' + 1)
    have hp_pos : 0 < p := nat_two_pow_pos (i' + 1)
    let qa := Nat.div a p
    let ra := Nat.mod a p
    let qb := Nat.div b p
    let rb := Nat.mod b p
    have hra : ra < p := nat_mod_lt a hp_pos
    have hrb : rb < p := nat_mod_lt b hp_pos
    have hdecomp : a + b + c = (ra + rb + c) + p * (qa + qb) := by
      have ha_eq : p * qa + ra = a := nat_div_add_mod a p
      have hb_eq : p * qb + rb = b := nat_div_add_mod b p
      rw [← ha_eq, ← hb_eq, Nat.mul_add]
      rw [Nat.add_assoc (p * qa) ra (p * qb + rb)]
      rw [Nat.add_left_comm ra (p * qb) rb]
      rw [← Nat.add_assoc (p * qa) (p * qb) (ra + rb)]
      rw [Nat.add_assoc (p * qa + p * qb) (ra + rb) c]
      rw [Nat.add_comm (p * qa + p * qb) (ra + rb + c)]
    have hdiv : Nat.div (a + b + c) p = Nat.div (ra + rb + c) p + (qa + qb) := by
      rw [hdecomp, nat_add_mul_div_left _ _ hp_pos]
    have hsum_lt : ra + rb + c < p + p := by
      have h1 : ra + 1 ≤ p := hra
      have h2 : rb + c ≤ p := by
        cases c with
        | zero =>
          rw [Nat.add_zero]
          exact Nat.le_of_lt hrb
        | succ c' =>
          have hc0 : c' = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hc)
          subst hc0
          exact hrb
      have h3 : (ra + 1) + (rb + c) ≤ p + p := Nat.add_le_add h1 h2
      have h4 : ra + rb + c + 1 = (ra + 1) + (rb + c) := by
        rw [Nat.add_assoc ra 1 (rb + c), Nat.add_comm 1 (rb + c),
          ← Nat.add_assoc ra (rb + c) 1, ← Nat.add_assoc ra rb c]
      rw [← h4] at h3
      exact h3
    have hcarry_div :
        Nat.div (ra + rb + c) p = if decide (p ≤ ra + rb + c) then 1 else 0 := by
      cases Nat.lt_or_ge (ra + rb + c) p with
      | inl hlt =>
        rw [decide_eq_false (Nat.not_le_of_gt hlt), ite_bool_false]
        exact nat_div_eq_of_lt hlt
      | inr hge =>
        rw [decide_eq_true hge, ite_bool_true]
        have hrem_lt : ra + rb + c - p < p := by
          have h1 : (ra + rb + c - p) + p < p + p := by
            rw [Nat.sub_add_cancel hge]
            exact hsum_lt
          exact nat_lt_of_add_lt_add_right h1
        have hsplit : ra + rb + c = (ra + rb + c - p) + p * 1 := by
          rw [Nat.mul_one, Nat.sub_add_cancel hge]
        rw [hsplit, nat_add_mul_div_left _ _ hp_pos, nat_div_eq_of_lt hrem_lt,
          Nat.zero_add]
    rw [nat_testBit_eq, nat_testBit_eq, nat_testBit_eq]
    change decide (Nat.mod (Nat.div (a + b + c) p) 2 = 1) =
      ((decide (Nat.mod qa 2 = 1) != decide (Nat.mod qb 2 = 1)) !=
        decide (p ≤ ra + rb + c))
    rw [hdiv, hcarry_div]
    have hmod2 :
        Nat.mod ((if decide (p ≤ ra + rb + c) then 1 else 0) + (qa + qb)) 2 =
          Nat.mod ((if decide (p ≤ ra + rb + c) then 1 else 0) +
            (Nat.mod qa 2 + Nat.mod qb 2)) 2 := by
      have h1 :
          Nat.mod ((if decide (p ≤ ra + rb + c) then 1 else 0) + (qa + qb)) 2 =
            Nat.mod ((if decide (p ≤ ra + rb + c) then 1 else 0) +
              Nat.mod (qa + qb) 2) 2 :=
        Eq.symm (nat_add_mod_cancel_right _ (qa + qb) 2)
      rw [← nat_add_mod_cancel_left qa qb 2,
        ← nat_add_mod_cancel_right (Nat.mod qa 2) qb 2,
        nat_add_mod_cancel_right] at h1
      exact h1
    rw [hmod2]
    cases decide (p ≤ ra + rb + c) with
    | false =>
      rw [ite_bool_false]
      cases nat_mod_two_cases qa with
      | inl ha0 =>
        cases nat_mod_two_cases qb with
        | inl hb0 => rw [ha0, hb0]; rfl
        | inr hb1 => rw [ha0, hb1]; rfl
      | inr ha1 =>
        cases nat_mod_two_cases qb with
        | inl hb0 => rw [ha1, hb0]; rfl
        | inr hb1 => rw [ha1, hb1]; rfl
    | true =>
      rw [ite_bool_true]
      cases nat_mod_two_cases qa with
      | inl ha0 =>
        cases nat_mod_two_cases qb with
        | inl hb0 => rw [ha0, hb0]; rfl
        | inr hb1 => rw [ha0, hb1]; rfl
      | inr ha1 =>
        cases nat_mod_two_cases qb with
        | inl hb0 => rw [ha1, hb0]; rfl
        | inr hb1 => rw [ha1, hb1]; rfl

private theorem bool_bne_cancel_left {a b c : Bool}
    (h : (a != b) = (a != c)) : b = c := by
  cases a <;> cases b <;> cases c <;> first | rfl | nomatch h

/-! ## Part 1: Two's-Complement Signed Bit-Vectors -/

/-- Most-significant bit of a `w`-bit bitvector (`false` when `w = 0`),
definitionally equal to `BitVec.msb x`. -/
@[expose] def msb {w : Nat} (x : BitVec w) : Bool :=
  decide (0 < w) && Anneal.BitVec.getLsbD x (w - 1)

/-- Conditional characterization of `msb`. -/
theorem msb_eq_ite {w : Nat} (x : BitVec w) :
    msb x = if w = 0 then false else Anneal.BitVec.getLsbD x (w - 1) := by
  cases w with
  | zero => rfl
  | succ w' =>
    unfold msb
    rw [decide_eq_true (Nat.zero_lt_succ w'), Bool.true_and,
      ite_prop_false (fun h => nomatch h)]

/-- The most-significant bit of a zero-width bitvector is `false`. -/
@[simp] theorem msb_zero (x : BitVec 0) : msb x = false :=
  rfl

/-- For positive width `w > 0`, `msb x` is bit `w - 1` of `x`. -/
theorem msb_of_pos {w : Nat} (hw : 0 < w) (x : BitVec w) :
    msb x = Anneal.BitVec.getLsbD x (w - 1) := by
  unfold msb
  rw [decide_eq_true hw, Bool.true_and]

/-- For `w > 0`, `msb x = true` if and only if `2^(w - 1) ≤ x.toNat`. -/
theorem msb_eq_true_iff {w : Nat} (hw : 0 < w) (x : BitVec w) :
    msb x = true ↔ Nat.pow 2 (w - 1) ≤ x.toNat := by
  rw [msb_of_pos hw]
  unfold Anneal.BitVec.getLsbD
  rw [nat_testBit_eq]
  have hp : 0 < Nat.pow 2 (w - 1) := nat_two_pow_pos (w - 1)
  have hlt2 : Nat.div x.toNat (Nat.pow 2 (w - 1)) < 2 := by
    rw [nat_div_lt_iff_lt_mul hp, Nat.mul_comm, ← nat_pow_succ,
      Nat.sub_add_cancel hw]
    exact x.isLt
  constructor
  · intro h
    cases hq : Nat.div x.toNat (Nat.pow 2 (w - 1)) with
    | zero =>
      rw [hq] at h
      nomatch h
    | succ q' =>
      have h1le : 1 ≤ Nat.div x.toNat (Nat.pow 2 (w - 1)) := by
        rw [hq]
        exact Nat.succ_le_succ (Nat.zero_le q')
      have hmul := (nat_le_div_iff_mul_le hp).1 h1le
      rw [Nat.one_mul] at hmul
      exact hmul
  · intro hge
    have h1le : 1 ≤ Nat.div x.toNat (Nat.pow 2 (w - 1)) := by
      rw [nat_le_div_iff_mul_le hp, Nat.one_mul]
      exact hge
    have hq1 : Nat.div x.toNat (Nat.pow 2 (w - 1)) = 1 :=
      Nat.le_antisymm (Nat.le_of_lt_succ hlt2) h1le
    rw [hq1]
    rfl

/-- For `w > 0`, `msb x = false` if and only if `x.toNat < 2^(w - 1)`. -/
theorem msb_eq_false_iff {w : Nat} (hw : 0 < w) (x : BitVec w) :
    msb x = false ↔ x.toNat < Nat.pow 2 (w - 1) := by
  constructor
  · intro hf
    cases Nat.lt_or_ge x.toNat (Nat.pow 2 (w - 1)) with
    | inl hlt => exact hlt
    | inr hge =>
      have ht := (msb_eq_true_iff hw x).2 hge
      rw [hf] at ht
      nomatch ht
  · intro hlt
    cases hm : msb x with
    | false => rfl
    | true =>
      have hge := (msb_eq_true_iff hw x).1 hm
      exact False.elim (Nat.not_lt_of_ge hge hlt)

/-- Two's-complement negation of a `w`-bit bitvector, definitionally equal to
`-x` (`BitVec.neg x`). -/
@[expose] def neg {w : Nat} (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (Nat.pow 2 w - x.toNat)

/-- `toNat` characterization of `neg x`. -/
@[simp] theorem toNat_neg {w : Nat} (x : BitVec w) :
    (neg x).toNat = Nat.mod (Nat.pow 2 w - x.toNat) (Nat.pow 2 w) :=
  rfl

/-- Exact `toNat` of `neg x` when `x.toNat > 0`. -/
theorem toNat_neg_of_pos {w : Nat} {x : BitVec w} (hx : 0 < x.toNat) :
    (neg x).toNat = Nat.pow 2 w - x.toNat :=
  Nat.mod_eq_of_lt (Nat.sub_lt (nat_two_pow_pos w) hx)

/-- Two's-complement negation of `0#w` is `0#w`. -/
@[simp] theorem neg_zero (w : Nat) :
    neg (BitVec.ofNat w 0) = BitVec.ofNat w 0 := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_neg, Anneal.BitVec.toNat_zero, Nat.sub_zero, nat_mod_self]

/-- Two's-complement negation is an involution (`-(-x) = x`). -/
@[simp] theorem neg_neg {w : Nat} (x : BitVec w) :
    neg (neg x) = x := by
  cases hx : x.toNat with
  | zero =>
    have hx0 : x = BitVec.ofNat w 0 :=
      Anneal.BitVec.eq_of_toNat_eq (Eq.trans hx (Eq.symm (Anneal.BitVec.toNat_zero w)))
    rw [hx0, neg_zero, neg_zero]
  | succ k =>
    have hpos : 0 < x.toNat := by
      rw [hx]
      exact Nat.zero_lt_succ k
    have hneg_pos : 0 < (neg x).toNat := by
      rw [toNat_neg_of_pos hpos]
      exact Nat.zero_lt_sub_of_lt x.isLt
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_neg_of_pos hneg_pos, toNat_neg_of_pos hpos]
    exact nat_sub_sub_self (Nat.le_of_lt x.isLt)

/-- Additive inverse law (`x + (-x) = 0#w`). -/
@[simp] theorem add_neg_self {w : Nat} (x : BitVec w) :
    x + neg x = BitVec.ofNat w 0 := by
  cases hx : x.toNat with
  | zero =>
    have hx0 : x = BitVec.ofNat w 0 :=
      Anneal.BitVec.eq_of_toNat_eq (Eq.trans hx (Eq.symm (Anneal.BitVec.toNat_zero w)))
    rw [hx0, neg_zero]
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.add_zero,
      nat_zero_mod]
  | succ k =>
    have hpos : 0 < x.toNat := by
      rw [hx]
      exact Nat.zero_lt_succ k
    have hxle : x.toNat ≤ Nat.pow 2 w := Nat.le_of_lt x.isLt
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, toNat_neg_of_pos hpos, Anneal.BitVec.toNat_zero,
      Nat.add_comm, Nat.sub_add_cancel hxle, nat_mod_self]

/-- Left additive inverse law (`(-x) + x = 0#w`). -/
@[simp] theorem neg_add_self {w : Nat} (x : BitVec w) :
    neg x + x = BitVec.ofNat w 0 := by
  have hcomm : neg x + x = x + neg x := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add, Nat.add_comm]
  rw [hcomm, add_neg_self]

/-- Bitvector subtraction equals adding the two's-complement negation. -/
theorem sub_eq_add_neg {w : Nat} (a b : BitVec w) :
    a - b = a + neg b := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_sub, Anneal.BitVec.toNat_add, toNat_neg,
    nat_add_mod_cancel_right, Nat.add_comm]

/-- Exact `toNat` of bitwise complement (`(~~~x).toNat = 2^w - 1 - x.toNat`).
-/
theorem toNat_not_eq_sub {w : Nat} (x : BitVec w) :
    (Anneal.BitVec.not x).toNat = Nat.pow 2 w - 1 - x.toNat := by
  have hsum := toNat_or_of_and_eq_zero (Anneal.BitVec.and_not_self x)
  rw [Anneal.BitVec.or_not_self, Anneal.BitVec.toNat_allOnes] at hsum
  have h1 := congrArg (fun z => z - x.toNat) (Eq.symm hsum)
  rw [Nat.add_comm x.toNat (Anneal.BitVec.not x).toNat, Nat.add_sub_cancel] at h1
  exact h1

/-- Two's-complement identity: `-x = ~~~x + 1#w`. -/
theorem neg_eq_not_add_one {w : Nat} (x : BitVec w) :
    neg x = Anneal.BitVec.not x + BitVec.ofNat w 1 := by
  cases w with
  | zero =>
    apply Anneal.BitVec.eq_of_toNat_eq
    have h1 : (neg x).toNat = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (neg x).isLt)
    have h2 : (Anneal.BitVec.not x + BitVec.ofNat 0 1).toNat = 0 :=
      Nat.eq_zero_of_le_zero
        (Nat.le_of_lt_succ (Anneal.BitVec.not x + BitVec.ofNat 0 1).isLt)
    rw [h1, h2]
  | succ w' =>
    have h1lt : 1 < Nat.pow 2 (w' + 1) := by
      rw [nat_pow_succ, Nat.mul_two]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
        (Nat.add_le_add (nat_two_pow_pos w') (nat_two_pow_pos w'))
    have hxle : x.toNat ≤ Nat.pow 2 (w' + 1) - 1 :=
      Nat.le_sub_one_of_lt x.isLt
    have hsub1 : (Nat.pow 2 (w' + 1) - 1 - x.toNat) + 1 =
        Nat.pow 2 (w' + 1) - x.toNat := by
      rw [nat_sub_add_comm hxle, Nat.sub_add_cancel (nat_two_pow_pos (w' + 1))]
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_neg, Anneal.BitVec.toNat_add, toNat_not_eq_sub,
      Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt h1lt, hsub1]

/-- Sign-bit mask (`2^(w - 1)` when `w > 0`, and `0#0` when `w = 0`). -/
@[expose] def signBit {w : Nat} : BitVec w :=
  if w = 0 then BitVec.ofNat w 0 else BitVec.ofNat w (Nat.pow 2 (w - 1))

/-- Exact `toNat` of `signBit` when `w > 0`. -/
theorem toNat_signBit_of_pos {w : Nat} (hw : 0 < w) :
    (signBit (w := w)).toNat = Nat.pow 2 (w - 1) := by
  unfold signBit
  rw [ite_prop_false (Nat.ne_of_gt hw), Anneal.BitVec.toNat_ofNat]
  exact nat_mod_eq_of_lt (nat_two_pow_sub_one_lt hw)

/-- Bit characterization of `signBit`. -/
@[simp] theorem getLsbD_signBit {w : Nat} (i : Nat) :
    Anneal.BitVec.getLsbD (signBit (w := w)) i =
      (decide (0 < w) && decide (i = w - 1)) := by
  cases w with
  | zero =>
    unfold signBit
    rw [ite_prop_true rfl, Anneal.BitVec.getLsbD_zero]
    rfl
  | succ w' =>
    unfold signBit
    rw [ite_prop_false (fun h => nomatch h), Anneal.BitVec.getLsbD_ofNat,
      decide_eq_true (Nat.zero_lt_succ w'), Bool.true_and, nat_testBit_two_pow]
    cases Nat.lt_or_ge i (w' + 1) with
    | inl hlt =>
      rw [decide_eq_true hlt, Bool.true_and]
    | inr hge =>
      have hne : ¬ (i = w' + 1 - 1) :=
        Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self w') hge)
      rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and,
        decide_eq_false hne]

/-- Order-preserving unsigned key for signed two's-complement comparison
(`(x ^^^ signBit).toNat`). Maps `INT_MIN` to `0`, `0` to `2^(w - 1)`, and
`INT_MAX` to `2^w - 1`. -/
@[expose] def signedKey {w : Nat} (x : BitVec w) : Nat :=
  (Anneal.BitVec.xor x signBit).toNat

/-- Upper bound `signedKey x < 2^w`. -/
theorem signedKey_lt {w : Nat} (x : BitVec w) :
    signedKey x < Nat.pow 2 w :=
  (Anneal.BitVec.xor x signBit).isLt

/-- `signedKey` is injective because XOR with `signBit` is an involution. -/
theorem signedKey_injective {w : Nat} {a b : BitVec w}
    (h : signedKey a = signedKey b) : a = b := by
  have hxor : Anneal.BitVec.xor a signBit = Anneal.BitVec.xor b signBit :=
    Anneal.BitVec.eq_of_toNat_eq h
  have h2 := congrArg (fun z => Anneal.BitVec.xor z signBit) hxor
  rw [Anneal.BitVec.xor_assoc, Anneal.BitVec.xor_assoc,
    Anneal.BitVec.xor_self, Anneal.BitVec.xor_zero, Anneal.BitVec.xor_zero] at h2
  exact h2

/-- For `w > 0` and non-negative `x` (`msb x = false`),
`signedKey x = x.toNat + 2^(w - 1)`. -/
theorem signedKey_eq_of_msb_false {w : Nat} (hw : 0 < w) {x : BitVec w}
    (h : msb x = false) :
    signedKey x = x.toNat + Nat.pow 2 (w - 1) := by
  have hdisj : Anneal.BitVec.and x signBit = BitVec.ofNat w 0 := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i _
    rw [Anneal.BitVec.getLsbD_and, getLsbD_signBit, decide_eq_true hw,
      Bool.true_and, Anneal.BitVec.getLsbD_zero]
    cases (inferInstance : Decidable (i = w - 1)) with
    | isTrue heq =>
      subst heq
      rw [decide_eq_true rfl, Bool.and_true, ← msb_of_pos hw, h]
    | isFalse hne =>
      rw [decide_eq_false hne, Bool.and_false]
  have hxor_or : Anneal.BitVec.xor x signBit = Anneal.BitVec.or x signBit := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i _
    rw [Anneal.BitVec.getLsbD_xor, Anneal.BitVec.getLsbD_or,
      getLsbD_signBit, decide_eq_true hw, Bool.true_and]
    cases (inferInstance : Decidable (i = w - 1)) with
    | isTrue heq =>
      subst heq
      rw [decide_eq_true rfl, ← msb_of_pos hw, h]
      rfl
    | isFalse hne =>
      rw [decide_eq_false hne]
      cases Anneal.BitVec.getLsbD x i <;> rfl
  unfold signedKey
  rw [hxor_or, toNat_or_of_and_eq_zero hdisj, toNat_signBit_of_pos hw]

/-- For `w > 0` and negative `x` (`msb x = true`),
`signedKey x = x.toNat - 2^(w - 1)`. -/
theorem signedKey_eq_of_msb_true {w : Nat} (hw : 0 < w) {x : BitVec w}
    (h : msb x = true) :
    signedKey x = x.toNat - Nat.pow 2 (w - 1) := by
  have hdisj :
      Anneal.BitVec.and (Anneal.BitVec.xor x signBit) signBit =
        BitVec.ofNat w 0 := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i _
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_xor,
      getLsbD_signBit, decide_eq_true hw, Bool.true_and,
      Anneal.BitVec.getLsbD_zero]
    cases (inferInstance : Decidable (i = w - 1)) with
    | isTrue heq =>
      subst heq
      rw [decide_eq_true rfl, ← msb_of_pos hw, h]
      rfl
    | isFalse hne =>
      rw [decide_eq_false hne, Bool.and_false]
  have hor_eq :
      Anneal.BitVec.or (Anneal.BitVec.xor x signBit) signBit = x := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i _
    rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_xor,
      getLsbD_signBit, decide_eq_true hw, Bool.true_and]
    cases (inferInstance : Decidable (i = w - 1)) with
    | isTrue heq =>
      subst heq
      rw [decide_eq_true rfl, ← msb_of_pos hw, h]
      rfl
    | isFalse hne =>
      rw [decide_eq_false hne]
      cases Anneal.BitVec.getLsbD x i <;> rfl
  have hsum := toNat_or_of_and_eq_zero hdisj
  rw [hor_eq, toNat_signBit_of_pos hw] at hsum
  have h1 := congrArg (fun z => z - Nat.pow 2 (w - 1)) hsum
  rw [Nat.add_sub_cancel] at h1
  exact Eq.symm h1

/-- For `w > 0` and negative `x` (`msb x = true`),
`signedKey x < 2^(w - 1)`. -/
theorem signedKey_lt_half_of_msb_true {w : Nat} (hw : 0 < w) {x : BitVec w}
    (h : msb x = true) :
    signedKey x < Nat.pow 2 (w - 1) := by
  rw [signedKey_eq_of_msb_true hw h]
  have hge := (msb_eq_true_iff hw x).1 h
  have h1 : (x.toNat - Nat.pow 2 (w - 1)) + Nat.pow 2 (w - 1) <
      Nat.pow 2 (w - 1) + Nat.pow 2 (w - 1) := by
    rw [Nat.sub_add_cancel hge, ← nat_two_pow_split hw]
    exact x.isLt
  exact nat_lt_of_add_lt_add_right h1

/-- For `w > 0` and non-negative `x` (`msb x = false`),
`2^(w - 1) ≤ signedKey x`. -/
theorem half_le_signedKey_of_msb_false {w : Nat} (hw : 0 < w) {x : BitVec w}
    (h : msb x = false) :
    Nat.pow 2 (w - 1) ≤ signedKey x := by
  rw [signedKey_eq_of_msb_false hw h]
  exact Nat.le_add_left (Nat.pow 2 (w - 1)) x.toNat

/-- Signed less-than-or-equal on `BitVec w` via `signedKey`. -/
@[expose] def sle {w : Nat} (a b : BitVec w) : Prop :=
  signedKey a ≤ signedKey b

/-- Signed strict less-than on `BitVec w` via `signedKey`. -/
@[expose] def slt {w : Nat} (a b : BitVec w) : Prop :=
  signedKey a < signedKey b

/-- Reflexivity of `sle`. -/
theorem sle_refl {w : Nat} (a : BitVec w) : sle a a :=
  Nat.le_refl (signedKey a)

/-- Transitivity of `sle`. -/
theorem sle_trans {w : Nat} {a b c : BitVec w}
    (hab : sle a b) (hbc : sle b c) : sle a c :=
  Nat.le_trans hab hbc

/-- Antisymmetry of `sle`. -/
theorem sle_antisymm {w : Nat} {a b : BitVec w}
    (hab : sle a b) (hba : sle b a) : a = b :=
  signedKey_injective (Nat.le_antisymm hab hba)

/-- Totality of `sle`. -/
theorem sle_total {w : Nat} (a b : BitVec w) : sle a b ∨ sle b a :=
  Nat.le_total (signedKey a) (signedKey b)

/-- Strict signed order is equivalent to non-strict order plus inequality. -/
theorem slt_iff_sle_and_ne {w : Nat} {a b : BitVec w} :
    slt a b ↔ sle a b ∧ a ≠ b := by
  unfold slt sle
  constructor
  · intro hlt
    exact ⟨Nat.le_of_lt hlt,
      fun heq => Nat.ne_of_lt hlt (congrArg signedKey heq)⟩
  · intro h
    exact Nat.lt_of_le_of_ne h.1 (fun heq => h.2 (signedKey_injective heq))

/-- Non-strict signed order is equivalent to strict order or equality. -/
theorem sle_iff_slt_or_eq {w : Nat} {a b : BitVec w} :
    sle a b ↔ slt a b ∨ a = b := by
  unfold sle slt
  constructor
  · intro hle
    cases Nat.lt_or_ge (signedKey a) (signedKey b) with
    | inl hlt => exact Or.inl hlt
    | inr hge => exact Or.inr (signedKey_injective (Nat.le_antisymm hle hge))
  · intro h
    cases h with
    | inl hlt => exact Nat.le_of_lt hlt
    | inr heq =>
      rw [heq]
      exact Nat.le_refl _

/-- Any negative bitvector is strictly less than any non-negative bitvector. -/
theorem slt_of_msb_true_false {w : Nat} {a b : BitVec w}
    (ha : msb a = true) (hb : msb b = false) : slt a b := by
  cases w with
  | zero =>
    rw [msb_zero] at ha
    nomatch ha
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
    exact Nat.lt_of_lt_of_le (signedKey_lt_half_of_msb_true hw ha)
      (half_le_signedKey_of_msb_false hw hb)

/-- When `a` and `b` have the same sign bit, signed order coincides with
unsigned `toNat` order. -/
theorem sle_iff_toNat_le_of_same_msb {w : Nat} {a b : BitVec w}
    (h : msb a = msb b) : sle a b ↔ a.toNat ≤ b.toNat := by
  cases w with
  | zero =>
    unfold sle
    have ha0 : a.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ a.isLt)
    have hb0 : b.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ b.isLt)
    have hka0 : signedKey a = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt a))
    have hkb0 : signedKey b = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt b))
    rw [ha0, hb0, hka0, hkb0]
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
    unfold sle
    cases ha : msb a with
    | false =>
      have hb : msb b = false := Eq.trans (Eq.symm h) ha
      rw [signedKey_eq_of_msb_false hw ha, signedKey_eq_of_msb_false hw hb]
      constructor
      · exact Nat.le_of_add_le_add_right
      · intro hle
        exact Nat.add_le_add_right hle (Nat.pow 2 (w' + 1 - 1))
    | true =>
      have hb : msb b = true := Eq.trans (Eq.symm h) ha
      have ha_ge := (msb_eq_true_iff hw a).1 ha
      have hb_ge := (msb_eq_true_iff hw b).1 hb
      rw [signedKey_eq_of_msb_true hw ha, signedKey_eq_of_msb_true hw hb]
      constructor
      · intro hle
        have h1 := Nat.add_le_add_right hle (Nat.pow 2 (w' + 1 - 1))
        rw [Nat.sub_add_cancel ha_ge, Nat.sub_add_cancel hb_ge] at h1
        exact h1
      · intro hle
        exact Nat.sub_le_sub_right hle (Nat.pow 2 (w' + 1 - 1))

/-- When `a` and `b` have the same sign bit, strict signed order coincides with
strict unsigned `toNat` order. -/
theorem slt_iff_toNat_lt_of_same_msb {w : Nat} {a b : BitVec w}
    (h : msb a = msb b) : slt a b ↔ a.toNat < b.toNat := by
  rw [slt_iff_sle_and_ne, sle_iff_toNat_le_of_same_msb h]
  constructor
  · intro ⟨hle, hne⟩
    exact Nat.lt_of_le_of_ne hle
      (fun heq => hne (Anneal.BitVec.eq_of_toNat_eq heq))
  · intro hlt
    exact ⟨Nat.le_of_lt hlt,
      fun heq => Nat.ne_of_lt hlt (congrArg BitVec.toNat heq)⟩

/-- Sign-extend (or truncate when `v ≤ w`) `x : BitVec w` to width `v`,
filling bit positions `w .. v - 1` with `msb x`. Defined purely over `Nat` /
`BitVec.ofNat` without `Int`. -/
@[expose] def signExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  if msb x then
    Anneal.BitVec.or (Anneal.BitVec.setWidth v x)
      (Anneal.BitVec.not (Anneal.BitVec.lowMask v w))
  else
    Anneal.BitVec.setWidth v x

/-- Exact `getLsbD` characterization of `signExtend v x` for all `i : Nat`. -/
@[simp] theorem getLsbD_signExtend {w : Nat} (v : Nat) (x : BitVec w)
    (i : Nat) :
    Anneal.BitVec.getLsbD (signExtend v x) i =
      (decide (i < v) &&
        if i < w then Anneal.BitVec.getLsbD x i else msb x) := by
  unfold signExtend
  cases hm : msb x with
  | false =>
    rw [ite_bool_false, Anneal.BitVec.getLsbD_setWidth]
    cases Nat.lt_or_ge i w with
    | inl hlt =>
      rw [ite_prop_true hlt]
    | inr hge =>
      rw [ite_prop_false (Nat.not_lt_of_ge hge),
        Anneal.BitVec.getLsbD_ge x hge]
  | true =>
    rw [ite_bool_true]
    cases Nat.lt_or_ge i v with
    | inr hgev =>
      rw [Anneal.BitVec.getLsbD_ge _ hgev,
        decide_eq_false (Nat.not_lt_of_ge hgev), Bool.false_and]
    | inl hltv =>
      rw [decide_eq_true hltv, Bool.true_and, Anneal.BitVec.getLsbD_or,
        Anneal.BitVec.getLsbD_setWidth, decide_eq_true hltv, Bool.true_and,
        Anneal.BitVec.getLsbD_not_of_lt _ hltv,
        Anneal.BitVec.getLsbD_lowMask hltv]
      cases Nat.lt_or_ge i w with
      | inl hltw =>
        rw [decide_eq_true hltw, ite_prop_true hltw, Bool.not_true,
          Bool.or_false]
      | inr hgew =>
        rw [decide_eq_false (Nat.not_lt_of_ge hgew),
          ite_prop_false (Nat.not_lt_of_ge hgew), Bool.not_false,
          Bool.or_true]

/-- Exact `testBit` characterization of `signExtend v x` for all `i : Nat`. -/
theorem testBit_signExtend {w : Nat} (v : Nat) (x : BitVec w) (i : Nat) :
    (signExtend v x).toNat.testBit i =
      (decide (i < v) && if i < w then x.toNat.testBit i else msb x) :=
  getLsbD_signExtend v x i

/-- Sign-extending to the same width `w` is the identity. -/
@[simp] theorem signExtend_self {w : Nat} (x : BitVec w) :
    signExtend w x = x := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_signExtend, decide_eq_true hi, Bool.true_and, ite_prop_true hi]

/-- For non-negative `x` (`msb x = false`), `signExtend v x` equals
zero-extension / truncation `Anneal.BitVec.setWidth v x`. -/
theorem signExtend_of_msb_false {w : Nat} (v : Nat) {x : BitVec w}
    (h : msb x = false) :
    signExtend v x = Anneal.BitVec.setWidth v x := by
  unfold signExtend
  rw [h, ite_bool_false]

/-- Truncating back after sign-extending to a wider width `v ≥ w` recovers
`x`. -/
theorem setWidth_signExtend_of_le {w v : Nat} (h : w ≤ v) (x : BitVec w) :
    Anneal.BitVec.setWidth w (signExtend v x) = x := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
    getLsbD_signExtend, decide_eq_true (Nat.lt_of_lt_of_le hi h),
    Bool.true_and, ite_prop_true hi]

/-- Arithmetic right shift of `x : BitVec w` by `k : Nat`, preserving `msb x`
in vacated upper bit positions. -/
@[expose] def ashr {w : Nat} (x : BitVec w) (k : Nat) : BitVec w :=
  if msb x then
    Anneal.BitVec.or (Anneal.BitVec.ushr x k)
      (Anneal.BitVec.not (Anneal.BitVec.lowMask w (w - k)))
  else
    Anneal.BitVec.ushr x k

/-- Exact `getLsbD` characterization of `ashr x k` for all `i : Nat`. -/
@[simp] theorem getLsbD_ashr {w : Nat} (x : BitVec w) (k i : Nat) :
    Anneal.BitVec.getLsbD (ashr x k) i =
      (decide (i < w) &&
        if i + k < w then Anneal.BitVec.getLsbD x (i + k) else msb x) := by
  unfold ashr
  cases hm : msb x with
  | false =>
    rw [ite_bool_false, Anneal.BitVec.getLsbD_ushr]
    cases Nat.lt_or_ge i w with
    | inr hge =>
      rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
      exact Anneal.BitVec.getLsbD_ge x (Nat.le_trans hge (Nat.le_add_right i k))
    | inl hlt =>
      rw [decide_eq_true hlt, Bool.true_and]
      cases Nat.lt_or_ge (i + k) w with
      | inl hlt2 =>
        rw [ite_prop_true hlt2]
      | inr hge2 =>
        rw [ite_prop_false (Nat.not_lt_of_ge hge2),
          Anneal.BitVec.getLsbD_ge x hge2]
  | true =>
    rw [ite_bool_true]
    cases Nat.lt_or_ge i w with
    | inr hge =>
      rw [Anneal.BitVec.getLsbD_ge _ hge,
        decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
    | inl hlt =>
      rw [decide_eq_true hlt, Bool.true_and, Anneal.BitVec.getLsbD_or,
        Anneal.BitVec.getLsbD_ushr, Anneal.BitVec.getLsbD_not_of_lt _ hlt,
        Anneal.BitVec.getLsbD_lowMask hlt]
      cases Nat.lt_or_ge (i + k) w with
      | inl hlt2 =>
        have hk_le : k ≤ w := Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left k i) hlt2)
        have hi_lt : i < w - k := by
          have h1 : i + k < (w - k) + k := by
            rw [Nat.sub_add_cancel hk_le]
            exact hlt2
          exact nat_lt_of_add_lt_add_right h1
        rw [decide_eq_true hi_lt, ite_prop_true hlt2, Bool.not_true,
          Bool.or_false]
      | inr hge2 =>
        have hnot_lt : ¬ (i < w - k) := by
          intro hi_lt
          have hwk_pos : 0 < w - k := Nat.lt_of_le_of_lt (Nat.zero_le i) hi_lt
          have hk_le : k ≤ w := by
            cases Nat.lt_or_ge k w with
            | inl hklt => exact Nat.le_of_lt hklt
            | inr hkge =>
              rw [Nat.sub_eq_zero_of_le hkge] at hwk_pos
              exact False.elim (Nat.not_lt_zero 0 hwk_pos)
          have h1 : i + k < w := by
            have h2 := Nat.add_lt_add_right hi_lt k
            rw [Nat.sub_add_cancel hk_le] at h2
            exact h2
          exact Nat.not_lt_of_ge hge2 h1
        rw [decide_eq_false hnot_lt, ite_prop_false (Nat.not_lt_of_ge hge2),
          Bool.not_false, Bool.or_true]

/-- Exact `testBit` characterization of `ashr x k` for all `i : Nat`. -/
theorem testBit_ashr {w : Nat} (x : BitVec w) (k i : Nat) :
    (ashr x k).toNat.testBit i =
      (decide (i < w) && if i + k < w then x.toNat.testBit (i + k) else msb x) :=
  getLsbD_ashr x k i

/-- Arithmetic right shift by `0` is the identity. -/
@[simp] theorem ashr_zero {w : Nat} (x : BitVec w) :
    ashr x 0 = x := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ashr, decide_eq_true hi, Bool.true_and, Nat.add_zero,
    ite_prop_true hi]

/-- For non-negative `x` (`msb x = false`), `ashr x k` equals logical right
shift `Anneal.BitVec.ushr x k`. -/
theorem ashr_of_msb_false {w : Nat} {x : BitVec w} (k : Nat)
    (h : msb x = false) :
    ashr x k = Anneal.BitVec.ushr x k := by
  unfold ashr
  rw [h, ite_bool_false]

/-- Arithmetic right shift preserves the sign bit `msb` for every width `w`
and shift amount `k`. -/
@[simp] theorem msb_ashr {w : Nat} (x : BitVec w) (k : Nat) :
    msb (ashr x k) = msb x := by
  cases w with
  | zero => rfl
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
    have hlt : w' < w' + 1 := Nat.lt_succ_self w'
    rw [msb_of_pos hw, msb_of_pos hw]
    change Anneal.BitVec.getLsbD (ashr x k) w' = Anneal.BitVec.getLsbD x w'
    rw [getLsbD_ashr, decide_eq_true hlt, Bool.true_and]
    cases k with
    | zero =>
      rw [Nat.add_zero, ite_prop_true hlt]
    | succ k' =>
      have hge : w' + 1 ≤ w' + (k' + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k')) w'
      rw [ite_prop_false (Nat.not_lt_of_ge hge), msb_of_pos hw]
      rfl

/-! ## Part 2: Tnum / `MaskEq` Transfer Functions -/

/-- Exact soundness of tnum truncation and zero-extension (`setWidth`). -/
theorem tnum_setWidth_sound {w : Nat} (v : Nat) {m x val : BitVec w}
    (h : Anneal.BitVec.MaskEq m x val) :
    Anneal.BitVec.MaskEq (Anneal.BitVec.setWidth v m)
      (Anneal.BitVec.setWidth v x) (Anneal.BitVec.setWidth v val) := by
  rw [Anneal.BitVec.maskEq_iff_getLsbD]
  intro i hi hm
  rw [Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and] at hm
  rw [Anneal.BitVec.getLsbD_setWidth, Anneal.BitVec.getLsbD_setWidth,
    decide_eq_true hi, Bool.true_and, Bool.true_and]
  cases Nat.lt_or_ge i w with
  | inl hlt =>
    exact Anneal.BitVec.maskEq_iff_getLsbD.1 h i hlt hm
  | inr hge =>
    rw [Anneal.BitVec.getLsbD_ge x hge, Anneal.BitVec.getLsbD_ge val hge]

/-- Exact soundness of tnum sign-extension (`signExtend`). -/
theorem tnum_signExtend_sound {w : Nat} (v : Nat) {m x val : BitVec w}
    (h : Anneal.BitVec.MaskEq m x val) :
    Anneal.BitVec.MaskEq (signExtend v m) (signExtend v x)
      (signExtend v val) := by
  rw [Anneal.BitVec.maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_signExtend, decide_eq_true hi, Bool.true_and] at hm
  rw [getLsbD_signExtend, getLsbD_signExtend, decide_eq_true hi,
    Bool.true_and, Bool.true_and]
  cases Nat.lt_or_ge i w with
  | inl hlt =>
    rw [ite_prop_true hlt] at hm
    rw [ite_prop_true hlt, ite_prop_true hlt]
    exact Anneal.BitVec.maskEq_iff_getLsbD.1 h i hlt hm
  | inr hge =>
    rw [ite_prop_false (Nat.not_lt_of_ge hge)] at hm
    rw [ite_prop_false (Nat.not_lt_of_ge hge),
      ite_prop_false (Nat.not_lt_of_ge hge)]
    cases w with
    | zero => rfl
    | succ w' =>
      have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
      rw [msb_of_pos hw] at hm
      rw [msb_of_pos hw, msb_of_pos hw]
      exact Anneal.BitVec.maskEq_iff_getLsbD.1 h w' (Nat.lt_succ_self w') hm

/-- Exact soundness of tnum arithmetic right shift (`ashr`). -/
theorem tnum_ashr_sound {w : Nat} {m x val : BitVec w} (k : Nat)
    (h : Anneal.BitVec.MaskEq m x val) :
    Anneal.BitVec.MaskEq (ashr m k) (ashr x k) (ashr val k) := by
  rw [Anneal.BitVec.maskEq_iff_getLsbD]
  intro i hi hm
  rw [getLsbD_ashr, decide_eq_true hi, Bool.true_and] at hm
  rw [getLsbD_ashr, getLsbD_ashr, decide_eq_true hi,
    Bool.true_and, Bool.true_and]
  cases Nat.lt_or_ge (i + k) w with
  | inl hlt =>
    rw [ite_prop_true hlt] at hm
    rw [ite_prop_true hlt, ite_prop_true hlt]
    exact Anneal.BitVec.maskEq_iff_getLsbD.1 h (i + k) hlt hm
  | inr hge =>
    rw [ite_prop_false (Nat.not_lt_of_ge hge)] at hm
    rw [ite_prop_false (Nat.not_lt_of_ge hge),
      ite_prop_false (Nat.not_lt_of_ge hge)]
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ w' =>
      have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
      rw [msb_of_pos hw] at hm
      rw [msb_of_pos hw, msb_of_pos hw]
      exact Anneal.BitVec.maskEq_iff_getLsbD.1 h w' (Nat.lt_succ_self w') hm

private theorem tnum_mod_two_pow_bounds {w : Nat} (i : Nat)
    {m x v : BitVec w}
    (h : Anneal.BitVec.MaskEq m x v)
    (hc : Anneal.BitVec.and v m = BitVec.ofNat w 0) :
    Nat.mod v.toNat (Nat.pow 2 i) ≤ Nat.mod x.toNat (Nat.pow 2 i) ∧
      Nat.mod x.toNat (Nat.pow 2 i) ≤
        Nat.mod (v.toNat + m.toNat) (Nat.pow 2 i) := by
  have hEq_i : Anneal.BitVec.MaskEq (Anneal.BitVec.setWidth i m)
      (Anneal.BitVec.setWidth i x) (Anneal.BitVec.setWidth i v) :=
    tnum_setWidth_sound i h
  have hDisj_i :
      Anneal.BitVec.and (Anneal.BitVec.setWidth i v)
        (Anneal.BitVec.setWidth i m) = BitVec.ofNat i 0 := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_setWidth,
      Anneal.BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and,
      Bool.true_and, Anneal.BitVec.getLsbD_zero]
    have hbit := congrArg (fun z => Anneal.BitVec.getLsbD z j) hc
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_zero] at hbit
    exact hbit
  have hbounds := Anneal.BitVec.tnum_and_bounds_sound hEq_i hDisj_i
  have hor_sw :
      Anneal.BitVec.or (Anneal.BitVec.setWidth i v)
        (Anneal.BitVec.setWidth i m) =
        Anneal.BitVec.setWidth i (Anneal.BitVec.or v m) := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_setWidth,
      Anneal.BitVec.getLsbD_setWidth, Anneal.BitVec.getLsbD_setWidth,
      decide_eq_true hj, Bool.true_and, Bool.true_and, Bool.true_and,
      Anneal.BitVec.getLsbD_or]
  have h1 : Nat.mod v.toNat (Nat.pow 2 i) ≤ Nat.mod x.toNat (Nat.pow 2 i) := by
    have hlo := hbounds.1
    change (Anneal.BitVec.setWidth i v).toNat ≤
      (Anneal.BitVec.setWidth i x).toNat at hlo
    rw [Anneal.BitVec.toNat_setWidth, Anneal.BitVec.toNat_setWidth] at hlo
    exact hlo
  have h2 :
      Nat.mod x.toNat (Nat.pow 2 i) ≤
        Nat.mod (v.toNat + m.toNat) (Nat.pow 2 i) := by
    have hhi := hbounds.2
    rw [hor_sw] at hhi
    change (Anneal.BitVec.setWidth i x).toNat ≤
      (Anneal.BitVec.setWidth i (Anneal.BitVec.or v m)).toNat at hhi
    rw [Anneal.BitVec.toNat_setWidth, Anneal.BitVec.toNat_setWidth,
      toNat_or_of_and_eq_zero hc] at hhi
    exact hhi
  exact ⟨h1, h2⟩

private theorem tnum_carry_sandwich_bit {w : Nat}
    {m₁ m₂ x₁ x₂ u₁ u₂ : BitVec w} {c : Nat} (hc : c ≤ 1)
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ u₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ u₂)
    (hc₁ : Anneal.BitVec.and u₁ m₁ = BitVec.ofNat w 0)
    (hc₂ : Anneal.BitVec.and u₂ m₂ = BitVec.ofNat w 0)
    {i : Nat} (hi : i < w)
    (hm₁ : Anneal.BitVec.getLsbD m₁ i = false)
    (hm₂ : Anneal.BitVec.getLsbD m₂ i = false)
    (hchi :
      ((u₁.toNat + m₁.toNat) + (u₂.toNat + m₂.toNat) + c).testBit i =
        (u₁.toNat + u₂.toNat + c).testBit i) :
    (x₁.toNat + x₂.toNat + c).testBit i =
      (u₁.toNat + u₂.toNat + c).testBit i := by
  have hx1_bit : x₁.toNat.testBit i = u₁.toNat.testBit i :=
    Anneal.BitVec.maskEq_iff_getLsbD.1 h₁ i hi hm₁
  have hx2_bit : x₂.toNat.testBit i = u₂.toNat.testBit i :=
    Anneal.BitVec.maskEq_iff_getLsbD.1 h₂ i hi hm₂
  have hz1_bit : (u₁.toNat + m₁.toNat).testBit i = u₁.toNat.testBit i := by
    rw [← toNat_or_of_and_eq_zero hc₁, Anneal.BitVec.testBit_or]
    change (Anneal.BitVec.getLsbD u₁ i || Anneal.BitVec.getLsbD m₁ i) = _
    rw [hm₁, Bool.or_false]
    rfl
  have hz2_bit : (u₂.toNat + m₂.toNat).testBit i = u₂.toNat.testBit i := by
    rw [← toNat_or_of_and_eq_zero hc₂, Anneal.BitVec.testBit_or]
    change (Anneal.BitVec.getLsbD u₂ i || Anneal.BitVec.getLsbD m₂ i) = _
    rw [hm₂, Bool.or_false]
    rfl
  rw [nat_testBit_add_add_bit _ _ hc i, nat_testBit_add_add_bit _ _ hc i]
  rw [nat_testBit_add_add_bit _ _ hc i, nat_testBit_add_add_bit _ _ hc i] at hchi
  cases i with
  | zero =>
    rw [ite_prop_true rfl, ite_prop_true rfl, hx1_bit, hx2_bit]
  | succ i' =>
    rw [ite_prop_false (fun h => nomatch h),
      ite_prop_false (fun h => nomatch h)] at hchi
    rw [ite_prop_false (fun h => nomatch h),
      ite_prop_false (fun h => nomatch h)]
    rw [hz1_bit, hz2_bit] at hchi
    rw [hx1_bit, hx2_bit]
    have hcarry_eq := bool_bne_cancel_left hchi
    have hb1 := tnum_mod_two_pow_bounds (i' + 1) h₁ hc₁
    have hb2 := tnum_mod_two_pow_bounds (i' + 1) h₂ hc₂
    have hle_lo :
        Nat.mod u₁.toNat (Nat.pow 2 (i' + 1)) +
            Nat.mod u₂.toNat (Nat.pow 2 (i' + 1)) + c ≤
          Nat.mod x₁.toNat (Nat.pow 2 (i' + 1)) +
            Nat.mod x₂.toNat (Nat.pow 2 (i' + 1)) + c :=
      Nat.add_le_add_right (Nat.add_le_add hb1.1 hb2.1) c
    have hle_hi :
        Nat.mod x₁.toNat (Nat.pow 2 (i' + 1)) +
            Nat.mod x₂.toNat (Nat.pow 2 (i' + 1)) + c ≤
          Nat.mod (u₁.toNat + m₁.toNat) (Nat.pow 2 (i' + 1)) +
            Nat.mod (u₂.toNat + m₂.toNat) (Nat.pow 2 (i' + 1)) + c :=
      Nat.add_le_add_right (Nat.add_le_add hb1.2 hb2.2) c
    have hc_eq :
        decide (Nat.pow 2 (i' + 1) ≤
          Nat.mod x₁.toNat (Nat.pow 2 (i' + 1)) +
            Nat.mod x₂.toNat (Nat.pow 2 (i' + 1)) + c) =
        decide (Nat.pow 2 (i' + 1) ≤
          Nat.mod u₁.toNat (Nat.pow 2 (i' + 1)) +
            Nat.mod u₂.toNat (Nat.pow 2 (i' + 1)) + c) := by
      cases hlo_d : decide (Nat.pow 2 (i' + 1) ≤
          Nat.mod u₁.toNat (Nat.pow 2 (i' + 1)) +
            Nat.mod u₂.toNat (Nat.pow 2 (i' + 1)) + c) with
      | true =>
        exact decide_eq_true (Nat.le_trans (of_decide_eq_true hlo_d) hle_lo)
      | false =>
        rw [hlo_d] at hcarry_eq
        have hnot_hi := of_decide_eq_false hcarry_eq
        exact decide_eq_false (fun hx => hnot_hi (Nat.le_trans hx hle_hi))
    rw [hc_eq]

/-- Soundness of carry-propagation unknown-bit (tnum) addition for canonical
tnums (`v₁ &&& m₁ = 0#w` and `v₂ &&& m₂ = 0#w`). -/
theorem tnum_add_sound {w : Nat} {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec w}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂)
    (hc₁ : Anneal.BitVec.and v₁ m₁ = BitVec.ofNat w 0)
    (hc₂ : Anneal.BitVec.and v₂ m₂ = BitVec.ofNat w 0) :
    let sm := m₁ + m₂
    let sv := v₁ + v₂
    let sigma := sm + sv
    let chi := Anneal.BitVec.xor sigma sv
    let mu := Anneal.BitVec.or chi (Anneal.BitVec.or m₁ m₂)
    Anneal.BitVec.MaskEq mu (x₁ + x₂)
      (Anneal.BitVec.and sv (Anneal.BitVec.not mu)) := by
  dsimp only
  rw [← Anneal.BitVec.maskEq_canonical]
  rw [Anneal.BitVec.maskEq_iff_getLsbD]
  intro i hi hmu
  rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_or] at hmu
  cases hchi_b : Anneal.BitVec.getLsbD
      (Anneal.BitVec.xor ((m₁ + m₂) + (v₁ + v₂)) (v₁ + v₂)) i with
  | true =>
    rw [hchi_b] at hmu
    nomatch hmu
  | false =>
    rw [hchi_b, Bool.false_or] at hmu
    cases hm1_b : Anneal.BitVec.getLsbD m₁ i with
    | true =>
      rw [hm1_b] at hmu
      nomatch hmu
    | false =>
      rw [hm1_b, Bool.false_or] at hmu
      have hsigma_eq :
          (m₁ + m₂) + (v₁ + v₂) =
            BitVec.ofNat w ((v₁.toNat + m₁.toNat) + (v₂.toNat + m₂.toNat) + 0) := by
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
          Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat,
          nat_add_mod_cancel_left, nat_add_mod_cancel_right, Nat.add_zero]
        have hrearr :
            (m₁.toNat + m₂.toNat) + (v₁.toNat + v₂.toNat) =
              (v₁.toNat + m₁.toNat) + (v₂.toNat + m₂.toNat) := by
          rw [Nat.add_comm (m₁.toNat + m₂.toNat) (v₁.toNat + v₂.toNat),
            Nat.add_assoc v₁.toNat v₂.toNat (m₁.toNat + m₂.toNat),
            Nat.add_left_comm v₂.toNat m₁.toNat m₂.toNat,
            ← Nat.add_assoc v₁.toNat m₁.toNat (v₂.toNat + m₂.toNat)]
        rw [hrearr]
      have hsv_eq :
          v₁ + v₂ = BitVec.ofNat w (v₁.toNat + v₂.toNat + 0) := by
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat, Nat.add_zero]
      have hx_eq :
          x₁ + x₂ = BitVec.ofNat w (x₁.toNat + x₂.toNat + 0) := by
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat, Nat.add_zero]
      rw [Anneal.BitVec.getLsbD_xor, hsigma_eq, hsv_eq,
        Anneal.BitVec.getLsbD_ofNat, Anneal.BitVec.getLsbD_ofNat,
        decide_eq_true hi, Bool.true_and, Bool.true_and] at hchi_b
      have hchi_eq :
          ((v₁.toNat + m₁.toNat) + (v₂.toNat + m₂.toNat) + 0).testBit i =
            (v₁.toNat + v₂.toNat + 0).testBit i := by
        cases h1b : ((v₁.toNat + m₁.toNat) + (v₂.toNat + m₂.toNat) + 0).testBit i
            <;> cases h2b : (v₁.toNat + v₂.toNat + 0).testBit i
        · rfl
        · rw [h1b, h2b] at hchi_b; nomatch hchi_b
        · rw [h1b, h2b] at hchi_b; nomatch hchi_b
        · rfl
      rw [hx_eq, hsv_eq, Anneal.BitVec.getLsbD_ofNat,
        Anneal.BitVec.getLsbD_ofNat, decide_eq_true hi,
        Bool.true_and, Bool.true_and]
      exact tnum_carry_sandwich_bit (Nat.zero_le 1) h₁ h₂ hc₁ hc₂ hi
        hm1_b hmu hchi_eq

/-- General carry-propagation tnum addition soundness that canonicalizes
non-canonical reference values `v₁, v₂` via `v₁' = v₁ &&& ~~~m₁` and
`v₂' = v₂ &&& ~~~m₂`. -/
theorem tnum_add_sound_general {w : Nat} {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec w}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂) :
    let v₁' := Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁)
    let v₂' := Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)
    let sm := m₁ + m₂
    let sv := v₁' + v₂'
    let sigma := sm + sv
    let chi := Anneal.BitVec.xor sigma sv
    let mu := Anneal.BitVec.or chi (Anneal.BitVec.or m₁ m₂)
    Anneal.BitVec.MaskEq mu (x₁ + x₂)
      (Anneal.BitVec.and sv (Anneal.BitVec.not mu)) := by
  have hc₁ : Anneal.BitVec.and (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁)) m₁ =
      BitVec.ofNat w 0 := by
    rw [Anneal.BitVec.and_assoc, Anneal.BitVec.and_comm (Anneal.BitVec.not m₁) m₁,
      Anneal.BitVec.and_not_self, Anneal.BitVec.and_zero]
  have hc₂ : Anneal.BitVec.and (Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)) m₂ =
      BitVec.ofNat w 0 := by
    rw [Anneal.BitVec.and_assoc, Anneal.BitVec.and_comm (Anneal.BitVec.not m₂) m₂,
      Anneal.BitVec.and_not_self, Anneal.BitVec.and_zero]
  exact tnum_add_sound (Anneal.BitVec.maskEq_canonical.1 h₁)
    (Anneal.BitVec.maskEq_canonical.1 h₂) hc₁ hc₂

/-- Soundness of borrow-propagation unknown-bit (tnum) subtraction for
canonical tnums (`v₁ &&& m₁ = 0#w` and `v₂ &&& m₂ = 0#w`). -/
theorem tnum_sub_sound {w : Nat} {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec w}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂)
    (hc₁ : Anneal.BitVec.and v₁ m₁ = BitVec.ofNat w 0)
    (hc₂ : Anneal.BitVec.and v₂ m₂ = BitVec.ofNat w 0) :
    let dv := v₁ - v₂
    let alpha := dv + m₁
    let beta := dv - m₂
    let chi := Anneal.BitVec.xor alpha beta
    let mu := Anneal.BitVec.or chi (Anneal.BitVec.or m₁ m₂)
    Anneal.BitVec.MaskEq mu (x₁ - x₂)
      (Anneal.BitVec.and dv (Anneal.BitVec.not mu)) := by
  dsimp only
  rw [← Anneal.BitVec.maskEq_canonical]
  rw [Anneal.BitVec.maskEq_iff_getLsbD]
  intro i hi hmu
  rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_or] at hmu
  cases hchi_b : Anneal.BitVec.getLsbD
      (Anneal.BitVec.xor ((v₁ - v₂) + m₁) ((v₁ - v₂) - m₂)) i with
  | true =>
    rw [hchi_b] at hmu
    nomatch hmu
  | false =>
    rw [hchi_b, Bool.false_or] at hmu
    cases hm1_b : Anneal.BitVec.getLsbD m₁ i with
    | true =>
      rw [hm1_b] at hmu
      nomatch hmu
    | false =>
      rw [hm1_b, Bool.false_or] at hmu
      let u₂ := Anneal.BitVec.and (Anneal.BitVec.not v₂) (Anneal.BitVec.not m₂)
      have hu2_disj : Anneal.BitVec.and u₂ m₂ = BitVec.ofNat w 0 := by
        unfold u₂
        rw [Anneal.BitVec.and_assoc,
          Anneal.BitVec.and_comm (Anneal.BitVec.not m₂) m₂,
          Anneal.BitVec.and_not_self, Anneal.BitVec.and_zero]
      have hu2_or : Anneal.BitVec.or u₂ m₂ = Anneal.BitVec.not v₂ := by
        apply Anneal.BitVec.eq_of_getLsbD_eq
        intro j hj
        unfold u₂
        rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_and,
          Anneal.BitVec.getLsbD_not_of_lt _ hj,
          Anneal.BitVec.getLsbD_not_of_lt _ hj]
        have hdj := congrArg (fun z => Anneal.BitVec.getLsbD z j) hc₂
        rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_zero] at hdj
        cases hm2j : Anneal.BitVec.getLsbD m₂ j with
        | false =>
          rw [Bool.not_false, Bool.and_true, Bool.or_false]
        | true =>
          rw [hm2j, Bool.and_true] at hdj
          rw [hdj, Bool.or_true]
          rfl
      have hnot_v2_sum : (Anneal.BitVec.not v₂).toNat = u₂.toNat + m₂.toNat := by
        rw [← hu2_or, toNat_or_of_and_eq_zero hu2_disj]
      have h2_not : Anneal.BitVec.MaskEq m₂ (Anneal.BitVec.not x₂) u₂ :=
        Anneal.BitVec.maskEq_canonical.1 (Anneal.BitVec.tnum_not_sound h₂)
      have h2_nv2 : Anneal.BitVec.MaskEq m₂ (Anneal.BitVec.not v₂) u₂ :=
        Anneal.BitVec.maskEq_canonical.1 (Anneal.BitVec.maskEq_refl m₂ _)
      have hsub_ofNat :
          ∀ a b : BitVec w,
            a - b = BitVec.ofNat w (a.toNat + (Anneal.BitVec.not b).toNat + 1) := by
        intro a b
        rw [sub_eq_add_neg, neg_eq_not_add_one]
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
          Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_ofNat,
          nat_add_mod_cancel_right, ← Nat.add_assoc, nat_add_mod_cancel_right]
      have halpha_eq :
          (v₁ - v₂) + m₁ =
            BitVec.ofNat w ((v₁.toNat + m₁.toNat) + (u₂.toNat + m₂.toNat) + 1) := by
        rw [hsub_ofNat v₁ v₂, hnot_v2_sum]
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat,
          Anneal.BitVec.toNat_ofNat, nat_add_mod_cancel_left]
        have hrearr :
            v₁.toNat + (u₂.toNat + m₂.toNat) + 1 + m₁.toNat =
              (v₁.toNat + m₁.toNat) + (u₂.toNat + m₂.toNat) + 1 := by
          rw [Nat.add_right_comm (v₁.toNat + (u₂.toNat + m₂.toNat)) 1 m₁.toNat,
            Nat.add_right_comm v₁.toNat (u₂.toNat + m₂.toNat) m₁.toNat]
        rw [hrearr]
      have hbeta_eq :
          (v₁ - v₂) - m₂ =
            BitVec.ofNat w (v₁.toNat + u₂.toNat + 1) := by
        have hcancel :
            ((v₁ - v₂) - m₂) + m₂ = v₁ - v₂ := by
          rw [sub_eq_add_neg]
          apply Anneal.BitVec.eq_of_toNat_eq
          have hassoc : ((v₁ - v₂) + neg m₂) + m₂ = (v₁ - v₂) + (neg m₂ + m₂) := by
            apply Anneal.BitVec.eq_of_toNat_eq
            rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
              Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
              nat_add_mod_cancel_left, nat_add_mod_cancel_right, Nat.add_assoc]
          rw [hassoc, neg_add_self, Anneal.BitVec.toNat_add,
            Anneal.BitVec.toNat_zero, Nat.add_zero]
          exact nat_mod_eq_of_lt (v₁ - v₂).isLt
        have hrhs :
            BitVec.ofNat w (v₁.toNat + u₂.toNat + 1) + m₂ = v₁ - v₂ := by
          rw [hsub_ofNat v₁ v₂, hnot_v2_sum]
          apply Anneal.BitVec.eq_of_toNat_eq
          rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat,
            Anneal.BitVec.toNat_ofNat, nat_add_mod_cancel_left]
          have hrearr :
              v₁.toNat + u₂.toNat + 1 + m₂.toNat =
                v₁.toNat + (u₂.toNat + m₂.toNat) + 1 := by
            rw [Nat.add_right_comm (v₁.toNat + u₂.toNat) 1 m₂.toNat,
              Nat.add_assoc v₁.toNat u₂.toNat m₂.toNat]
          rw [hrearr]
        have hsum_eq :
            ((v₁ - v₂) - m₂) + m₂ =
              BitVec.ofNat w (v₁.toNat + u₂.toNat + 1) + m₂ :=
          Eq.trans hcancel (Eq.symm hrhs)
        have hsub_both := congrArg (fun z => z + neg m₂) hsum_eq
        have hclean : ∀ a : BitVec w, (a + m₂) + neg m₂ = a := by
          intro a
          apply Anneal.BitVec.eq_of_toNat_eq
          have hassoc : (a + m₂) + neg m₂ = a + (m₂ + neg m₂) := by
            apply Anneal.BitVec.eq_of_toNat_eq
            rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
              Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
              nat_add_mod_cancel_left, nat_add_mod_cancel_right, Nat.add_assoc]
          rw [hassoc, add_neg_self, Anneal.BitVec.toNat_add,
            Anneal.BitVec.toNat_zero, Nat.add_zero]
          exact nat_mod_eq_of_lt a.isLt
        rw [hclean, hclean] at hsub_both
        exact hsub_both
      rw [Anneal.BitVec.getLsbD_xor, halpha_eq, hbeta_eq,
        Anneal.BitVec.getLsbD_ofNat, Anneal.BitVec.getLsbD_ofNat,
        decide_eq_true hi, Bool.true_and, Bool.true_and] at hchi_b
      have hchi_eq :
          ((v₁.toNat + m₁.toNat) + (u₂.toNat + m₂.toNat) + 1).testBit i =
            (v₁.toNat + u₂.toNat + 1).testBit i := by
        cases h1b : ((v₁.toNat + m₁.toNat) + (u₂.toNat + m₂.toNat) + 1).testBit i
            <;> cases h2b : (v₁.toNat + u₂.toNat + 1).testBit i
        · rfl
        · rw [h1b, h2b] at hchi_b; nomatch hchi_b
        · rw [h1b, h2b] at hchi_b; nomatch hchi_b
        · rfl
      have hx_bit := tnum_carry_sandwich_bit (Nat.le_refl 1) h₁ h2_not hc₁
        hu2_disj hi hm1_b hmu hchi_eq
      have hdv_bit := tnum_carry_sandwich_bit (Nat.le_refl 1)
        (Anneal.BitVec.maskEq_refl m₁ v₁) h2_nv2 hc₁ hu2_disj hi hm1_b hmu
        hchi_eq
      rw [hsub_ofNat x₁ x₂, hsub_ofNat v₁ v₂, Anneal.BitVec.getLsbD_ofNat,
        Anneal.BitVec.getLsbD_ofNat, decide_eq_true hi,
        Bool.true_and, Bool.true_and]
      exact Eq.trans hx_bit (Eq.symm hdv_bit)

/-- General borrow-propagation tnum subtraction soundness that canonicalizes
non-canonical reference values `v₁, v₂` via `v₁' = v₁ &&& ~~~m₁` and
`v₂' = v₂ &&& ~~~m₂`. -/
theorem tnum_sub_sound_general {w : Nat} {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec w}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂) :
    let v₁' := Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁)
    let v₂' := Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)
    let dv := v₁' - v₂'
    let alpha := dv + m₁
    let beta := dv - m₂
    let chi := Anneal.BitVec.xor alpha beta
    let mu := Anneal.BitVec.or chi (Anneal.BitVec.or m₁ m₂)
    Anneal.BitVec.MaskEq mu (x₁ - x₂)
      (Anneal.BitVec.and dv (Anneal.BitVec.not mu)) := by
  have hc₁ : Anneal.BitVec.and (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁)) m₁ =
      BitVec.ofNat w 0 := by
    rw [Anneal.BitVec.and_assoc, Anneal.BitVec.and_comm (Anneal.BitVec.not m₁) m₁,
      Anneal.BitVec.and_not_self, Anneal.BitVec.and_zero]
  have hc₂ : Anneal.BitVec.and (Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)) m₂ =
      BitVec.ofNat w 0 := by
    rw [Anneal.BitVec.and_assoc, Anneal.BitVec.and_comm (Anneal.BitVec.not m₂) m₂,
      Anneal.BitVec.and_not_self, Anneal.BitVec.and_zero]
  exact tnum_sub_sound (Anneal.BitVec.maskEq_canonical.1 h₁)
    (Anneal.BitVec.maskEq_canonical.1 h₂) hc₁ hc₂

/-! ## Part 3: Width-Parametric Unsigned & Signed Interval Transfers -/

/-- Unsigned remainder of two `w`-bit bitvectors, definitionally equal to
`x % y` (`BitVec.umod x y`). -/
@[expose] def urem {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNatLT (Nat.mod x.toNat y.toNat)
    (Nat.lt_of_le_of_lt (Nat.mod_le x.toNat y.toNat) x.isLt)

/-- `toNat` characterization of `urem x y`. -/
@[simp] theorem toNat_urem {w : Nat} (x y : BitVec w) :
    (urem x y).toNat = Nat.mod x.toNat y.toNat :=
  rfl

/-- Exact divisor bound for unsigned remainder (`x % y < y` when `y > 0`). -/
theorem urem_lt {w : Nat} {x y : BitVec w} (hy : 0 < y.toNat) :
    urem x y < y :=
  Nat.mod_lt x.toNat hy

/-- Dividend upper bound for unsigned remainder (`x % y ≤ x`). -/
theorem urem_le_left {w : Nat} (x y : BitVec w) :
    urem x y ≤ x :=
  Nat.mod_le x.toNat y.toNat

/-- Soundness of unsigned interval remainder: when `0 < y.toNat`, `x ≤ umax`,
and `y ≤ ymax`, we have `(x % y).toNat ≤ umax.toNat` and
`(x % y).toNat < ymax.toNat`. -/
theorem range_urem_sound {w : Nat} {x umax y ymax : BitVec w}
    (hy : 0 < y.toNat) (hx : x ≤ umax) (hymax : y ≤ ymax) :
    (urem x y).toNat ≤ umax.toNat ∧ (urem x y).toNat < ymax.toNat :=
  ⟨Nat.le_trans (Nat.mod_le x.toNat y.toNat) hx,
    Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat hy) hymax⟩

/-- Soundness of unsigned interval left shift when no high bits shift out
(`umax.toNat * 2^kmax < 2^w`). -/
theorem range_shl_no_overflow_sound {w : Nat}
    {umin x umax : BitVec w} {kmin k kmax : Nat}
    (hlo : umin ≤ x) (hhi : x ≤ umax)
    (hklo : kmin ≤ k) (hkhi : k ≤ kmax)
    (hno_ovf : umax.toNat * Nat.pow 2 kmax < Nat.pow 2 w) :
    Anneal.BitVec.shl umin kmin ≤ Anneal.BitVec.shl x k ∧
      Anneal.BitVec.shl x k ≤ Anneal.BitVec.shl umax kmax := by
  have h1 : umin.toNat * Nat.pow 2 kmin ≤ x.toNat * Nat.pow 2 k :=
    Nat.mul_le_mul hlo (nat_pow_le_pow_right hklo)
  have h2 : x.toNat * Nat.pow 2 k ≤ umax.toNat * Nat.pow 2 kmax :=
    Nat.mul_le_mul hhi (nat_pow_le_pow_right hkhi)
  have hlt_x : x.toNat * Nat.pow 2 k < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h2 hno_ovf
  have hlt_min : umin.toNat * Nat.pow 2 kmin < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt h1 hlt_x
  constructor
  · change (Anneal.BitVec.shl umin kmin).toNat ≤ (Anneal.BitVec.shl x k).toNat
    rw [Anneal.BitVec.toNat_shl, Anneal.BitVec.toNat_shl,
      nat_shiftLeft_eq, nat_shiftLeft_eq,
      nat_mod_eq_of_lt hlt_min, nat_mod_eq_of_lt hlt_x]
    exact h1
  · change (Anneal.BitVec.shl x k).toNat ≤ (Anneal.BitVec.shl umax kmax).toNat
    rw [Anneal.BitVec.toNat_shl, Anneal.BitVec.toNat_shl,
      nat_shiftLeft_eq, nat_shiftLeft_eq,
      nat_mod_eq_of_lt hlt_x, nat_mod_eq_of_lt hno_ovf]
    exact h2

/-- Soundness of unsigned interval logical right shift (`ushr`). -/
theorem range_ushr_sound {w : Nat}
    {umin x umax : BitVec w} {kmin k kmax : Nat}
    (hlo : umin ≤ x) (hhi : x ≤ umax)
    (hklo : kmin ≤ k) (hkhi : k ≤ kmax) :
    Anneal.BitVec.ushr umin kmax ≤ Anneal.BitVec.ushr x k ∧
      Anneal.BitVec.ushr x k ≤ Anneal.BitVec.ushr umax kmin := by
  constructor
  · change Nat.shiftRight umin.toNat kmax ≤ Nat.shiftRight x.toNat k
    rw [nat_shiftRight_eq_div_pow, nat_shiftRight_eq_div_pow]
    exact Nat.le_trans
      (nat_div_le_div_left (nat_pow_le_pow_right hkhi) (nat_two_pow_pos k))
      (nat_div_le_div_right hlo (Nat.pow 2 k))
  · change Nat.shiftRight x.toNat k ≤ Nat.shiftRight umax.toNat kmin
    rw [nat_shiftRight_eq_div_pow, nat_shiftRight_eq_div_pow]
    exact Nat.le_trans
      (nat_div_le_div_right hhi (Nat.pow 2 k))
      (nat_div_le_div_left (nat_pow_le_pow_right hklo) (nat_two_pow_pos kmin))

/-- Pointwise left upper bound `(x &&& y).toNat ≤ x.toNat`. -/
theorem toNat_and_le_left {w : Nat} (x y : BitVec w) :
    (Anneal.BitVec.and x y).toNat ≤ x.toNat := by
  apply nat_le_of_testBit_imp w _ _ (Anneal.BitVec.and x y).isLt x.isLt
  intro i _ hbit
  rw [Anneal.BitVec.testBit_and] at hbit
  cases hxi : x.toNat.testBit i with
  | true => rfl
  | false =>
    rw [hxi, Bool.false_and] at hbit
    nomatch hbit

/-- Pointwise right upper bound `(x &&& y).toNat ≤ y.toNat`. -/
theorem toNat_and_le_right {w : Nat} (x y : BitVec w) :
    (Anneal.BitVec.and x y).toNat ≤ y.toNat := by
  rw [Anneal.BitVec.and_comm]
  exact toNat_and_le_left y x

private theorem nat_le_min {c a b : Nat} (ha : c ≤ a) (hb : c ≤ b) :
    c ≤ min a b := by
  change c ≤ if a ≤ b then a else b
  cases Nat.le_total a b with
  | inl h =>
    rw [ite_prop_true h]
    exact ha
  | inr h =>
    cases (inferInstance : Decidable (a ≤ b)) with
    | isTrue hle =>
      rw [ite_prop_true hle]
      exact ha
    | isFalse hnot =>
      rw [ite_prop_false hnot]
      exact hb

private theorem nat_max_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) :
    max a b ≤ c := by
  change (if a ≤ b then b else a) ≤ c
  cases (inferInstance : Decidable (a ≤ b)) with
  | isTrue hle =>
    rw [ite_prop_true hle]
    exact hb
  | isFalse hnot =>
    rw [ite_prop_false hnot]
    exact ha

/-- Pointwise upper bound `(x &&& y).toNat ≤ min x.toNat y.toNat`. -/
theorem toNat_and_le_min {w : Nat} (x y : BitVec w) :
    (Anneal.BitVec.and x y).toNat ≤ min x.toNat y.toNat :=
  nat_le_min (toNat_and_le_left x y) (toNat_and_le_right x y)

/-- Unsigned interval upper-bound soundness for bitwise AND. -/
theorem range_and_upper_sound {w : Nat} {x umax₁ y umax₂ : BitVec w}
    (hx : x ≤ umax₁) (hy : y ≤ umax₂) :
    (Anneal.BitVec.and x y).toNat ≤ min umax₁.toNat umax₂.toNat :=
  nat_le_min
    (Nat.le_trans (toNat_and_le_left x y) hx)
    (Nat.le_trans (toNat_and_le_right x y) hy)

/-- Pointwise left lower bound `x.toNat ≤ (x ||| y).toNat`. -/
theorem le_toNat_or_left {w : Nat} (x y : BitVec w) :
    x.toNat ≤ (Anneal.BitVec.or x y).toNat := by
  apply nat_le_of_testBit_imp w _ _ x.isLt (Anneal.BitVec.or x y).isLt
  intro i _ hbit
  rw [Anneal.BitVec.testBit_or, hbit, Bool.true_or]

/-- Pointwise right lower bound `y.toNat ≤ (x ||| y).toNat`. -/
theorem le_toNat_or_right {w : Nat} (x y : BitVec w) :
    y.toNat ≤ (Anneal.BitVec.or x y).toNat := by
  rw [Anneal.BitVec.or_comm]
  exact le_toNat_or_left y x

/-- Pointwise lower bound `max x.toNat y.toNat ≤ (x ||| y).toNat`. -/
theorem max_le_toNat_or {w : Nat} (x y : BitVec w) :
    max x.toNat y.toNat ≤ (Anneal.BitVec.or x y).toNat :=
  nat_max_le (le_toNat_or_left x y) (le_toNat_or_right x y)

/-- Unsigned interval lower-bound soundness for bitwise OR. -/
theorem range_or_lower_sound {w : Nat} {umin₁ x umin₂ y : BitVec w}
    (hx : umin₁ ≤ x) (hy : umin₂ ≤ y) :
    max umin₁.toNat umin₂.toNat ≤ (Anneal.BitVec.or x y).toNat :=
  nat_max_le
    (Nat.le_trans hx (le_toNat_or_left x y))
    (Nat.le_trans hy (le_toNat_or_right x y))

/-- Pointwise upper bound `(x ||| y).toNat ≤ x.toNat + y.toNat`. -/
theorem toNat_or_le_add {w : Nat} (x y : BitVec w) :
    (Anneal.BitVec.or x y).toNat ≤ x.toNat + y.toNat := by
  rw [← toNat_or_add_and x y]
  exact Nat.le_add_right _ _

/-- Unsigned interval upper-bound soundness for bitwise OR. -/
theorem range_or_upper_sound {w : Nat} {x umax₁ y umax₂ : BitVec w}
    (hx : x ≤ umax₁) (hy : y ≤ umax₂) :
    (Anneal.BitVec.or x y).toNat ≤ umax₁.toNat + umax₂.toNat ∧
      (Anneal.BitVec.or x y).toNat < Nat.pow 2 w :=
  ⟨Nat.le_trans (toNat_or_le_add x y) (Nat.add_le_add hx hy),
    (Anneal.BitVec.or x y).isLt⟩

/-- Pointwise comparison `(x ^^^ y).toNat ≤ (x ||| y).toNat`. -/
theorem toNat_xor_le_or {w : Nat} (x y : BitVec w) :
    (Anneal.BitVec.xor x y).toNat ≤ (Anneal.BitVec.or x y).toNat := by
  apply nat_le_of_testBit_imp w _ _
    (Anneal.BitVec.xor x y).isLt (Anneal.BitVec.or x y).isLt
  intro i _ hbit
  rw [Anneal.BitVec.testBit_xor] at hbit
  rw [Anneal.BitVec.testBit_or]
  cases hxi : x.toNat.testBit i <;> cases hyi : y.toNat.testBit i
  · rw [hxi, hyi] at hbit; nomatch hbit
  · rfl
  · rfl
  · rw [hxi, hyi] at hbit; nomatch hbit

/-- Pointwise upper bound `(x ^^^ y).toNat ≤ x.toNat + y.toNat`. -/
theorem toNat_xor_le_add {w : Nat} (x y : BitVec w) :
    (Anneal.BitVec.xor x y).toNat ≤ x.toNat + y.toNat :=
  Nat.le_trans (toNat_xor_le_or x y) (toNat_or_le_add x y)

/-- Unsigned interval upper-bound soundness for bitwise XOR. -/
theorem range_xor_upper_sound {w : Nat} {x umax₁ y umax₂ : BitVec w}
    (hx : x ≤ umax₁) (hy : y ≤ umax₂) :
    (Anneal.BitVec.xor x y).toNat ≤ umax₁.toNat + umax₂.toNat ∧
      (Anneal.BitVec.xor x y).toNat < Nat.pow 2 w :=
  ⟨Nat.le_trans (toNat_xor_le_add x y) (Nat.add_le_add hx hy),
    (Anneal.BitVec.xor x y).isLt⟩

private theorem signedKey_eq_mod_add_half {w : Nat} (hw : 0 < w)
    (x : BitVec w) :
    signedKey x = Nat.mod (x.toNat + Nat.pow 2 (w - 1)) (Nat.pow 2 w) := by
  cases hm : msb x with
  | false =>
    rw [signedKey_eq_of_msb_false hw hm]
    have hlt := (msb_eq_false_iff hw x).1 hm
    have hsum_lt : x.toNat + Nat.pow 2 (w - 1) < Nat.pow 2 w := by
      rw [nat_two_pow_split hw]
      exact Nat.add_lt_add_right hlt (Nat.pow 2 (w - 1))
    exact Eq.symm (Nat.mod_eq_of_lt hsum_lt)
  | true =>
    rw [signedKey_eq_of_msb_true hw hm]
    have hge := (msb_eq_true_iff hw x).1 hm
    have hlt_half : x.toNat - Nat.pow 2 (w - 1) < Nat.pow 2 (w - 1) := by
      have h1 : (x.toNat - Nat.pow 2 (w - 1)) + Nat.pow 2 (w - 1) <
          Nat.pow 2 (w - 1) + Nat.pow 2 (w - 1) := by
        rw [Nat.sub_add_cancel hge, ← nat_two_pow_split hw]
        exact x.isLt
      exact nat_lt_of_add_lt_add_right h1
    have hsplit :
        x.toNat + Nat.pow 2 (w - 1) =
          Nat.pow 2 w + (x.toNat - Nat.pow 2 (w - 1)) := by
      rw [nat_two_pow_split hw]
      have hx_eq : x.toNat = (x.toNat - Nat.pow 2 (w - 1)) + Nat.pow 2 (w - 1) :=
        Eq.symm (Nat.sub_add_cancel hge)
      have h1 := congrArg (fun z => z + Nat.pow 2 (w - 1)) hx_eq
      rw [Nat.add_assoc, Nat.add_comm (x.toNat - Nat.pow 2 (w - 1))] at h1
      exact h1
    rw [hsplit, nat_add_mod_left]
    exact Eq.symm (nat_mod_eq_of_lt
      (Nat.lt_trans hlt_half (nat_two_pow_sub_one_lt hw)))

/-- Exact `signedKey` of overflow-free and underflow-free signed addition
(`2^(w - 1) ≤ signedKey a + signedKey b < 2^(w - 1) + 2^w`). -/
theorem signedKey_add_no_overflow {w : Nat} (hw : 0 < w) {a b : BitVec w}
    (hno_udf : Nat.pow 2 (w - 1) ≤ signedKey a + signedKey b)
    (hno_ovf : signedKey a + signedKey b < Nat.pow 2 (w - 1) + Nat.pow 2 w) :
    signedKey (a + b) = signedKey a + signedKey b - Nat.pow 2 (w - 1) := by
  let H := Nat.pow 2 (w - 1)
  have hpow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  have hmod_sum :
      Nat.mod (signedKey a + signedKey b) (Nat.pow 2 w) =
        Nat.mod (a.toNat + b.toNat) (Nat.pow 2 w) := by
    rw [signedKey_eq_mod_add_half hw a, signedKey_eq_mod_add_half hw b,
      nat_add_mod_cancel_left, nat_add_mod_cancel_right]
    have hrearr :
        (a.toNat + H) + (b.toNat + H) = (H + H) + (a.toNat + b.toNat) := by
      rw [Nat.add_assoc a.toNat H (b.toNat + H),
        Nat.add_left_comm H b.toNat H, ← Nat.add_assoc a.toNat b.toNat (H + H),
        Nat.add_comm (a.toNat + b.toNat) (H + H)]
    change Nat.mod ((a.toNat + H) + (b.toNat + H)) (Nat.pow 2 w) = _
    rw [hrearr, ← hpow, nat_add_mod_left]
  have htarget_lt : signedKey a + signedKey b - H < Nat.pow 2 w := by
    have h1 : (signedKey a + signedKey b - H) + H < Nat.pow 2 w + H := by
      rw [Nat.sub_add_cancel hno_udf, Nat.add_comm (Nat.pow 2 w) H]
      exact hno_ovf
    exact nat_lt_of_add_lt_add_right h1
  rw [signedKey_eq_mod_add_half hw (a + b), Anneal.BitVec.toNat_add,
    ← hmod_sum, nat_add_mod_cancel_left]
  have hadd_H :
      (signedKey a + signedKey b) + H =
        (H + H) + (signedKey a + signedKey b - H) := by
    have hsub : signedKey a + signedKey b =
        (signedKey a + signedKey b - H) + H :=
      Eq.symm (Nat.sub_add_cancel hno_udf)
    have h1 := congrArg (fun z => z + H) hsub
    rw [Nat.add_assoc (signedKey a + signedKey b - H) H H,
      Nat.add_comm (signedKey a + signedKey b - H) (H + H)] at h1
    exact h1
  change Nat.mod ((signedKey a + signedKey b) + H) (Nat.pow 2 w) = _
  rw [hadd_H, ← hpow, nat_add_mod_left]
  exact nat_mod_eq_of_lt htarget_lt

/-- Soundness of signed interval addition when neither underflow
(`2^(w - 1) ≤ signedKey smin₁ + signedKey smin₂`) nor overflow
(`signedKey smax₁ + signedKey smax₂ < 2^(w - 1) + 2^w`) occurs. -/
theorem signed_range_add_no_overflow_sound {w : Nat}
    {smin₁ x smax₁ smin₂ y smax₂ : BitVec w}
    (hlo₁ : sle smin₁ x) (hhi₁ : sle x smax₁)
    (hlo₂ : sle smin₂ y) (hhi₂ : sle y smax₂)
    (hno_udf : Nat.pow 2 (w - 1) ≤ signedKey smin₁ + signedKey smin₂)
    (hno_ovf : signedKey smax₁ + signedKey smax₂ <
      Nat.pow 2 (w - 1) + Nat.pow 2 w) :
    sle (smin₁ + smin₂) (x + y) ∧ sle (x + y) (smax₁ + smax₂) := by
  cases w with
  | zero =>
    unfold sle
    have h1 : signedKey (smin₁ + smin₂) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt _))
    have h2 : signedKey (x + y) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt _))
    have h3 : signedKey (smax₁ + smax₂) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt _))
    rw [h1, h2, h3]
    exact ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
    have hsum_lo : signedKey smin₁ + signedKey smin₂ ≤ signedKey x + signedKey y :=
      Nat.add_le_add hlo₁ hlo₂
    have hsum_hi : signedKey x + signedKey y ≤ signedKey smax₁ + signedKey smax₂ :=
      Nat.add_le_add hhi₁ hhi₂
    have hlo_ovf : signedKey smin₁ + signedKey smin₂ <
        Nat.pow 2 (w' + 1 - 1) + Nat.pow 2 (w' + 1) :=
      Nat.lt_of_le_of_lt (Nat.le_trans hsum_lo hsum_hi) hno_ovf
    have hxy_udf : Nat.pow 2 (w' + 1 - 1) ≤ signedKey x + signedKey y :=
      Nat.le_trans hno_udf hsum_lo
    have hxy_ovf : signedKey x + signedKey y <
        Nat.pow 2 (w' + 1 - 1) + Nat.pow 2 (w' + 1) :=
      Nat.lt_of_le_of_lt hsum_hi hno_ovf
    have hhi_udf : Nat.pow 2 (w' + 1 - 1) ≤ signedKey smax₁ + signedKey smax₂ :=
      Nat.le_trans hxy_udf hsum_hi
    unfold sle
    rw [signedKey_add_no_overflow hw hno_udf hlo_ovf,
      signedKey_add_no_overflow hw hxy_udf hxy_ovf,
      signedKey_add_no_overflow hw hhi_udf hno_ovf]
    exact ⟨Nat.sub_le_sub_right hsum_lo _, Nat.sub_le_sub_right hsum_hi _⟩

/-- Unsigned minimum of two `w`-bit bitvectors. -/
@[expose] def bvMin {w : Nat} (a b : BitVec w) : BitVec w :=
  if a.toNat ≤ b.toNat then a else b

/-- Unsigned maximum of two `w`-bit bitvectors. -/
@[expose] def bvMax {w : Nat} (a b : BitVec w) : BitVec w :=
  if a.toNat ≤ b.toNat then b else a

/-- Signed minimum of two `w`-bit bitvectors (under `sle`). -/
@[expose] def sbvMin {w : Nat} (a b : BitVec w) : BitVec w :=
  if signedKey a ≤ signedKey b then a else b

/-- Signed maximum of two `w`-bit bitvectors (under `sle`). -/
@[expose] def sbvMax {w : Nat} (a b : BitVec w) : BitVec w :=
  if signedKey a ≤ signedKey b then b else a

private theorem le_bvMin {w : Nat} {x a b : BitVec w}
    (ha : x ≤ a) (hb : x ≤ b) : x ≤ bvMin a b := by
  unfold bvMin
  cases (inferInstance : Decidable (a.toNat ≤ b.toNat)) with
  | isTrue h =>
    rw [ite_prop_true h]
    exact ha
  | isFalse h =>
    rw [ite_prop_false h]
    exact hb

private theorem bvMax_le {w : Nat} {a b x : BitVec w}
    (ha : a ≤ x) (hb : b ≤ x) : bvMax a b ≤ x := by
  unfold bvMax
  cases (inferInstance : Decidable (a.toNat ≤ b.toNat)) with
  | isTrue h =>
    rw [ite_prop_true h]
    exact hb
  | isFalse h =>
    rw [ite_prop_false h]
    exact ha

private theorem sle_sbvMin {w : Nat} {x a b : BitVec w}
    (ha : sle x a) (hb : sle x b) : sle x (sbvMin a b) := by
  unfold sbvMin
  cases (inferInstance : Decidable (signedKey a ≤ signedKey b)) with
  | isTrue h =>
    rw [ite_prop_true h]
    exact ha
  | isFalse h =>
    rw [ite_prop_false h]
    exact hb

private theorem sbvMax_sle {w : Nat} {a b x : BitVec w}
    (ha : sle a x) (hb : sle b x) : sle (sbvMax a b) x := by
  unfold sbvMax
  cases (inferInstance : Decidable (signedKey a ≤ signedKey b)) with
  | isTrue h =>
    rw [ite_prop_true h]
    exact hb
  | isFalse h =>
    rw [ite_prop_false h]
    exact ha

/-- Unsigned interval intersection soundness. -/
theorem range_intersect_sound {w : Nat} {lo₁ hi₁ lo₂ hi₂ x : BitVec w}
    (h1 : lo₁ ≤ x ∧ x ≤ hi₁) (h2 : lo₂ ≤ x ∧ x ≤ hi₂) :
    bvMax lo₁ lo₂ ≤ x ∧ x ≤ bvMin hi₁ hi₂ :=
  ⟨bvMax_le h1.1 h2.1, le_bvMin h1.2 h2.2⟩

/-- Unsigned branch refinement on `x ≤ c`. -/
theorem range_refine_ule {w : Nat} {lo hi x c : BitVec w}
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hc : x ≤ c) :
    lo ≤ x ∧ x ≤ bvMin hi c :=
  ⟨hlo, le_bvMin hhi hc⟩

/-- Unsigned branch refinement on `c ≤ x`. -/
theorem range_refine_uge {w : Nat} {lo hi x c : BitVec w}
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hc : c ≤ x) :
    bvMax lo c ≤ x ∧ x ≤ hi :=
  ⟨bvMax_le hlo hc, hhi⟩

/-- Unsigned branch refinement on strict `x < c`. -/
theorem range_refine_ult {w : Nat} {lo hi x c : BitVec w}
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hc : x < c) :
    lo ≤ x ∧ x ≤ bvMin hi (c - BitVec.ofNat w 1) := by
  cases w with
  | zero =>
    have hx0 : x.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ x.isLt)
    have hc0 : c.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ c.isLt)
    have hlt : x.toNat < c.toNat := hc
    rw [hx0, hc0] at hlt
    exact False.elim (Nat.not_lt_zero 0 hlt)
  | succ w' =>
    have h1lt : 1 < Nat.pow 2 (w' + 1) := by
      rw [nat_pow_succ, Nat.mul_two]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
        (Nat.add_le_add (nat_two_pow_pos w') (nat_two_pow_pos w'))
    have h1le : BitVec.ofNat (w' + 1) 1 ≤ c := by
      change (BitVec.ofNat (w' + 1) 1).toNat ≤ c.toNat
      rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt h1lt]
      exact Nat.lt_of_le_of_lt (Nat.zero_le x.toNat) hc
    have hxc : x ≤ c - BitVec.ofNat (w' + 1) 1 := by
      change x.toNat ≤ (c - BitVec.ofNat (w' + 1) 1).toNat
      rw [Anneal.BitVec.toNat_sub_of_le h1le, Anneal.BitVec.toNat_ofNat,
        nat_mod_eq_of_lt h1lt]
      exact Nat.le_sub_one_of_lt hc
    exact ⟨hlo, le_bvMin hhi hxc⟩

/-- Unsigned branch refinement on strict `c < x`. -/
theorem range_refine_ugt {w : Nat} {lo hi x c : BitVec w}
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hc : c < x) :
    bvMax lo (c + BitVec.ofNat w 1) ≤ x ∧ x ≤ hi := by
  cases w with
  | zero =>
    have hx0 : x.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ x.isLt)
    have hc0 : c.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ c.isLt)
    have hlt : c.toNat < x.toNat := hc
    rw [hx0, hc0] at hlt
    exact False.elim (Nat.not_lt_zero 0 hlt)
  | succ w' =>
    have h1lt : 1 < Nat.pow 2 (w' + 1) := by
      rw [nat_pow_succ, Nat.mul_two]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
        (Nat.add_le_add (nat_two_pow_pos w') (nat_two_pow_pos w'))
    have hc1_le : c.toNat + 1 ≤ x.toNat := hc
    have hc1_lt : c.toNat + 1 < Nat.pow 2 (w' + 1) :=
      Nat.lt_of_le_of_lt hc1_le x.isLt
    have hcx : c + BitVec.ofNat (w' + 1) 1 ≤ x := by
      change (c + BitVec.ofNat (w' + 1) 1).toNat ≤ x.toNat
      rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat,
        nat_mod_eq_of_lt h1lt, nat_mod_eq_of_lt hc1_lt]
      exact hc1_le
    exact ⟨bvMax_le hlo hcx, hhi⟩

/-- Signed interval intersection soundness. -/
theorem signed_range_intersect_sound {w : Nat} {lo₁ hi₁ lo₂ hi₂ x : BitVec w}
    (h1 : sle lo₁ x ∧ sle x hi₁) (h2 : sle lo₂ x ∧ sle x hi₂) :
    sle (sbvMax lo₁ lo₂) x ∧ sle x (sbvMin hi₁ hi₂) :=
  ⟨sbvMax_sle h1.1 h2.1, sle_sbvMin h1.2 h2.2⟩

/-- Signed branch refinement on `sle x c`. -/
theorem signed_range_refine_sle {w : Nat} {lo hi x c : BitVec w}
    (hlo : sle lo x) (hhi : sle x hi) (hc : sle x c) :
    sle lo x ∧ sle x (sbvMin hi c) :=
  ⟨hlo, sle_sbvMin hhi hc⟩

/-- Signed branch refinement on `sle c x`. -/
theorem signed_range_refine_sge {w : Nat} {lo hi x c : BitVec w}
    (hlo : sle lo x) (hhi : sle x hi) (hc : sle c x) :
    sle (sbvMax lo c) x ∧ sle x hi :=
  ⟨sbvMax_sle hlo hc, hhi⟩

private theorem signedKey_sub_one {w : Nat} (hw : 0 < w) {c : BitVec w}
    (hpos : 0 < signedKey c) :
    signedKey (c - BitVec.ofNat w 1) = signedKey c - 1 := by
  have h1lt : 1 < Nat.pow 2 w := by
    rw [nat_two_pow_split hw]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
      (Nat.add_le_add (nat_two_pow_pos (w - 1)) (nat_two_pow_pos (w - 1)))
  have hmod_c :
      Nat.mod ((c - BitVec.ofNat w 1).toNat + Nat.pow 2 (w - 1)) (Nat.pow 2 w) =
        Nat.mod ((signedKey c - 1) + Nat.pow 2 w) (Nat.pow 2 w) := by
    rw [Anneal.BitVec.toNat_sub, Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt h1lt, nat_add_mod_cancel_left]
    have hkey := signedKey_eq_mod_add_half hw c
    have hrearr :
        (Nat.pow 2 w - 1) + c.toNat + Nat.pow 2 (w - 1) =
          (Nat.pow 2 w - 1) + (c.toNat + Nat.pow 2 (w - 1)) :=
      Nat.add_assoc _ _ _
    rw [hrearr, ← nat_add_mod_cancel_right (Nat.pow 2 w - 1) _ (Nat.pow 2 w),
      ← hkey]
    have hstep :
        (Nat.pow 2 w - 1) + signedKey c = (signedKey c - 1) + Nat.pow 2 w := by
      have hsc : signedKey c = 1 + (signedKey c - 1) := by
        rw [Nat.add_comm 1 (signedKey c - 1)]
        exact Eq.symm (Nat.sub_add_cancel hpos)
      have h1 := congrArg (fun z => (Nat.pow 2 w - 1) + z) hsc
      rw [← Nat.add_assoc (Nat.pow 2 w - 1) 1 (signedKey c - 1),
        Nat.sub_add_cancel (nat_two_pow_pos w),
        Nat.add_comm (Nat.pow 2 w) (signedKey c - 1)] at h1
      exact h1
    rw [hstep]
  rw [signedKey_eq_mod_add_half hw (c - BitVec.ofNat w 1), hmod_c,
    Nat.add_comm (signedKey c - 1) (Nat.pow 2 w), nat_add_mod_left]
  exact nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ 1) (signedKey_lt c))

private theorem signedKey_add_one {w : Nat} (hw : 0 < w) {c : BitVec w}
    (hlt : signedKey c + 1 < Nat.pow 2 w) :
    signedKey (c + BitVec.ofNat w 1) = signedKey c + 1 := by
  have h1lt : 1 < Nat.pow 2 w := by
    rw [nat_two_pow_split hw]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
      (Nat.add_le_add (nat_two_pow_pos (w - 1)) (nat_two_pow_pos (w - 1)))
  rw [signedKey_eq_mod_add_half hw (c + BitVec.ofNat w 1),
    Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_ofNat,
    nat_mod_eq_of_lt h1lt, nat_add_mod_cancel_left]
  have hrearr :
      c.toNat + 1 + Nat.pow 2 (w - 1) = (c.toNat + Nat.pow 2 (w - 1)) + 1 :=
    Nat.add_right_comm c.toNat 1 (Nat.pow 2 (w - 1))
  rw [hrearr, ← nat_add_mod_cancel_left (c.toNat + Nat.pow 2 (w - 1)) 1 (Nat.pow 2 w),
    ← signedKey_eq_mod_add_half hw c]
  exact nat_mod_eq_of_lt hlt

/-- Signed branch refinement on strict `slt x c`. -/
theorem signed_range_refine_slt {w : Nat} {lo hi x c : BitVec w}
    (hlo : sle lo x) (hhi : sle x hi) (hc : slt x c) :
    sle lo x ∧ sle x (sbvMin hi (c - BitVec.ofNat w 1)) := by
  cases w with
  | zero =>
    have hx0 : signedKey x = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt x))
    have hc0 : signedKey c = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt c))
    have hlt : signedKey x < signedKey c := hc
    rw [hx0, hc0] at hlt
    exact False.elim (Nat.not_lt_zero 0 hlt)
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
    have hc_pos : 0 < signedKey c := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
    have hxc : sle x (c - BitVec.ofNat (w' + 1) 1) := by
      unfold sle
      rw [signedKey_sub_one hw hc_pos]
      exact Nat.le_sub_one_of_lt hc
    exact ⟨hlo, sle_sbvMin hhi hxc⟩

/-- Signed branch refinement on strict `slt c x`. -/
theorem signed_range_refine_sgt {w : Nat} {lo hi x c : BitVec w}
    (hlo : sle lo x) (hhi : sle x hi) (hc : slt c x) :
    sle (sbvMax lo (c + BitVec.ofNat w 1)) x ∧ sle x hi := by
  cases w with
  | zero =>
    have hx0 : signedKey x = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt x))
    have hc0 : signedKey c = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (signedKey_lt c))
    have hlt : signedKey c < signedKey x := hc
    rw [hx0, hc0] at hlt
    exact False.elim (Nat.not_lt_zero 0 hlt)
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.zero_lt_succ w'
    have hc1_le : signedKey c + 1 ≤ signedKey x := hc
    have hc1_lt : signedKey c + 1 < Nat.pow 2 (w' + 1) :=
      Nat.lt_of_le_of_lt hc1_le (signedKey_lt x)
    have hcx : sle (c + BitVec.ofNat (w' + 1) 1) x := by
      unfold sle
      rw [signedKey_add_one hw hc1_lt]
      exact hc1_le
    exact ⟨sbvMax_sle hlo hcx, hhi⟩

/-! ## Part 4: Bitfield Extraction and Byte-Swap (`bswap16`/`32`/`64`) -/

/-- Extract a `len`-bit field starting at bit offset `lo` from `x : BitVec w`.
-/
@[expose] def extractBits {w : Nat} (x : BitVec w) (lo len : Nat) : BitVec len :=
  Anneal.BitVec.setWidth len (Anneal.BitVec.ushr x lo)

/-- Exact `getLsbD` characterization of `extractBits x lo len`. -/
@[simp] theorem getLsbD_extractBits {w : Nat} (x : BitVec w)
    (lo len i : Nat) :
    Anneal.BitVec.getLsbD (extractBits x lo len) i =
      (decide (i < len) && Anneal.BitVec.getLsbD x (i + lo)) := by
  unfold extractBits
  rw [Anneal.BitVec.getLsbD_setWidth, Anneal.BitVec.getLsbD_ushr]

/-- Exact `testBit` characterization of `extractBits x lo len`. -/
theorem testBit_extractBits {w : Nat} (x : BitVec w) (lo len i : Nat) :
    (extractBits x lo len).toNat.testBit i =
      (decide (i < len) && x.toNat.testBit (i + lo)) :=
  getLsbD_extractBits x lo len i

/-- Extracting a zero-width bitfield always yields `0#0`. -/
@[simp] theorem extractBits_zero_width {w : Nat} (x : BitVec w) (lo : Nat) :
    extractBits x lo 0 = BitVec.ofNat 0 0 := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  exact False.elim (Nat.not_lt_zero i hi)

/-- `extractBits` distributes over bitwise OR. -/
theorem extractBits_or {w : Nat} (x y : BitVec w) (lo len : Nat) :
    extractBits (Anneal.BitVec.or x y) lo len =
      Anneal.BitVec.or (extractBits x lo len) (extractBits y lo len) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_extractBits, Anneal.BitVec.getLsbD_or,
    Anneal.BitVec.getLsbD_or, getLsbD_extractBits, getLsbD_extractBits,
    decide_eq_true hi, Bool.true_and, Bool.true_and, Bool.true_and]

/-- Extracting a field placed at bit offset `lo` (`lo + len ≤ w`) recovers
the original field exactly. -/
theorem extractBits_shl_setWidth {w len : Nat} (a : BitVec len) {lo : Nat}
    (hfit : lo + len ≤ w) :
    extractBits (Anneal.BitVec.shl (Anneal.BitVec.setWidth w a) lo) lo len =
      a := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  have hilo_lt : i + lo < w := by
    rw [Nat.add_comm i lo]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi lo) hfit
  rw [getLsbD_extractBits, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_shl, decide_eq_true hilo_lt, Bool.true_and,
    decide_eq_true (Nat.le_add_left lo i), Bool.true_and,
    Nat.add_sub_cancel, Anneal.BitVec.getLsbD_setWidth,
    decide_eq_true (Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.le_add_left len lo) hfit)),
    Bool.true_and]

private theorem extractBits_shl_setWidth_disjoint {w len₁ len₂ : Nat}
    (b : BitVec len₂) {lo₁ lo₂ : Nat}
    (hdisj : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁) :
    extractBits (Anneal.BitVec.shl (Anneal.BitVec.setWidth w b) lo₂) lo₁ len₁ =
      BitVec.ofNat len₁ 0 := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_extractBits, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_shl, Anneal.BitVec.getLsbD_zero]
  cases hdisj with
  | inl hleft =>
    have hlt : i + lo₁ < lo₂ := by
      rw [Nat.add_comm i lo₁]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi lo₁) hleft
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, Bool.and_false]
  | inr hright =>
    have hge : len₂ ≤ i + lo₁ - lo₂ := by
      have h1 : lo₂ + len₂ ≤ i + lo₁ :=
        Nat.le_trans hright (Nat.le_add_left lo₁ i)
      have h2 : len₂ + lo₂ ≤ (i + lo₁ - lo₂) + lo₂ := by
        rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_right lo₂ len₂) h1),
          Nat.add_comm len₂ lo₂]
        exact h1
      exact Nat.le_of_add_le_add_right h2
    rw [Anneal.BitVec.getLsbD_setWidth, Anneal.BitVec.getLsbD_ge b hge,
      Bool.and_false, Bool.and_false, Bool.and_false]

/-- Extracting two non-overlapping bitfields packed with bitwise OR recovers
both fields cleanly. -/
theorem extractBits_or_disjoint {w len₁ len₂ : Nat}
    (a : BitVec len₁) (b : BitVec len₂) {lo₁ lo₂ : Nat}
    (hfit₁ : lo₁ + len₁ ≤ w) (hfit₂ : lo₂ + len₂ ≤ w)
    (hdisj : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁) :
    let packed := Anneal.BitVec.or
      (Anneal.BitVec.shl (Anneal.BitVec.setWidth w a) lo₁)
      (Anneal.BitVec.shl (Anneal.BitVec.setWidth w b) lo₂)
    extractBits packed lo₁ len₁ = a ∧ extractBits packed lo₂ len₂ = b := by
  dsimp only
  constructor
  · rw [extractBits_or, extractBits_shl_setWidth a hfit₁,
      extractBits_shl_setWidth_disjoint b hdisj, Anneal.BitVec.or_zero]
  · rw [extractBits_or, extractBits_shl_setWidth_disjoint a (Or.symm hdisj),
      extractBits_shl_setWidth b hfit₂, Anneal.BitVec.zero_or]

/-- Exact soundness of tnum bitfield extraction (`extractBits`). -/
theorem tnum_extractBits_sound {w : Nat} {m x val : BitVec w}
    (lo len : Nat) (h : Anneal.BitVec.MaskEq m x val) :
    Anneal.BitVec.MaskEq (extractBits m lo len) (extractBits x lo len)
      (extractBits val lo len) :=
  tnum_setWidth_sound len (Anneal.BitVec.tnum_ushr_sound lo h)

/-- Move byte `src` (bits `8 * src .. 8 * src + 7`) of `x` into byte position
`dst` (bits `8 * dst .. 8 * dst + 7`). -/
@[expose] def moveByte {w : Nat} (x : BitVec w) (src dst : Nat) : BitVec w :=
  Anneal.BitVec.shl
    (Anneal.BitVec.setWidth w (extractBits x (8 * src) 8))
    (8 * dst)

private theorem getLsbD_moveByte {w : Nat} (x : BitVec w) (src dst i : Nat)
    (hi : i < w) :
    Anneal.BitVec.getLsbD (moveByte x src dst) i =
      (decide (Nat.div i 8 = dst) &&
        Anneal.BitVec.getLsbD x (Nat.mod i 8 + 8 * src)) := by
  unfold moveByte
  rw [Anneal.BitVec.getLsbD_shl, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_setWidth, getLsbD_extractBits]
  have h8pos : 0 < 8 := by decide
  cases Nat.lt_or_ge (Nat.div i 8) dst with
  | inl hlt =>
    have hne : ¬ (Nat.div i 8 = dst) := Nat.ne_of_lt hlt
    have hi_lt : i < 8 * dst := by
      rw [Nat.mul_comm 8 dst]
      exact (Nat.div_lt_iff_lt_mul h8pos).1 hlt
    rw [decide_eq_false hne, decide_eq_false (Nat.not_le_of_gt hi_lt),
      Bool.false_and, Bool.false_and]
  | inr hge =>
    cases Nat.lt_or_ge dst (Nat.div i 8) with
    | inl hgt =>
      have hne : ¬ (Nat.div i 8 = dst) := Nat.ne_of_gt hgt
      have hdst1_le : dst + 1 ≤ Nat.div i 8 := hgt
      have hmul_le : 8 * dst + 8 ≤ i := by
        have h1 : (dst + 1) * 8 ≤ i := (Nat.le_div_iff_mul_le h8pos).1 hdst1_le
        rw [Nat.succ_mul, Nat.mul_comm dst 8] at h1
        exact h1
      have hsub_ge : 8 ≤ i - 8 * dst := by
        have h1 : 8 + 8 * dst ≤ (i - 8 * dst) + 8 * dst := by
          rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_right (8 * dst) 8) hmul_le),
            Nat.add_comm 8 (8 * dst)]
          exact hmul_le
        exact Nat.le_of_add_le_add_right h1
      rw [decide_eq_false hne, Bool.false_and,
        decide_eq_false (Nat.not_lt_of_ge hsub_ge),
        Bool.false_and, Bool.and_false, Bool.and_false]
    | inr hle =>
      have heq : Nat.div i 8 = dst := Nat.le_antisymm hle hge
      have hi_decomp : 8 * dst + Nat.mod i 8 = i := by
        rw [← heq]
        exact nat_div_add_mod i 8
      have h8dst_le : 8 * dst ≤ i := by
        rw [← hi_decomp]
        exact Nat.le_add_right (8 * dst) (Nat.mod i 8)
      have hsub_eq : i - 8 * dst = Nat.mod i 8 := by
        have h1 := congrArg (fun z => z - 8 * dst) (Eq.symm hi_decomp)
        rw [Nat.add_comm (8 * dst) (Nat.mod i 8), Nat.add_sub_cancel] at h1
        exact h1
      have hmod_lt : Nat.mod i 8 < 8 := nat_mod_lt i h8pos
      have hmod_lt_w : Nat.mod i 8 < w :=
        Nat.lt_of_le_of_lt (Nat.mod_le i 8) hi
      rw [decide_eq_true heq, Bool.true_and, decide_eq_true h8dst_le,
        Bool.true_and, hsub_eq, decide_eq_true hmod_lt_w, Bool.true_and,
        decide_eq_true hmod_lt, Bool.true_and]

/-- Build the low `k` destination bytes of byte-reversed `x : BitVec (8 * n)`
via structural `@Nat.rec`. -/
@[expose] def bswapBytesAux {n : Nat} (x : BitVec (8 * n)) (k : Nat) : BitVec (8 * n) :=
  @Nat.rec (fun _ => BitVec (8 * n))
    (BitVec.ofNat (8 * n) 0)
    (fun j acc => Anneal.BitVec.or acc (moveByte x (n - 1 - j) j))
    k

private theorem bswapBytesAux_succ {n : Nat} (x : BitVec (8 * n)) (k : Nat) :
    bswapBytesAux x (k + 1) =
      Anneal.BitVec.or (bswapBytesAux x k) (moveByte x (n - 1 - k) k) :=
  rfl

private theorem getLsbD_bswapBytesAux {n : Nat} (x : BitVec (8 * n)) (k : Nat) :
    ∀ i, i < 8 * n →
      Anneal.BitVec.getLsbD (bswapBytesAux x k) i =
        (decide (Nat.div i 8 < k) &&
          Anneal.BitVec.getLsbD x (Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8))) := by
  induction k with
  | zero =>
    intro i _
    change Anneal.BitVec.getLsbD (BitVec.ofNat (8 * n) 0) i = _
    rw [Anneal.BitVec.getLsbD_zero, decide_eq_false (Nat.not_lt_zero _),
      Bool.false_and]
  | succ k ih =>
    intro i hi
    rw [bswapBytesAux_succ, Anneal.BitVec.getLsbD_or, ih i hi,
      getLsbD_moveByte x (n - 1 - k) k i hi]
    cases Nat.lt_or_ge (Nat.div i 8) k with
    | inl hlt =>
      rw [decide_eq_true hlt, decide_eq_true (Nat.lt_succ_of_lt hlt),
        decide_eq_false (Nat.ne_of_lt hlt), Bool.true_and,
        Bool.false_and, Bool.or_false]
    | inr hge =>
      cases Nat.lt_or_ge k (Nat.div i 8) with
      | inl hgt =>
        rw [decide_eq_false (Nat.not_lt_of_ge hge),
          decide_eq_false (Nat.not_lt_of_ge hgt),
          decide_eq_false (Nat.ne_of_gt hgt), Bool.false_and, Bool.false_and,
          Bool.false_or]
      | inr hle =>
        have heq : Nat.div i 8 = k := Nat.le_antisymm hle hge
        rw [heq, decide_eq_false (Nat.lt_irrefl k),
          decide_eq_true (Nat.lt_succ_self k), decide_eq_true rfl,
          Bool.false_and, Bool.true_and, Bool.false_or]

/-- Reverse the `n` bytes of a `(8 * n)`-bit bitvector. -/
@[expose] def bswapBytes (n : Nat) (x : BitVec (8 * n)) : BitVec (8 * n) :=
  bswapBytesAux x n

/-- Exact `getLsbD` characterization of `bswapBytes n x`. -/
@[simp] theorem getLsbD_bswapBytes (n : Nat) (x : BitVec (8 * n)) (i : Nat) :
    Anneal.BitVec.getLsbD (bswapBytes n x) i =
      (decide (i < 8 * n) &&
        Anneal.BitVec.getLsbD x (Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8))) := by
  cases Nat.lt_or_ge i (8 * n) with
  | inr hge =>
    rw [Anneal.BitVec.getLsbD_ge _ hge,
      decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
  | inl hlt =>
    have hdiv_lt : Nat.div i 8 < n := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 8), Nat.mul_comm n 8]
      exact hlt
    unfold bswapBytes
    rw [getLsbD_bswapBytesAux x n i hlt, decide_eq_true hdiv_lt,
      decide_eq_true hlt, Bool.true_and]

/-- Byte reversal is an involution for every byte count `n`. -/
@[simp] theorem bswapBytes_bswapBytes (n : Nat) (x : BitVec (8 * n)) :
    bswapBytes n (bswapBytes n x) = x := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  have h8pos : 0 < 8 := by decide
  have hdiv_lt : Nat.div i 8 < n := by
    rw [nat_div_lt_iff_lt_mul h8pos, Nat.mul_comm n 8]
    exact hi
  have hdiv_le : Nat.div i 8 ≤ n - 1 := Nat.le_sub_one_of_lt hdiv_lt
  have hrev_lt : n - 1 - Nat.div i 8 < n :=
    Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) (Nat.div i 8))
      (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hdiv_lt) Nat.one_pos)
  let j := Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8)
  have hj_lt : j < 8 * n := by
    have hmod_lt : Nat.mod i 8 < 8 := nat_mod_lt i h8pos
    have h1 : j < 8 + 8 * (n - 1 - Nat.div i 8) :=
      Nat.add_lt_add_right hmod_lt _
    have h2 : 8 + 8 * (n - 1 - Nat.div i 8) =
        8 * ((n - 1 - Nat.div i 8) + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    have h3 : 8 * ((n - 1 - Nat.div i 8) + 1) ≤ 8 * n :=
      Nat.mul_le_mul_left 8 hrev_lt
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 h3
  have hj_div : Nat.div j 8 = n - 1 - Nat.div i 8 := by
    unfold j
    rw [nat_add_mul_div_left _ _ h8pos,
      nat_div_eq_of_lt (nat_mod_lt i h8pos), Nat.zero_add]
  have hj_mod : Nat.mod j 8 = Nat.mod i 8 := by
    unfold j
    rw [nat_add_mul_mod_self_left, nat_mod_eq_of_lt (nat_mod_lt i h8pos)]
  have hj_back : Nat.mod j 8 + 8 * (n - 1 - Nat.div j 8) = i := by
    rw [hj_mod, hj_div, nat_sub_sub_self hdiv_le, Nat.add_comm]
    exact nat_div_add_mod i 8
  rw [getLsbD_bswapBytes, decide_eq_true hi, Bool.true_and,
    getLsbD_bswapBytes, decide_eq_true hj_lt, Bool.true_and, hj_back]

/-- Byte reversal is injective for every byte count `n`. -/
theorem bswapBytes_injective {n : Nat} {x y : BitVec (8 * n)}
    (h : bswapBytes n x = bswapBytes n y) : x = y := by
  rw [← bswapBytes_bswapBytes n x, ← bswapBytes_bswapBytes n y, h]

/-- Exact soundness of tnum byte reversal (`bswapBytes`). -/
theorem tnum_bswapBytes_sound (n : Nat) {m x val : BitVec (8 * n)}
    (h : Anneal.BitVec.MaskEq m x val) :
    Anneal.BitVec.MaskEq (bswapBytes n m) (bswapBytes n x)
      (bswapBytes n val) := by
  rw [Anneal.BitVec.maskEq_iff_getLsbD]
  intro i hi hm
  have h8pos : 0 < 8 := by decide
  have hdiv_lt : Nat.div i 8 < n := by
    rw [nat_div_lt_iff_lt_mul h8pos, Nat.mul_comm n 8]
    exact hi
  have hrev_lt : n - 1 - Nat.div i 8 < n :=
    Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) (Nat.div i 8))
      (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hdiv_lt) Nat.one_pos)
  have hj_lt : Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8) < 8 * n := by
    have h1 : Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8) <
        8 + 8 * (n - 1 - Nat.div i 8) :=
      Nat.add_lt_add_right (nat_mod_lt i h8pos) _
    have h2 : 8 + 8 * (n - 1 - Nat.div i 8) =
        8 * ((n - 1 - Nat.div i 8) + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 8 hrev_lt)
  rw [getLsbD_bswapBytes, decide_eq_true hi, Bool.true_and] at hm
  rw [getLsbD_bswapBytes, getLsbD_bswapBytes, decide_eq_true hi,
    Bool.true_and]
  exact Anneal.BitVec.maskEq_iff_getLsbD.1 h _ hj_lt hm

/-- 16-bit byte swap (`u16::swap_bytes`). -/
@[expose] def bswap16 (x : BitVec 16) : BitVec 16 :=
  bswapBytes 2 x

/-- 32-bit byte swap (`u32::swap_bytes`). -/
@[expose] def bswap32 (x : BitVec 32) : BitVec 32 :=
  bswapBytes 4 x

/-- 64-bit byte swap (`u64::swap_bytes`). -/
@[expose] def bswap64 (x : BitVec 64) : BitVec 64 :=
  bswapBytes 8 x

/-- `bswap16` is an involution (`bswap16 (bswap16 x) = x`). -/
@[simp] theorem bswap16_bswap16 (x : BitVec 16) :
    bswap16 (bswap16 x) = x :=
  bswapBytes_bswapBytes 2 x

/-- `bswap32` is an involution (`bswap32 (bswap32 x) = x`). -/
@[simp] theorem bswap32_bswap32 (x : BitVec 32) :
    bswap32 (bswap32 x) = x :=
  bswapBytes_bswapBytes 4 x

/-- `bswap64` is an involution (`bswap64 (bswap64 x) = x`). -/
@[simp] theorem bswap64_bswap64 (x : BitVec 64) :
    bswap64 (bswap64 x) = x :=
  bswapBytes_bswapBytes 8 x

/-- `bswap16` is injective. -/
theorem bswap16_injective {x y : BitVec 16} (h : bswap16 x = bswap16 y) :
    x = y :=
  bswapBytes_injective h

/-- `bswap32` is injective. -/
theorem bswap32_injective {x y : BitVec 32} (h : bswap32 x = bswap32 y) :
    x = y :=
  bswapBytes_injective h

/-- `bswap64` is injective. -/
theorem bswap64_injective {x y : BitVec 64} (h : bswap64 x = bswap64 y) :
    x = y :=
  bswapBytes_injective h

/-- Shift-and-OR characterization of `bswap16`:
`bswap16 x = (x >>> 8) ||| (x <<< 8)`. -/
theorem bswap16_eq_ushr_or_shl (x : BitVec 16) :
    bswap16 x =
      Anneal.BitVec.or (Anneal.BitVec.ushr x 8) (Anneal.BitVec.shl x 8) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold bswap16
  rw [getLsbD_bswapBytes, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_ushr,
    Anneal.BitVec.getLsbD_shl, decide_eq_true hi, Bool.true_and]
  have h8pos : 0 < 8 := by decide
  cases Nat.lt_or_ge i 8 with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, Bool.or_false,
      nat_div_eq_of_lt hlt, nat_mod_eq_of_lt hlt]
  | inr hge =>
    have hdiv1 : Nat.div i 8 = 1 := by
      have h1 : 1 ≤ Nat.div i 8 := by
        rw [nat_le_div_iff_mul_le h8pos, Nat.one_mul]
        exact hge
      have h2 : Nat.div i 8 < 2 := by
        rw [nat_div_lt_iff_lt_mul h8pos]
        exact hi
      exact Nat.le_antisymm (Nat.le_of_lt_succ h2) h1
    have hmod_eq : Nat.mod i 8 = i - 8 := by
      have hdecomp := nat_div_add_mod i 8
      rw [hdiv1, Nat.mul_one] at hdecomp
      have h1 := congrArg (fun z => z - 8) hdecomp
      rw [Nat.add_comm 8 (Nat.mod i 8), Nat.add_sub_cancel] at h1
      exact h1
    have hge16 : 16 ≤ i + 8 := Nat.add_le_add_right hge 8
    rw [decide_eq_true hge, Bool.true_and, Anneal.BitVec.getLsbD_ge x hge16,
      Bool.false_or, hdiv1, hmod_eq]
    rfl

end Anneal.BitVecArith

end
