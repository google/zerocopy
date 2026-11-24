-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.SimpLemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Anneal.NatBitwise

public section

namespace Anneal.AiPcc

/-!
# Bitwise Extensionality and Modular Arithmetic (`Anneal.AiPcc.BitArith`)

Width-capped (`1 <= w <= 128`) modular arithmetic, `bitAt` extensionality, and
structural `Nat` bitwise/division lemmas supporting the `Tnum`,
`WrappedInterval`, `StridedCong`, and reduced-product domains without `omega`
or `noncomputable` definitions.
-/

/-- True iff `1 ≤ w ≤ 128` (a supported MIR integer bitwidth). -/
@[expose] def validWidth (w : Nat) : Bool :=
  Nat.ble 1 w && Nat.ble w 128

/-- `2^w` computed as `1 <<< w`. -/
@[expose] def modPow2 (w : Nat) : Nat :=
  Nat.shiftLeft 1 w

/-- Unsigned `w`-bit modular reduction `x mod 2^w`. -/
@[expose] def wrapVal (w x : Nat) : Nat :=
  Nat.mod x (modPow2 w)

/-- Tests whether bit `k` of `n` is `1` (`(n / 2^k) mod 2 == 1`). -/
@[expose] def bitAt (n k : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div n (modPow2 k)) 2) 1

/-- Bitwise relative complement `a & ~b` (`a ^^^ (a &&& b)`). -/
@[expose] def andNot (a b : Nat) : Nat :=
  Nat.xor a (Nat.land a b)

/-- `modPow2 0 = 1`. -/
theorem modPow2_zero : modPow2 0 = 1 := rfl

/-- `n <<< k = n * 2^k`. -/
theorem shiftLeft_mul_pow : ∀ (k n : Nat), Nat.shiftLeft n k = n * Nat.pow 2 k
  | 0, n => by dsimp only [Nat.shiftLeft, Nat.pow]; rw [Nat.mul_one]
  | k + 1, n => by
    dsimp only [Nat.shiftLeft]
    have hPow : Nat.pow 2 (k + 1) = Nat.pow 2 k * 2 := by
      have h := @Nat.pow_succ 2 k
      dsimp only [HPow.hPow, Pow.pow] at h
      exact h
    rw [shiftLeft_mul_pow k (2 * n), hPow]
    rw [Nat.mul_comm 2 n, Nat.mul_assoc n 2 (Nat.pow 2 k), Nat.mul_comm 2 (Nat.pow 2 k)]

/-- `modPow2 w = 2^w`. -/
theorem modPow2_eq_pow (w : Nat) : modPow2 w = Nat.pow 2 w := by
  dsimp only [modPow2]
  rw [shiftLeft_mul_pow, Nat.one_mul]

/-- `modPow2 (k + 1) = 2 * modPow2 k`. -/
theorem modPow2_succ (k : Nat) : modPow2 (k + 1) = 2 * modPow2 k := by
  have hPow : Nat.pow 2 (k + 1) = Nat.pow 2 k * 2 := by
    have h := @Nat.pow_succ 2 k
    dsimp only [HPow.hPow, Pow.pow] at h
    exact h
  rw [modPow2_eq_pow (k + 1), modPow2_eq_pow k, hPow, Nat.mul_comm]

/-- `0 < modPow2 w` for every bitwidth `w`. -/
theorem modPow2_pos : ∀ w : Nat, 0 < modPow2 w
  | 0 => Nat.zero_lt_succ 0
  | w + 1 => by
    rw [modPow2_succ w, Nat.two_mul]
    have hw := modPow2_pos w
    exact Nat.lt_of_lt_of_le hw (Nat.le_add_right (modPow2 w) (modPow2 w))

/-- `modPow2 (a + b) = modPow2 a * modPow2 b`. -/
theorem modPow2_add (a b : Nat) : modPow2 (a + b) = modPow2 a * modPow2 b := by
  induction a with
  | zero => rw [Nat.zero_add, modPow2_zero, Nat.one_mul]
  | succ a ih =>
    rw [Nat.succ_add, modPow2_succ (a + b), ih, modPow2_succ a, Nat.mul_assoc]

/-- Monotonicity of `modPow2`: `a ≤ b → modPow2 a ≤ modPow2 b`. -/
theorem modPow2_mono {a b : Nat} (h : a ≤ b) : modPow2 a ≤ modPow2 b := by
  have hSub : a + (b - a) = b := Nat.add_sub_of_le h
  rw [← hSub, modPow2_add]
  have hPos := modPow2_pos (b - a)
  have hMul := Nat.mul_le_mul_left (modPow2 a) hPos
  rw [Nat.mul_one] at hMul
  exact hMul

/-- Right cancellation of strict inequality across addition. -/
theorem nat_lt_of_add_lt_add_right {a b c : Nat} (h : a + c < b + c) : a < b := by
  induction c with
  | zero => rw [Nat.add_zero, Nat.add_zero] at h; exact h
  | succ c ih =>
    rw [Nat.add_succ, Nat.add_succ] at h
    exact ih (Nat.lt_of_succ_lt_succ h)

/-- Left cancellation of strict inequality across addition. -/
theorem nat_lt_of_add_lt_add_left {a b c : Nat} (h : c + a < c + b) : a < b := by
  rw [Nat.add_comm c a, Nat.add_comm c b] at h
  exact nat_lt_of_add_lt_add_right h

/-- `a ≤ Nat.max a b`. -/
theorem nat_le_max_left (a b : Nat) : a ≤ Nat.max a b := by
  dsimp only [Nat.max]
  rw [Nat.max_def]
  cases Nat.lt_or_ge b a with
  | inl hlt =>
    rw [ite_eq_right (Nat.not_le_of_gt hlt)]
    exact Nat.le_refl a
  | inr hle =>
    rw [ite_eq_left hle]
    exact hle

/-- `b ≤ Nat.max a b`. -/
theorem nat_le_max_right (a b : Nat) : b ≤ Nat.max a b := by
  dsimp only [Nat.max]
  rw [Nat.max_def]
  cases Nat.lt_or_ge b a with
  | inl hlt =>
    rw [ite_eq_right (Nat.not_le_of_gt hlt)]
    exact Nat.le_of_lt hlt
  | inr hle =>
    rw [ite_eq_left hle]
    exact Nat.le_refl b

/-- Strict inequality cancellation on left multiplication. -/
theorem nat_lt_of_mul_lt_mul_left {a b c : Nat} (h : a * b < a * c) : b < c := by
  cases Nat.lt_or_ge b c with
  | inl hlt => exact hlt
  | inr hge => exact False.elim (Nat.not_le_of_gt h (Nat.mul_le_mul_left a hge))

/-- `Nat.min a b ≤ a`. -/
theorem nat_min_le_left (a b : Nat) : Nat.min a b ≤ a := by
  dsimp only [Nat.min]
  rw [Nat.min_def]
  cases Nat.lt_or_ge b a with
  | inl hlt => rw [ite_eq_right (Nat.not_le_of_gt hlt)]; exact Nat.le_of_lt hlt
  | inr hle => rw [ite_eq_left hle]; exact Nat.le_refl a

/-- `Nat.min a b ≤ b`. -/
theorem nat_min_le_right (a b : Nat) : Nat.min a b ≤ b := by
  dsimp only [Nat.min]
  rw [Nat.min_def]
  cases Nat.lt_or_ge b a with
  | inl hlt => rw [ite_eq_right (Nat.not_le_of_gt hlt)]; exact Nat.le_refl b
  | inr hle => rw [ite_eq_left hle]; exact hle

/-- Greatest-lower-bound property of `Nat.min`. -/
theorem nat_le_min {c a b : Nat} (hca : c ≤ a) (hcb : c ≤ b) : c ≤ Nat.min a b := by
  dsimp only [Nat.min]
  rw [Nat.min_def]
  cases Nat.lt_or_ge b a with
  | inl hlt => rw [ite_eq_right (Nat.not_le_of_gt hlt)]; exact hcb
  | inr hle => rw [ite_eq_left hle]; exact hca

/-- Remainder bound `Nat.mod a b < b` when `0 < b`. -/
theorem nat_mod_lt (a : Nat) {b : Nat} (h : 0 < b) : Nat.mod a b < b := Nat.mod_lt a h

/-- `Nat.mod n n = 0`. -/
theorem nat_mod_self (n : Nat) : Nat.mod n n = 0 := Nat.mod_self n

/-- `Nat.mod n 1 = 0`. -/
theorem nat_mod_one (n : Nat) : Nat.mod n 1 = 0 := Nat.mod_one n

/-- `Nat.mod a b = a` when `a < b`. -/
theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a := Nat.mod_eq_of_lt h

/-- One-step remainder reduction `Nat.mod a b = Nat.mod (a - b) b` for `b ≤ a`.
-/
theorem nat_mod_eq_sub_mod {a b : Nat} (h : b ≤ a) :
    Nat.mod a b = Nat.mod (a - b) b := Nat.mod_eq_sub_mod h

/-- `Nat.mod (a + b) b = Nat.mod a b`. -/
theorem nat_add_mod_self_right (a b : Nat) :
    Nat.mod (a + b) b = Nat.mod a b := Nat.add_mod_right a b

/-- `Nat.mod (a + b) a = Nat.mod b a`. -/
theorem nat_add_mod_self_left (a b : Nat) : Nat.mod (a + b) a = Nat.mod b a := Nat.add_mod_left a b

/-- `Nat.mod (x + m * q) m = Nat.mod x m`. -/
theorem nat_add_mul_mod_self_left (x m q : Nat) :
    Nat.mod (x + m * q) m = Nat.mod x m := Nat.add_mul_mod_self_left x m q

/-- `Nat.mod (a * b + c) a = Nat.mod c a`. -/
theorem nat_mul_add_mod_self_left (a b c : Nat) :
    Nat.mod (a * b + c) a = Nat.mod c a := Nat.mul_add_mod_self_left a b c

/-- `Nat.mod (x + q * m) m = Nat.mod x m`. -/
theorem nat_add_mul_mod_self_right (x q m : Nat) :
    Nat.mod (x + q * m) m = Nat.mod x m := Nat.add_mul_mod_self_right x q m

/-- Euclidean division identity `k * (m / k) + m % k = m`. -/
theorem nat_div_add_mod (m k : Nat) : k * Nat.div m k + Nat.mod m k = m := Nat.div_add_mod m k

/-- `x / k < n ↔ x < n * k` for `0 < k`. -/
theorem nat_div_lt_iff_lt_mul {x k n : Nat} (hk : 0 < k) :
    Nat.div x k < n ↔ x < n * k := Nat.div_lt_iff_lt_mul hk

/-- Dividing by `2^(k + 1)` shifts right by one bit then divides by `2^k`. -/
theorem nat_div_modPow2_succ (n k : Nat) :
    Nat.div n (modPow2 (k + 1)) = Nat.div (Nat.div n 2) (modPow2 k) := by
  rw [modPow2_succ k]
  have h : Nat.div (Nat.div n 2) (modPow2 k) = Nat.div n (2 * modPow2 k) :=
    Nat.div_div_eq_div_mul n 2 (modPow2 k)
  exact h.symm

/-- Every natural number has remainder `0` or `1` modulo `2`. -/
theorem mod2_cases (n : Nat) : Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hLt : Nat.mod n 2 < 2 := Nat.mod_lt n (Nat.zero_lt_succ 1)
  cases h : Nat.mod n 2 with
  | zero => left; rfl
  | succ m =>
    cases m with
    | zero => right; rfl
    | succ m' =>
      rw [h] at hLt
      have hBad := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hLt)
      nomatch hBad

/-- Two naturals with equal `mod 2` and `div 2` are equal. -/
theorem nat_eq_of_mod2_div2 {a b : Nat}
    (hMod : Nat.mod a 2 = Nat.mod b 2)
    (hDiv : Nat.div a 2 = Nat.div b 2) : a = b := by
  have ha := Nat.div_add_mod a 2
  have hb := Nat.div_add_mod b 2
  dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at ha hb
  rw [← ha, ← hb, hDiv, hMod]

/-- Equal bit `0` implies equal remainder modulo `2`. -/
theorem mod2_eq_of_bitAt_eq {a b : Nat} (h : bitAt a 0 = bitAt b 0) :
    Nat.mod a 2 = Nat.mod b 2 := by
  dsimp only [bitAt, modPow2_zero] at h
  have ha : Nat.div a 1 = a := Nat.div_one a
  have hb : Nat.div b 1 = b := Nat.div_one b
  rw [ha, hb] at h
  cases mod2_cases a with
  | inl ha0 =>
    cases mod2_cases b with
    | inl hb0 => rw [ha0, hb0]
    | inr hb1 => rw [ha0, hb1] at h; nomatch h
  | inr ha1 =>
    cases mod2_cases b with
    | inl hb0 => rw [ha1, hb0] at h; nomatch h
    | inr hb1 => rw [ha1, hb1]

/-- Bit `0` tests whether `n mod 2 == 1`. -/
theorem bitAt_zero (n : Nat) : bitAt n 0 = Nat.beq (Nat.mod n 2) 1 := by
  dsimp only [bitAt, modPow2_zero]
  have h : Nat.div n 1 = n := Nat.div_one n
  rw [h]

/-- `bitAt n (k + 1) = bitAt (n / 2) k`. -/
theorem bitAt_succ (n k : Nat) : bitAt n (k + 1) = bitAt (Nat.div n 2) k := by
  dsimp only [bitAt]
  rw [nat_div_modPow2_succ]

/-- All bits of `0` are `false`. -/
theorem bitAt_zero_nat (k : Nat) : bitAt 0 k = false := by
  dsimp only [bitAt]
  have h0 : Nat.div 0 (modPow2 k) = 0 := Nat.zero_div (modPow2 k)
  rw [h0]
  rfl

/-- A natural number whose bits are all `false` equals `0`. -/
theorem nat_zero_of_bitAt_false (y : Nat) (hAll : ∀ k : Nat, bitAt y k = false) : y = 0 := by
  refine Nat.strongRecOn (motive := fun n => (∀ k, bitAt n k = false) → n = 0) y ?_ hAll
  intro n ih hF
  cases n with
  | zero => rfl
  | succ m =>
    have hDivLt : Nat.div (m + 1) 2 < m + 1 := by
      have h := Nat.div_lt_self (Nat.zero_lt_succ m) (Nat.lt_succ_self 1)
      dsimp only [HDiv.hDiv, Div.div] at h
      exact h
    have hDivZero : Nat.div (m + 1) 2 = 0 :=
      ih (Nat.div (m + 1) 2) hDivLt (fun k => by rw [← bitAt_succ (m + 1) k]; exact hF (k + 1))
    have hModZero : Nat.mod (m + 1) 2 = 0 := by
      have h0 := hF 0
      rw [bitAt_zero] at h0
      cases mod2_cases (m + 1) with
      | inl hm0 => exact hm0
      | inr hm1 => rw [hm1] at h0; nomatch h0
    have hTot : (m + 1) = 0 := nat_eq_of_mod2_div2 (b := 0) hModZero hDivZero
    nomatch hTot

/-- Bitwise extensionality on `Nat`: equal `bitAt` at every index implies `a =
b`. -/
theorem nat_eq_of_bitAt : ∀ a b : Nat, (∀ k : Nat, bitAt a k = bitAt b k) → a = b := by
  intro a
  refine Nat.strongRecOn (motive := fun x => ∀ y, (∀ k, bitAt x k = bitAt y k) → x = y) a ?_
  intro x ih y hAll
  cases x with
  | zero =>
    have hFy : ∀ k, bitAt y k = false := fun k => by rw [← hAll k, bitAt_zero_nat k]
    exact (nat_zero_of_bitAt_false y hFy).symm
  | succ m =>
    have hDivLt : Nat.div (m + 1) 2 < m + 1 := by
      have h := Nat.div_lt_self (Nat.zero_lt_succ m) (Nat.lt_succ_self 1)
      dsimp only [HDiv.hDiv, Div.div] at h
      exact h
    have hDivEq : Nat.div (m + 1) 2 = Nat.div y 2 := by
      apply ih (Nat.div (m + 1) 2) hDivLt
      intro k
      rw [← bitAt_succ (m + 1) k, ← bitAt_succ y k]
      exact hAll (k + 1)
    have hModEq : Nat.mod (m + 1) 2 = Nat.mod y 2 := mod2_eq_of_bitAt_eq (hAll 0)
    exact nat_eq_of_mod2_div2 hModEq hDivEq

/-- `(2 * r) mod 2 = 0`. -/
theorem mod2_two_mul (r : Nat) : Nat.mod (2 * r) 2 = 0 := by
  have h := Nat.mul_mod_right 2 r
  dsimp only [HMod.hMod, Mod.mod] at h
  exact h

/-- `(2 * r + 1) mod 2 = 1`. -/
theorem mod2_two_mul_add_one (r : Nat) : Nat.mod (2 * r + 1) 2 = 1 := by
  have h := Nat.mul_add_mod_self_left 2 r 1
  dsimp only [HMod.hMod, Mod.mod] at h
  exact h

/-- `(2 * r) / 2 = r`. -/
theorem div2_two_mul (r : Nat) : Nat.div (2 * r) 2 = r := by
  have h := Nat.mul_div_right r (Nat.zero_lt_succ 1)
  dsimp only [HDiv.hDiv, Div.div] at h
  exact h

/-- `(2 * r + 1) / 2 = r`. -/
theorem div2_two_mul_add_one (r : Nat) : Nat.div (2 * r + 1) 2 = r := by
  have h := Nat.add_mul_div_left 1 r (Nat.zero_lt_succ 1)
  dsimp only [HDiv.hDiv, Div.div] at h
  have h12 : Nat.div 1 2 = 0 := rfl
  rw [Nat.add_comm (2 * r) 1, h, h12, Nat.zero_add]

/-- Rewrites `if b = true then x else y` as a `Bool` match. -/
theorem ite_bool_eq_match {α : Type} (b : Bool) (x y : α) :
    (if b = true then x else y) = match b with | true => x | false => y := by
  cases b <;> rfl

/-- Unfolds `Nat.bitwise f 0 m`. -/
theorem bitwise_zero_left (f : Bool → Bool → Bool) (m : Nat) :
    Nat.bitwise f 0 m = match f false true with | true => m | false => 0 := by
  rw [Anneal.NatBitwise.unfold_eq f 0 m, ite_eq_left rfl, ite_bool_eq_match]

/-- Unfolds `Nat.bitwise f (n' + 1) 0`. -/
theorem bitwise_zero_right (f : Bool → Bool → Bool) (n' : Nat) :
    Nat.bitwise f (n' + 1) 0 = match f true false with | true => n' + 1 | false => 0 := by
  rw [Anneal.NatBitwise.unfold_eq f (n' + 1) 0, ite_eq_right (Nat.succ_ne_zero n'),
      ite_eq_left rfl, ite_bool_eq_match]

/-- Reflexivity of `Nat.beq`. -/
theorem nat_beq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => nat_beq_refl n

/-- Soundness of `a = b → Nat.beq a b = true`. -/
theorem nat_beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [h]; exact nat_beq_refl b

/-- One-bit recurrence for `Nat.bitwise f (n' + 1) (m' + 1)`. -/
theorem bitwise_succ_succ (f : Bool → Bool → Bool) (n' m' : Nat) :
    Nat.bitwise f (n' + 1) (m' + 1) =
      match f (Nat.beq (Nat.mod (n' + 1) 2) 1) (Nat.beq (Nat.mod (m' + 1) 2) 1) with
      | true =>
        Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2) +
          Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2) + 1
      | false =>
        Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2) +
          Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2) := by
  rw [Anneal.NatBitwise.unfold_eq f (n' + 1) (m' + 1)]
  rw [ite_eq_right (Nat.succ_ne_zero n'), ite_eq_right (Nat.succ_ne_zero m')]
  dsimp only [HDiv.hDiv, Div.div]
  cases hn : Nat.beq (Nat.mod (n' + 1) 2) 1 <;> cases hm : Nat.beq (Nat.mod (m' + 1) 2) 1
  · have hn0 : ¬ (Nat.mod (n' + 1) 2 = 1) := fun h => by
      have ht := nat_beq_of_eq h
      rw [ht] at hn; nomatch hn
    have hm0 : ¬ (Nat.mod (m' + 1) 2 = 1) := fun h => by
      have ht := nat_beq_of_eq h
      rw [ht] at hm; nomatch hm
    change (let b₁ := Nat.mod (n' + 1) 2 = 1; let b₂ := Nat.mod (m' + 1) 2 = 1;
      let r := Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2);
      if f (decide b₁) (decide b₂) = true then r + r + 1 else r + r) = _
    dsimp only
    rw [decide_eq_false hn0, decide_eq_false hm0, ite_bool_eq_match]
  · have hn0 : ¬ (Nat.mod (n' + 1) 2 = 1) := fun h => by
      have ht := nat_beq_of_eq h
      rw [ht] at hn; nomatch hn
    have hm1 : Nat.mod (m' + 1) 2 = 1 := Nat.eq_of_beq_eq_true hm
    change (let b₁ := Nat.mod (n' + 1) 2 = 1; let b₂ := Nat.mod (m' + 1) 2 = 1;
      let r := Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2);
      if f (decide b₁) (decide b₂) = true then r + r + 1 else r + r) = _
    dsimp only
    rw [decide_eq_false hn0, decide_eq_true hm1, ite_bool_eq_match]
  · have hn1 : Nat.mod (n' + 1) 2 = 1 := Nat.eq_of_beq_eq_true hn
    have hm0 : ¬ (Nat.mod (m' + 1) 2 = 1) := fun h => by
      have ht := nat_beq_of_eq h
      rw [ht] at hm; nomatch hm
    change (let b₁ := Nat.mod (n' + 1) 2 = 1; let b₂ := Nat.mod (m' + 1) 2 = 1;
      let r := Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2);
      if f (decide b₁) (decide b₂) = true then r + r + 1 else r + r) = _
    dsimp only
    rw [decide_eq_true hn1, decide_eq_false hm0, ite_bool_eq_match]
  · have hn1 : Nat.mod (n' + 1) 2 = 1 := Nat.eq_of_beq_eq_true hn
    have hm1 : Nat.mod (m' + 1) 2 = 1 := Nat.eq_of_beq_eq_true hm
    change (let b₁ := Nat.mod (n' + 1) 2 = 1; let b₂ := Nat.mod (m' + 1) 2 = 1;
      let r := Nat.bitwise f (Nat.div (n' + 1) 2) (Nat.div (m' + 1) 2);
      if f (decide b₁) (decide b₂) = true then r + r + 1 else r + r) = _
    dsimp only
    rw [decide_eq_true hn1, decide_eq_true hm1, ite_bool_eq_match]

/-- Least-significant bit of `Nat.bitwise f n m` when `f false false = false`.
-/
theorem bitwise_mod2 (f : Bool → Bool → Bool) (hf : f false false = false) (n m : Nat) :
    Nat.mod (Nat.bitwise f n m) 2 =
      match f (Nat.beq (Nat.mod n 2) 1) (Nat.beq (Nat.mod m 2) 1) with
      | true => 1
      | false => 0 := by
  cases n with
  | zero =>
    rw [bitwise_zero_left]
    have h0 : Nat.mod 0 2 = 0 := rfl
    rw [h0]
    dsimp only [Nat.beq]
    cases hft : f false true with
    | true =>
      cases mod2_cases m with
      | inl hm0 => rw [hm0]; dsimp only [Nat.beq]; rw [hf]
      | inr hm1 => rw [hm1]; dsimp only [Nat.beq]; rw [hft]
    | false =>
      cases mod2_cases m with
      | inl hm0 => rw [hm0]; dsimp only [Nat.beq]; rw [hf]
      | inr hm1 => rw [hm1]; dsimp only [Nat.beq]; rw [hft]
  | succ n' =>
    cases m with
    | zero =>
      rw [bitwise_zero_right]
      have h0 : Nat.mod 0 2 = 0 := rfl
      rw [h0]
      dsimp only [Nat.beq]
      cases htf : f true false with
      | true =>
        cases mod2_cases (n' + 1) with
        | inl hn0 => rw [hn0]; dsimp only [Nat.beq]; rw [hf]
        | inr hn1 => rw [hn1]; dsimp only [Nat.beq]; rw [htf]
      | false =>
        cases mod2_cases (n' + 1) with
        | inl hn0 => rw [hn0]; dsimp only [Nat.beq]; rw [hf]
        | inr hn1 => rw [hn1]; dsimp only [Nat.beq]; rw [htf]
    | succ m' =>
      rw [bitwise_succ_succ]
      cases f (Nat.beq (Nat.mod (n' + 1) 2) 1) (Nat.beq (Nat.mod (m' + 1) 2) 1) with
      | true => rw [← Nat.two_mul]; exact mod2_two_mul_add_one _
      | false => rw [← Nat.two_mul]; exact mod2_two_mul _

/-- Right-shift commutation `(Nat.bitwise f n m) / 2 = Nat.bitwise f (n / 2) (m
/ 2)`. -/
theorem bitwise_div2 (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.div (Nat.bitwise f n m) 2 = Nat.bitwise f (Nat.div n 2) (Nat.div m 2) := by
  cases n with
  | zero =>
    rw [bitwise_zero_left]
    have hz : Nat.div 0 2 = 0 := rfl
    rw [hz, bitwise_zero_left]
    cases f false true with
    | true => rfl
    | false => exact Nat.zero_div 2
  | succ n' =>
    cases m with
    | zero =>
      rw [bitwise_zero_right]
      have hz : Nat.div 0 2 = 0 := rfl
      rw [hz]
      have hR : Nat.bitwise f (Nat.div (n' + 1) 2) 0 =
          match f true false with | true => Nat.div (n' + 1) 2 | false => 0 := by
        cases hq : Nat.div (n' + 1) 2 with
        | zero => rw [bitwise_zero_left]; cases f false true <;> cases f true false <;> rfl
        | succ k => rw [bitwise_zero_right]
      rw [hR]
      cases f true false with
      | true => rfl
      | false => exact Nat.zero_div 2
    | succ m' =>
      rw [bitwise_succ_succ]
      cases f (Nat.beq (Nat.mod (n' + 1) 2) 1) (Nat.beq (Nat.mod (m' + 1) 2) 1) with
      | true => rw [← Nat.two_mul]; exact div2_two_mul_add_one _
      | false => rw [← Nat.two_mul]; exact div2_two_mul _

/-- Bitwise homomorphism `bitAt (Nat.bitwise f n m) k = f (bitAt n k) (bitAt m
k)`. -/
theorem bitAt_bitwise (f : Bool → Bool → Bool) (hf : f false false = false)
    (n m k : Nat) : bitAt (Nat.bitwise f n m) k = f (bitAt n k) (bitAt m k) := by
  revert n m
  induction k with
  | zero =>
    intro n m
    rw [bitAt_zero, bitAt_zero, bitAt_zero, bitwise_mod2 f hf]
    cases f (Nat.beq (Nat.mod n 2) 1) (Nat.beq (Nat.mod m 2) 1) <;> rfl
  | succ k ih =>
    intro n m
    rw [bitAt_succ, bitAt_succ, bitAt_succ, bitwise_div2, ih]

/-- Bit `k` of `Nat.land a b`. -/
theorem bitAt_land (a b k : Nat) : bitAt (Nat.land a b) k = (bitAt a k && bitAt b k) := by
  rw [Anneal.NatBitwise.land_eq_bitwise]
  exact bitAt_bitwise and rfl a b k

/-- Bit `k` of `Nat.lor a b`. -/
theorem bitAt_lor (a b k : Nat) : bitAt (Nat.lor a b) k = (bitAt a k || bitAt b k) := by
  rw [Anneal.NatBitwise.lor_eq_bitwise]
  exact bitAt_bitwise or rfl a b k

/-- Bit `k` of `Nat.xor a b`. -/
theorem bitAt_xor (a b k : Nat) : bitAt (Nat.xor a b) k = bne (bitAt a k) (bitAt b k) := by
  rw [Anneal.NatBitwise.xor_eq_bitwise]
  exact bitAt_bitwise bne rfl a b k

/-- Bit `k` of `andNot a b`. -/
theorem bitAt_andNot (a b k : Nat) : bitAt (andNot a b) k = (bitAt a k && !bitAt b k) := by
  dsimp only [andNot]
  rw [bitAt_xor, bitAt_land]
  cases bitAt a k <;> cases bitAt b k <;> rfl

/-- `(x mod (2 * P)) mod 2 = x mod 2`. -/
theorem nat_mod_two_mul_mod2 (x P : Nat) :
    Nat.mod (Nat.mod x (2 * P)) 2 = Nat.mod x 2 := by
  have hDiv := Nat.div_add_mod x (2 * P)
  dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at hDiv
  have hMod : Nat.mod x 2 = Nat.mod (2 * P * Nat.div x (2 * P) + Nat.mod x (2 * P)) 2 := by
    rw [hDiv]
  rw [Nat.mul_assoc 2 P (Nat.div x (2 * P)), Nat.add_comm] at hMod
  have hStep : Nat.mod (Nat.mod x (2 * P) + 2 * (P * Nat.div x (2 * P))) 2 =
      Nat.mod (Nat.mod x (2 * P)) 2 :=
    Nat.add_mul_mod_self_left (Nat.mod x (2 * P)) 2 (P * Nat.div x (2 * P))
  rw [hStep] at hMod
  exact hMod.symm

/-- `(x mod (2 * P)) / 2 = (x / 2) mod P` for `0 < P`. -/
theorem nat_mod_two_mul_div2 (x P : Nat) (hP : 0 < P) :
    Nat.div (Nat.mod x (2 * P)) 2 = Nat.mod (Nat.div x 2) P := by
  have hx := Nat.div_add_mod x 2
  have hxd := Nat.div_add_mod (Nat.div x 2) P
  dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at hx hxd
  let q := Nat.div (Nat.div x 2) P
  let r := Nat.mod (Nat.div x 2) P
  let b := Nat.mod x 2
  have hrLt : r < P := Nat.mod_lt (Nat.div x 2) hP
  have hbLt : b < 2 := Nat.mod_lt x (Nat.zero_lt_succ 1)
  have hBound : 2 * r + b < 2 * P := by
    have hSub : r + 1 ≤ P := hrLt
    have hMul : 2 * (r + 1) ≤ 2 * P := Nat.mul_le_mul_left 2 hSub
    rw [Nat.mul_add 2 r 1, Nat.mul_one] at hMul
    have hB1 : b ≤ 1 := Nat.le_of_lt_succ hbLt
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.add_le_add_left hB1 (2 * r))
      (Nat.lt_succ_of_le (Nat.le_refl (2 * r + 1)))) hMul
  have hxDecomp : x = (2 * P) * q + (2 * r + b) := by
    have h1 : x = 2 * (P * q + r) + b := by
      dsimp only [q, r, b]
      rw [hxd, hx]
    rw [Nat.mul_add 2 (P * q) r, ← Nat.mul_assoc 2 P q, Nat.add_assoc] at h1
    exact h1
  have hModEq : Nat.mod x (2 * P) = 2 * r + b := by
    have hAddMod : Nat.mod ((2 * P) * q + (2 * r + b)) (2 * P) = Nat.mod (2 * r + b) (2 * P) :=
      Nat.mul_add_mod_self_left (2 * P) q (2 * r + b)
    rw [← hxDecomp] at hAddMod
    rw [hAddMod]
    exact Nat.mod_eq_of_lt hBound
  rw [hModEq, Nat.add_comm (2 * r) b]
  have hDivStep : Nat.div (b + 2 * r) 2 = Nat.div b 2 + r :=
    Nat.add_mul_div_left b r (Nat.zero_lt_succ 1)
  have hbDiv0 : Nat.div b 2 = 0 := Nat.div_eq_of_lt hbLt
  rw [hDivStep, hbDiv0, Nat.zero_add]

/-- Soundness of `Nat.blt a b = true → a < b`. -/
theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

/-- Completeness of `a < b → Nat.blt a b = true`. -/
theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

/-- Bit `k` of `x mod 2^w` equals `bitAt x k` below `w` and `false` at or above
`w`. -/
theorem bitAt_mod_modPow2 : ∀ k w x : Nat,
    bitAt (Nat.mod x (modPow2 w)) k = match Nat.blt k w with | true => bitAt x k | false => false
  | 0, 0, x => by
    have hm : Nat.mod x (modPow2 0) = 0 := Nat.mod_one x
    rw [hm, bitAt_zero_nat]
    rfl
  | 0, w' + 1, x => by
    rw [bitAt_zero, bitAt_zero, modPow2_succ w', nat_mod_two_mul_mod2]
    rfl
  | k' + 1, 0, x => by
    have hm : Nat.mod x (modPow2 0) = 0 := Nat.mod_one x
    rw [hm, bitAt_zero_nat]
    rfl
  | k' + 1, w' + 1, x => by
    rw [bitAt_succ, bitAt_succ, modPow2_succ w',
        nat_mod_two_mul_div2 x (modPow2 w') (modPow2_pos w'),
        bitAt_mod_modPow2 k' w' (Nat.div x 2)]
    cases hk : Nat.blt k' w' with
    | true =>
      have hLt : k' < w' := lt_of_blt_true hk
      have hS : Nat.blt (k' + 1) (w' + 1) = true := blt_true_of_lt (Nat.succ_lt_succ hLt)
      rw [hS]
    | false =>
      have hNot : ¬ (k' < w') := fun h => by
        have ht := blt_true_of_lt h
        rw [ht] at hk; nomatch hk
      cases hS : Nat.blt (k' + 1) (w' + 1) with
      | false => rfl
      | true =>
        have hLt := Nat.lt_of_succ_lt_succ (lt_of_blt_true hS)
        exact False.elim (hNot hLt)

/-- Bit `0` of `2 * x` is `false`. -/
theorem bitAt_two_mul_zero (x : Nat) : bitAt (2 * x) 0 = false := by
  rw [bitAt_zero, mod2_two_mul]; rfl

/-- Bit `k + 1` of `2 * x` equals `bitAt x k`. -/
theorem bitAt_two_mul_succ (x k : Nat) : bitAt (2 * x) (k + 1) = bitAt x k := by
  rw [bitAt_succ, div2_two_mul]

/-- Bit `k` of `x <<< s`. -/
theorem bitAt_shiftLeft : ∀ s x k : Nat,
    bitAt (Nat.shiftLeft x s) k = match Nat.ble s k with | true => bitAt x (k - s) | false => false
  | 0, x, k => by
    dsimp only [Nat.shiftLeft]
    have hb : Nat.ble 0 k = true := Nat.ble_eq_true_of_le (Nat.zero_le k)
    rw [hb, Nat.sub_zero]
  | s + 1, x, 0 => by
    dsimp only [Nat.shiftLeft]
    have hMul : Nat.shiftLeft (2 * x) s = (Nat.shiftLeft x s) * 2 := by
      rw [shiftLeft_mul_pow, shiftLeft_mul_pow, Nat.mul_comm 2 x, Nat.mul_assoc,
          Nat.mul_comm 2 (Nat.pow 2 s), ← Nat.mul_assoc]
    have h2 : Nat.shiftLeft (2 * x) s = 2 * Nat.shiftLeft x s := by
      rw [hMul, Nat.mul_comm]
    rw [h2, bitAt_two_mul_zero]
    rfl
  | s + 1, x, k + 1 => by
    dsimp only [Nat.shiftLeft]
    rw [bitAt_shiftLeft s (2 * x) (k + 1)]
    cases hs : Nat.ble s (k + 1) with
    | false =>
      have hNot : ¬ (s ≤ k + 1) := fun h => by
        have ht := Nat.ble_eq_true_of_le h; rw [ht] at hs; nomatch hs
      cases hs2 : Nat.ble (s + 1) (k + 1) with
      | false => rfl
      | true =>
        have hLe := Nat.le_of_ble_eq_true hs2
        exact False.elim (hNot (Nat.le_trans (Nat.le_succ s) hLe))
    | true =>
      have hLe : s ≤ k + 1 := Nat.le_of_ble_eq_true hs
      cases hEq : Nat.beq s (k + 1) with
      | true =>
        have hsEq : s = k + 1 := Nat.eq_of_beq_eq_true hEq
        rw [hsEq, Nat.sub_self, bitAt_two_mul_zero]
        have hf : Nat.ble (k + 1 + 1) (k + 1) = false := by
          cases hb : Nat.ble (k + 1 + 1) (k + 1) with
          | false => rfl
          | true => exact False.elim (Nat.not_succ_le_self (k + 1) (Nat.le_of_ble_eq_true hb))
        rw [hf]
      | false =>
        have hNe : s ≠ k + 1 := fun h => by rw [h, nat_beq_refl] at hEq; nomatch hEq
        have hLt : s < k + 1 := Nat.lt_of_le_of_ne hLe hNe
        have hSle : s ≤ k := Nat.le_of_lt_succ hLt
        have hDiffAdd : k + 1 - s + s = k - s + 1 + s := by
          rw [Nat.sub_add_cancel hLe, Nat.add_assoc, Nat.add_comm 1 s,
              ← Nat.add_assoc (k - s) s 1, Nat.sub_add_cancel hSle]
        have hDiff : k + 1 - s = (k - s) + 1 := Nat.add_right_cancel hDiffAdd
        rw [hDiff, bitAt_two_mul_succ]
        have hs' : Nat.ble (s + 1) (k + 1) = true := Nat.ble_eq_true_of_le (Nat.succ_le_succ hSle)
        rw [hs', Nat.succ_sub_succ]

/-- Bit `k` of `x >>> s` equals `bitAt x (k + s)`. -/
theorem bitAt_shiftRight : ∀ s x k : Nat,
    bitAt (Nat.shiftRight x s) k = bitAt x (k + s)
  | 0, x, k => by dsimp only [Nat.shiftRight]; rw [Nat.add_zero]
  | s + 1, x, k => by
    have hDiv : Nat.shiftRight x (s + 1) = Nat.div (Nat.shiftRight x s) 2 := rfl
    rw [hDiv, ← bitAt_succ, bitAt_shiftRight s x (k + 1),
        Nat.add_assoc, Nat.add_comm 1 s, ← Nat.add_assoc]

/-- If all bits at index `≥ w` are `false`, then `x < 2^w`. -/
theorem lt_modPow2_of_bitAt_zero {x w : Nat} (h : ∀ k, w ≤ k → bitAt x k = false) :
    x < modPow2 w := by
  have hEq : x = Nat.mod x (modPow2 w) := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_mod_modPow2]
    cases hk : Nat.blt k w with
    | true => rfl
    | false =>
      have hNot : ¬ (k < w) := fun hLt => by
        have ht := blt_true_of_lt hLt; rw [ht] at hk; nomatch hk
      exact h k (Nat.le_of_not_lt hNot)
  rw [hEq]
  exact Nat.mod_lt x (modPow2_pos w)

/-- If `x < 2^w`, then every bit at index `k ≥ w` is `false`. -/
theorem bitAt_zero_ge_of_lt_modPow2 {x w : Nat} (h : x < modPow2 w) :
    ∀ k, w ≤ k → bitAt x k = false := by
  intro k hk
  have hx : x = Nat.mod x (modPow2 w) := (Nat.mod_eq_of_lt h).symm
  rw [hx, bitAt_mod_modPow2]
  cases hLt : Nat.blt k w with
  | false => rfl
  | true =>
    have hKl : k < w := lt_of_blt_true hLt
    exact False.elim (Nat.not_le_of_gt hKl hk)

/-- Nested power-of-two remainder `(x mod 2^w) mod 2^k = x mod 2^k` for `k ≤ w`.
-/
theorem mod_modPow2_of_le {k w : Nat} (h : k ≤ w) (x : Nat) :
    Nat.mod (Nat.mod x (modPow2 w)) (modPow2 k) = Nat.mod x (modPow2 k) := by
  apply nat_eq_of_bitAt
  intro j
  rw [bitAt_mod_modPow2, bitAt_mod_modPow2, bitAt_mod_modPow2]
  cases hjk : Nat.blt j k with
  | false => rfl
  | true =>
    have hLt : j < k := lt_of_blt_true hjk
    have hjw : Nat.blt j w = true := blt_true_of_lt (Nat.lt_of_lt_of_le hLt h)
    rw [hjw]

/-- Disjoint-bit addition identity `a &&& b = 0 → a + b = a ||| b`. -/
theorem nat_add_eq_lor_of_disjoint : ∀ a b : Nat, Nat.land a b = 0 → a + b = Nat.lor a b := by
  intro a
  refine Nat.strongRecOn (motive := fun x => ∀ y, Nat.land x y = 0 → x + y = Nat.lor x y) a ?_
  intro x ih y hDisj
  cases x with
  | zero =>
    rw [Nat.zero_add]
    have hLor0 : Nat.lor 0 y = y := by
      apply nat_eq_of_bitAt; intro k; rw [bitAt_lor, bitAt_zero_nat]; rfl
    exact hLor0.symm
  | succ x' =>
    have hDivLt : Nat.div (x' + 1) 2 < x' + 1 :=
      Nat.div_lt_self (Nat.zero_lt_succ x') (Nat.lt_succ_self 1)
    have hDisjDiv : Nat.land (Nat.div (x' + 1) 2) (Nat.div y 2) = 0 := by
      apply nat_eq_of_bitAt
      intro k
      rw [bitAt_land, bitAt_zero_nat, ← bitAt_succ, ← bitAt_succ]
      have hB : bitAt (Nat.land (x' + 1) y) (k + 1) = bitAt 0 (k + 1) := by rw [hDisj]
      rw [bitAt_land, bitAt_zero_nat] at hB
      exact hB
    have hIH := ih (Nat.div (x' + 1) 2) hDivLt (Nat.div y 2) hDisjDiv
    have hBit0 : bitAt (Nat.land (x' + 1) y) 0 = false := by rw [hDisj]; exact bitAt_zero_nat 0
    rw [bitAt_land, bitAt_zero, bitAt_zero] at hBit0
    have hDivMod :
        Nat.div (x' + 1 + y) 2 = Nat.div (x' + 1) 2 + Nat.div y 2 ∧
        Nat.mod (x' + 1 + y) 2 = Nat.mod (Nat.lor (x' + 1) y) 2 := by
      have hx := Nat.div_add_mod (x' + 1) 2
      have hy := Nat.div_add_mod y 2
      dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at hx hy
      have hSumAux : ∀ q1 r1 q2 r2 : Nat,
          (2 * q1 + r1) + (2 * q2 + r2) = 2 * (q1 + q2) + (r1 + r2) := by
        intro q1 r1 q2 r2
        rw [Nat.mul_add 2 q1 q2, Nat.add_assoc (2 * q1) r1, ← Nat.add_assoc r1 (2 * q2) r2,
            Nat.add_comm r1 (2 * q2), Nat.add_assoc (2 * q2) r1 r2, ← Nat.add_assoc (2 * q1)]
      have hSum : (x' + 1) + y =
          2 * (Nat.div (x' + 1) 2 + Nat.div y 2) + (Nat.mod (x' + 1) 2 + Nat.mod y 2) := by
        have hTmp := hSumAux (Nat.div (x' + 1) 2) (Nat.mod (x' + 1) 2) (Nat.div y 2) (Nat.mod y 2)
        rw [hx, hy] at hTmp
        exact hTmp
      cases mod2_cases (x' + 1) with
      | inl hx0 =>
        cases mod2_cases y with
        | inl hy0 =>
          rw [hx0, hy0, Nat.add_zero] at hSum
          rw [hSum, Nat.mul_comm 2 _]
          have h0 : Nat.mod (Nat.lor (x' + 1) y) 2 = 0 := by
            rw [Anneal.NatBitwise.lor_eq_bitwise, bitwise_mod2 or rfl, hx0, hy0]
            rfl
          rw [h0]
          exact ⟨Nat.mul_div_left _ (Nat.zero_lt_succ 1), Nat.mul_mod_left _ 2⟩
        | inr hy1 =>
          rw [hx0, hy1, Nat.zero_add] at hSum
          rw [hSum]
          have h1 : Nat.mod (Nat.lor (x' + 1) y) 2 = 1 := by
            rw [Anneal.NatBitwise.lor_eq_bitwise, bitwise_mod2 or rfl, hx0, hy1]
            rfl
          rw [h1]
          exact ⟨div2_two_mul_add_one _, mod2_two_mul_add_one _⟩
      | inr hx1 =>
        cases mod2_cases y with
        | inl hy0 =>
          rw [hx1, hy0, Nat.add_zero] at hSum
          rw [hSum]
          have h1 : Nat.mod (Nat.lor (x' + 1) y) 2 = 1 := by
            rw [Anneal.NatBitwise.lor_eq_bitwise, bitwise_mod2 or rfl, hx1, hy0]
            rfl
          rw [h1]
          exact ⟨div2_two_mul_add_one _, mod2_two_mul_add_one _⟩
        | inr hy1 =>
          rw [hx1, hy1] at hBit0; nomatch hBit0
    apply nat_eq_of_mod2_div2 hDivMod.2
    rw [hDivMod.1, hIH]
    have hLorDiv :
        Nat.div (Nat.lor (x' + 1) y) 2 =
          Nat.lor (Nat.div (x' + 1) 2) (Nat.div y 2) := by
      rw [Anneal.NatBitwise.lor_eq_bitwise, Anneal.NatBitwise.lor_eq_bitwise]
      exact bitwise_div2 or (x' + 1) y
    exact hLorDiv.symm

/-- Bitwise dominance implies numerical order `a ≤ b`. -/
theorem nat_le_of_bitAt_imp {a b : Nat} (h : ∀ k : Nat, bitAt a k = true → bitAt b k = true) :
    a ≤ b := by
  let d := andNot b a
  have hDisj : Nat.land a d = 0 := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_land, bitAt_andNot, bitAt_zero_nat]
    cases bitAt a k <;> cases bitAt b k <;> rfl
  have hSumEq : Nat.lor a d = b := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_lor, bitAt_andNot]
    cases ha : bitAt a k with
    | false => cases bitAt b k <;> rfl
    | true =>
      have hb := h k ha
      rw [hb]
      rfl
  have hAdd := nat_add_eq_lor_of_disjoint a d hDisj
  rw [hSumEq] at hAdd
  rw [← hAdd]
  exact Nat.le_add_right a d

/-- `(a || b) = false → a = false`. -/
theorem bool_or_false_left {a b : Bool} (h : (a || b) = false) : a = false := by
  cases a <;> cases b <;> first | rfl | nomatch h

/-- `(a || b) = false → b = false`. -/
theorem bool_or_false_right {a b : Bool} (h : (a || b) = false) : b = false := by
  cases a <;> cases b <;> first | rfl | nomatch h

/-- `(a && b) = true → a = true`. -/
theorem bool_and_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> first | rfl | nomatch h

/-- `(a && b) = true → b = true`. -/
theorem bool_and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | nomatch h

/-- Modular addition congruence `(a + b) mod P = ((a mod P) + (b mod P)) mod P`.
-/
theorem mod_sum_mod_cancel (a b P : Nat) :
    Nat.mod (a + b) P = Nat.mod (Nat.mod a P + Nat.mod b P) P := by
  have ha := Nat.div_add_mod a P
  have hb := Nat.div_add_mod b P
  dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at ha hb
  have hDecomp : a + b = (Nat.mod a P + Nat.mod b P) + P * (Nat.div a P + Nat.div b P) := by
    have h1 : (P * Nat.div a P + Nat.mod a P) + (P * Nat.div b P + Nat.mod b P) =
        (Nat.mod a P + Nat.mod b P) + P * (Nat.div a P + Nat.div b P) := by
      rw [Nat.mul_add P, Nat.add_assoc (P * Nat.div a P) (Nat.mod a P),
          ← Nat.add_assoc (Nat.mod a P) (P * Nat.div b P) (Nat.mod b P),
          Nat.add_comm (Nat.mod a P) (P * Nat.div b P),
          Nat.add_assoc (P * Nat.div b P), ← Nat.add_assoc (P * Nat.div a P),
          Nat.add_comm (P * Nat.div a P + P * Nat.div b P) (Nat.mod a P + Nat.mod b P)]
    rw [ha, hb] at h1
    exact h1
  rw [hDecomp]
  exact Nat.add_mul_mod_self_left (Nat.mod a P + Nat.mod b P) P (Nat.div a P + Nat.div b P)

/-- `((a mod M) + b) mod M = (a + b) mod M` for `0 < M`. -/
theorem mod_add_mod_left (a b M : Nat) (hM : 0 < M) :
    Nat.mod (Nat.mod a M + b) M = Nat.mod (a + b) M := by
  have h1 := mod_sum_mod_cancel a b M
  have h2 := mod_sum_mod_cancel (Nat.mod a M) b M
  rw [nat_mod_eq_of_lt (nat_mod_lt a hM)] at h2
  exact Eq.trans h2 h1.symm

/-- `(a + (b mod M)) mod M = (a + b) mod M` for `0 < M`. -/
theorem mod_add_mod_right (a b M : Nat) (hM : 0 < M) :
    Nat.mod (a + Nat.mod b M) M = Nat.mod (a + b) M := by
  rw [Nat.add_comm a (Nat.mod b M), mod_add_mod_left b a M hM, Nat.add_comm b a]

end Anneal.AiPcc

end
