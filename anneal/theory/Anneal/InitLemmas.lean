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
public import Init.Data.Fin.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Data.UInt.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.List.Basic

public section

/-!
# Shared Foundation-Locked `Init` Lemmas (`Anneal.InitLemmas`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`,
admitted theory tactics only) lemma pack consolidating seven high-frequency
helper clusters across `anneal/theory/` and `anneal/correspondence/`:

1. `Bool` connectives and `ite`/`dite` branch reduction from propositional
   hypotheses.
2. Generic `BEq` reflection bridges (`beq_refl` / `eq_of_beq` <-> `beq_iff`),
   `natListBeq`, and polymorphic `List.beq` reflection (`list_beq_refl`,
   `list_eq_of_beq`, `list_beq_iff`).
3. `Nat` power-of-two monotonicity, division, and modulo identities.
4. Constructive `IntBalance` sign-magnitude bridge, `Int` order, and
   `Int.ofNat` subtraction lemmas over `Init.Data.Int.Basic` without `omega`.
5. Total `@Nat.rec` list indexing, slicing, and range-replacement lemmas.
6. `BitVec` bounded `toNat`/`ofNat`, non-wrapping `+`, and `<`/`<=` bridges
   over `Init.Data.BitVec.BasicAux` (general `BitVec` `toNat` laws live in
   `Anneal.BitVec`).
7. Fixed-width `UInt8`/`UInt16`/`UInt32`/`UInt64` extensionality, bounded
   `toNat`/`ofNat`, and nonzero lemmas over `Init.Data.UInt.BasicAux`.
-/

namespace Anneal.InitLemmas

universe u v

/-! ## 1. `Bool` Connectives and `ite` / `dite` Eliminators -/

theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => cases b <;> nomatch h
  | true => rfl

theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => cases b <;> nomatch h
  | true => exact h

theorem bool_and_iff (a b : Bool) :
    (a && b) = true ↔ (a = true ∧ b = true) := by
  constructor
  · intro h
    exact ⟨bool_and_left h, bool_and_right h⟩
  · intro h
    rw [h.1, h.2]
    rfl

theorem bool_or_eq_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | false => exact ⟨rfl, h⟩
  | true => nomatch h

theorem bool_not_true_eq_false {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => nomatch h

theorem bool_not_false_eq_true {b : Bool} (h : (!b) = false) : b = true := by
  cases b with
  | false => nomatch h
  | true => rfl

theorem bool_and_eq_false_iff (a b : Bool) :
    (a && b) = false ↔ (a = false ∨ b = false) := by
  cases a <;> cases b <;> constructor <;> intro h
  · exact Or.inl rfl
  · rfl
  · exact Or.inl rfl
  · rfl
  · exact Or.inr rfl
  · rfl
  · nomatch h
  · cases h with
    | inl h1 => nomatch h1
    | inr h2 => nomatch h2

theorem bool_or_eq_true_iff (a b : Bool) :
    (a || b) = true ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> constructor <;> intro h
  · nomatch h
  · cases h with
    | inl h1 => nomatch h1
    | inr h2 => nomatch h2
  · exact Or.inr rfl
  · rfl
  · exact Or.inl rfl
  · rfl
  · exact Or.inl rfl
  · rfl

theorem bool_or_eq_false_iff (a b : Bool) :
    (a || b) = false ↔ (a = false ∧ b = false) := by
  cases a <;> cases b <;> constructor <;> intro h
  · exact ⟨rfl, rfl⟩
  · rfl
  · nomatch h
  · nomatch h.2
  · nomatch h
  · nomatch h.1
  · nomatch h
  · nomatch h.1

theorem bool_not_not (b : Bool) : (!!b) = b := by
  cases b <;> rfl

theorem bool_eq_false_of_ne_true {b : Bool} (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)

theorem bool_eq_true_of_ne_false {b : Bool} (h : b ≠ false) : b = true := by
  cases b with
  | false => exact False.elim (h rfl)
  | true => rfl

theorem ite_true_of {α : Type u} {c : Prop} [d : Decidable c] {a b : α}
    (h : c) : (if c then a else b) = a := by
  cases d with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

theorem ite_false_of {α : Type u} {c : Prop} [d : Decidable c] {a b : α}
    (h : ¬ c) : (if c then a else b) = b := by
  cases d with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

theorem dite_true_of {α : Type u} {c : Prop} [d : Decidable c]
    {t : c → α} {e : ¬ c → α} (h : c) :
    (if hc : c then t hc else e hc) = t h := by
  cases d with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

theorem dite_false_of {α : Type u} {c : Prop} [d : Decidable c]
    {t : c → α} {e : ¬ c → α} (h : ¬ c) :
    (if hc : c then t hc else e hc) = e h := by
  cases d with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-! ## 2. Generic `BEq` Bridges and `Nat` / `List Nat` Equality Reflection -/

theorem beq_refl_of_iff {α : Type u} (beqFn : α → α → Bool)
    (hIff : ∀ a b : α, beqFn a b = true ↔ a = b) (x : α) :
    beqFn x x = true :=
  (hIff x x).2 rfl

theorem eq_of_beq_of_iff {α : Type u} (beqFn : α → α → Bool)
    (hIff : ∀ a b : α, beqFn a b = true ↔ a = b) {x y : α}
    (h : beqFn x y = true) : x = y :=
  (hIff x y).1 h

theorem beq_iff_of_refl_and_eq {α : Type u} (beqFn : α → α → Bool)
    (hRefl : ∀ x : α, beqFn x x = true)
    (hEq : ∀ {x y : α}, beqFn x y = true → x = y) (a b : α) :
    beqFn a b = true ↔ a = b := by
  constructor
  · intro h
    exact hEq h
  · intro h
    rw [h]
    exact hRefl b

theorem nat_beq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => nat_beq_refl n

theorem nat_eq_of_beq {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

theorem nat_beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  beq_iff_of_refl_and_eq Nat.beq nat_beq_refl (fun h => nat_eq_of_beq h) a b

/-- Structural Boolean equality on `List Nat` defined via `List.foldr`. -/
@[expose] def natListBeq (xs ys : List Nat) : Bool :=
  List.foldr
    (fun (x : Nat) (ih : List Nat → Bool) (ys' : List Nat) =>
      match ys' with
      | [] => false
      | y :: rest => Nat.beq x y && ih rest)
    (fun ys' => match ys' with | [] => true | _ :: _ => false)
    xs ys

theorem natListBeq_cons_cons (x y : Nat) (xs ys : List Nat) :
    natListBeq (x :: xs) (y :: ys) = (Nat.beq x y && natListBeq xs ys) := rfl

theorem natListBeq_refl : ∀ xs : List Nat, natListBeq xs xs = true
  | [] => rfl
  | x :: xs => by
    rw [natListBeq_cons_cons, nat_beq_refl x, natListBeq_refl xs]
    rfl

theorem eq_of_natListBeq :
    ∀ {xs ys : List Nat}, natListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by nomatch h
  | _ :: _, [], h => by nomatch h
  | x :: xs, y :: ys, h => by
    rw [natListBeq_cons_cons] at h
    have hx : x = y := nat_eq_of_beq (bool_and_left h)
    have hxs : xs = ys := eq_of_natListBeq (bool_and_right h)
    rw [hx, hxs]

theorem natListBeq_iff (xs ys : List Nat) :
    natListBeq xs ys = true ↔ xs = ys :=
  beq_iff_of_refl_and_eq natListBeq natListBeq_refl
    (fun h => eq_of_natListBeq h) xs ys

theorem list_beq_refl {α : Type u} [BEq α] [LawfulBEq α] :
    ∀ (xs : List α), List.beq xs xs = true
  | [] => rfl
  | x :: xs => by
    change ((x == x) && List.beq xs xs) = true
    rw [beq_self_eq_true x, list_beq_refl xs]
    rfl

theorem list_eq_of_beq {α : Type u} [BEq α] [LawfulBEq α] :
    ∀ {xs ys : List α}, List.beq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by nomatch h
  | _ :: _, [], h => by nomatch h
  | x :: xs, y :: ys, h => by
    change ((x == y) && List.beq xs ys) = true at h
    have hx : x = y := eq_of_beq (bool_and_left h)
    have hxs : xs = ys := list_eq_of_beq (bool_and_right h)
    rw [hx, hxs]

theorem list_beq_iff {α : Type u} [BEq α] [LawfulBEq α] (xs ys : List α) :
    List.beq xs ys = true ↔ xs = ys :=
  beq_iff_of_refl_and_eq List.beq list_beq_refl
    (fun h => list_eq_of_beq h) xs ys

/-! ## 3. `Nat` Power, Division, and Modulo Lemmas -/

theorem add_four_rearrange (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, ← Nat.add_assoc a c (b + d)]

theorem nat_pow_zero (b : Nat) : Nat.pow b 0 = 1 := rfl

theorem nat_pow_succ (b n : Nat) : Nat.pow b (n + 1) = Nat.pow b n * b :=
  Nat.pow_succ b n

theorem nat_pow_add (b m : Nat) :
    ∀ n : Nat, Nat.pow b (m + n) = Nat.pow b m * Nat.pow b n
  | 0 => by
    rw [Nat.add_zero, nat_pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, nat_pow_succ, nat_pow_succ, nat_pow_add b m n,
        Nat.mul_assoc]

theorem nat_two_pow_pos : ∀ n : Nat, 0 < Nat.pow 2 n
  | 0 => by decide
  | n + 1 => by
    rw [nat_pow_succ]
    have ih := nat_two_pow_pos n
    have hTwo : Nat.pow 2 n * 2 = Nat.pow 2 n + Nat.pow 2 n :=
      Nat.mul_two (Nat.pow 2 n)
    rw [hTwo]
    exact Nat.lt_of_lt_of_le ih (Nat.le_add_right (Nat.pow 2 n) (Nat.pow 2 n))

theorem nat_div_add_mod (m k : Nat) :
    k * Nat.div m k + Nat.mod m k = m :=
  Nat.div_add_mod m k

theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

theorem nat_add_lt_add_of_le_of_lt {a b c d : Nat}
    (h1 : a ≤ b) (h2 : c < d) : a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right h1 c) (Nat.add_lt_add_left h2 b)

theorem nat_add_lt_add_of_lt_of_le {a b c d : Nat}
    (h1 : a < b) (h2 : c ≤ d) : a + c < b + d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right h1 c) (Nat.add_le_add_left h2 b)

theorem nat_sub_add_cancel {a b : Nat} (h : b ≤ a) : (a - b) + b = a :=
  Nat.sub_add_cancel h

theorem nat_add_sub_cancel_left (a b : Nat) : (a + b) - a = b := by
  rw [Nat.add_comm a b]
  exact Nat.add_sub_cancel b a

theorem nat_sub_sub_self {a b : Nat} (h : b ≤ a) : a - (a - b) = b := by
  have hAdd : (a - b) + b = a := Nat.sub_add_cancel h
  have h1 := congrArg (fun z => z - (a - b)) hAdd.symm
  rw [nat_add_sub_cancel_left (a - b) b] at h1
  exact h1

theorem nat_le_of_add_le_add_right {a b c : Nat} (h : a + c ≤ b + c) : a ≤ b :=
  Nat.le_of_add_le_add_right h

theorem nat_lt_of_add_lt_add_right {a b c : Nat} (h : a + c < b + c) : a < b := by
  induction c with
  | zero => rw [Nat.add_zero, Nat.add_zero] at h; exact h
  | succ c ih =>
    rw [Nat.add_succ, Nat.add_succ] at h
    exact ih (Nat.lt_of_succ_lt_succ h)

theorem nat_lt_of_add_lt_add_left {a b c : Nat} (h : c + a < c + b) : a < b := by
  rw [Nat.add_comm c a, Nat.add_comm c b] at h
  exact nat_lt_of_add_lt_add_right h

theorem nat_ble_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem nat_blt_iff (a b : Nat) : Nat.blt a b = true ↔ a < b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem nat_ble_false_iff (a b : Nat) : Nat.ble a b = false ↔ b < a := by
  constructor
  · intro h
    cases Nat.lt_or_ge b a with
    | inl hLt => exact hLt
    | inr hGe => rw [Nat.ble_eq_true_of_le hGe] at h; nomatch h
  · intro hLt
    cases h : Nat.ble a b with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_ble_eq_true h))

theorem nat_blt_false_iff (a b : Nat) : Nat.blt a b = false ↔ b ≤ a := by
  constructor
  · intro h
    cases Nat.lt_or_ge a b with
    | inr hGe => exact hGe
    | inl hLt =>
      dsimp only [Nat.blt] at h
      rw [Nat.ble_eq_true_of_le hLt] at h; nomatch h
  · intro hGe
    cases h : Nat.blt a b with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt (Nat.le_of_ble_eq_true h) hGe)

theorem nat_mod_lt (a : Nat) {b : Nat} (h : 0 < b) : Nat.mod a b < b :=
  Nat.mod_lt a h

theorem nat_mod_le (a b : Nat) : Nat.mod a b ≤ a :=
  Nat.mod_le a b

theorem nat_mod_zero (a : Nat) : Nat.mod a 0 = a :=
  Nat.mod_zero a

theorem nat_zero_mod (b : Nat) : Nat.mod 0 b = 0 :=
  Nat.zero_mod b

theorem nat_mod_self (a : Nat) : Nat.mod a a = 0 :=
  Nat.mod_self a

theorem nat_mod_mod (a b : Nat) : Nat.mod (Nat.mod a b) b = Nat.mod a b := by
  cases b with
  | zero => rw [nat_mod_zero, nat_mod_zero]
  | succ b' => exact Nat.mod_eq_of_lt (Nat.mod_lt a (Nat.zero_lt_succ b'))

theorem nat_add_mod_self_left (a b : Nat) : Nat.mod (a + b) a = Nat.mod b a :=
  Nat.add_mod_left a b

theorem nat_add_mod_self_right (a b : Nat) : Nat.mod (a + b) b = Nat.mod a b :=
  Nat.add_mod_right a b

theorem nat_add_mul_mod_self_left (a b c : Nat) :
    Nat.mod (a + b * c) b = Nat.mod a b :=
  Nat.add_mul_mod_self_left a b c

theorem nat_mul_mod_right (a b : Nat) : Nat.mod (a * b) a = 0 :=
  Nat.mul_mod_right a b

theorem nat_mul_mod_left (a b : Nat) : Nat.mod (a * b) b = 0 :=
  Nat.mul_mod_left a b

theorem nat_mod_mod_of_dvd {a b c : Nat} (h : Nat.mod b c = 0) :
    Nat.mod (Nat.mod a b) c = Nat.mod a c := by
  have hb : b = c * Nat.div b c := by
    have h1 : c * Nat.div b c + Nat.mod b c = b := Nat.div_add_mod b c
    rw [h, Nat.add_zero] at h1
    exact h1.symm
  have ha : Nat.mod a b + c * (Nat.div b c * Nat.div a b) = a := by
    rw [← Nat.mul_assoc, ← hb]
    exact Nat.mod_add_div a b
  exact (Nat.add_mul_mod_self_left (Nat.mod a b) c
    (Nat.div b c * Nat.div a b)).symm.trans (congrArg (fun k => Nat.mod k c) ha)

theorem nat_div_le_self (a b : Nat) : Nat.div a b ≤ a :=
  Nat.div_le_self a b

theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

theorem nat_zero_div (b : Nat) : Nat.div 0 b = 0 :=
  Nat.zero_div b

theorem nat_div_one (a : Nat) : Nat.div a 1 = a :=
  Nat.div_one a

theorem nat_mul_div_cancel_left {a : Nat} (b : Nat) (h : 0 < a) :
    Nat.div (a * b) a = b :=
  Nat.mul_div_right b h

theorem nat_div_lt_of_lt_mul {a b c : Nat} (h : a < b * c) : Nat.div a b < c := by
  cases Nat.lt_or_ge (Nat.div a b) c with
  | inl hLt => exact hLt
  | inr hGe =>
    have h1 : b * c ≤ b * Nat.div a b := Nat.mul_le_mul_left b hGe
    have h2 : b * Nat.div a b ≤ a :=
      Nat.le_trans (Nat.le_add_right (b * Nat.div a b) (Nat.mod a b))
        (Nat.le_of_eq (Nat.div_add_mod a b))
    exact False.elim (Nat.not_le_of_gt h (Nat.le_trans h1 h2))

theorem div2_mod2_inj (m n : Nat)
    (hDiv : Nat.div n 2 = Nat.div m 2)
    (hMod : Nat.mod n 2 = Nat.mod m 2) : n = m := by
  have hm : 2 * Nat.div m 2 + Nat.mod m 2 = m := Nat.div_add_mod m 2
  have hn : 2 * Nat.div n 2 + Nat.mod n 2 = n := Nat.div_add_mod n 2
  rw [hDiv, hMod] at hn
  rw [← hn, hm]

theorem nat_two_pow_lt_succ (n : Nat) : Nat.pow 2 n < Nat.pow 2 (n + 1) := by
  rw [nat_pow_succ, Nat.mul_two]
  exact Nat.lt_add_of_pos_right (nat_two_pow_pos n)

theorem nat_two_pow_lt_of_lt {i j : Nat} (h : i < j) :
    Nat.pow 2 i < Nat.pow 2 j :=
  Nat.lt_of_lt_of_le (nat_two_pow_lt_succ i)
    (Nat.pow_le_pow_right (by decide : 0 < 2) h)

theorem nat_two_pow_le_of_le {i j : Nat} (h : i ≤ j) :
    Nat.pow 2 i ≤ Nat.pow 2 j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

theorem nat_mul_add_mod_self_left (a b c : Nat) :
    Nat.mod (a * b + c) a = Nat.mod c a :=
  Nat.mul_add_mod_self_left a b c

theorem nat_add_mod_mod (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  have hDiv : Nat.mod b m + m * Nat.div b m = b := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod b m
  have hStep :
      Nat.mod (a + Nat.mod b m) m =
        Nat.mod (a + Nat.mod b m + m * Nat.div b m) m :=
    Eq.symm (nat_add_mul_mod_self_left (a + Nat.mod b m) m (Nat.div b m))
  rw [Nat.add_assoc a (Nat.mod b m) (m * Nat.div b m), hDiv] at hStep
  exact hStep

theorem nat_mod_add_mod (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm (Nat.mod a m) b, nat_add_mod_mod, Nat.add_comm b a]

theorem nat_mod_mod_mul_left (n a b : Nat) :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a :=
  nat_mod_mod_of_dvd (nat_mul_mod_right a b)

theorem nat_mod_sq_sub_succ (p k : Nat) (hk : k < p) :
    Nat.mod (p * p - (k + 1)) p = p - (k + 1) := by
  have hPos : 0 < p := Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) hk
  have hFactor : p * p = p * (p - 1) + p := by
    have hMul : p = (p - 1) + 1 := Eq.symm (Nat.sub_add_cancel hPos)
    have hDist : p * ((p - 1) + 1) = p * (p - 1) + p := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [← hMul] at hDist
    exact hDist
  rw [hFactor, Nat.add_sub_assoc hk, Nat.add_comm (p * (p - 1)) (p - (k + 1)),
      nat_add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hPos (Nat.zero_lt_succ k))

/-! ## 4. Constructive `IntBalance` Sign-Magnitude `Nat` Bridge -/

/-- Nonnegative magnitude component of an `Int`. -/
@[expose] def intPos : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

/-- Negative magnitude component of an `Int` (`0` for nonnegative `Int`). -/
@[expose] def intNeg : Int → Nat
  | .ofNat _ => 0
  | .negSucc m => m + 1

/-- `IntBalance x p n` represents `x = (p : Int) - (n : Int)` using pure `Nat`
addition (`intPos x + n = intNeg x + p`), avoiding `Int` ring tactics. -/
@[expose] def IntBalance (x : Int) (p n : Nat) : Prop :=
  intPos x + n = intNeg x + p

theorem intBalance_self (x : Int) : IntBalance x (intPos x) (intNeg x) :=
  Nat.add_comm (intPos x) (intNeg x)

theorem intBalance_ofNat (n : Nat) : IntBalance (Int.ofNat n) n 0 := by
  dsimp only [IntBalance, intPos, intNeg]
  rw [Nat.zero_add, Nat.add_zero]

theorem intBalance_subNatNat (p n : Nat) :
    IntBalance (Int.subNatNat p n) p n := by
  unfold Int.subNatNat
  cases hSub : n - p with
  | zero =>
    have hLe : n ≤ p := Nat.le_of_sub_eq_zero hSub
    dsimp only [IntBalance, intPos, intNeg]
    rw [Nat.zero_add, Nat.sub_add_cancel hLe]
  | succ k =>
    have hLt : p < n := Nat.lt_of_sub_eq_succ hSub
    have hAdd : p + (k + 1) = n := by
      rw [← hSub]
      exact Nat.add_sub_of_le (Nat.le_of_lt hLt)
    dsimp only [IntBalance, intPos, intNeg]
    rw [Nat.zero_add, Nat.add_comm (k + 1) p]
    exact hAdd.symm

/-! ### Abstract-Modulus-Safe `Int` Order, Subtraction, and Negation Helpers -/

theorem int_ofNat_add (a b : Nat) :
    Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := rfl

theorem int_ofNat_mul (a b : Nat) :
    Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) := rfl

theorem int_subNatNat_of_le {a b : Nat} (h : b ≤ a) :
    Int.subNatNat a b = Int.ofNat (a - b) := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]

theorem int_subNatNat_of_lt {a b : Nat} (h : a < b) :
    Int.subNatNat a b = Int.negSucc (b - a - 1) := by
  unfold Int.subNatNat
  have hPos : 0 < b - a := Nat.sub_pos_of_lt h
  cases hSub : b - a with
  | zero => rw [hSub] at hPos; nomatch hPos
  | succ k => rfl

theorem int_ofNat_sub_eq_subNatNat (a b : Nat) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero =>
    unfold Int.subNatNat
    rw [Nat.zero_sub a, Nat.sub_zero]
    change Int.ofNat (a + 0) = Int.ofNat a
    rw [Nat.add_zero]
  | succ _ => rfl

theorem int_ofNat_sub_of_le {a b : Nat} (h : b ≤ a) :
    Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) :=
  (int_ofNat_sub_eq_subNatNat a b).trans (int_subNatNat_of_le h)

theorem int_ofNat_sub_of_lt {a b : Nat} (h : a < b) :
    Int.ofNat a - Int.ofNat b = Int.negSucc (b - a - 1) :=
  (int_ofNat_sub_eq_subNatNat a b).trans (int_subNatNat_of_lt h)

theorem int_ofNat_le_iff (a b : Nat) :
    (Int.ofNat a ≤ Int.ofNat b) ↔ a ≤ b := by
  constructor
  · intro hLe
    have hNonNeg : Int.NonNeg (Int.ofNat b - Int.ofNat a) := hLe
    cases Nat.lt_or_ge b a with
    | inr hGe => exact hGe
    | inl hLt =>
      rw [int_ofNat_sub_of_lt hLt] at hNonNeg
      nomatch hNonNeg
  · intro hLe
    change Int.NonNeg (Int.ofNat b - Int.ofNat a)
    rw [int_ofNat_sub_of_le hLe]
    exact Int.NonNeg.mk (b - a)

theorem int_ofNat_lt_iff (a b : Nat) :
    (Int.ofNat a < Int.ofNat b) ↔ a < b := by
  change (Int.ofNat a + 1 ≤ Int.ofNat b) ↔ Nat.succ a ≤ b
  exact int_ofNat_le_iff (Nat.succ a) b

theorem int_negSucc_le_ofNat (m n : Nat) : Int.negSucc m ≤ Int.ofNat n := by
  change Int.NonNeg (Int.ofNat n - Int.negSucc m)
  exact Int.NonNeg.mk (n + Nat.succ m)

theorem int_negSucc_lt_ofNat (m n : Nat) : Int.negSucc m < Int.ofNat n := by
  change Int.NonNeg (Int.ofNat n - (Int.negSucc m + 1))
  cases m with
  | zero => exact Int.NonNeg.mk (n + 0)
  | succ m' => exact Int.NonNeg.mk (n + Nat.succ m')

theorem int_not_ofNat_le_negSucc (n m : Nat) : ¬ (Int.ofNat n ≤ Int.negSucc m) := by
  intro h
  change Int.NonNeg (Int.negSucc m - Int.ofNat n) at h
  cases n with
  | zero => nomatch h
  | succ _ => nomatch h

theorem int_not_ofNat_lt_negSucc (n m : Nat) : ¬ (Int.ofNat n < Int.negSucc m) := by
  intro h
  change Int.NonNeg (Int.negSucc m - Int.ofNat (n + 1)) at h
  nomatch h

theorem int_negSucc_le_negSucc_iff (m n : Nat) :
    (Int.negSucc m ≤ Int.negSucc n) ↔ n ≤ m := by
  constructor
  · intro h
    change Int.NonNeg (Int.subNatNat (Nat.succ m) (Nat.succ n)) at h
    cases Nat.lt_or_ge m n with
    | inr hGe => exact hGe
    | inl hLt =>
      rw [int_subNatNat_of_lt (Nat.succ_lt_succ hLt)] at h
      nomatch h
  · intro h
    change Int.NonNeg (Int.subNatNat (Nat.succ m) (Nat.succ n))
    rw [int_subNatNat_of_le (Nat.succ_le_succ h)]
    exact Int.NonNeg.mk (Nat.succ m - Nat.succ n)

theorem int_negSucc_lt_negSucc_iff (m n : Nat) :
    (Int.negSucc m < Int.negSucc n) ↔ n < m := by
  cases m with
  | zero =>
    constructor
    · intro h
      change Int.NonNeg (Int.negSucc n - Int.ofNat 0) at h
      nomatch h
    · intro h; nomatch h
  | succ m' =>
    have hAdd : Int.negSucc (m' + 1) + 1 = Int.negSucc m' := rfl
    change (Int.negSucc (m' + 1) + 1 ≤ Int.negSucc n) ↔ n < m' + 1
    rw [hAdd]
    exact (int_negSucc_le_negSucc_iff m' n).trans
      ⟨Nat.lt_succ_of_le, Nat.le_of_lt_succ⟩

theorem int_neg_ofNat_succ (n : Nat) :
    Neg.neg (Int.ofNat (n + 1)) = Int.negSucc n := rfl

theorem int_neg_negSucc (n : Nat) :
    Neg.neg (Int.negSucc n) = Int.ofNat (n + 1) := rfl

theorem nonNeg_subNatNat_le {a b : Nat}
    (h : Int.NonNeg (Int.subNatNat a b)) : b ≤ a := by
  cases Nat.lt_or_ge a b with
  | inl hLt =>
    rw [int_subNatNat_of_lt hLt] at h
    nomatch h
  | inr hGe => exact hGe

theorem le_nonNeg_subNatNat {a b : Nat} (h : b ≤ a) :
    Int.NonNeg (Int.subNatNat a b) := by
  rw [int_subNatNat_of_le h]
  exact Int.NonNeg.mk (a - b)

theorem int_ofNat_zero_le (n : Nat) : (0 : Int) ≤ Int.ofNat n :=
  (int_ofNat_le_iff 0 n).mpr (Nat.zero_le n)

theorem int_le_refl (a : Int) : a ≤ a := by
  cases a with
  | ofNat x => exact (int_ofNat_le_iff x x).mpr (Nat.le_refl x)
  | negSucc x => exact (int_negSucc_le_negSucc_iff x x).mpr (Nat.le_refl x)

theorem int_le_trans {a b c : Int} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      cases c with
      | ofNat z =>
        exact (int_ofNat_le_iff x z).mpr (Nat.le_trans
          ((int_ofNat_le_iff x y).mp hab) ((int_ofNat_le_iff y z).mp hbc))
      | negSucc z => exact False.elim (int_not_ofNat_le_negSucc y z hbc)
    | negSucc y => exact False.elim (int_not_ofNat_le_negSucc x y hab)
  | negSucc x =>
    cases b with
    | ofNat y =>
      cases c with
      | ofNat z => exact int_negSucc_le_ofNat x z
      | negSucc z => exact False.elim (int_not_ofNat_le_negSucc y z hbc)
    | negSucc y =>
      cases c with
      | ofNat z => exact int_negSucc_le_ofNat x z
      | negSucc z =>
        exact (int_negSucc_le_negSucc_iff x z).mpr (Nat.le_trans
          ((int_negSucc_le_negSucc_iff y z).mp hbc)
          ((int_negSucc_le_negSucc_iff x y).mp hab))

theorem int_lt_of_lt_of_le {a b c : Int} (hab : a < b) (hbc : b ≤ c) : a < c :=
  int_le_trans hab hbc

theorem int_add_one_le_add_one {a b : Int} (h : a ≤ b) : a + 1 ≤ b + 1 := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      exact (int_ofNat_le_iff (x + 1) (y + 1)).mpr
        (Nat.succ_le_succ ((int_ofNat_le_iff x y).mp h))
    | negSucc y => exact False.elim (int_not_ofNat_le_negSucc x y h)
  | negSucc x =>
    cases b with
    | ofNat y =>
      cases x with
      | zero => exact (int_ofNat_le_iff 0 (y + 1)).mpr (Nat.zero_le (y + 1))
      | succ x' => exact int_negSucc_le_ofNat x' (y + 1)
    | negSucc y =>
      have hyx : y ≤ x := (int_negSucc_le_negSucc_iff x y).mp h
      cases x with
      | zero =>
        cases y with
        | zero => exact (int_ofNat_le_iff 0 0).mpr (Nat.le_refl 0)
        | succ y' =>
          exact False.elim (Nat.not_lt_of_le hyx (Nat.zero_lt_succ y'))
      | succ x' =>
        cases y with
        | zero => exact int_negSucc_le_ofNat x' 0
        | succ y' =>
          exact (int_negSucc_le_negSucc_iff x' y').mpr
            (Nat.le_of_succ_le_succ hyx)

theorem int_lt_of_le_of_lt {a b c : Int} (hab : a ≤ b) (hbc : b < c) : a < c :=
  int_le_trans (int_add_one_le_add_one hab) hbc

theorem int_le_antisymm {a b : Int} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      exact congrArg Int.ofNat (Nat.le_antisymm
        ((int_ofNat_le_iff x y).mp hab) ((int_ofNat_le_iff y x).mp hba))
    | negSucc y => exact False.elim (int_not_ofNat_le_negSucc x y hab)
  | negSucc x =>
    cases b with
    | ofNat y => exact False.elim (int_not_ofNat_le_negSucc y x hba)
    | negSucc y =>
      exact congrArg Int.negSucc (Nat.le_antisymm
        ((int_negSucc_le_negSucc_iff y x).mp hba)
        ((int_negSucc_le_negSucc_iff x y).mp hab))

theorem int_not_add_one_le (a : Int) (h : a + 1 ≤ a) : False := by
  cases a with
  | ofNat n =>
    exact Nat.not_lt_of_le ((int_ofNat_le_iff (n + 1) n).mp h)
      (Nat.lt_succ_self n)
  | negSucc m =>
    cases m with
    | zero => exact int_not_ofNat_le_negSucc 0 0 h
    | succ k =>
      exact Nat.not_lt_of_le ((int_negSucc_le_negSucc_iff k (k + 1)).mp h)
        (Nat.lt_succ_self k)

theorem int_not_lt_of_ge {a b : Int} (h : b ≤ a) : ¬ (a < b) :=
  fun hlt => int_not_add_one_le a (int_le_trans hlt h)

theorem int_not_le_of_gt {a b : Int} (h : b < a) : ¬ (a ≤ b) :=
  fun hle => int_not_add_one_le b (int_le_trans h hle)

theorem int_sub_ofNat_neg_swap (a b : Nat) :
    Int.ofNat b - Int.ofNat a = Int.neg (Int.ofNat a - Int.ofNat b) := by
  rw [int_ofNat_sub_eq_subNatNat b a, int_ofNat_sub_eq_subNatNat a b]
  unfold Int.subNatNat
  cases Nat.lt_or_ge a b with
  | inl hab =>
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hab)]
    cases hS : b - a with
    | zero =>
      exact False.elim (Nat.not_lt_of_le (Nat.le_of_sub_eq_zero hS) hab)
    | succ _ => rfl
  | inr hba =>
    rw [Nat.sub_eq_zero_of_le hba]
    cases hS : a - b with
    | zero =>
      have hEq : a = b := Nat.le_antisymm (Nat.le_of_sub_eq_zero hS) hba
      subst hEq
      rfl
    | succ _ => rfl

/-! ## 5. Total `@Nat.rec` List Indexing and Slice Helpers -/

/-- Total list element lookup returning `none` when `idx ≥ xs.length`. -/
@[expose] def listNth {α : Type u} (xs : List α) (idx : Nat) : Option α :=
  @Nat.rec (fun _ => List α → Option α)
    (fun cur => match cur with | [] => none | x :: _ => some x)
    (fun _ ih cur => match cur with | [] => none | _ :: rest => ih rest)
    idx xs

theorem listNth_zero {α : Type u} (xs : List α) :
    listNth xs 0 = match xs with | [] => none | x :: _ => some x := rfl

theorem listNth_succ {α : Type u} (xs : List α) (n : Nat) :
    listNth xs (n + 1) =
      match xs with | [] => none | _ :: rest => listNth rest n := rfl

theorem listNth_map {α : Type u} {β : Type v} (f : α → β) :
    ∀ (idx : Nat) (xs : List α),
      listNth (xs.map f) idx = (listNth xs idx).map f
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: rest => listNth_map f n rest

/-- Total functional list update leaving out-of-bounds indices unchanged. -/
@[expose] def listSet {α : Type u} (xs : List α) (idx : Nat) (val : α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun cur => match cur with | [] => [] | _ :: rest => val :: rest)
    (fun _ ih cur => match cur with | [] => [] | x :: rest => x :: ih rest)
    idx xs

theorem listSet_length {α : Type u} (val : α) :
    ∀ (idx : Nat) (xs : List α), (listSet xs idx val).length = xs.length
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: rest => congrArg Nat.succ (listSet_length val n rest)

theorem listNth_listSet_same {α : Type u} (val : α) :
    ∀ (idx : Nat) (xs : List α),
      idx < xs.length → listNth (listSet xs idx val) idx = some val
  | 0, [], h => by nomatch h
  | 0, _ :: _, _ => rfl
  | _ + 1, [], h => by nomatch h
  | n + 1, _ :: rest, h =>
    listNth_listSet_same val n rest (Nat.lt_of_succ_lt_succ h)

theorem listNth_listSet_other {α : Type u} (val : α) :
    ∀ (idx q : Nat) (xs : List α),
      idx ≠ q → listNth (listSet xs idx val) q = listNth xs q
  | 0, 0, _, hNe => False.elim (hNe rfl)
  | 0, _ + 1, [], _ => rfl
  | 0, _ + 1, _ :: _, _ => rfl
  | _ + 1, 0, [], _ => rfl
  | _ + 1, 0, _ :: _, _ => rfl
  | _ + 1, _ + 1, [], _ => rfl
  | n + 1, m + 1, _ :: rest, hNe =>
    listNth_listSet_other val n m rest (fun h => hNe (congrArg Nat.succ h))

/-- Total list prefix take defined via `@Nat.rec` (no `._unsafe_rec`). -/
@[expose] def listTake {α : Type u} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun _ => [])
    (fun _ ih cur => match cur with | [] => [] | x :: rest => x :: ih rest)
    n xs

/-- Total list prefix drop defined via `@Nat.rec` (no `._unsafe_rec`). -/
@[expose] def listDrop {α : Type u} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun cur => cur)
    (fun _ ih cur => match cur with | [] => [] | _ :: rest => ih rest)
    n xs

theorem listTake_append_listDrop {α : Type u} :
    ∀ (n : Nat) (xs : List α), listTake n xs ++ listDrop n xs = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: rest =>
    congrArg (List.cons x) (listTake_append_listDrop n rest)

/-- Total byte/element slice replacement `xs[off .. off + patch.length] :=
patch`, preserving length when `off + patch.length <= xs.length`. -/
@[expose] def replaceSlice {α : Type u} (xs : List α) (off : Nat) (patch : List α) :
    List α :=
  listTake off xs ++ patch ++ listDrop (off + patch.length) xs

theorem listTake_length_of_le {α : Type u} :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length → (listTake n xs).length = n
  | 0, _, _ => rfl
  | _ + 1, [], h => by nomatch h
  | n + 1, _ :: rest, h =>
    congrArg Nat.succ (listTake_length_of_le n rest (Nat.le_of_succ_le_succ h))

theorem listDrop_nil {α : Type u} :
    ∀ n : Nat, listDrop n ([] : List α) = []
  | 0 => rfl
  | _ + 1 => rfl

theorem listDrop_succ_cons {α : Type u} (n : Nat) (x : α) (rest : List α) :
    listDrop (n + 1) (x :: rest) = listDrop n rest := rfl

theorem listDrop_length {α : Type u} :
    ∀ (n : Nat) (xs : List α), (listDrop n xs).length = xs.length - n
  | 0, xs => (Nat.sub_zero xs.length).symm
  | n + 1, [] => by
    rw [listDrop_nil (n + 1)]
    dsimp only [List.length]
    exact (Nat.zero_sub (n + 1)).symm
  | n + 1, x :: rest => by
    rw [listDrop_succ_cons n x rest, listDrop_length n rest]
    dsimp only [List.length]
    exact (Nat.succ_sub_succ_eq_sub rest.length n).symm

theorem replaceSlice_length {α : Type u} (xs : List α) (off : Nat)
    (patch : List α) (hBound : off + patch.length ≤ xs.length) :
    (replaceSlice xs off patch).length = xs.length := by
  dsimp only [replaceSlice]
  rw [List.length_append, List.length_append]
  have hOffLe : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off patch.length) hBound
  rw [listTake_length_of_le off xs hOffLe, listDrop_length]
  exact Nat.add_sub_of_le hBound

/-! ## 6. `BitVec` Bounded `toNat`, Non-Wrapping `+`, and Order -/

/- `BitVec` extensionality from `toNat`, kept private because
`Anneal.BitVec.eq_of_toNat_eq` and `Anneal.PureLift.BvLin.bv_eq_of_toNat_eq`
already export it and `Anneal.MirSymExec.Bits` opens both
`Anneal.InitLemmas` and `Anneal.PureLift.BvLin`. -/
private theorem bitVec_eq_of_toNat_eq {w : Nat} {a b : BitVec w}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

theorem bv_toNat_lt {w : Nat} (x : BitVec w) : x.toNat < Nat.pow 2 w :=
  x.toFin.isLt

theorem bv_toNat_ofNat_of_lt {w n : Nat} (h : n < Nat.pow 2 w) :
    (BitVec.ofNat w n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem bv_toNat_add_of_lt {w : Nat} {x y : BitVec w}
    (h : x.toNat + y.toNat < Nat.pow 2 w) :
    (x + y).toNat = x.toNat + y.toNat :=
  Nat.mod_eq_of_lt h

theorem bv_add_ofNat_of_lt {w a b : Nat} (h : a + b < Nat.pow 2 w) :
    BitVec.ofNat w a + BitVec.ofNat w b = BitVec.ofNat w (a + b) := by
  apply bitVec_eq_of_toNat_eq
  have ha : a < Nat.pow 2 w := Nat.lt_of_le_of_lt (Nat.le_add_right a b) h
  have hb : b < Nat.pow 2 w := Nat.lt_of_le_of_lt (Nat.le_add_left b a) h
  change
      Nat.mod ((BitVec.ofNat w a).toNat + (BitVec.ofNat w b).toNat)
        (Nat.pow 2 w) =
      (BitVec.ofNat w (a + b)).toNat
  rw [bv_toNat_ofNat_of_lt ha, bv_toNat_ofNat_of_lt hb, bv_toNat_ofNat_of_lt h]
  exact Nat.mod_eq_of_lt h

theorem bv_lt_iff_toNat_lt {w : Nat} (x y : BitVec w) :
    (x < y) ↔ x.toNat < y.toNat := Iff.rfl

theorem bv_le_iff_toNat_le {w : Nat} (x y : BitVec w) :
    (x ≤ y) ↔ x.toNat ≤ y.toNat := Iff.rfl

theorem bv_not_add_lt_left_of_lt {w : Nat} {x y : BitVec w}
    (h : x.toNat + y.toNat < Nat.pow 2 w) : ¬ (x + y < x) := by
  rw [bv_lt_iff_toNat_lt, bv_toNat_add_of_lt h]
  exact Nat.not_lt_of_ge (Nat.le_add_right x.toNat y.toNat)

/-! ## 7. Fixed-Width `UInt8`, `UInt16`, `UInt32`, and `UInt64` Lemmas -/

theorem u8_eq_of_toNat_eq {x y : UInt8} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt8.ofBitVec (bitVec_eq_of_toNat_eq h)

theorem u16_eq_of_toNat_eq {x y : UInt16} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt16.ofBitVec (bitVec_eq_of_toNat_eq h)

theorem u32_eq_of_toNat_eq {x y : UInt32} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt32.ofBitVec (bitVec_eq_of_toNat_eq h)

theorem u64_eq_of_toNat_eq {x y : UInt64} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt64.ofBitVec (bitVec_eq_of_toNat_eq h)

theorem u8_toNat_lt (x : UInt8) : x.toNat < Nat.pow 2 8 :=
  x.toBitVec.toFin.isLt

theorem u16_toNat_lt (x : UInt16) : x.toNat < Nat.pow 2 16 :=
  x.toBitVec.toFin.isLt

theorem u32_toNat_lt (x : UInt32) : x.toNat < Nat.pow 2 32 :=
  x.toBitVec.toFin.isLt

theorem u64_toNat_lt (x : UInt64) : x.toNat < Nat.pow 2 64 :=
  x.toBitVec.toFin.isLt

theorem u8_toNat_ofNat (n : Nat) :
    (UInt8.ofNat n).toNat = Nat.mod n (Nat.pow 2 8) := rfl

theorem u16_toNat_ofNat (n : Nat) :
    (UInt16.ofNat n).toNat = Nat.mod n (Nat.pow 2 16) := rfl

theorem u32_toNat_ofNat (n : Nat) :
    (UInt32.ofNat n).toNat = Nat.mod n (Nat.pow 2 32) := rfl

theorem u64_toNat_ofNat (n : Nat) :
    (UInt64.ofNat n).toNat = Nat.mod n (Nat.pow 2 64) := rfl

theorem u8_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 8) :
    (UInt8.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u16_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 16) :
    (UInt16.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u32_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 32) :
    (UInt32.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u64_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u8_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 8) :
    UInt8.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt8.ofNat n).toNat = (0 : UInt8).toNat :=
    congrArg UInt8.toNat hEq
  rw [u8_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem u16_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 16) :
    UInt16.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt16.ofNat n).toNat = (0 : UInt16).toNat :=
    congrArg UInt16.toNat hEq
  rw [u16_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem u32_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 32) :
    UInt32.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt32.ofNat n).toNat = (0 : UInt32).toNat :=
    congrArg UInt32.toNat hEq
  rw [u32_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem u64_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 64) :
    UInt64.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt64.ofNat n).toNat = (0 : UInt64).toNat :=
    congrArg UInt64.toNat hEq
  rw [u64_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

/-! ## 8. Kernel-Checked Edge-Case Canaries -/

/-- Canary exercising Section 1 `Bool` and `ite`/`dite` branch lemmas. -/
theorem canary_bool_ite_edge :
    ((true && false) = false) ∧
    (false = false ∧ false = false) ∧
    (if false then (1 : Nat) else 2) = 2 ∧
    (if _ : (0 : Nat) < 1 then (3 : Nat) else 4) = 3 :=
  ⟨rfl, bool_or_eq_false rfl, ite_false_of (by decide),
    dite_true_of (by decide)⟩

/-- Canary exercising Section 2 `BEq` and `natListBeq` edge cases
(empty lists, length mismatch, element mismatch, and reflexivity). -/
theorem canary_natListBeq_edge :
    natListBeq [] [] = true ∧
    natListBeq [] [0] = false ∧
    natListBeq [0] [] = false ∧
    natListBeq [1, 2] [1, 3] = false ∧
    (natListBeq [1, 2] [1, 2] = true ↔ [1, 2] = [1, 2]) :=
  ⟨rfl, rfl, rfl, rfl, natListBeq_iff [1, 2] [1, 2]⟩

/-- Canary exercising Section 3 `Nat` power, division, and modulo lemmas
(including zero exponent and `div2_mod2_inj`). -/
theorem canary_nat_pow_div_mod_edge (n : Nat) :
    0 < Nat.pow 2 0 ∧
    Nat.pow 2 (2 + 3) = Nat.pow 2 2 * Nat.pow 2 3 ∧
    Nat.mod 0 1 = 0 ∧
    div2_mod2_inj n n rfl rfl = rfl :=
  ⟨nat_two_pow_pos 0, nat_pow_add 2 2 3, nat_mod_eq_of_lt (by decide), rfl⟩

/-- Canary exercising Section 4 `IntBalance` edge cases (`0`, negative,
and nonnegative results from `Int.subNatNat`). -/
theorem canary_intBalance_edge :
    IntBalance (Int.ofNat 0) 0 0 ∧
    IntBalance (Int.subNatNat 0 0) 0 0 ∧
    IntBalance (Int.subNatNat 3 5) 3 5 ∧
    IntBalance (Int.subNatNat 5 3) 5 3 :=
  ⟨intBalance_ofNat 0, intBalance_subNatNat 0 0,
    intBalance_subNatNat 3 5, intBalance_subNatNat 5 3⟩

/-- Canary exercising Section 5 `@Nat.rec` list operations on empty,
out-of-bounds, and in-bounds inputs. -/
theorem canary_list_ops_edge :
    listNth ([] : List Nat) 0 = none ∧
    listNth [10] 5 = none ∧
    listSet ([] : List Nat) 0 1 = [] ∧
    listSet [10, 20] 5 99 = [10, 20] ∧
    listTake 5 [10, 20] = [10, 20] ∧
    listDrop 5 [10, 20] = [] ∧
    replaceSlice ([] : List Nat) 0 [] = [] ∧
    replaceSlice [1, 2, 3, 4] 1 [8, 9] = [1, 8, 9, 4] ∧
    (replaceSlice [1, 2, 3, 4] 1 [8, 9]).length = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    replaceSlice_length [1, 2, 3, 4] 1 [8, 9] (by decide)⟩

/-- Canary exercising Section 1-4 expanded `Bool`, `Nat`, `Nat.mod`/`Nat.div`,
and abstract-`N` `Int` helpers. -/
theorem canary_expanded_init_lemmas_edge (a b : Nat) :
    ((false && true) = false ↔ (false = false ∨ true = false)) ∧
    (Nat.mod (Nat.mod a 16) 4 = Nat.mod a 4) ∧
    (Int.subNatNat (a + b) a = Int.ofNat b) ∧
    (Int.negSucc 3 < Int.ofNat 0) ∧
    (Int.negSucc 5 < Int.negSucc 2) :=
  ⟨bool_and_eq_false_iff false true,
   nat_mod_mod_of_dvd (by decide),
   by rw [int_subNatNat_of_le (Nat.le_add_right a b), nat_add_sub_cancel_left],
   int_negSucc_lt_ofNat 3 0,
   (int_negSucc_lt_negSucc_iff 5 2).mpr (by decide)⟩

/-- Canary exercising Section 3 power-of-two monotonicity and modular
identities (power-of-two strict monotonicity, nested product modulus, squared
prime-stride tail wraparound). -/
theorem canary_nat_mod_edge (n : Nat) :
    Nat.pow 2 0 < Nat.pow 2 3 ∧
    Nat.mod (Nat.mod n (4 * 3)) 4 = Nat.mod n 4 ∧
    Nat.mod (3 * 3 - (0 + 1)) 3 = 3 - (0 + 1) :=
  ⟨nat_two_pow_lt_of_lt (by decide), nat_mod_mod_mul_left n 4 3,
    nat_mod_sq_sub_succ 3 0 (by decide)⟩

/-- Canary exercising Section 4 constructive `Int` order and `Int.ofNat`
subtraction across negative, zero, and nonnegative boundaries. -/
theorem canary_int_order_sub_edge :
    Int.negSucc 2 ≤ Int.ofNat 1 ∧
    Int.negSucc 2 ≤ Int.negSucc 0 ∧
    ¬ (Int.ofNat 2 < Int.negSucc 0) ∧
    Int.ofNat 5 - Int.ofNat 2 = Int.ofNat 3 ∧
    Int.ofNat 2 - Int.ofNat 5 = Int.neg (Int.ofNat 5 - Int.ofNat 2) :=
  ⟨int_le_trans (int_negSucc_le_ofNat 2 0) ((int_ofNat_le_iff 0 1).mpr
      (by decide)),
    (int_negSucc_le_negSucc_iff 2 0).mpr (by decide),
    int_not_lt_of_ge (int_negSucc_le_ofNat 0 2),
    int_ofNat_sub_of_le (by decide : 2 ≤ 5),
    int_sub_ofNat_neg_swap 5 2⟩

/-- Canary exercising Section 2 polymorphic `List.beq` equality reflection
on empty lists, length mismatches, element mismatches, and matching lists. -/
theorem canary_list_beq_edge :
    List.beq ([] : List Nat) [] = true ∧
    List.beq ([] : List Nat) [0] = false ∧
    List.beq [1, 2] [1, 3] = false ∧
    (List.beq [1, 2] [1, 2] = true ↔ [1, 2] = [1, 2]) :=
  ⟨rfl, rfl, rfl, list_beq_iff [1, 2] [1, 2]⟩

/-- Canary exercising Section 6 bounded `ofNat`/`toNat`, non-wrapping
`BitVec` `+`, and `<`/`≤` bridges at width `8`. -/
theorem canary_bv_arith_order_edge :
    (BitVec.ofNat 8 200).toNat = 200 ∧
    BitVec.ofNat 8 10 + BitVec.ofNat 8 20 = BitVec.ofNat 8 30 ∧
    (BitVec.ofNat 8 100 + BitVec.ofNat 8 155).toNat = 255 ∧
    ¬ (BitVec.ofNat 8 10 + BitVec.ofNat 8 20 < BitVec.ofNat 8 10) ∧
    (BitVec.ofNat 8 10 ≤ BitVec.ofNat 8 20) :=
  ⟨bv_toNat_ofNat_of_lt (by decide),
    bv_add_ofNat_of_lt (by decide),
    bv_toNat_add_of_lt (by decide),
    bv_not_add_lt_left_of_lt (by decide),
    (bv_le_iff_toNat_le (BitVec.ofNat 8 10) (BitVec.ofNat 8 20)).2
      (by decide)⟩

/-- Canary exercising Section 7 fixed-width `UInt8`..`UInt64` wraparound,
extensionality, bounded `ofNat`, and symmetric nonzero lemmas. -/
theorem canary_uint_edge :
    UInt8.ofNat 256 = UInt8.ofNat 0 ∧
    UInt16.ofNat 65536 = UInt16.ofNat 0 ∧
    (UInt32.ofNat 7).toNat = 7 ∧
    (UInt64.ofNat 9).toNat = 9 ∧
    UInt8.ofNat 1 ≠ 0 ∧
    UInt16.ofNat 1 ≠ 0 ∧
    UInt32.ofNat 1 ≠ 0 ∧
    UInt64.ofNat 1 ≠ 0 :=
  ⟨u8_eq_of_toNat_eq rfl,
    u16_eq_of_toNat_eq rfl,
    u32_toNat_ofNat_of_lt (by decide),
    u64_toNat_ofNat_of_lt (by decide),
    u8_ofNat_ne_zero (by decide) (by decide),
    u16_ofNat_ne_zero (by decide) (by decide),
    u32_ofNat_ne_zero (by decide) (by decide),
    u64_ofNat_ne_zero (by decide) (by decide)⟩

end Anneal.InitLemmas

end
