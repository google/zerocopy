-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic

/-!
# Shared Foundation-Locked `Init` Lemmas (`Anneal.InitLemmas`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`,
admitted theory tactics only) lemma pack consolidating five high-frequency
helper clusters across `anneal/theory/` and `anneal/correspondence/`:

1. `Bool` connectives and `ite`/`dite` branch reduction from propositional
   hypotheses.
2. Generic `BEq` reflection bridges (`beq_refl` / `eq_of_beq` <-> `beq_iff`)
   plus `natListBeq`.
3. `Nat` power-of-two, division, and modulo identities.
4. Constructive `IntBalance` sign-magnitude `Nat` bridge for `Int` reasoning
   without `omega`.
5. Total `@Nat.rec` list indexing, slicing, and range-replacement lemmas.
-/

namespace Anneal.InitLemmas

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
def natListBeq (xs ys : List Nat) : Bool :=
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

theorem div2_mod2_inj (m n : Nat)
    (hDiv : Nat.div n 2 = Nat.div m 2)
    (hMod : Nat.mod n 2 = Nat.mod m 2) : n = m := by
  have hm : 2 * Nat.div m 2 + Nat.mod m 2 = m := Nat.div_add_mod m 2
  have hn : 2 * Nat.div n 2 + Nat.mod n 2 = n := Nat.div_add_mod n 2
  rw [hDiv, hMod] at hn
  rw [← hn, hm]

/-! ## 4. Constructive `IntBalance` Sign-Magnitude `Nat` Bridge -/

/-- Nonnegative magnitude component of an `Int`. -/
def intPos : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

/-- Negative magnitude component of an `Int` (`0` for nonnegative `Int`). -/
def intNeg : Int → Nat
  | .ofNat _ => 0
  | .negSucc m => m + 1

/-- `IntBalance x p n` represents `x = (p : Int) - (n : Int)` using pure `Nat`
addition (`intPos x + n = intNeg x + p`), avoiding `Int` ring tactics. -/
def IntBalance (x : Int) (p n : Nat) : Prop :=
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

/-! ## 5. Total `@Nat.rec` List Indexing and Slice Helpers -/

/-- Total list element lookup returning `none` when `idx ≥ xs.length`. -/
def listNth {α : Type u} (xs : List α) (idx : Nat) : Option α :=
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
def listSet {α : Type u} (xs : List α) (idx : Nat) (val : α) : List α :=
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
def listTake {α : Type u} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun _ => [])
    (fun _ ih cur => match cur with | [] => [] | x :: rest => x :: ih rest)
    n xs

/-- Total list prefix drop defined via `@Nat.rec` (no `._unsafe_rec`). -/
def listDrop {α : Type u} (n : Nat) (xs : List α) : List α :=
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
def replaceSlice {α : Type u} (xs : List α) (off : Nat) (patch : List α) :
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

/-! ## 6. Kernel-Checked Edge-Case Canaries -/

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

end Anneal.InitLemmas
