-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic

universe u v

namespace Anneal.ListChunks

/-!
# Reusable 3-Axiom List Chunking and Ceiling Division (`Anneal.ListChunks`)

Kernel-checked, universe-polymorphic list chunking and ceiling-division algebra
built strictly on Anneal's 51-module `foundation-lock.json` foundation (no
`omega`, no `bv_decide`, no `Std.*`, and zero `_unsafe_rec` auxiliaries).

Operations use `HDiv.hDiv` and `HMod.hMod` directly so every statement matches
standard `/` and `%` syntax under `rw` and `simp` in downstream proofs while
staying within `allowedTheorySyntaxKinds`.

1. **Ceiling Division (`divCeil`):** exact formula equivalence with
   `(n + k - 1) / k` for `0 < k`, positivity, zero characterization, multiple
   and shift cancellation, monotonicity, and strict decrease `divCeil n k < n`
   for `1 < n` and `1 < k`.
2. **Total Structural Chunking (`chunksOfAux` / `chunksOf`):** `@Nat.rec`
   fuel-bounded chunking with `chunksOfAux_fuel_irrel` proving independence
   from fuel `≥ xs.length`.
3. **Chunking Equations & Invariants:** unfolding on `[]` and `x :: xs`,
   `flatten` round-trip, exact length `divCeil xs.length k`, injectivity,
   exact-multiple append distributivity, `getElem?` indexing, non-emptiness,
   and per-chunk length bounds.
-/

/-! ## Part 0: Foundation-Only `Nat` and `List` Helpers -/

private theorem ite_prop_true {α : Type u} {P : Prop} {inst : Decidable P}
    {t e : α} (h : P) : (@ite α P inst t e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem ite_prop_false {α : Type u} {P : Prop} {inst : Decidable P}
    {t e : α} (h : ¬ P) : (@ite α P inst t e) = e := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem nat_div_le_div_right {a b : Nat} (h : a ≤ b) (c : Nat) :
    HDiv.hDiv a c ≤ HDiv.hDiv b c := by
  cases c with
  | zero =>
    rw [Nat.div_zero, Nat.div_zero]
    exact Nat.le_refl 0
  | succ c =>
    have hc : 0 < Nat.succ c := Nat.zero_lt_succ c
    exact (Nat.le_div_iff_mul_le hc).2
      (Nat.le_trans (Nat.div_mul_le_self a (Nat.succ c)) h)

private theorem list_take_append_drop {α : Type u} (n : Nat) (xs : List α) :
    xs.take n ++ xs.drop n = xs := by
  induction n generalizing xs with
  | zero =>
    rw [List.take_zero, List.drop_zero, List.nil_append]
  | succ n ih =>
    cases xs with
    | nil =>
      rw [List.take_nil, List.drop_nil, List.nil_append]
    | cons x rest =>
      rw [List.take_succ_cons, List.drop_succ_cons, List.cons_append, ih]

private theorem list_length_drop {α : Type u} (n : Nat) (xs : List α) :
    (xs.drop n).length = xs.length - n := by
  induction n generalizing xs with
  | zero =>
    rw [List.drop_zero, Nat.sub_zero]
  | succ n ih =>
    cases xs with
    | nil =>
      rw [List.drop_nil, List.length_nil, Nat.zero_sub]
    | cons x rest =>
      rw [List.drop_succ_cons, List.length_cons, ih, Nat.succ_sub_succ]

private theorem list_length_take_eq {α : Type u} (n : Nat) (xs : List α) :
    (xs.take n).length = if n ≤ xs.length then n else xs.length := by
  induction n generalizing xs with
  | zero =>
    rw [List.take_zero, List.length_nil, ite_prop_true (Nat.zero_le xs.length)]
  | succ n ih =>
    cases xs with
    | nil =>
      rw [List.take_nil, List.length_nil,
        ite_prop_false (Nat.not_succ_le_zero n)]
    | cons x rest =>
      rw [List.take_succ_cons, List.length_cons, List.length_cons, ih]
      cases Nat.lt_or_ge rest.length n with
      | inl hlt =>
        have h1 : ¬ (n ≤ rest.length) := Nat.not_le_of_gt hlt
        have h2 : ¬ (n + 1 ≤ rest.length + 1) :=
          Nat.not_le_of_gt (Nat.succ_lt_succ hlt)
        rw [ite_prop_false h1, ite_prop_false h2]
      | inr hge =>
        rw [ite_prop_true hge, ite_prop_true (Nat.succ_le_succ hge)]

private theorem list_length_take_le_left {α : Type u} (n : Nat) (xs : List α) :
    (xs.take n).length ≤ n := by
  rw [list_length_take_eq]
  cases Nat.lt_or_ge xs.length n with
  | inl hlt =>
    rw [ite_prop_false (Nat.not_le_of_gt hlt)]
    exact Nat.le_of_lt hlt
  | inr hge =>
    rw [ite_prop_true hge]
    exact Nat.le_refl n

private theorem list_length_take_of_le {α : Type u} {n : Nat} {xs : List α}
    (h : n ≤ xs.length) : (xs.take n).length = n := by
  rw [list_length_take_eq, ite_prop_true h]

private theorem list_drop_drop {α : Type u} (m n : Nat) (xs : List α) :
    (xs.drop m).drop n = xs.drop (m + n) := by
  induction m generalizing xs with
  | zero =>
    rw [List.drop_zero, Nat.zero_add]
  | succ m ih =>
    cases xs with
    | nil =>
      rw [List.drop_nil, List.drop_nil, List.drop_nil]
    | cons x rest =>
      rw [List.drop_succ_cons, Nat.succ_add, List.drop_succ_cons, ih]

private theorem list_take_append_of_le {α : Type u} (n : Nat) (xs ys : List α)
    (h : n ≤ xs.length) : (xs ++ ys).take n = xs.take n := by
  induction n generalizing xs with
  | zero =>
    rw [List.take_zero, List.take_zero]
  | succ n ih =>
    cases xs with
    | nil =>
      exact False.elim (Nat.not_succ_le_zero n h)
    | cons x rest =>
      rw [List.cons_append, List.take_succ_cons, List.take_succ_cons]
      rw [List.length_cons] at h
      exact congrArg (List.cons x) (ih rest (Nat.le_of_succ_le_succ h))

private theorem list_drop_append_of_le {α : Type u} (n : Nat) (xs ys : List α)
    (h : n ≤ xs.length) : (xs ++ ys).drop n = xs.drop n ++ ys := by
  induction n generalizing xs with
  | zero =>
    rw [List.drop_zero, List.drop_zero]
  | succ n ih =>
    cases xs with
    | nil =>
      exact False.elim (Nat.not_succ_le_zero n h)
    | cons x rest =>
      rw [List.cons_append, List.drop_succ_cons, List.drop_succ_cons]
      rw [List.length_cons] at h
      exact ih rest (Nat.le_of_succ_le_succ h)

private theorem list_drop_cons_length_le {α : Type u} {k : Nat} (hk : 0 < k)
    (x : α) (xs : List α) : ((x :: xs).drop k).length ≤ xs.length := by
  cases k with
  | zero =>
    exact False.elim (Nat.lt_irrefl 0 hk)
  | succ k' =>
    rw [List.drop_succ_cons, list_length_drop]
    exact Nat.sub_le xs.length k'

/-! ## Part 1: Ceiling Division (`divCeil`) -/

/-- Ceiling division `⌈n / k⌉` with `divCeil 0 k = 0` for all `k`. -/
def divCeil (n k : Nat) : Nat :=
  if n = 0 then 0 else HDiv.hDiv (n - 1) k + 1

/-- Ceiling division of zero is zero for every divisor `k`. -/
@[simp] theorem divCeil_zero_left (k : Nat) : divCeil 0 k = 0 := rfl

/-- Step equation of `divCeil` at `n + 1`. -/
@[simp] theorem divCeil_succ (n k : Nat) :
    divCeil (n + 1) k = HDiv.hDiv n k + 1 :=
  rfl

/-- Equivalence between `divCeil n k` and `(n + k - 1) / k` for `0 < k`. -/
theorem divCeil_eq_add_sub_div {n k : Nat} (hk : 0 < k) :
    divCeil n k = HDiv.hDiv (n + k - 1) k := by
  cases n with
  | zero =>
    rw [divCeil_zero_left, Nat.zero_add]
    exact Eq.symm (Nat.div_eq_of_lt (Nat.sub_lt hk Nat.zero_lt_one))
  | succ m =>
    rw [divCeil_succ]
    have hsub : m + 1 + k - 1 = m + k := by
      rw [Nat.add_right_comm, Nat.add_sub_cancel]
    rw [hsub, Nat.add_div_right m hk]

/-- Ceiling division of a positive dividend by a positive divisor is positive.
-/
theorem divCeil_pos {n k : Nat} (hn : 0 < n) (hk : 0 < k) :
    0 < divCeil n k := by
  have _ := hk
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ m => exact Nat.zero_lt_succ (HDiv.hDiv m k)

/-- For `0 < k`, `divCeil n k = 0` holds if and only if `n = 0`. -/
theorem divCeil_eq_zero_iff {n k : Nat} (hk : 0 < k) :
    divCeil n k = 0 ↔ n = 0 := by
  have _ := hk
  cases n with
  | zero =>
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ m =>
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- Ceiling division is exact on multiples `q * k` when `0 < k`. -/
theorem divCeil_mul_right (q k : Nat) (hk : 0 < k) :
    divCeil (q * k) k = q := by
  cases q with
  | zero =>
    rw [Nat.zero_mul, divCeil_zero_left]
  | succ q =>
    have hk_eq : k = (k - 1) + 1 := Eq.symm (Nat.sub_add_cancel hk)
    have hmul : (q + 1) * k = (q * k + (k - 1)) + 1 := by
      rw [Nat.succ_mul, Nat.add_assoc]
      exact congrArg (Nat.add (q * k)) hk_eq
    rw [hmul, divCeil_succ, Nat.add_comm (q * k) (k - 1),
      Nat.add_mul_div_right (k - 1) q hk,
      Nat.div_eq_of_lt (Nat.sub_lt hk Nat.zero_lt_one), Nat.zero_add]

/-- Adding a multiple `q * k` shifts `divCeil` by `q` when `0 < k`. -/
theorem divCeil_add_mul_right (n q k : Nat) (hk : 0 < k) :
    divCeil (n + q * k) k = divCeil n k + q := by
  cases n with
  | zero =>
    rw [Nat.zero_add, divCeil_zero_left, Nat.zero_add]
    exact divCeil_mul_right q k hk
  | succ m =>
    have hsum : m + 1 + q * k = (m + q * k) + 1 := by
      rw [Nat.add_right_comm]
    rw [hsum, divCeil_succ, divCeil_succ, Nat.add_mul_div_right m q hk,
      Nat.add_right_comm]

/-- Ceiling division never exceeds the dividend when `0 < k`. -/
theorem divCeil_le_self (n k : Nat) (hk : 0 < k) :
    divCeil n k ≤ n := by
  have _ := hk
  cases n with
  | zero =>
    exact Nat.le_refl 0
  | succ m =>
    rw [divCeil_succ]
    exact Nat.succ_le_succ (Nat.div_le_self m k)

/-- Ceiling division strictly decreases any `n > 1` when `k > 1`. -/
theorem divCeil_lt_self {n k : Nat} (hn : 1 < n) (hk : 1 < k) :
    divCeil n k < n := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 1 hn)
  | succ n' =>
    cases n' with
    | zero => exact False.elim (Nat.lt_irrefl 1 hn)
    | succ m =>
      rw [divCeil_succ]
      have hpos : 0 < m + 1 := Nat.zero_lt_succ m
      have hk0 : 0 < k := Nat.lt_trans Nat.zero_lt_one hk
      have hlt : HDiv.hDiv (m + 1) k < m + 1 := by
        rw [Nat.div_lt_iff_lt_mul hk0]
        have h1 : (m + 1) * 1 < (m + 1) * k :=
          Nat.mul_lt_mul_of_pos_left hk hpos
        rw [Nat.mul_one] at h1
        exact h1
      exact Nat.succ_lt_succ hlt

/-- Ceiling division is monotone in its dividend when `0 < k`. -/
theorem divCeil_mono {a b k : Nat} (hab : a ≤ b) (hk : 0 < k) :
    divCeil a k ≤ divCeil b k := by
  have _ := hk
  cases a with
  | zero =>
    exact Nat.zero_le (divCeil b k)
  | succ a' =>
    cases b with
    | zero =>
      exact False.elim (Nat.not_succ_le_zero a' hab)
    | succ b' =>
      rw [divCeil_succ, divCeil_succ]
      exact Nat.succ_le_succ
        (nat_div_le_div_right (Nat.le_of_succ_le_succ hab) k)

/-- Ceiling division by `1` is the identity. -/
@[simp] theorem divCeil_one_right (n : Nat) : divCeil n 1 = n := by
  cases n with
  | zero => rfl
  | succ m => rw [divCeil_succ, Nat.div_one]

/-- Subtracting one chunk of size `k` from a positive `n` drops `divCeil` by
`1`. -/
theorem divCeil_eq_succ_sub {n k : Nat} (hn : 0 < n) (hk : 0 < k) :
    divCeil n k = divCeil (n - k) k + 1 := by
  cases Nat.lt_or_ge k n with
  | inl hgt =>
    have hsplit : n = (n - k) + 1 * k := by
      rw [Nat.one_mul]
      exact Eq.symm (Nat.sub_add_cancel (Nat.le_of_lt hgt))
    have h1 := congrArg (fun z => divCeil z k) hsplit
    rw [divCeil_add_mul_right (n - k) 1 k hk] at h1
    exact h1
  | inr hle =>
    have hsub0 : n - k = 0 := Nat.sub_eq_zero_of_le hle
    rw [hsub0, divCeil_zero_left, Nat.zero_add]
    cases n with
    | zero => exact False.elim (Nat.lt_irrefl 0 hn)
    | succ m =>
      rw [divCeil_succ, Nat.div_eq_of_lt (Nat.lt_of_succ_le hle)]

/-! ## Part 2: Fuel-Bounded Structural Chunking (`chunksOfAux` / `chunksOf`) -/

/-- Fuel-bounded structural list chunking. Using `@Nat.rec` avoids compiler
`_unsafe_rec` auxiliaries while remaining `rfl`-reducible on `0` and
`fuel + 1`. -/
def chunksOfAux {α : Type u} (k : Nat) (fuel : Nat) (xs : List α) :
    List (List α) :=
  @Nat.rec (fun _ => List α → List (List α))
    (fun _ => [])
    (fun _ ih ys =>
      match ys with
      | [] => []
      | x :: rest => (x :: rest).take k :: ih ((x :: rest).drop k))
    fuel xs

/-- Base equation of `chunksOfAux` with zero fuel. -/
@[simp] theorem chunksOfAux_zero {α : Type u} (k : Nat) (xs : List α) :
    chunksOfAux k 0 xs = [] :=
  rfl

/-- Empty-list equation of `chunksOfAux` with positive fuel. -/
@[simp] theorem chunksOfAux_succ_nil {α : Type u} (k fuel : Nat) :
    chunksOfAux (α := α) k (fuel + 1) [] = [] :=
  rfl

/-- Cons step equation of `chunksOfAux` with positive fuel. -/
@[simp] theorem chunksOfAux_succ_cons {α : Type u} (k fuel : Nat)
    (x : α) (xs : List α) :
    chunksOfAux k (fuel + 1) (x :: xs) =
      (x :: xs).take k :: chunksOfAux k fuel ((x :: xs).drop k) :=
  rfl

/-- Fuel irrelevance: when `0 < k`, any two fuel budgets `≥ xs.length` produce
the identical chunk list. -/
theorem chunksOfAux_fuel_irrel {α : Type u} {k : Nat} (hk : 0 < k) :
    ∀ (fuel₁ fuel₂ : Nat) (xs : List α),
      xs.length ≤ fuel₁ → xs.length ≤ fuel₂ →
      chunksOfAux k fuel₁ xs = chunksOfAux k fuel₂ xs := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
    intro fuel₂ xs h1 _
    cases xs with
    | nil =>
      cases fuel₂ with
      | zero => rfl
      | succ fuel₂' => rfl
    | cons _ _ =>
      exact False.elim (Nat.not_succ_le_zero _ h1)
  | succ fuel₁ ih =>
    intro fuel₂ xs h1 h2
    cases xs with
    | nil =>
      cases fuel₂ with
      | zero => rfl
      | succ fuel₂' => rfl
    | cons x rest =>
      cases fuel₂ with
      | zero =>
        exact False.elim (Nat.not_succ_le_zero _ h2)
      | succ fuel₂' =>
        rw [chunksOfAux_succ_cons, chunksOfAux_succ_cons]
        rw [List.length_cons] at h1
        rw [List.length_cons] at h2
        have hdrop : ((x :: rest).drop k).length ≤ rest.length :=
          list_drop_cons_length_le hk x rest
        have h1' : ((x :: rest).drop k).length ≤ fuel₁ :=
          Nat.le_trans hdrop (Nat.le_of_succ_le_succ h1)
        have h2' : ((x :: rest).drop k).length ≤ fuel₂' :=
          Nat.le_trans hdrop (Nat.le_of_succ_le_succ h2)
        exact congrArg (List.cons ((x :: rest).take k))
          (ih fuel₂' ((x :: rest).drop k) h1' h2')

/-- Partition `xs` into contiguous chunks of size `k` (with a possibly shorter
final chunk when `k` does not divide `xs.length`). Returns `[]` when `k = 0`.
-/
def chunksOf {α : Type u} (k : Nat) (xs : List α) : List (List α) :=
  if k = 0 then [] else chunksOfAux k xs.length xs

/-- Chunking with size `0` always yields `[]`. -/
@[simp] theorem chunksOf_zero_size {α : Type u} (xs : List α) :
    chunksOf 0 xs = [] :=
  rfl

/-- Chunking the empty list always yields `[]`. -/
@[simp] theorem chunksOf_nil {α : Type u} (k : Nat) :
    chunksOf (α := α) k [] = [] := by
  unfold chunksOf
  cases k with
  | zero => rfl
  | succ _ => rfl

private theorem chunksOf_eq_aux {α : Type u} {k : Nat} (hk : 0 < k)
    (xs : List α) :
    chunksOf k xs = chunksOfAux k xs.length xs := by
  unfold chunksOf
  exact ite_prop_false (Nat.ne_of_gt hk)

/-! ## Part 3: Chunking Equations and Algebraic Invariants -/

/-- Recursive unfolding of `chunksOf k` on a non-empty list `x :: xs` when
`0 < k`. -/
theorem chunksOf_cons {α : Type u} {k : Nat} (hk : 0 < k)
    (x : α) (xs : List α) :
    chunksOf k (x :: xs) =
      (x :: xs).take k :: chunksOf k ((x :: xs).drop k) := by
  rw [chunksOf_eq_aux hk (x :: xs), chunksOf_eq_aux hk ((x :: xs).drop k),
    List.length_cons, chunksOfAux_succ_cons]
  have hdrop : ((x :: xs).drop k).length ≤ xs.length :=
    list_drop_cons_length_le hk x xs
  exact congrArg (List.cons ((x :: xs).take k))
    (chunksOfAux_fuel_irrel hk xs.length ((x :: xs).drop k).length
      ((x :: xs).drop k) hdrop (Nat.le_refl _))

/-- Recursive unfolding of `chunksOf k` on any non-empty list when `0 < k`. -/
theorem chunksOf_of_nonempty {α : Type u} {k : Nat} (hk : 0 < k)
    {xs : List α} (hne : xs ≠ []) :
    chunksOf k xs = xs.take k :: chunksOf k (xs.drop k) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x rest => exact chunksOf_cons hk x rest

private theorem chunksOf_flatten_aux {α : Type u} {k : Nat} (hk : 0 < k) :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → (chunksOf k xs).flatten = xs := by
  intro n
  induction n with
  | zero =>
    intro xs hle
    cases xs with
    | nil => rw [chunksOf_nil]; rfl
    | cons _ _ => exact False.elim (Nat.not_succ_le_zero _ hle)
  | succ n ih =>
    intro xs hle
    cases xs with
    | nil => rw [chunksOf_nil]; rfl
    | cons x rest =>
      rw [List.length_cons] at hle
      have hdrop : ((x :: rest).drop k).length ≤ n :=
        Nat.le_trans (list_drop_cons_length_le hk x rest)
          (Nat.le_of_succ_le_succ hle)
      rw [chunksOf_cons hk, List.flatten_cons, ih ((x :: rest).drop k) hdrop,
        list_take_append_drop]

/-- Flattening `chunksOf k xs` recovers `xs` whenever `0 < k`. -/
@[simp] theorem chunksOf_flatten {α : Type u} {k : Nat} (hk : 0 < k)
    (xs : List α) :
    (chunksOf k xs).flatten = xs :=
  chunksOf_flatten_aux hk xs.length xs (Nat.le_refl xs.length)

private theorem chunksOf_length_aux {α : Type u} {k : Nat} (hk : 0 < k) :
    ∀ (n : Nat) (xs : List α),
      xs.length ≤ n → (chunksOf k xs).length = divCeil xs.length k := by
  intro n
  induction n with
  | zero =>
    intro xs hle
    cases xs with
    | nil => rw [chunksOf_nil]; rfl
    | cons _ _ => exact False.elim (Nat.not_succ_le_zero _ hle)
  | succ n ih =>
    intro xs hle
    cases xs with
    | nil => rw [chunksOf_nil]; rfl
    | cons x rest =>
      rw [List.length_cons] at hle
      have hdrop : ((x :: rest).drop k).length ≤ n :=
        Nat.le_trans (list_drop_cons_length_le hk x rest)
          (Nat.le_of_succ_le_succ hle)
      rw [chunksOf_cons hk, List.length_cons, ih ((x :: rest).drop k) hdrop,
        list_length_drop]
      exact Eq.symm (divCeil_eq_succ_sub (Nat.zero_lt_succ rest.length) hk)

/-- The number of chunks produced by `chunksOf k xs` equals
`divCeil xs.length k` whenever `0 < k`. -/
@[simp] theorem chunksOf_length {α : Type u} {k : Nat} (hk : 0 < k)
    (xs : List α) :
    (chunksOf k xs).length = divCeil xs.length k :=
  chunksOf_length_aux hk xs.length xs (Nat.le_refl xs.length)

/-- Chunking never increases list length when `0 < k`. -/
theorem chunksOf_length_le {α : Type u} {k : Nat} (hk : 0 < k) (xs : List α) :
    (chunksOf k xs).length ≤ xs.length := by
  rw [chunksOf_length hk]
  exact divCeil_le_self xs.length k hk

/-- Chunking strictly shrinks any list of length `> 1` when `k > 1`. -/
theorem chunksOf_length_lt {α : Type u} {k : Nat} (hk : 1 < k)
    {xs : List α} (hxs : 1 < xs.length) :
    (chunksOf k xs).length < xs.length := by
  rw [chunksOf_length (Nat.lt_trans Nat.zero_lt_one hk)]
  exact divCeil_lt_self hxs hk

private theorem chunksOf_append_exact_aux {α : Type u} {k : Nat} (hk : 0 < k) :
    ∀ (n : Nat) (xs ys : List α),
      xs.length ≤ n → HMod.hMod xs.length k = 0 →
      chunksOf k (xs ++ ys) = chunksOf k xs ++ chunksOf k ys := by
  intro n
  induction n with
  | zero =>
    intro xs ys hle _
    cases xs with
    | nil =>
      rw [List.nil_append, chunksOf_nil, List.nil_append]
    | cons _ _ =>
      exact False.elim (Nat.not_succ_le_zero _ hle)
  | succ n ih =>
    intro xs ys hle hdiv
    cases xs with
    | nil =>
      rw [List.nil_append, chunksOf_nil, List.nil_append]
    | cons x rest =>
      have hk_le : k ≤ (x :: rest).length := by
        cases Nat.lt_or_ge (x :: rest).length k with
        | inl hlt =>
          rw [Nat.mod_eq_of_lt hlt] at hdiv
          nomatch hdiv
        | inr hge =>
          exact hge
      rw [List.length_cons] at hle
      have hdrop_le : ((x :: rest).drop k).length ≤ n :=
        Nat.le_trans (list_drop_cons_length_le hk x rest)
          (Nat.le_of_succ_le_succ hle)
      have hdrop_div : HMod.hMod ((x :: rest).drop k).length k = 0 := by
        rw [list_length_drop]
        have hsub : (x :: rest).length - k + k = (x :: rest).length :=
          Nat.sub_add_cancel hk_le
        have hmod := congrArg (fun z => HMod.hMod z k) hsub
        rw [Nat.add_mod_right] at hmod
        rw [hmod]
        exact hdiv
      rw [List.cons_append, chunksOf_cons hk, chunksOf_cons hk, List.cons_append]
      rw [← List.cons_append, list_take_append_of_le k (x :: rest) ys hk_le,
        list_drop_append_of_le k (x :: rest) ys hk_le]
      exact congrArg (List.cons ((x :: rest).take k))
        (ih ((x :: rest).drop k) ys hdrop_le hdrop_div)

/-- Chunking distributes over `++` when the left list's length is an exact
multiple of `k`. -/
theorem chunksOf_append_exact {α : Type u} {k : Nat} (hk : 0 < k)
    (xs ys : List α) (hdiv : HMod.hMod xs.length k = 0) :
    chunksOf k (xs ++ ys) = chunksOf k xs ++ chunksOf k ys :=
  chunksOf_append_exact_aux hk xs.length xs ys (Nat.le_refl xs.length) hdiv

/-- Indexed lookup of the `i`-th chunk returns `some ((xs.drop (i * k)).take k)`
for every in-bounds index `i < (chunksOf k xs).length`. -/
theorem chunksOf_getElem? {α : Type u} {k : Nat} (hk : 0 < k)
    (xs : List α) (i : Nat) (hi : i < (chunksOf k xs).length) :
    (chunksOf k xs)[i]? = some ((xs.drop (i * k)).take k) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil =>
      rw [chunksOf_nil, List.length_nil] at hi
      exact False.elim (Nat.not_lt_zero 0 hi)
    | cons x rest =>
      rw [chunksOf_cons hk, Nat.zero_mul, List.drop_zero]
      rfl
  | succ i ih =>
    cases xs with
    | nil =>
      rw [chunksOf_nil, List.length_nil] at hi
      exact False.elim (Nat.not_lt_zero _ hi)
    | cons x rest =>
      rw [chunksOf_cons hk, List.length_cons] at hi
      rw [chunksOf_cons hk]
      have hstep :
          ((x :: rest).take k :: chunksOf k ((x :: rest).drop k))[i + 1]? =
            (chunksOf k ((x :: rest).drop k))[i]? :=
        rfl
      rw [hstep, ih ((x :: rest).drop k) (Nat.lt_of_succ_lt_succ hi),
        list_drop_drop, Nat.succ_mul, Nat.add_comm]

/-- `chunksOf k` is injective when `0 < k`. -/
theorem chunksOf_eq_imp_eq {α : Type u} {k : Nat} (hk : 0 < k)
    {xs ys : List α} (h : chunksOf k xs = chunksOf k ys) :
    xs = ys := by
  rw [← chunksOf_flatten hk xs, ← chunksOf_flatten hk ys, h]

private theorem chunksOf_elem_length_le_aux {α : Type u} {k : Nat}
    (hk : 0 < k) :
    ∀ (n : Nat) (xs c : List α),
      xs.length ≤ n → c ∈ chunksOf k xs → c.length ≤ k := by
  intro n
  induction n with
  | zero =>
    intro xs c hle hc
    cases xs with
    | nil =>
      rw [chunksOf_nil] at hc
      cases hc
    | cons _ _ =>
      exact False.elim (Nat.not_succ_le_zero _ hle)
  | succ n ih =>
    intro xs c hle hc
    cases xs with
    | nil =>
      rw [chunksOf_nil] at hc
      cases hc
    | cons x rest =>
      rw [List.length_cons] at hle
      rw [chunksOf_cons hk] at hc
      cases hc with
      | head =>
        exact list_length_take_le_left k (x :: rest)
      | tail _ hmem =>
        have hdrop : ((x :: rest).drop k).length ≤ n :=
          Nat.le_trans (list_drop_cons_length_le hk x rest)
            (Nat.le_of_succ_le_succ hle)
        exact ih ((x :: rest).drop k) c hdrop hmem

/-- Every chunk in `chunksOf k xs` has length at most `k`. -/
theorem chunksOf_elem_length_le {α : Type u} {k : Nat} (hk : 0 < k)
    {xs c : List α} (hc : c ∈ chunksOf k xs) :
    c.length ≤ k :=
  chunksOf_elem_length_le_aux hk xs.length xs c (Nat.le_refl xs.length) hc

private theorem chunksOf_elem_nonempty_aux {α : Type u} {k : Nat}
    (hk : 0 < k) :
    ∀ (n : Nat) (xs c : List α),
      xs.length ≤ n → c ∈ chunksOf k xs → c ≠ [] := by
  intro n
  induction n with
  | zero =>
    intro xs c hle hc
    cases xs with
    | nil =>
      rw [chunksOf_nil] at hc
      cases hc
    | cons _ _ =>
      exact False.elim (Nat.not_succ_le_zero _ hle)
  | succ n ih =>
    intro xs c hle hc
    cases xs with
    | nil =>
      rw [chunksOf_nil] at hc
      cases hc
    | cons x rest =>
      rw [List.length_cons] at hle
      rw [chunksOf_cons hk] at hc
      cases hc with
      | head =>
        cases k with
        | zero => exact False.elim (Nat.lt_irrefl 0 hk)
        | succ k' =>
          rw [List.take_succ_cons]
          intro hnil
          nomatch hnil
      | tail _ hmem =>
        have hdrop : ((x :: rest).drop k).length ≤ n :=
          Nat.le_trans (list_drop_cons_length_le hk x rest)
            (Nat.le_of_succ_le_succ hle)
        exact ih ((x :: rest).drop k) c hdrop hmem

/-- Every chunk in `chunksOf k xs` is non-empty when `0 < k`. -/
theorem chunksOf_elem_nonempty {α : Type u} {k : Nat} (hk : 0 < k)
    {xs c : List α} (hc : c ∈ chunksOf k xs) :
    c ≠ [] :=
  chunksOf_elem_nonempty_aux hk xs.length xs c (Nat.le_refl xs.length) hc

/-- Every full chunk `(i + 1) * k ≤ xs.length` has exact length `k`. -/
theorem chunksOf_elem_length_exact {α : Type u} {k : Nat} (hk : 0 < k)
    (xs : List α) (i : Nat) (hi : (i + 1) * k ≤ xs.length) :
    ((xs.drop (i * k)).take k).length = k := by
  have _ := hk
  apply list_length_take_of_le
  rw [list_length_drop]
  rw [Nat.succ_mul, Nat.add_comm] at hi
  exact Nat.le_sub_of_add_le hi

/-- Two lists of equal length have equal chunk lengths at every in-bounds
chunk index `i`. -/
theorem chunksOf_same_len_elem_length_eq {α : Type u} {β : Type v} {k : Nat}
    (hk : 0 < k) {xs : List α} {ys : List β} (hlen : xs.length = ys.length)
    (i : Nat) (hi : i < (chunksOf k xs).length) :
    ((xs.drop (i * k)).take k).length = ((ys.drop (i * k)).take k).length := by
  have _ := hk
  have _ := hi
  rw [list_length_take_eq, list_length_take_eq, list_length_drop,
    list_length_drop, hlen]

end Anneal.ListChunks
