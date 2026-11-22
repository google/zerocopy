-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic

/-!
# CPS Spine-Forcing and `@Nat.rec` Combinators (`Anneal.SpineForce`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`, zero
`noncomputable`, allowed theory tactics only) combinators providing explicit
weak-head / spine-forcing CPS wrappers and raw `@Nat.rec` iteration helpers:

1. **`withStrictNat` (`@Nat.casesOn` WHNF Wrapper):**
   Case-splits `n` via `@Nat.casesOn` (`0` or `Nat.succ p`) before passing the
   reconstructed `Nat` to `k`, with extensional identity `withStrictNat_eq`.

2. **CPS Spine-Forcing (`forceNat`, `forceOption`, `forceList`):**
   Pattern-matches and reconstructs the `Nat`, `Option`, or `List` constructor
   spine in continuation-passing style before invoking `cont`, intended for
   callers that want explicit constructor spines before continuing proof or
   checker evaluation, with zero-axiom extensional identities (`forceNat_eq`,
   `forceOption_eq`, `forceList_eq`).

3. **Zero-`._unsafe_rec` Bounded Iteration & Quantifiers (`natFold`, `runPow2`,
   `checkRange`):**
   Equation-compiler recursion over fuel or indices can emit `._unsafe_rec`
   auxiliaries rejected by `TrustedBoundary`. Defining combinators directly via
   `@Nat.rec` guarantees zero `._unsafe_rec` and zero `noncomputable` markers:
   `natFold` folds linearly, `runPow2` iterates `stepChunk` `2 ^ pow2Depth`
   times via recursive doubling (`ih (ih cur)`), and `checkRange_sound`
   discharges bounded `∀ i < n, P i` goals from boolean reflection checks.
-/

namespace Anneal.SpineForce

/-! ## 1. `@Nat.casesOn` WHNF Wrapper (`withStrictNat`) -/

/-- Case-split `n` into weak-head form (`0` or `Nat.succ _`) via `@Nat.casesOn`
before passing the reconstructed `Nat` to `k`. -/
def withStrictNat {α : Type u} (n : Nat) (k : Nat → α) : α :=
  @Nat.casesOn (fun _ => α) n (k 0) (fun p => k (Nat.succ p))

/-- Proves `withStrictNat` equals direct application `k n`. -/
theorem withStrictNat_eq {α : Type u} (n : Nat) (k : Nat → α) :
    withStrictNat n k = k n := by
  cases n <;> rfl

/-! ## 2. CPS Spine-Forcing (`forceNat`, `forceOption`, `forceList`) -/

/-- Force the full Peano spine of `n` in CPS before invoking `cont`. -/
def forceNat {α : Type u} (n : Nat) (cont : Nat → α) : α :=
  @Nat.rec (fun _ => (Nat → α) → α)
    (fun k => k 0)
    (fun _ ih k => ih (fun m' => k (m' + 1)))
    n cont

/-- Proves `forceNat` is extensionally equal to `cont n`. -/
theorem forceNat_eq {α : Type u} :
    ∀ (n : Nat) (cont : Nat → α), forceNat n cont = cont n
  | 0, _ => rfl
  | m + 1, cont => by
    dsimp only [forceNat]
    exact forceNat_eq m (fun m' => cont (m' + 1))

/-- Case-split `opt` in WHNF before passing the reconstructed `Option` to
`cont`. -/
def forceOption {α : Type u} {β : Type v} (opt : Option α)
    (cont : Option α → β) : β :=
  match opt with
  | none => cont none
  | some x => cont (some x)

/-- Proves `forceOption` is extensionally equal to `cont opt`. -/
theorem forceOption_eq {α : Type u} {β : Type v} (opt : Option α)
    (cont : Option α → β) : forceOption opt cont = cont opt := by
  cases opt <;> rfl

/-- Force the cons-spine of `xs` in CPS before passing the rebuilt list to
`cont`. -/
def forceList {α : Type u} {β : Type v} (xs : List α)
    (cont : List α → β) : β :=
  List.foldr
    (fun (x : α) (ih : (List α → β) → β) (k : List α → β) =>
      ih (fun xs' => k (x :: xs')))
    (fun k => k [])
    xs cont

/-- Proves `forceList` is extensionally equal to `cont xs`. -/
theorem forceList_eq {α : Type u} {β : Type v} :
    ∀ (xs : List α) (cont : List α → β), forceList xs cont = cont xs
  | [], _ => rfl
  | x :: xs, cont => by
    dsimp only [forceList, List.foldr]
    exact forceList_eq xs (fun xs' => cont (x :: xs'))

/-! ## 3. Zero-`._unsafe_rec` Iteration & Recursive-Doubling Stepper -/

/-- Apply `stepFn k` over `steps` steps counting down from `steps - 1` to `0`
using raw `@Nat.rec` (emitting no `._unsafe_rec` auxiliaries). -/
def natFold {α : Type u} (steps : Nat) (stepFn : Nat → α → α) (init : α) : α :=
  @Nat.rec (fun _ => α → α)
    (fun acc => acc)
    (fun k ih acc => ih (stepFn k acc))
    steps init

/-- Base reduction for `natFold` at `0` steps. -/
theorem natFold_zero {α : Type u} (stepFn : Nat → α → α) (init : α) :
    natFold 0 stepFn init = init := rfl

/-- Step reduction for `natFold` at `n + 1` steps. -/
theorem natFold_succ {α : Type u} (n : Nat) (stepFn : Nat → α → α)
    (init : α) :
    natFold (n + 1) stepFn init = natFold n stepFn (stepFn n init) := rfl

/-- Proves `natFold` preserves any invariant `inv` that holds on `init` and is
preserved by `stepFn k` for all `k < steps`. -/
theorem natFold_preserves {α : Type u} (inv : α → Prop)
    (stepFn : Nat → α → α) :
    ∀ (steps : Nat) (init : α),
      (∀ (k : Nat) (acc : α), k < steps → inv acc → inv (stepFn k acc)) →
      inv init →
      inv (natFold steps stepFn init)
  | 0, _, _, hInit => hInit
  | n + 1, init, hStep, hInit =>
    natFold_preserves inv stepFn n (stepFn n init)
      (fun k acc hLt hAcc =>
        hStep k acc (Nat.lt_trans hLt (Nat.lt_succ_self n)) hAcc)
      (hStep n init (Nat.lt_succ_self n) hInit)

/-- Apply `stepChunk` `2 ^ pow2Depth` times via recursive doubling
(`ih (ih cur)`) over raw `@Nat.rec`, structuring composition in a balanced
binary call tree of depth `pow2Depth`. -/
def runPow2 {α : Type u} (pow2Depth : Nat) (stepChunk : α → α) (st : α) : α :=
  @Nat.rec (fun _ => α → α)
    stepChunk
    (fun _ ih cur => ih (ih cur))
    pow2Depth st

/-- Base reduction for `runPow2` at depth `0` (`2 ^ 0 = 1` chunk). -/
theorem runPow2_zero {α : Type u} (stepChunk : α → α) (st : α) :
    runPow2 0 stepChunk st = stepChunk st := rfl

/-- Recursive doubling equation for `runPow2` at depth `d + 1`. -/
theorem runPow2_succ {α : Type u} (d : Nat) (stepChunk : α → α) (st : α) :
    runPow2 (d + 1) stepChunk st =
      runPow2 d stepChunk (runPow2 d stepChunk st) := rfl

/-- Proves `runPow2` preserves any invariant `inv` preserved by `stepChunk`. -/
theorem runPow2_preserves {α : Type u} (inv : α → Prop) (stepChunk : α → α)
    (hStep : ∀ s : α, inv s → inv (stepChunk s)) :
    ∀ (d : Nat) (st : α), inv st → inv (runPow2 d stepChunk st)
  | 0, st, hInv => hStep st hInv
  | d + 1, st, hInv =>
    runPow2_preserves inv stepChunk hStep d (runPow2 d stepChunk st)
      (runPow2_preserves inv stepChunk hStep d st hInv)

/-! ## 4. Bounded Quantifier Reflection (`checkRange` / `checkRange_sound`) -/

/-- Boolean checker verifying `predB k = true` for every `k < bound` using
raw `@Nat.rec`. -/
def checkRange (predB : Nat → Bool) (bound : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k acc => predB k && acc)
    bound

/-- Base reduction for `checkRange` at bound `0`. -/
theorem checkRange_zero (predB : Nat → Bool) :
    checkRange predB 0 = true := rfl

/-- Step reduction for `checkRange` at bound `n + 1`. -/
theorem checkRange_succ (predB : Nat → Bool) (n : Nat) :
    checkRange predB (n + 1) = (predB n && checkRange predB n) := rfl

/-- Extract per-index `predB i = true` evidence for `i < bound` from
`checkRange predB bound = true`. -/
theorem checkRange_true_imp (predB : Nat → Bool) :
    ∀ (bound i : Nat),
      checkRange predB bound = true → i < bound → predB i = true
  | 0, _, _, hLt => by nomatch hLt
  | n + 1, i, hChk, hLt => by
    rw [checkRange_succ] at hChk
    have hHead : predB n = true := by
      cases hb : predB n with
      | false => rw [hb] at hChk; nomatch hChk
      | true => rfl
    have hTail : checkRange predB n = true := by
      rw [hHead] at hChk
      exact hChk
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hLt) with
    | inl hEq =>
      rw [hEq]
      exact hHead
    | inr hSubLt =>
      exact checkRange_true_imp predB n i hTail hSubLt

/-- Discharge `∀ i, i < bound → P i` via `rfl` or `decide` whenever `predB`
reflects `P`. -/
theorem checkRange_sound {P : Nat → Prop} (predB : Nat → Bool)
    (hReflect : ∀ i : Nat, predB i = true → P i)
    (bound : Nat) (hOk : checkRange predB bound = true) :
    ∀ i : Nat, i < bound → P i :=
  fun i hLt => hReflect i (checkRange_true_imp predB bound i hOk hLt)

/-! ## 5. Kernel-Checked Canaries -/

/-- Canary verifying `withStrictNat` handles `0` cleanly. -/
theorem withStrictNat_zero_canary :
    withStrictNat 0 (fun x => x + 1) = 1 := rfl

/-- Canary verifying `withStrictNat` computes `k n` on compound arithmetic. -/
theorem withStrictNat_canary :
    withStrictNat (2 + 3) (fun x => x + 1) = 6 := rfl

/-- Canary verifying `forceNat` reduces in the kernel to `cont n`. -/
theorem forceNat_canary :
    forceNat 4 (fun n => n * 2) = 8 := rfl

/-- Canary verifying `forceOption` preserves `none`. -/
theorem forceOption_none_canary :
    forceOption (none : Option Nat)
      (fun opt => match opt with | none => 0 | some x => x + 1) = 0 := rfl

/-- Canary verifying `forceOption` splits `some` cleanly. -/
theorem forceOption_canary :
    forceOption (some 7)
      (fun opt => match opt with | none => 0 | some x => x + 1) = 8 := rfl

/-- Canary verifying `forceList` handles the empty list cleanly. -/
theorem forceList_nil_canary :
    forceList ([] : List Nat) (fun xs => xs.length) = 0 := rfl

/-- Canary verifying `forceList` handles a singleton list cleanly. -/
theorem forceList_singleton_canary :
    forceList [42] (fun xs => xs.length) = 1 := rfl

/-- Canary verifying `forceList` handles nested lists (outer spine). -/
theorem forceList_nested_canary :
    forceList [[1], [], [2, 3]] (fun xs => xs.length) = 3 := rfl

/-- Canary verifying `forceList` materializes a concrete list spine. -/
theorem forceList_canary :
    forceList [1, 2, 3] (fun xs => xs.length) = 3 := rfl

/-- Canary verifying `natFold` handles `0` steps cleanly. -/
theorem natFold_zero_canary :
    natFold 0 (fun k acc => acc + k) 5 = 5 := rfl

/-- Canary verifying `natFold` computes `0 + 3 + 2 + 1 + 0 = 6`. -/
theorem natFold_canary :
    natFold 4 (fun k acc => acc + k) 0 = 6 := rfl

/-- Canary verifying `natFold_preserves` maintains bounded positivity. -/
theorem natFold_preserves_canary :
    0 < natFold 4 (fun _ acc => acc + 1) 1 :=
  natFold_preserves (fun x => 0 < x) (fun _ acc => acc + 1) 4 1
    (fun _ _ _ h => Nat.lt_trans h (Nat.lt_succ_self _))
    (Nat.lt_succ_self 0)

/-- Canary verifying `runPow2 0` applies `stepChunk` once (`2 ^ 0 = 1`). -/
theorem runPow2_zero_canary :
    runPow2 0 (fun x => x + 1) 5 = 6 := rfl

/-- Canary verifying `runPow2 3` steps `8` times (`2 ^ 3 = 8`). -/
theorem runPow2_canary :
    runPow2 3 (fun x => x + 1) 0 = 8 := rfl

/-- Canary verifying `runPow2_preserves` keeps positive numbers positive. -/
theorem runPow2_preserves_canary :
    0 < runPow2 3 (fun x => x + 1) 1 :=
  runPow2_preserves (fun x => 0 < x) (fun x => x + 1)
    (fun _ h => Nat.lt_trans h (Nat.lt_succ_self _)) 3 1 (Nat.lt_succ_self 0)

/-- Canary verifying `checkRange_sound` handles bound `0` vacuously. -/
theorem checkRange_zero_canary : ∀ i : Nat, i < 0 → i < 10 :=
  checkRange_sound (fun i => decide (i < 10))
    (fun _ h => of_decide_eq_true h) 0 rfl

/-- Canary verifying `checkRange_sound` discharges `∀ i < 5, i < 10`. -/
theorem checkRange_canary : ∀ i : Nat, i < 5 → i < 10 :=
  checkRange_sound (fun i => decide (i < 10))
    (fun _ h => of_decide_eq_true h) 5 rfl

end Anneal.SpineForce
