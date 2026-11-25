-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.MirTotal.Ops

public section

namespace Anneal.ByteRun

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# Mixed-`InitMask` Padded Aggregate & `[T; N]` Copy Laws (`Anneal.ByteRun.Copy`)

Zero-axiom (`[]`), LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`,
`0` `omega`) run-decomposed untyped byte-copy algebra over
`Trusted.MirSemantics.{MemoryState, Allocation, AllocByte, readBytes,
writeBytes}`. `copyRangeComp` and `copyRepeatedlyComp` model untyped,
overlap-tolerant (read-then-write) byte-range copies; they do not perform
rustc's typed-copy padding/provenance reset (`validate_place`) or
non-overlapping source/destination UB checks:

1. **Run-decomposed mixed `InitMask` & provenance layouts (`ByteRun`,
   `flattenByteRuns`, `repeatByteRuns`, `projectRunAtSplit`):** Models
   padded `#[repr(C)]` structs and `MaybeUninit` aggregates as contiguous runs
   of `.initPlain` scalar bytes, `.initProv` provenance-carrying pointer bytes,
   and `.uninitPad` padding bytes.
2. **Untyped byte-range `copyRangeComp` soundness (`copyRangeComp_sound`):**
   Proves `copyRangeComp` refines `Trusted.MirSemantics.readBytes` +
   `writeBytes` (`[]` zero axioms) for non-empty slices, preserving mixed
   `.init`/`.uninit` and provenance runs verbatim, projecting post-copy runs via
   `readBytes`, and framing disjoint slices.
3. **`[T; N]` `Repeat` array-copy fusion (`copyRepeatedlyComp`,
   `copyRepeatedlyComp_sound`):** Proves via `@Nat.rec` contiguous splice fusion
   that `n` sequential element copies over disjoint source and destination
   ranges fuse into a single `repeatByteRuns n runs` write (`[]` zero axioms),
   preserving every element `0 ≤ i < n` and framing disjoint memory.
-/

/-! ## 1. Constructive Arithmetic, Modular Stride, & Contiguous Splice Fusion -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalse (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

private theorem bandIntro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]
  rfl

private theorem borFalseElim {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => exact False.elim (boolTrueNeFalse h)
  | false => exact ⟨rfl, h⟩

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α} (hb : b = true) :
    (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) :
    (if b then t else e) = e := by
  subst hb
  rfl

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBeq_of_eq (a b : Nat) (h : a = b) : Nat.beq a b = true := by
  subst h
  exact natBeq_refl a

private theorem natBle_refl (a : Nat) : Nat.ble a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBle_zero_left (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_zero_right (a : Nat) (h : Nat.ble a 0 = true) :
    a = 0 := by
  cases a with
  | zero => rfl
  | succ _ => exact False.elim (boolFalseNeTrue h)

private theorem natBle_succ_right (a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble a (b + 1) = true := by
  revert b h
  induction a with
  | zero => intro _ _; rfl
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact ih b' h

private theorem natBle_trans (a b c : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b c = true) :
    Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_left c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrue h2)
      | succ c' => exact ih b' c' h1 h2

private theorem natAdd_zero_left (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_succ_left (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => exact natAdd_zero_left b
  | succ a' ih => exact Eq.trans (natAdd_succ_left a' b) (congrArg Nat.succ ih)

private theorem natAdd_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBle_add_right (a b : Nat) : Nat.ble a (a + b) = true := by
  induction b with
  | zero => exact natBle_refl a
  | succ _ ih => exact natBle_succ_right a _ ih

private theorem natBle_add_mono_right (a b c : Nat) (h : Nat.ble a b = true) :
    Nat.ble (a + c) (b + c) = true := by
  induction c with
  | zero => exact h
  | succ _ ih => exact ih

private theorem natBle_add_mono_left (c a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble (c + a) (c + b) = true := by
  rw [natAdd_comm c a, natAdd_comm c b]
  exact natBle_add_mono_right a b c h

private theorem natBeq_zero_false_of_blt_zero (n : Nat)
    (h : Nat.blt 0 n = true) :
    Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (boolFalseNeTrue h)
  | succ _ => rfl

private theorem natBlt_pos_mul (n sz : Nat)
    (hn : Nat.blt 0 n = true) (hsz : Nat.blt 0 sz = true) :
    Nat.blt 0 (n * sz) = true := by
  cases n with
  | zero => exact False.elim (boolFalseNeTrue hn)
  | succ _ =>
    cases sz with
    | zero => exact False.elim (boolFalseNeTrue hsz)
    | succ _ =>
      rw [Nat.succ_mul, Nat.add_succ]
      rfl

private theorem natSub_add_cancel_of_ble (a b : Nat) (h : Nat.ble a b = true) :
    a + (b - a) = b := by
  revert b
  induction a with
  | zero => intro b _; exact natAdd_zero_left b
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' =>
      rw [Nat.succ_sub_succ, natAdd_succ_left]
      exact congrArg Nat.succ (ih b' h)

private theorem pow2_pos (n : Nat) : 0 < Nat.pow 2 n := by
  induction n with
  | zero => exact Nat.zero_lt_succ 0
  | succ n' ih =>
    change 0 < Nat.pow 2 n' * 2
    rw [Nat.mul_succ, Nat.mul_one]
    exact Nat.lt_of_lt_of_le ih
      (Nat.le_add_left (Nat.pow 2 n') (Nat.pow 2 n'))

private theorem modCoreGo_congr {y : Nat} (hy : 0 < y) :
    ∀ (f1 f2 x : Nat) (h1 : x < f1) (h2 : x < f2),
      Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2
  | 0, _, _, h1, _ => False.elim (Nat.not_lt_zero _ h1)
  | _, 0, _, _, h2 => False.elim (Nat.not_lt_zero _ h2)
  | f1 + 1, f2 + 1, x, h1, h2 => by
    unfold Nat.modCore.go
    cases Nat.decLe y x with
    | isFalse _ => rfl
    | isTrue hle =>
      exact modCoreGo_congr hy f1 f2 (x - y)
        (Nat.div_rec_fuel_lemma hy hle h1) (Nat.div_rec_fuel_lemma hy hle h2)

private theorem dite_pos_eq {α : Type} {P : Prop} [d : Decidable P]
    (hp : P) (t : P → α) (e : ¬ P → α) :
    dite P t e = t hp := by
  cases d with
  | isFalse hn => exact False.elim (hn hp)
  | isTrue _ => rfl

private theorem dite_neg_eq {α : Type} {P : Prop} [d : Decidable P]
    (hnp : ¬ P) (t : P → α) (e : ¬ P → α) :
    dite P t e = e hnp := by
  cases d with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem modCoreGo_step {y : Nat} (hy : 0 < y) (f x : Nat)
    (h : x < f + 1) :
    Nat.modCore.go y hy (f + 1) x h =
      dite (y ≤ x)
        (fun hle =>
          Nat.modCore.go y hy f (x - y) (Nat.div_rec_fuel_lemma hy hle h))
        (fun _ => x) := rfl

private theorem mod_succ_step (x' y : Nat) :
    Nat.mod (x' + 1) y = ite (y ≤ x' + 1) (Nat.modCore (x' + 1) y) (x' + 1) :=
  rfl

private theorem modCore_of_pos (x y : Nat) (hy : 0 < y) :
    Nat.modCore x y = Nat.modCore.go y hy (x + 1) x (Nat.lt_succ_self x) := by
  unfold Nat.modCore
  exact dite_pos_eq hy _ _

private theorem ite_split {α : Type} {P : Prop} [d : Decidable P] {t e r : α}
    (hT : P → t = r) (hF : ¬ P → e = r) :
    ite P t e = r := by
  cases d with
  | isTrue hp => exact hT hp
  | isFalse hnp => exact hF hnp

private theorem mod_eq_modCore_of_pos (x y : Nat) (hy : 0 < y) :
    Nat.mod x y = Nat.modCore x y := by
  cases x with
  | zero =>
    rw [modCore_of_pos 0 y hy, modCoreGo_step hy 0 0 (Nat.lt_succ_self 0),
      dite_neg_eq (fun hLe0 => Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hy hLe0))]
    rfl
  | succ x' =>
    rw [mod_succ_step x' y]
    refine ite_split (fun _ => rfl) (fun hNotLe => ?_)
    rw [modCore_of_pos (x' + 1) y hy,
      modCoreGo_step hy (x' + 1) (x' + 1) (Nat.lt_succ_self (x' + 1)),
      dite_neg_eq hNotLe]

private theorem natAdd_sub_self (x k : Nat) : (x + k) - k = x := by
  induction k with
  | zero => rfl
  | succ _ ih =>
    rw [Nat.add_succ, Nat.succ_sub_succ]
    exact ih

private theorem natMod_add_self_of_pos (x k : Nat) (hk : 0 < k) :
    Nat.mod (x + k) k = Nat.mod x k := by
  rw [mod_eq_modCore_of_pos (x + k) k hk, mod_eq_modCore_of_pos x k hk,
    modCore_of_pos (x + k) k hk, modCore_of_pos x k hk,
    modCoreGo_step hk (x + k) (x + k) (Nat.lt_succ_self (x + k)),
    dite_pos_eq (Nat.le_add_left k x)]
  have hSub : (x + k) - k = x := natAdd_sub_self x k
  have hGoal : ∀ (f1 z : Nat) (hz : z = x) (hFz : z < f1),
      Nat.modCore.go k hk f1 z hFz =
        Nat.modCore.go k hk (x + 1) x (Nat.lt_succ_self x) := by
    intro f1 z hz hFz
    cases hz
    exact modCoreGo_congr hk f1 (x + 1) x hFz (Nat.lt_succ_self x)
  exact hGoal (x + k) ((x + k) - k) hSub
    (Nat.div_rec_fuel_lemma hk (Nat.le_add_left k x)
      (Nat.lt_succ_self (x + k)))

private theorem natMod_add_mul_self_of_pos (x k m : Nat) (hk : 0 < k) :
    Nat.mod (x + k * m) k = Nat.mod x k := by
  induction m with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ m' ih =>
    rw [Nat.mul_succ, ← natAdd_assoc x (k * m') k,
      natMod_add_self_of_pos (x + k * m') k hk]
    exact ih

private theorem exists_mul_of_mod_zero_fuel (k : Nat) (hk : 0 < k) :
    ∀ (fuel s : Nat), s < fuel → Nat.mod s k = 0 → Exists (fun q => s = k * q)
  | 0, _, hLt, _ => False.elim (Nat.not_lt_zero _ hLt)
  | fuel + 1, s, hLt, hMod => by
    cases Nat.decLe k s with
    | isFalse hNotLe =>
      have hEqS : Nat.mod s k = s := by
        rw [mod_eq_modCore_of_pos s k hk, modCore_of_pos s k hk,
          modCoreGo_step hk s s (Nat.lt_succ_self s), dite_neg_eq hNotLe]
      rw [hEqS] at hMod
      exact ⟨0, Eq.trans hMod (Nat.mul_zero k).symm⟩
    | isTrue hLe =>
      have hSplit : (s - k) + k = s := by
        rw [natAdd_comm (s - k) k]
        exact natSub_add_cancel_of_ble k s (Nat.ble_eq_true_of_le hLe)
      have hModSub : Nat.mod (s - k) k = 0 := by
        have hStep := natMod_add_self_of_pos (s - k) k hk
        rw [hSplit] at hStep
        exact Eq.trans hStep.symm hMod
      have hSubLt : s - k < fuel :=
        Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_lt_of_le hk hLe) hk)
          (Nat.le_of_lt_succ hLt)
      cases exists_mul_of_mod_zero_fuel k hk fuel (s - k) hSubLt hModSub with
      | intro q' hq' =>
        refine ⟨q' + 1, ?_⟩
        rw [Nat.mul_succ, ← hq', hSplit]

private theorem natMod_add_mul_zero_of_pos (off stride k i : Nat) (hk : 0 < k)
    (hOff : Nat.mod off k = 0) (hStride : Nat.mod stride k = 0) :
    Nat.mod (off + i * stride) k = 0 := by
  cases exists_mul_of_mod_zero_fuel k hk (stride + 1) stride
      (Nat.lt_succ_self stride) hStride with
  | intro q hq =>
    induction i with
    | zero =>
      rw [Nat.zero_mul, Nat.add_zero]
      exact hOff
    | succ i' ih =>
      rw [Nat.succ_mul, ← natAdd_assoc off (i' * stride) stride, hq,
        natMod_add_mul_self_of_pos (off + i' * (k * q)) k q hk, ← hq]
      exact ih

private theorem listAppend_nil_right {α : Type} (xs : List α) : xs ++ [] = xs :=
  by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem listAppend_assoc {α : Type} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem listLength_append {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => exact (natAdd_zero_left ys.length).symm
  | cons _ tl ih =>
    change (tl ++ ys).length + 1 = (tl.length + 1) + ys.length
    rw [ih, natAdd_succ_left]

private theorem listDrop_nil {α : Type} (n : Nat) :
    List.drop n ([] : List α) = [] := by
  cases n <;> rfl

private theorem listTake_length_of_ble {α : Type} (n : Nat) (xs : List α)
    (h : Nat.ble n xs.length = true) : (xs.take n).length = n := by
  revert xs
  induction n with
  | zero => intro _ _; rfl
  | succ n' ih =>
    intro xs h
    cases xs with
    | nil => exact False.elim (boolFalseNeTrue h)
    | cons _ tl =>
      change (tl.take n').length + 1 = n' + 1
      exact congrArg Nat.succ (ih tl h)

private theorem listDrop_add {α : Type} (a b : Nat) (xs : List α) :
    xs.drop (a + b) = (xs.drop a).drop b := by
  rw [natAdd_comm a b]
  revert xs
  induction a with
  | zero => intro _; rfl
  | succ a' ih =>
    intro xs
    cases xs with
    | nil =>
      rw [listDrop_nil (b + (a' + 1)), listDrop_nil (a' + 1), listDrop_nil b]
    | cons _ tl =>
      change tl.drop (b + a') = (tl.drop a').drop b
      exact ih tl

private theorem listTake_append_drop {α : Type} (n : Nat) (xs : List α) :
    xs.take n ++ xs.drop n = xs := by
  revert xs
  induction n with
  | zero => intro _; rfl
  | succ n' ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons hd tl =>
      change hd :: (tl.take n' ++ tl.drop n') = hd :: tl
      exact congrArg (List.cons hd) (ih tl)

private theorem listDrop_take_length_of_ble {α : Type} (off sz : Nat)
    (xs : List α) (h : Nat.ble (off + sz) xs.length = true) :
    ((xs.drop off).take sz).length = sz := by
  revert xs
  induction off with
  | zero =>
    intro xs h
    rw [natAdd_zero_left] at h
    exact listTake_length_of_ble sz xs h
  | succ _ ih =>
    intro xs h
    cases xs with
    | nil =>
      rw [natAdd_succ_left] at h
      exact False.elim (boolFalseNeTrue h)
    | cons _ tl =>
      rw [natAdd_succ_left] at h
      exact ih tl h

private theorem listSplice_length {α : Type} (off : Nat) (mid xs : List α)
    (h : Nat.ble (off + mid.length) xs.length = true) :
    (xs.take off ++ mid ++ xs.drop (off + mid.length)).length = xs.length := by
  revert xs
  induction off with
  | zero =>
    intro xs h
    rw [natAdd_zero_left] at h
    rw [natAdd_zero_left]
    change (mid ++ xs.drop mid.length).length = xs.length
    rw [listLength_append]
    have hEq := listTake_append_drop mid.length xs
    have hLen := congrArg List.length hEq
    rw [listLength_append, listTake_length_of_ble mid.length xs h] at hLen
    exact hLen
  | succ off' ih =>
    intro xs h
    cases xs with
    | nil =>
      rw [natAdd_succ_left] at h
      exact False.elim (boolFalseNeTrue h)
    | cons hd tl =>
      rw [natAdd_succ_left] at h
      rw [natAdd_succ_left]
      change
        (hd :: (tl.take off' ++ mid ++ tl.drop (off' + mid.length))).length =
          tl.length + 1
      exact congrArg Nat.succ (ih tl h)

private theorem listDrop_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem listTake_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem listDrop_append_of_len {α : Type} (n : Nat) (xs ys : List α)
    (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  subst h
  exact listDrop_append_exact xs ys

private theorem listTake_append_of_len {α : Type} (n : Nat) (xs ys : List α)
    (h : xs.length = n) :
    (xs ++ ys).take n = xs := by
  subst h
  exact listTake_append_exact xs ys

private theorem listDrop_append_ge {α : Type} (n : Nat) (xs ys : List α)
    (h : Nat.ble xs.length n = true) :
    (xs ++ ys).drop n = ys.drop (n - xs.length) := by
  revert n
  induction xs with
  | nil => intro _ _; rfl
  | cons _ tl ih =>
    intro n h
    cases n with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ n' =>
      change (tl ++ ys).drop n' = ys.drop ((n' + 1) - (tl.length + 1))
      rw [Nat.succ_sub_succ]
      exact ih n' h

private theorem listDrop_take_splice_same {α : Type} (off : Nat)
    (mid xs : List α) (h : Nat.ble (off + mid.length) xs.length = true) :
    ((xs.take off ++ mid ++ xs.drop (off + mid.length)).drop off).take
        mid.length = mid := by
  have hOffLe : Nat.ble off xs.length = true :=
    natBle_trans off (off + mid.length) xs.length
      (natBle_add_right off mid.length) h
  have hTakeLen : (xs.take off).length = off :=
    listTake_length_of_ble off xs hOffLe
  rw [listAppend_assoc, listDrop_append_of_len off (xs.take off) _ hTakeLen]
  exact listTake_append_exact mid (xs.drop (off + mid.length))

/-- Contiguous splice fusion: splicing `mid1` at `off` and then `mid2`
immediately adjacent at `off + mid1.length` equals a single splice of
`mid1 ++ mid2` at `off`. -/
theorem listSplice_contiguous_fuse {α : Type} (off : Nat)
    (mid1 mid2 xs : List α)
    (h1 : Nat.ble (off + mid1.length) xs.length = true) :
    let xs1 := xs.take off ++ mid1 ++ xs.drop (off + mid1.length)
    xs1.take (off + mid1.length) ++ mid2 ++
        xs1.drop ((off + mid1.length) + mid2.length) =
      xs.take off ++ (mid1 ++ mid2) ++
        xs.drop (off + (mid1 ++ mid2).length) := by
  dsimp only
  have hOffLe : Nat.ble off xs.length = true :=
    natBle_trans off (off + mid1.length) xs.length
      (natBle_add_right off mid1.length) h1
  have hPreLen : (xs.take off ++ mid1).length = off + mid1.length := by
    rw [listLength_append, listTake_length_of_ble off xs hOffLe]
  have hTake1 :
      (xs.take off ++ mid1 ++ xs.drop (off + mid1.length)).take
          (off + mid1.length) = xs.take off ++ mid1 :=
    listTake_append_of_len (off + mid1.length) (xs.take off ++ mid1) _ hPreLen
  have hDrop1 :
      (xs.take off ++ mid1 ++ xs.drop (off + mid1.length)).drop
          ((off + mid1.length) + mid2.length) =
        xs.drop (off + (mid1 ++ mid2).length) := by
    rw [listDrop_add (off + mid1.length) mid2.length
        (xs.take off ++ mid1 ++ xs.drop (off + mid1.length)),
      listDrop_append_of_len (off + mid1.length) (xs.take off ++ mid1) _
        hPreLen,
      ← listDrop_add (off + mid1.length) mid2.length xs,
      natAdd_assoc off mid1.length mid2.length,
      listLength_append mid1 mid2]
  rw [hTake1, hDrop1, listAppend_assoc (xs.take off) mid1 mid2]

private theorem listDrop_take_comm_le {α : Type} (off sz n : Nat) (xs : List α)
    (h : Nat.ble (off + sz) n = true) :
    ((xs.take n).drop off).take sz = (xs.drop off).take sz := by
  revert n xs
  induction off with
  | zero =>
    intro n xs h
    rw [natAdd_zero_left] at h
    change ((xs.take n).take sz) = xs.take sz
    revert n xs
    induction sz with
    | zero => intro _ _ _; rfl
    | succ _ ihSz =>
      intro n xs hLe
      cases n with
      | zero => exact False.elim (boolFalseNeTrue hLe)
      | succ n' =>
        cases xs with
        | nil => rfl
        | cons hd tl =>
          change hd :: ((tl.take n').take _) = hd :: tl.take _
          exact congrArg (List.cons hd) (ihSz n' tl hLe)
  | succ off' ih =>
    intro n xs h
    rw [natAdd_succ_left] at h
    cases n with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ n' =>
      cases xs with
      | nil => rfl
      | cons _ tl =>
        change ((tl.take n').drop off').take sz = (tl.drop off').take sz
        exact ih n' tl h

private theorem listDrop_take_splice_disjoint {α : Type} (off1 off2 sz2 : Nat)
    (mid1 xs : List α)
    (h1 : Nat.ble (off1 + mid1.length) xs.length = true)
    (hDisj :
      (Nat.ble (off1 + mid1.length) off2 || Nat.ble (off2 + sz2) off1) = true) :
    ((xs.take off1 ++ mid1 ++ xs.drop (off1 + mid1.length)).drop off2).take
        sz2 = (xs.drop off2).take sz2 := by
  have hOff1Le : Nat.ble off1 xs.length = true :=
    natBle_trans off1 (off1 + mid1.length) xs.length
      (natBle_add_right off1 mid1.length) h1
  have hPreLen : (xs.take off1 ++ mid1).length = off1 + mid1.length := by
    rw [listLength_append, listTake_length_of_ble off1 xs hOff1Le]
  cases hLeft : Nat.ble (off1 + mid1.length) off2 with
  | true =>
    have hGePre : Nat.ble (xs.take off1 ++ mid1).length off2 = true := by
      rw [hPreLen]; exact hLeft
    rw [listDrop_append_ge off2 (xs.take off1 ++ mid1)
        (xs.drop (off1 + mid1.length)) hGePre,
      hPreLen, ← listDrop_add (off1 + mid1.length) _ xs,
      natSub_add_cancel_of_ble (off1 + mid1.length) off2 hLeft]
  | false =>
    have hDisj2 : Nat.ble (off2 + sz2) off1 = true := by
      rw [hLeft] at hDisj; exact hDisj
    have hTakeLen : (xs.take off1).length = off1 :=
      listTake_length_of_ble off1 xs hOff1Le
    rw [listAppend_assoc]
    have hSubTake :
        ((xs.take off1 ++ (mid1 ++ xs.drop (off1 + mid1.length))).take off1) =
          xs.take off1 :=
      listTake_append_of_len off1 (xs.take off1) _ hTakeLen
    rw [← listDrop_take_comm_le off2 sz2 off1
        (xs.take off1 ++ (mid1 ++ xs.drop (off1 + mid1.length))) hDisj2,
      hSubTake]
    exact listDrop_take_comm_le off2 sz2 off1 xs hDisj2

/-- Repeats a slice `n` times (`[elem; n]`) via `@Nat.rec` (`0` `._unsafe_rec`).
-/
@[expose] def repeatSlice {α : Type} (n : Nat) (elem : List α) : List α :=
  @Nat.rec (fun _ => List α) [] (fun _ acc => acc ++ elem) n

/-- Base equation `repeatSlice 0 elem = []`. -/
theorem repeatSlice_zero {α : Type} (elem : List α) :
    repeatSlice 0 elem = [] := rfl

/-- Step equation `repeatSlice (n + 1) elem = repeatSlice n elem ++ elem`. -/
theorem repeatSlice_succ {α : Type} (n : Nat) (elem : List α) :
    repeatSlice (n + 1) elem = repeatSlice n elem ++ elem := rfl

/-- Length of `repeatSlice n elem` equals `n * elem.length`. -/
theorem repeatSlice_length {α : Type} (n : Nat) (elem : List α) :
    (repeatSlice n elem).length = n * elem.length := by
  induction n with
  | zero => rw [Nat.zero_mul]; rfl
  | succ _ ih => rw [repeatSlice_succ, listLength_append, ih, Nat.succ_mul]

private theorem repeatSlice_cons_head {α : Type} (n : Nat) (elem : List α) :
    elem ++ repeatSlice n elem = repeatSlice n elem ++ elem := by
  induction n with
  | zero => exact listAppend_nil_right elem
  | succ n' ih =>
    rw [repeatSlice_succ, ← listAppend_assoc elem (repeatSlice n' elem) elem,
      ih]

/-- Projecting element `i` (`i < n`) from `repeatSlice n elem` recovers `elem`.
-/
theorem repeatSlice_project_elem {α : Type} (n i : Nat) (elem : List α)
    (hLt : Nat.blt i n = true) :
    ((repeatSlice n elem).drop (i * elem.length)).take elem.length = elem := by
  revert i
  induction n with
  | zero =>
    intro i hLt
    cases i <;> exact False.elim (boolFalseNeTrue hLt)
  | succ n' ih =>
    intro i hLt
    rw [repeatSlice_succ, ← repeatSlice_cons_head n' elem]
    cases i with
    | zero =>
      rw [Nat.zero_mul]
      exact listTake_append_exact elem (repeatSlice n' elem)
    | succ i' =>
      have hLt' : Nat.blt i' n' = true := hLt
      rw [Nat.succ_mul, natAdd_comm (i' * elem.length) elem.length,
        listDrop_add elem.length (i' * elem.length)
          (elem ++ repeatSlice n' elem),
        listDrop_append_exact elem (repeatSlice n' elem)]
      exact ih i' hLt'

/-! ## 2. `findAllocation` / `replaceAllocation` & `writeBytes` Algebra -/

private theorem findAllocation_allocId (id : AllocId)
    (allocs : List Allocation) (a : Allocation)
    (h : findAllocation id allocs = some a) : a.allocId = id := by
  induction allocs with
  | nil => nomatch h
  | cons hd _ ih =>
    dsimp only [findAllocation] at h
    cases hEq : Nat.beq hd.allocId id with
    | true =>
      rw [ite_bool_true hEq] at h
      injection h with hA
      subst hA
      exact natEq_of_beq hd.allocId id hEq
    | false =>
      rw [ite_bool_false hEq] at h
      exact ih h

private theorem replaceAllocation_self (id : AllocId)
    (allocs : List Allocation) (a : Allocation)
    (h : findAllocation id allocs = some a) :
    replaceAllocation a allocs = allocs := by
  have hId := findAllocation_allocId id allocs a h
  induction allocs with
  | nil => nomatch h
  | cons hd _ ih =>
    dsimp only [findAllocation] at h
    dsimp only [replaceAllocation]
    cases hEq : Nat.beq hd.allocId id with
    | true =>
      rw [ite_bool_true hEq] at h
      injection h with hA
      subst hA
      rw [natBeq_refl hd.allocId, ite_bool_true rfl]
    | false =>
      rw [ite_bool_false hEq] at h
      rw [hId, hEq, ite_bool_false rfl]
      exact congrArg (List.cons hd) (ih h)

private theorem findAllocation_replaceAllocation_same
    (allocs : List Allocation) (aOld aNew : Allocation)
    (hFind : findAllocation aOld.allocId allocs = some aOld)
    (hSameId : aNew.allocId = aOld.allocId) :
    findAllocation aOld.allocId (replaceAllocation aNew allocs) = some aNew :=
  by
  induction allocs with
  | nil => nomatch hFind
  | cons hd _ ih =>
    dsimp only [findAllocation] at hFind
    dsimp only [replaceAllocation]
    rw [hSameId]
    cases hEq : Nat.beq hd.allocId aOld.allocId with
    | true =>
      rw [ite_bool_true rfl]
      dsimp only [findAllocation]
      rw [hSameId, natBeq_refl aOld.allocId, ite_bool_true rfl]
    | false =>
      rw [ite_bool_false hEq] at hFind
      rw [ite_bool_false rfl]
      dsimp only [findAllocation]
      rw [hEq, ite_bool_false rfl]
      exact ih hFind

private theorem findAllocation_replaceAllocation_ne (otherId : AllocId)
    (allocs : List Allocation) (aNew : Allocation)
    (hNe : Nat.beq aNew.allocId otherId = false) :
    findAllocation otherId (replaceAllocation aNew allocs) =
      findAllocation otherId allocs := by
  induction allocs with
  | nil => rfl
  | cons hd _ ih =>
    dsimp only [replaceAllocation]
    cases hEq : Nat.beq hd.allocId aNew.allocId with
    | true =>
      rw [ite_bool_true rfl]
      have hHdEq := natEq_of_beq hd.allocId aNew.allocId hEq
      dsimp only [findAllocation]
      rw [hHdEq, hNe, ite_bool_false rfl, ite_bool_false rfl]
    | false =>
      rw [ite_bool_false rfl]
      dsimp only [findAllocation]
      cases Nat.beq hd.allocId otherId with
      | true => rw [ite_bool_true rfl, ite_bool_true rfl]
      | false =>
        rw [ite_bool_false rfl, ite_bool_false rfl]
        exact ih

private theorem replaceAllocation_replaceAllocation_same
    (allocs : List Allocation) (a1 a2 : Allocation)
    (hSame : a2.allocId = a1.allocId) :
    replaceAllocation a2 (replaceAllocation a1 allocs) =
      replaceAllocation a2 allocs := by
  induction allocs with
  | nil => rfl
  | cons hd _ ih =>
    dsimp only [replaceAllocation]
    rw [hSame]
    cases hEq : Nat.beq hd.allocId a1.allocId with
    | true =>
      rw [ite_bool_true rfl]
      dsimp only [replaceAllocation]
      rw [hSame, natBeq_refl a1.allocId]
      rfl
    | false =>
      rw [ite_bool_false rfl]
      dsimp only [replaceAllocation]
      rw [hSame, hEq, ite_bool_false rfl]
      exact congrArg (List.cons hd) ih

/-- Sufficient half-open byte-range separation
(`off1 + sz1 ≤ off2 ∨ off2 + sz2 ≤ off1`; exact disjointness
`[off1, off1 + sz1) ∩ [off2, off2 + sz2) = ∅` on non-empty slices). -/
@[expose] def rangesDisjoint (off1 sz1 off2 sz2 : Nat) : Bool :=
  Nat.ble (off1 + sz1) off2 || Nat.ble (off2 + sz2) off1

private theorem writeBytes_ok_inversion (m m' : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bs : List AllocByte)
    (hPos : Nat.blt 0 bs.length = true)
    (hWrite : writeBytes m place alignLog2 bs = .ok m') :
    Exists (fun a =>
      findAllocation place.allocId m.allocations = some a ∧
      a.mutability = .mut ∧
      a.live = true ∧
      isInBounds a place.offset bs.length = true ∧
      isAligned a place.offset alignLog2 = true ∧
      m' = MemoryState.mk m.nextAllocId
        (replaceAllocation
          (Allocation.mk a.allocId a.alignLog2 .mut
            (a.bytes.take place.offset ++ bs ++
              a.bytes.drop (place.offset + bs.length))
            true)
          m.allocations)) := by
  dsimp only [writeBytes] at hWrite
  cases hFind : findAllocation place.allocId m.allocations with
  | none => rw [hFind] at hWrite; nomatch hWrite
  | some a =>
    rw [hFind] at hWrite
    dsimp only at hWrite
    rw [natBeq_zero_false_of_blt_zero bs.length hPos, ite_bool_false rfl] at hWrite
    cases hGuard :
        (!a.live || !isInBounds a place.offset bs.length ||
          !isAligned a place.offset alignLog2) with
    | true => rw [ite_bool_true hGuard] at hWrite; nomatch hWrite
    | false =>
      rw [ite_bool_false hGuard] at hWrite
      have hG1 := borFalseElim hGuard
      have hG2 := borFalseElim hG1.1
      have hLive : a.live = true := by
        cases hl : a.live with
        | true => rfl
        | false => rw [hl] at hG2; exact False.elim (boolTrueNeFalse hG2.1)
      have hBounds : isInBounds a place.offset bs.length = true := by
        cases hb : isInBounds a place.offset bs.length with
        | true => rfl
        | false => rw [hb] at hG2; exact False.elim (boolTrueNeFalse hG2.2)
      have hAlign : isAligned a place.offset alignLog2 = true := by
        cases ha : isAligned a place.offset alignLog2 with
        | true => rfl
        | false => rw [ha] at hG1; exact False.elim (boolTrueNeFalse hG1.2)
      have hMutCase :
          a.mutability = .mut ∧
          m' = MemoryState.mk m.nextAllocId
            (replaceAllocation
              (Allocation.mk a.allocId a.alignLog2 a.mutability
                (a.bytes.take place.offset ++ bs ++
                  a.bytes.drop (place.offset + bs.length))
                a.live)
              m.allocations) :=
        @Mutability.casesOn
          (fun mu =>
            (match mu with
              | .shared => Except.error FaultKind.undefined
              | .mut =>
                Except.ok (MemoryState.mk m.nextAllocId
                  (replaceAllocation
                    (Allocation.mk a.allocId a.alignLog2 mu
                      (a.bytes.take place.offset ++ bs ++
                        a.bytes.drop (place.offset + bs.length))
                      a.live)
                    m.allocations))) = Except.ok m' →
            mu = .mut ∧
            m' = MemoryState.mk m.nextAllocId
              (replaceAllocation
                (Allocation.mk a.allocId a.alignLog2 mu
                  (a.bytes.take place.offset ++ bs ++
                    a.bytes.drop (place.offset + bs.length))
                  a.live)
                m.allocations))
          a.mutability
          (fun hBad => by nomatch hBad)
          (fun hOk => by
            injection hOk with hM
            exact ⟨rfl, hM.symm⟩)
          hWrite
      have hM' : m' = MemoryState.mk m.nextAllocId
          (replaceAllocation
            (Allocation.mk a.allocId a.alignLog2 .mut
              (a.bytes.take place.offset ++ bs ++
                a.bytes.drop (place.offset + bs.length))
              true)
            m.allocations) := by
        have hTmp := hMutCase.2
        rw [hMutCase.1, hLive] at hTmp
        exact hTmp
      exact ⟨a, rfl, hMutCase.1, hLive, hBounds, hAlign, hM'⟩

private theorem writeBytes_ok_of_valid (m : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bs : List AllocByte) (a : Allocation)
    (hPos : Nat.blt 0 bs.length = true)
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hMut : a.mutability = .mut)
    (hLive : a.live = true)
    (hBounds : isInBounds a place.offset bs.length = true)
    (hAlign : isAligned a place.offset alignLog2 = true) :
    writeBytes m place alignLog2 bs =
      .ok (MemoryState.mk m.nextAllocId
        (replaceAllocation
          (Allocation.mk a.allocId a.alignLog2 .mut
            (a.bytes.take place.offset ++ bs ++
              a.bytes.drop (place.offset + bs.length))
            true)
          m.allocations)) := by
  dsimp only [writeBytes]
  rw [hFind]
  dsimp only
  rw [natBeq_zero_false_of_blt_zero bs.length hPos, ite_bool_false rfl]
  have hGuard :
      (!a.live || !isInBounds a place.offset bs.length ||
        !isAligned a place.offset alignLog2) = false := by
    rw [hLive, hBounds, hAlign]; rfl
  rw [ite_bool_false hGuard, hMut, hLive]

/-- Reading back the exact slice written by `writeBytes` returns `bs`. -/
theorem readBytes_after_writeBytes_same (m m' : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bs : List AllocByte)
    (hPos : Nat.blt 0 bs.length = true)
    (hWrite : writeBytes m place alignLog2 bs = .ok m') :
    readBytes m' place bs.length alignLog2 = .ok bs := by
  cases writeBytes_ok_inversion m m' place alignLog2 bs hPos hWrite with
  | intro a hA =>
    have hFind := hA.1
    have hBounds := hA.2.2.2.1
    have hAlign := hA.2.2.2.2.1
    have hM' := hA.2.2.2.2.2
    have hAllocId := findAllocation_allocId place.allocId m.allocations a hFind
    let bytes' :=
      a.bytes.take place.offset ++ bs ++ a.bytes.drop (place.offset + bs.length)
    let a' := Allocation.mk a.allocId a.alignLog2 .mut bytes' true
    have hLen' : bytes'.length = a.bytes.length :=
      listSplice_length place.offset bs a.bytes hBounds
    have hFind' : findAllocation place.allocId m'.allocations = some a' := by
      rw [hM']; dsimp only; rw [← hAllocId]
      exact findAllocation_replaceAllocation_same m.allocations a a'
        (by rw [hAllocId]; exact hFind) rfl
    dsimp only [readBytes]
    rw [hFind']
    dsimp only
    rw [natBeq_zero_false_of_blt_zero bs.length hPos, ite_bool_false rfl]
    have hLv' : a'.live = true := rfl
    have hInB' : isInBounds a' place.offset bs.length = true := by
      dsimp only [isInBounds, a']; rw [hLen']; exact hBounds
    have hAl' : isAligned a' place.offset alignLog2 = true := hAlign
    have hGuard' :
        (!a'.live || !isInBounds a' place.offset bs.length ||
          !isAligned a' place.offset alignLog2) = false := by
      rw [hLv', hInB', hAl']; rfl
    rw [ite_bool_false hGuard']
    exact congrArg Except.ok
      (listDrop_take_splice_same place.offset bs a.bytes hBounds)

/-- Reading an aligned sub-slice `[subRelOff, subRelOff + subSz)` after
`writeBytes` returns `(bs.drop subRelOff).take subSz`. -/
theorem readBytes_after_writeBytes_subslice (m m' : MemoryState)
    (place : MemPlace) (alignLog2 subRelOff subSz subAlign : Nat)
    (bs : List AllocByte)
    (hPos : Nat.blt 0 bs.length = true)
    (hSubPos : Nat.blt 0 subSz = true)
    (hSubIn : Nat.ble (subRelOff + subSz) bs.length = true)
    (hWrite : writeBytes m place alignLog2 bs = .ok m')
    (hSubAlign : ∀ a, findAllocation place.allocId m.allocations = some a →
      isAligned a (place.offset + subRelOff) subAlign = true) :
    readBytes m' ⟨place.allocId, place.offset + subRelOff⟩ subSz subAlign =
      .ok ((bs.drop subRelOff).take subSz) := by
  cases writeBytes_ok_inversion m m' place alignLog2 bs hPos hWrite with
  | intro a hA =>
    have hFind := hA.1
    have hBounds := hA.2.2.2.1
    have hM' := hA.2.2.2.2.2
    have hAlSub := hSubAlign a hFind
    have hAllocId := findAllocation_allocId place.allocId m.allocations a hFind
    let bytes' :=
      a.bytes.take place.offset ++ bs ++ a.bytes.drop (place.offset + bs.length)
    let a' := Allocation.mk a.allocId a.alignLog2 .mut bytes' true
    have hLen' : bytes'.length = a.bytes.length :=
      listSplice_length place.offset bs a.bytes hBounds
    have hFind' : findAllocation place.allocId m'.allocations = some a' := by
      rw [hM']; dsimp only; rw [← hAllocId]
      exact findAllocation_replaceAllocation_same m.allocations a a'
        (by rw [hAllocId]; exact hFind) rfl
    have hSubBounds :
        Nat.ble ((place.offset + subRelOff) + subSz) a.bytes.length = true := by
      rw [natAdd_assoc place.offset subRelOff subSz]
      exact natBle_trans (place.offset + (subRelOff + subSz))
        (place.offset + bs.length) a.bytes.length
        (natBle_add_mono_left place.offset (subRelOff + subSz) bs.length hSubIn)
        hBounds
    dsimp only [readBytes]
    rw [hFind']
    dsimp only
    rw [natBeq_zero_false_of_blt_zero subSz hSubPos, ite_bool_false rfl]
    have hLv' : a'.live = true := rfl
    have hInB' :
        isInBounds a' (place.offset + subRelOff) subSz = true := by
      dsimp only [isInBounds, a']; rw [hLen']; exact hSubBounds
    have hAl' :
        isAligned a' (place.offset + subRelOff) subAlign = true := hAlSub
    have hGuard' :
        (!a'.live || !isInBounds a' (place.offset + subRelOff) subSz ||
          !isAligned a' (place.offset + subRelOff) subAlign) = false := by
      rw [hLv', hInB', hAl']; rfl
    rw [ite_bool_false hGuard']
    have hOffLe : Nat.ble place.offset a.bytes.length = true :=
      natBle_trans place.offset (place.offset + bs.length) a.bytes.length
        (natBle_add_right place.offset bs.length) hBounds
    have hTakeLen : (a.bytes.take place.offset).length = place.offset :=
      listTake_length_of_ble place.offset a.bytes hOffLe
    have hSlice :
        (bytes'.drop (place.offset + subRelOff)).take subSz =
          (bs.drop subRelOff).take subSz := by
      dsimp only [bytes']
      rw [listAppend_assoc, listDrop_add place.offset subRelOff,
        listDrop_append_of_len place.offset (a.bytes.take place.offset) _
          hTakeLen]
      have hRemSub : Nat.ble subSz (bs.drop subRelOff).length = true := by
        have hSubEq := listDrop_take_length_of_ble subRelOff subSz bs hSubIn
        have hTakeSub := listTake_append_drop subSz (bs.drop subRelOff)
        have hLenEq := congrArg List.length hTakeSub
        rw [listLength_append, hSubEq] at hLenEq
        rw [← hLenEq]
        exact natBle_add_right subSz ((bs.drop subRelOff).drop subSz).length
      have hDropLe :
          ∀ {α : Type} (r : Nat) (u v : List α),
            Nat.ble r u.length = true → (u ++ v).drop r = u.drop r ++ v := by
        intro α r u
        revert r
        induction u with
        | nil =>
          intro r _ hR
          have hZ := natBle_zero_right r hR
          subst hZ
          rfl
        | cons _ uTl ihU =>
          intro r v hR
          cases r with
          | zero => rfl
          | succ r' => exact ihU r' v hR
      have hRelLe : Nat.ble subRelOff bs.length = true :=
        natBle_trans subRelOff (subRelOff + subSz) bs.length
          (natBle_add_right subRelOff subSz) hSubIn
      rw [hDropLe subRelOff bs (a.bytes.drop (place.offset + bs.length)) hRelLe]
      have hTakeLe :
          ∀ {α : Type} (k : Nat) (u v : List α),
            Nat.ble k u.length = true → (u ++ v).take k = u.take k := by
        intro α k
        induction k with
        | zero => intro _ _ _; rfl
        | succ _ ihK =>
          intro u v hK
          cases u with
          | nil => exact False.elim (boolFalseNeTrue hK)
          | cons uHd uTl => exact congrArg (List.cons uHd) (ihK uTl v hK)
      exact hTakeLe subSz (bs.drop subRelOff) _ hRemSub
    exact congrArg Except.ok hSlice

/-- Disjoint-frame law for `readBytes` across `writeBytes`. -/
theorem readBytes_after_writeBytes_disjoint (m m' : MemoryState)
    (writePlace readPlace : MemPlace) (writeAlign readSz readAlign : Nat)
    (bs : List AllocByte)
    (hPos : Nat.blt 0 bs.length = true)
    (hDisj :
      (!Nat.beq writePlace.allocId readPlace.allocId ||
        rangesDisjoint writePlace.offset bs.length
          readPlace.offset readSz) = true)
    (hWrite : writeBytes m writePlace writeAlign bs = .ok m') :
    readBytes m' readPlace readSz readAlign =
      readBytes m readPlace readSz readAlign := by
  dsimp only [readBytes]
  cases writeBytes_ok_inversion m m' writePlace writeAlign bs hPos hWrite with
  | intro a hA =>
    have hFind := hA.1
    have hLive := hA.2.2.1
    have hBounds := hA.2.2.2.1
    have hM' := hA.2.2.2.2.2
    have hAllocId :=
      findAllocation_allocId writePlace.allocId m.allocations a hFind
    let bytes' :=
      a.bytes.take writePlace.offset ++ bs ++
        a.bytes.drop (writePlace.offset + bs.length)
    let a' := Allocation.mk a.allocId a.alignLog2 .mut bytes' true
    cases hIdEq : Nat.beq writePlace.allocId readPlace.allocId with
    | false =>
      have hNe : Nat.beq a'.allocId readPlace.allocId = false := by
        dsimp only [a']; rw [hAllocId]; exact hIdEq
      have hFind2 :
          findAllocation readPlace.allocId m'.allocations =
            findAllocation readPlace.allocId m.allocations := by
        rw [hM']; dsimp only
        exact findAllocation_replaceAllocation_ne readPlace.allocId
          m.allocations a' hNe
      rw [hFind2]
    | true =>
      have hRangeDisj :
          rangesDisjoint writePlace.offset bs.length
            readPlace.offset readSz = true := by
        rw [hIdEq] at hDisj; exact hDisj
      have hId12 := natEq_of_beq writePlace.allocId readPlace.allocId hIdEq
      have hFind' :
          findAllocation readPlace.allocId m'.allocations = some a' := by
        rw [← hId12, hM']; dsimp only; rw [← hAllocId]
        exact findAllocation_replaceAllocation_same m.allocations a a'
          (by rw [hAllocId]; exact hFind) rfl
      have hFindOrig :
          findAllocation readPlace.allocId m.allocations = some a := by
        rw [← hId12]; exact hFind
      rw [hFind', hFindOrig]
      dsimp only
      have hLen' : bytes'.length = a.bytes.length :=
        listSplice_length writePlace.offset bs a.bytes hBounds
      have hLvEq : a'.live = a.live := hLive.symm
      have hInBEq :
          isInBounds a' readPlace.offset readSz =
            isInBounds a readPlace.offset readSz := by
        dsimp only [isInBounds, a']; rw [hLen']
      have hAlEq :
          isAligned a' readPlace.offset readAlign =
            isAligned a readPlace.offset readAlign := rfl
      cases Nat.beq readSz 0 with
      | true =>
        rw [ite_bool_true rfl, ite_bool_true rfl, hAlEq]
      | false =>
        rw [ite_bool_false rfl, ite_bool_false rfl]
        have hGuardEq :
            (!a'.live || !isInBounds a' readPlace.offset readSz ||
              !isAligned a' readPlace.offset readAlign) =
            (!a.live || !isInBounds a readPlace.offset readSz ||
              !isAligned a readPlace.offset readAlign) := by
          rw [hLvEq, hInBEq, hAlEq]
        rw [hGuardEq]
        cases (!a.live || !isInBounds a readPlace.offset readSz ||
            !isAligned a readPlace.offset readAlign) with
        | true => rfl
        | false =>
          exact congrArg Except.ok
            (listDrop_take_splice_disjoint writePlace.offset readPlace.offset
              readSz bs a.bytes hBounds hRangeDisj)

/-! ## 3. Run-Decomposed `ByteRun` Aggregate & `[T; N]` `Repeat` Copy Laws -/

/-- Run-level mixed `InitMask` / provenance byte descriptor:
- `initPlain bs`: initialized scalar bytes (`.init b none`),
- `initProv prov bs`: initialized provenance bytes (`.init b (some prov)`),
- `uninitPad len`: uninitialized padding run (`List.replicate len .uninit`). -/
inductive ByteRun where
  | initPlain (bytes : List UInt8)
  | initProv (prov : AllocId) (bytes : List UInt8)
  | uninitPad (len : Nat)

/-- Expands a single `ByteRun` into `List AllocByte`. -/
@[expose] def ByteRun.toAllocBytes (r : ByteRun) : List AllocByte :=
  match r with
  | .initPlain bs => bs.map (fun b => AllocByte.init b none)
  | .initProv p bs => bs.map (fun b => AllocByte.init b (some p))
  | .uninitPad len => List.replicate len AllocByte.uninit

/-- Byte length of `r`. -/
@[expose] def ByteRun.byteLen (r : ByteRun) : Nat :=
  r.toAllocBytes.length

/-- Flattens a contiguous list of `ByteRun`s into `List AllocByte`. -/
@[expose] def flattenByteRuns (runs : List ByteRun) : List AllocByte :=
  runs.foldr (fun r acc => r.toAllocBytes ++ acc) []

/-- Repeats an aggregate run layout `n` times (`[T; n]`). -/
@[expose] def repeatByteRuns (n : Nat) (runs : List ByteRun) : List ByteRun :=
  repeatSlice n runs

/-- Total byte length of `runs`. -/
abbrev runsByteLen (runs : List ByteRun) : Nat :=
  (flattenByteRuns runs).length

/-- Homomorphism of `flattenByteRuns` over `++`. -/
theorem flattenByteRuns_append (r1 r2 : List ByteRun) :
    flattenByteRuns (r1 ++ r2) = flattenByteRuns r1 ++ flattenByteRuns r2 := by
  induction r1 with
  | nil => rfl
  | cons hd tl ih =>
    change hd.toAllocBytes ++ flattenByteRuns (tl ++ r2) =
      (hd.toAllocBytes ++ flattenByteRuns tl) ++ flattenByteRuns r2
    rw [ih, listAppend_assoc]

/-- Commutation of `flattenByteRuns` with `repeatByteRuns`. -/
theorem flattenByteRuns_repeat (n : Nat) (runs : List ByteRun) :
    flattenByteRuns (repeatByteRuns n runs) =
      repeatSlice n (flattenByteRuns runs) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    change flattenByteRuns (repeatSlice n' runs ++ runs) =
      repeatSlice n' (flattenByteRuns runs) ++ flattenByteRuns runs
    rw [flattenByteRuns_append, ← ih]
    rfl

/-- Exact sub-slice projection of `focus` inside `pre ++ (focus :: post)`. -/
theorem projectRunAtSplit (pre : List ByteRun) (focus : ByteRun)
    (post : List ByteRun) :
    ((flattenByteRuns (pre ++ (focus :: post))).drop
        (flattenByteRuns pre).length).take focus.byteLen =
      focus.toAllocBytes := by
  rw [flattenByteRuns_append]
  change ((flattenByteRuns pre ++
      (focus.toAllocBytes ++ flattenByteRuns post)).drop
    (flattenByteRuns pre).length).take focus.toAllocBytes.length =
      focus.toAllocBytes
  rw [listDrop_append_exact (flattenByteRuns pre),
    listTake_append_exact focus.toAllocBytes (flattenByteRuns post)]

/-- Computable untyped, overlap-tolerant (read-then-write) byte-range copy
`[src, src + sz)` → `[dst, dst + sz)` backed by
`Anneal.MirTotal.{readBytesComp, writeBytesComp}` (`sz = 0` rejected
fail-closed with `.unsupported`). Does not reset typed padding/provenance or
enforce non-overlapping source and destination ranges. -/
@[expose] def copyRangeComp (m : MemoryState) (src dst : MemPlace)
    (sz alignLog2 : Nat) : Except FaultKind MemoryState :=
  if Nat.beq sz 0 then
    .error .unsupported
  else
    match readBytesComp m src sz alignLog2 with
    | .error k => .error k
    | .ok bs => writeBytesComp m dst alignLog2 bs

/-- Computable untyped, overlap-tolerant `N`-element repeat byte copy executing
`n` sequential `copyRangeComp` element writes via `@Nat.rec` (`n = 0` or
`elemSz = 0` rejected fail-closed with `.unsupported`). Does not reset typed
padding/provenance or enforce non-overlap (`copyRepeatedlyComp_sound` requires
source/destination disjointness as an explicit premise). -/
@[expose] def copyRepeatedlyComp (m : MemoryState) (src dst : MemPlace)
    (elemSz alignLog2 n : Nat) : Except FaultKind MemoryState :=
  if Nat.beq n 0 || Nat.beq elemSz 0 then
    .error .unsupported
  else
    @Nat.rec (fun _ => Except FaultKind MemoryState) (.ok m)
      (fun i acc =>
        match acc with
        | .error k => .error k
        | .ok mCur =>
          copyRangeComp mCur src ⟨dst.allocId, dst.offset + i * elemSz⟩
            elemSz alignLog2)
      n

/-- Universal run-decomposed mixed-mask `copyRangeComp` soundness (`[]` zero
axioms): proves `writeBytes` / `readBytes` refinement on non-empty slices,
post-copy `readBytes` run-boundary field/padding projection, and disjoint-slice
framing. -/
theorem copyRangeComp_sound (m m' : MemoryState) (src dst : MemPlace)
    (runs : List ByteRun) (alignLog2 : Nat)
    (hPos : Nat.blt 0 (runsByteLen runs) = true)
    (hReadSrc :
      readBytes m src (runsByteLen runs) alignLog2 = .ok (flattenByteRuns runs))
    (hCopy :
      copyRangeComp m src dst (runsByteLen runs) alignLog2 = .ok m') :
    writeBytes m dst alignLog2 (flattenByteRuns runs) = .ok m' ∧
    readBytes m' dst (runsByteLen runs) alignLog2 =
      .ok (flattenByteRuns runs) ∧
    (∀ (pre post : List ByteRun) (focus : ByteRun) (focusAlign : Nat),
      runs = pre ++ (focus :: post) →
      Nat.blt 0 focus.byteLen = true →
      (∀ a, findAllocation dst.allocId m.allocations = some a →
        isAligned a (dst.offset + (flattenByteRuns pre).length) focusAlign =
          true) →
      readBytes m' ⟨dst.allocId, dst.offset + (flattenByteRuns pre).length⟩
          focus.byteLen focusAlign =
        .ok focus.toAllocBytes) ∧
    (∀ (otherPlace : MemPlace) (otherSz otherAlign : Nat),
      (!Nat.beq dst.allocId otherPlace.allocId ||
        rangesDisjoint dst.offset (runsByteLen runs)
          otherPlace.offset otherSz) = true →
      readBytes m' otherPlace otherSz otherAlign =
        readBytes m otherPlace otherSz otherAlign) := by
  let bs := flattenByteRuns runs
  unfold copyRangeComp at hCopy
  rw [natBeq_zero_false_of_blt_zero (runsByteLen runs) hPos,
    ite_bool_false rfl, readBytesComp_eq, hReadSrc] at hCopy
  dsimp only at hCopy
  rw [writeBytesComp_eq] at hCopy
  refine ⟨hCopy, readBytes_after_writeBytes_same m m' dst alignLog2 bs hPos
      hCopy, ?_, ?_⟩
  · intro pre post focus focusAlign hSplit hFocusPos hFocusAlign
    have hSubIn :
        Nat.ble ((flattenByteRuns pre).length + focus.byteLen) bs.length =
          true := by
      have hLenEq :
          bs.length =
            ((flattenByteRuns pre).length + focus.byteLen) +
              (flattenByteRuns post).length := by
        change (flattenByteRuns runs).length = _
        rw [hSplit, flattenByteRuns_append]
        change (flattenByteRuns pre ++
            (focus.toAllocBytes ++ flattenByteRuns post)).length = _
        rw [listLength_append, listLength_append]
        exact Eq.symm (natAdd_assoc (flattenByteRuns pre).length
          focus.toAllocBytes.length (flattenByteRuns post).length)
      rw [hLenEq]
      exact natBle_add_right ((flattenByteRuns pre).length + focus.byteLen)
        (flattenByteRuns post).length
    have hSub :=
      readBytes_after_writeBytes_subslice m m' dst alignLog2
        (flattenByteRuns pre).length focus.byteLen focusAlign bs hPos hFocusPos
        hSubIn hCopy hFocusAlign
    have hProj :
        (bs.drop (flattenByteRuns pre).length).take focus.byteLen =
          focus.toAllocBytes := by
      change ((flattenByteRuns runs).drop (flattenByteRuns pre).length).take
          focus.byteLen = focus.toAllocBytes
      rw [hSplit]
      exact projectRunAtSplit pre focus post
    rw [hProj] at hSub
    exact hSub
  · intro otherPlace otherSz otherAlign hDisj
    exact readBytes_after_writeBytes_disjoint m m' dst otherPlace alignLog2
      otherSz otherAlign bs hPos hDisj hCopy

private theorem copyRepeatedly_fold_fused (m : MemoryState) (src dst : MemPlace)
    (elemBs : List AllocByte) (elemSz alignLog2 n : Nat) (aDst : Allocation)
    (hElemPos : Nat.blt 0 elemSz = true)
    (hElemLen : elemBs.length = elemSz)
    (hReadSrc : readBytes m src elemSz alignLog2 = .ok elemBs)
    (hFindDst : findAllocation dst.allocId m.allocations = some aDst)
    (hMutDst : aDst.mutability = .mut)
    (hLiveDst : aDst.live = true)
    (hBoundsAll : Nat.ble (dst.offset + n * elemSz) aDst.bytes.length = true)
    (hAlignDst : isAligned aDst dst.offset alignLog2 = true)
    (hStrideMod : Nat.mod elemSz (Nat.pow 2 alignLog2) = 0)
    (hDisjSrcDst :
      (!Nat.beq dst.allocId src.allocId ||
        rangesDisjoint dst.offset (n * elemSz) src.offset elemSz) = true) :
    ∀ (j : Nat), Nat.ble j n = true →
      @Nat.rec (fun _ => Except FaultKind MemoryState)
        (Except.ok m : Except FaultKind MemoryState)
        (fun i acc =>
          match acc with
          | .error k => .error k
          | .ok mCur =>
            copyRangeComp mCur src ⟨dst.allocId, dst.offset + i * elemSz⟩
              elemSz alignLog2)
        j =
      .ok (MemoryState.mk m.nextAllocId
        (replaceAllocation
          (Allocation.mk aDst.allocId aDst.alignLog2 .mut
            (aDst.bytes.take dst.offset ++ repeatSlice j elemBs ++
              aDst.bytes.drop (dst.offset + j * elemSz))
            true)
          m.allocations)) := by
  have hAllocId : aDst.allocId = dst.allocId :=
    findAllocation_allocId dst.allocId m.allocations aDst hFindDst
  intro j
  induction j with
  | zero =>
    intro _
    change Except.ok m = _
    rw [repeatSlice_zero, Nat.zero_mul, Nat.add_zero, listAppend_nil_right,
      listTake_append_drop dst.offset aDst.bytes]
    have hSelf :
        Allocation.mk aDst.allocId aDst.alignLog2 .mut aDst.bytes true =
          aDst := by
      cases aDst with
      | mk id al mu bys lv =>
        dsimp only at hMutDst hLiveDst
        subst hMutDst; subst hLiveDst
        rfl
    rw [hSelf, replaceAllocation_self dst.allocId m.allocations aDst hFindDst]
  | succ j' ih =>
    intro hJ1Le
    have hJLe : Nat.ble j' n = true :=
      natBle_trans j' (j' + 1) n (natBle_succ_right j' j' (natBle_refl j'))
        hJ1Le
    have hPrev := ih hJLe
    let stepFn :
        Nat → Except FaultKind MemoryState → Except FaultKind MemoryState :=
      fun i acc =>
        match acc with
        | .error k => .error k
        | .ok mCur =>
          copyRangeComp mCur src ⟨dst.allocId, dst.offset + i * elemSz⟩
            elemSz alignLog2
    change stepFn j'
      (@Nat.rec (fun _ => Except FaultKind MemoryState) (Except.ok m) stepFn j')
      = _
    rw [hPrev]
    dsimp only [stepFn]
    let bytesJ :=
      aDst.bytes.take dst.offset ++ repeatSlice j' elemBs ++
        aDst.bytes.drop (dst.offset + j' * elemSz)
    let aJ := Allocation.mk aDst.allocId aDst.alignLog2 .mut bytesJ true
    let mJ := MemoryState.mk m.nextAllocId (replaceAllocation aJ m.allocations)
    have hRepJLen : (repeatSlice j' elemBs).length = j' * elemSz := by
      rw [repeatSlice_length, hElemLen]
    have hJMulLe : Nat.ble (j' * elemSz) (n * elemSz) = true :=
      Nat.ble_eq_true_of_le
        (Nat.mul_le_mul_right elemSz (Nat.le_of_ble_eq_true hJLe))
    have hJ1MulLe : Nat.ble ((j' + 1) * elemSz) (n * elemSz) = true :=
      Nat.ble_eq_true_of_le
        (Nat.mul_le_mul_right elemSz (Nat.le_of_ble_eq_true hJ1Le))
    have hBoundsJ :
        Nat.ble (dst.offset + (repeatSlice j' elemBs).length)
          aDst.bytes.length = true := by
      rw [hRepJLen]
      exact natBle_trans (dst.offset + j' * elemSz) (dst.offset + n * elemSz)
        aDst.bytes.length
        (natBle_add_mono_left dst.offset (j' * elemSz) (n * elemSz) hJMulLe)
        hBoundsAll
    have hLenBytesJ : bytesJ.length = aDst.bytes.length := by
      have hTmp :=
        listSplice_length dst.offset (repeatSlice j' elemBs) aDst.bytes
          hBoundsJ
      rw [hRepJLen] at hTmp
      exact hTmp
    have hReadMJ : readBytes mJ src elemSz alignLog2 = .ok elemBs := by
      cases hIdEq : Nat.beq dst.allocId src.allocId with
      | false =>
        have hNe : Nat.beq aJ.allocId src.allocId = false := by
          dsimp only [aJ]; rw [hAllocId]; exact hIdEq
        have hFindSrc :
            findAllocation src.allocId mJ.allocations =
              findAllocation src.allocId m.allocations :=
          findAllocation_replaceAllocation_ne src.allocId m.allocations aJ hNe
        dsimp only [readBytes]
        rw [hFindSrc]
        dsimp only [readBytes] at hReadSrc
        exact hReadSrc
      | true =>
        have hRangeDisjAll :
            rangesDisjoint dst.offset (n * elemSz) src.offset elemSz = true :=
          by
          rw [hIdEq] at hDisjSrcDst; exact hDisjSrcDst
        have hRangeDisjJ :
            (Nat.ble (dst.offset + (repeatSlice j' elemBs).length) src.offset ||
              Nat.ble (src.offset + elemSz) dst.offset) = true := by
          rw [hRepJLen]
          dsimp only [rangesDisjoint] at hRangeDisjAll
          cases hL : Nat.ble (dst.offset + n * elemSz) src.offset with
          | true =>
            have hSubL :
                Nat.ble (dst.offset + j' * elemSz) src.offset = true :=
              natBle_trans (dst.offset + j' * elemSz) (dst.offset + n * elemSz)
                src.offset
                (natBle_add_mono_left dst.offset (j' * elemSz) (n * elemSz)
                  hJMulLe) hL
            rw [hSubL]; rfl
          | false =>
            rw [hL] at hRangeDisjAll
            change Nat.ble (src.offset + elemSz) dst.offset = true
              at hRangeDisjAll
            rw [hRangeDisjAll]
            cases Nat.ble (dst.offset + j' * elemSz) src.offset <;> rfl
        have hId12 := natEq_of_beq dst.allocId src.allocId hIdEq
        have hFindSrcJ : findAllocation src.allocId mJ.allocations = some aJ :=
          by
          rw [← hId12]; dsimp only [mJ]; rw [← hAllocId]
          exact findAllocation_replaceAllocation_same m.allocations aDst aJ
            (by rw [hAllocId]; exact hFindDst) rfl
        have hFindSrc0 :
            findAllocation src.allocId m.allocations = some aDst := by
          rw [← hId12]; exact hFindDst
        dsimp only [readBytes]
        rw [hFindSrcJ]
        dsimp only [readBytes] at hReadSrc
        rw [hFindSrc0] at hReadSrc
        dsimp only
        dsimp only at hReadSrc
        rw [natBeq_zero_false_of_blt_zero elemSz hElemPos, ite_bool_false rfl]
        rw [natBeq_zero_false_of_blt_zero elemSz hElemPos, ite_bool_false rfl] at hReadSrc
        have hLvEq : aJ.live = aDst.live := hLiveDst.symm
        have hInBEq :
            isInBounds aJ src.offset elemSz =
              isInBounds aDst src.offset elemSz := by
          dsimp only [isInBounds, aJ]; rw [hLenBytesJ]
        have hAlEq :
            isAligned aJ src.offset alignLog2 =
              isAligned aDst src.offset alignLog2 := rfl
        have hGuardEq :
            (!aJ.live || !isInBounds aJ src.offset elemSz ||
              !isAligned aJ src.offset alignLog2) =
            (!aDst.live || !isInBounds aDst src.offset elemSz ||
              !isAligned aDst src.offset alignLog2) := by
          rw [hLvEq, hInBEq, hAlEq]
        rw [hGuardEq]
        cases hG :
            (!aDst.live || !isInBounds aDst src.offset elemSz ||
              !isAligned aDst src.offset alignLog2) with
        | true => rw [hG, ite_bool_true rfl] at hReadSrc; nomatch hReadSrc
        | false =>
          rw [hG, ite_bool_false rfl] at hReadSrc
          rw [ite_bool_false rfl]
          have hDisjSlice :=
            listDrop_take_splice_disjoint dst.offset src.offset elemSz
              (repeatSlice j' elemBs) aDst.bytes hBoundsJ hRangeDisjJ
          rw [hRepJLen] at hDisjSlice
          dsimp only [aJ, bytesJ]
          rw [hDisjSlice]
          exact hReadSrc
    dsimp only [copyRangeComp]
    rw [natBeq_zero_false_of_blt_zero elemSz hElemPos, ite_bool_false rfl,
      readBytesComp_eq, hReadMJ]
    dsimp only
    rw [writeBytesComp_eq]
    have hFindDstJ : findAllocation dst.allocId mJ.allocations = some aJ := by
      dsimp only [mJ]; rw [← hAllocId]
      exact findAllocation_replaceAllocation_same m.allocations aDst aJ
        (by rw [hAllocId]; exact hFindDst) rfl
    have hBoundsStep :
        isInBounds aJ (dst.offset + j' * elemSz) elemBs.length = true := by
      dsimp only [isInBounds, aJ]
      rw [hLenBytesJ, hElemLen, natAdd_assoc dst.offset (j' * elemSz) elemSz,
        ← Nat.succ_mul j' elemSz]
      exact natBle_trans (dst.offset + (j' + 1) * elemSz)
        (dst.offset + n * elemSz) aDst.bytes.length
        (natBle_add_mono_left dst.offset ((j' + 1) * elemSz) (n * elemSz)
          hJ1MulLe) hBoundsAll
    have hAlignStep :
        isAligned aJ (dst.offset + j' * elemSz) alignLog2 = true := by
      dsimp only [isAligned] at hAlignDst
      have hAlLe := bandLeft hAlignDst
      have hOffMod := natEq_of_beq _ _ (bandRight hAlignDst)
      dsimp only [isAligned, aJ]
      refine bandIntro hAlLe (natBeq_of_eq _ 0 ?_)
      exact natMod_add_mul_zero_of_pos dst.offset elemSz (Nat.pow 2 alignLog2)
        j' (pow2_pos alignLog2) hOffMod hStrideMod
    have hElemBsPos : Nat.blt 0 elemBs.length = true := by
      rw [hElemLen]; exact hElemPos
    rw [writeBytes_ok_of_valid mJ ⟨dst.allocId, dst.offset + j' * elemSz⟩
      alignLog2 elemBs aJ hElemBsPos hFindDstJ rfl rfl hBoundsStep hAlignStep]
    have hFuse :=
      listSplice_contiguous_fuse dst.offset (repeatSlice j' elemBs) elemBs
        aDst.bytes hBoundsJ
    dsimp only at hFuse
    rw [hRepJLen] at hFuse
    have hLenNext :
        (repeatSlice j' elemBs ++ elemBs).length = (j' + 1) * elemSz := by
      rw [listLength_append, hRepJLen, hElemLen, ← Nat.succ_mul]
    rw [hLenNext] at hFuse
    dsimp only [aJ, mJ, bytesJ]
    rw [hFuse, ← repeatSlice_succ j' elemBs,
      replaceAllocation_replaceAllocation_same m.allocations
        (Allocation.mk aDst.allocId aDst.alignLog2 .mut
          (aDst.bytes.take dst.offset ++ repeatSlice j' elemBs ++
            aDst.bytes.drop (dst.offset + j' * elemSz)) true)
        (Allocation.mk aDst.allocId aDst.alignLog2 .mut
          (aDst.bytes.take dst.offset ++ repeatSlice (j' + 1) elemBs ++
            aDst.bytes.drop (dst.offset + (j' + 1) * elemSz)) true)
        rfl]

/-- Universal `[T; N]` `Repeat` mixed-mask byte-copy fusion (`[]` zero axioms):
`copyRepeatedlyComp` fuses `n ≥ 1` element copies into the single bulk
`repeatByteRuns n runs` allocation write, preserving every element index
`0 ≤ i < n` and framing disjoint slices. -/
theorem copyRepeatedlyComp_sound (m : MemoryState) (src dst : MemPlace)
    (runs : List ByteRun) (alignLog2 n : Nat) (aDst : Allocation)
    (hNPos : Nat.blt 0 n = true)
    (hElemPos : Nat.blt 0 (runsByteLen runs) = true)
    (hReadSrc :
      readBytes m src (runsByteLen runs) alignLog2 = .ok (flattenByteRuns runs))
    (hFindDst : findAllocation dst.allocId m.allocations = some aDst)
    (hMutDst : aDst.mutability = .mut)
    (hLiveDst : aDst.live = true)
    (hBoundsAll :
      isInBounds aDst dst.offset (n * runsByteLen runs) = true)
    (hAlignDst : isAligned aDst dst.offset alignLog2 = true)
    (hStrideMod : Nat.mod (runsByteLen runs) (Nat.pow 2 alignLog2) = 0)
    (hDisj :
      (!Nat.beq dst.allocId src.allocId ||
        rangesDisjoint dst.offset (n * runsByteLen runs)
          src.offset (runsByteLen runs)) = true) :
    ∃ mFinal : MemoryState,
      copyRepeatedlyComp m src dst (runsByteLen runs) alignLog2 n =
        .ok mFinal ∧
      writeBytes m dst alignLog2 (flattenByteRuns (repeatByteRuns n runs)) =
        .ok mFinal ∧
      readBytes mFinal dst (n * runsByteLen runs) alignLog2 =
        .ok (flattenByteRuns (repeatByteRuns n runs)) ∧
      (∀ i : Nat, Nat.blt i n = true →
        readBytes mFinal ⟨dst.allocId, dst.offset + i * runsByteLen runs⟩
          (runsByteLen runs) alignLog2 = .ok (flattenByteRuns runs)) ∧
      (∀ (otherPlace : MemPlace) (otherSz otherAlign : Nat),
        (!Nat.beq dst.allocId otherPlace.allocId ||
          rangesDisjoint dst.offset (n * runsByteLen runs)
            otherPlace.offset otherSz) = true →
        readBytes mFinal otherPlace otherSz otherAlign =
          readBytes m otherPlace otherSz otherAlign) := by
  let elemBs := flattenByteRuns runs
  let elemSz := runsByteLen runs
  let repBs := flattenByteRuns (repeatByteRuns n runs)
  have hRepEq : repBs = repeatSlice n elemBs := flattenByteRuns_repeat n runs
  have hRepLen : repBs.length = n * elemSz := by
    rw [hRepEq, repeatSlice_length]
  have hRepPos : Nat.blt 0 repBs.length = true := by
    rw [hRepLen]
    exact natBlt_pos_mul n elemSz hNPos hElemPos
  let mFinal := MemoryState.mk m.nextAllocId
    (replaceAllocation
      (Allocation.mk aDst.allocId aDst.alignLog2 .mut
        (aDst.bytes.take dst.offset ++ repeatSlice n elemBs ++
          aDst.bytes.drop (dst.offset + n * elemSz))
        true)
      m.allocations)
  have hExec : copyRepeatedlyComp m src dst elemSz alignLog2 n = .ok mFinal :=
    by
    unfold copyRepeatedlyComp
    rw [natBeq_zero_false_of_blt_zero n hNPos,
      natBeq_zero_false_of_blt_zero elemSz hElemPos,
      ite_bool_false (rfl : (false || false) = false)]
    exact copyRepeatedly_fold_fused m src dst elemBs elemSz alignLog2 n aDst
      hElemPos rfl hReadSrc hFindDst hMutDst hLiveDst hBoundsAll hAlignDst
      hStrideMod hDisj n (natBle_refl n)
  have hWriteBulk : writeBytes m dst alignLog2 repBs = .ok mFinal := by
    have hB : isInBounds aDst dst.offset repBs.length = true := by
      dsimp only [isInBounds]; rw [hRepLen]; exact hBoundsAll
    have hW := writeBytes_ok_of_valid m dst alignLog2 repBs aDst hRepPos
      hFindDst hMutDst hLiveDst hB hAlignDst
    have hLenEq : repBs.length = n * elemSz := hRepLen
    rw [hLenEq, hRepEq] at hW
    rw [hRepEq]
    exact hW
  have hReadBulk : readBytes mFinal dst (n * elemSz) alignLog2 = .ok repBs := by
    rw [← hRepLen]
    exact readBytes_after_writeBytes_same m mFinal dst alignLog2 repBs hRepPos
      hWriteBulk
  refine ⟨mFinal, hExec, hWriteBulk, hReadBulk, ?_, ?_⟩
  · intro i hILt
    have hI1Le : Nat.ble (i + 1) n = true :=
      Nat.ble_eq_true_of_le (Nat.le_of_ble_eq_true hILt)
    have hSubIn : Nat.ble (i * elemSz + elemSz) repBs.length = true := by
      rw [hRepLen, ← Nat.succ_mul i elemSz]
      exact Nat.ble_eq_true_of_le
        (Nat.mul_le_mul_right elemSz (Nat.le_of_ble_eq_true hI1Le))
    have hSubAl :
        ∀ a, findAllocation dst.allocId m.allocations = some a →
          isAligned a (dst.offset + i * elemSz) alignLog2 = true := by
      intro a hF
      rw [hFindDst] at hF
      injection hF with hAEq
      subst hAEq
      dsimp only [isAligned] at hAlignDst
      have hAlLe := bandLeft hAlignDst
      have hOffMod := natEq_of_beq _ _ (bandRight hAlignDst)
      dsimp only [isAligned]
      refine bandIntro hAlLe (natBeq_of_eq _ 0 ?_)
      exact natMod_add_mul_zero_of_pos dst.offset elemSz (Nat.pow 2 alignLog2) i
        (pow2_pos alignLog2) hOffMod hStrideMod
    have hSubRead := readBytes_after_writeBytes_subslice m mFinal dst alignLog2
      (i * elemSz) elemSz alignLog2 repBs hRepPos hElemPos hSubIn hWriteBulk
      hSubAl
    rw [hRepEq] at hSubRead
    have hProj := repeatSlice_project_elem n i elemBs hILt
    change readBytes mFinal ⟨dst.allocId, dst.offset + i * elemBs.length⟩
        elemBs.length alignLog2 =
      Except.ok
        (((repeatSlice n elemBs).drop (i * elemBs.length)).take elemBs.length)
      at hSubRead
    rw [hProj] at hSubRead
    exact hSubRead
  · intro otherPlace otherSz otherAlign hOtherDisj
    have hDisjRep :
        (!Nat.beq dst.allocId otherPlace.allocId ||
          rangesDisjoint dst.offset repBs.length
            otherPlace.offset otherSz) = true := by
      rw [hRepLen]; exact hOtherDisj
    exact readBytes_after_writeBytes_disjoint m mFinal dst otherPlace alignLog2
      otherSz otherAlign repBs hRepPos hDisjRep hWriteBulk

end Anneal.ByteRun

end
