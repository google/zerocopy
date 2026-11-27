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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.InitLemmas
public import Anneal.MirTotal.Ops
public import Anneal.ByteSubLens.Lens
public import Anneal.Core.SepPCM
public import Anneal.Core.BitValidity
public import Anneal.Core.FixedByteCodec

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics
open Anneal.InitLemmas Anneal.MirTotal Anneal.ByteSubLens

/-!
# Verified `zerocopy::Ptr` Typestate Algebra (`Core.PtrTypestate`)

Models `zerocopy`'s three-axis pointer typestate invariants (`Aliasing`,
`Alignment`, `Validity`) grounded in `Trusted.MirSemantics.MemoryState`,
`Anneal.ByteSubLens.ByteSubLens`, `Anneal.Core.SepPCM.ByteHeaplet`, and
`Anneal.Core.FixedByteCodec`:

1. **Invariant Partial Order (`AliasingInv`, `AlignInv`, `ValidityInv`,
   `PtrInv`):**
   Computable and propositional subtyping orders (`AliasingLe`, `AlignLe`,
   `ValidityLe`, `PtrInvLe`) with full partial-order laws (reflexivity,
   transitivity, antisymmetry) and strict separation refutations. `AliasingInv`
   models `Shared` and `Exclusive` (matching `zerocopy::invariant::Aliasing`).
   `ValidityLe` captures the partial order (`safe, initialized ≤
   asInitialized ≤ uninit` with `.safe` and `.initialized` incomparable).
   `ValidityHolds` is monotone along `ValidityLe`; weakening a pointer
   (`ptrHolds_weaken`) also carries the mutation obligation below.
2. **Heap-Grounded Judgment (`PtrHolds`, `ptrHeapletPred`, framing):**
   Connects `(sub : ByteSubLens, c : FixedByteCodec α n, inv : PtrInv,
   containsUnsafeCell : Bool)` to `MemoryState` (`findAllocation`, `a.live`,
   `PtrSpanInBounds` (in bounds of an allocation that fits in `isize`),
   `a.mutability`, `isAligned`, and slice validity).
3. **Verified `zerocopy::Ptr` & Cast Transitions:**
   Proves soundness and fail-closed rejections for `into_shared`,
   `reborrow_shared`, `as_ref`, `as_mut`, `forget_aligned`,
   `try_into_aligned`, `assume_alignment`, `read` (`ptrRead`, requiring
   `Copy`), `ptrWrite`, `recall_validity`, `transmute`, and `try_cast_into`.
   Every validity change follows `zerocopy`'s `TryTransmuteFromPtr`
   obligations: every source-valid referent is destination-valid
   (`ValidityIncl`), and when the destination permits mutation every
   destination-valid referent is source-valid (`MutationCompat`), stated as a
   write-back clause (`PtrWriteBack`); casts between types also require both
   endpoints to satisfy `Read<A>` (`castReadCompat`) and, like `transmute`,
   forget alignment. The section explicitly distinguishes padded `padRight`
   codecs (`0 < pad`, which satisfy `.safe` and `.asInitialized` while
   refuting `.initialized` and `IsInitCodec`) from `AllDecodableInit`
   codecs.

Scope notes:
- This is a model over `MemoryState`, `ByteSubLens`, `ByteHeaplet`, and
  `FixedByteCodec` rather than captured MIR bodies of `zerocopy::Ptr<'a, T, I>`.
- Inside `PtrHolds`, `.exclusive` enforces `a.mutability = .mut` (and gates
  `canAsMut` / `ptrWrite`) without an internal global uniqueness token;
  cross-pointer exclusivity is stated explicitly via `DisjointPtrWrites` /
  `MemDisjointFrame` or `ptrHeapletPred`. `PtrHolds` is a duplicable state
  predicate, so the obligations `zerocopy` enforces by typing appear as
  premises of conversion theorems, made load-bearing by write-back clauses.
- `.shared` permits both `.shared` and `.mut` allocations (`ptrRead` uses
  `readBytes`, unlike `&mut`-only `byteSubLensGet`). `containsUnsafeCell` and
  `isCopy` are abstract caller-supplied flags (not queried from `MirTy`),
  unused inside `PtrHolds`'s heap predicate; `containsUnsafeCell` is checked by
  `canAsRef` / `canPtrRead` / `castReadCompat` / `ptrPermitsMutation`, and
  `isCopy` by `ptrRead`. `canAsRef` requiring `containsUnsafeCell = false` is
  conservatively stricter than `zerocopy::Ptr::as_ref` (which admits shared
  `&UnsafeCell` references), and `castReadCompat` conservatively omits
  `zerocopy`'s "sound for shared code to operate on both" transmute
  alternative for distinct types.
- `PtrHolds` and `ptrHeapletPred` require non-zero byte sizes (`0 < n`),
  excluding 0-byte ZST codecs (`unitCodec`, `FixedByteCodec.array 0 c`) even
  though those codecs satisfy `AllDecodableInit`.
- `ptrHeapletPred` asserts exclusive ownership over `ByteHeaplet`
  (`byteHeapletPCM`) rather than a shared fractional permission algebra.
-/

/-! ## 0. Private Constructive Arithmetic and Slice Helpers -/

private theorem pt_false_ne_true (h : false = true) : False := by
  nomatch h

private theorem pt_true_ne_false (h : true = false) : False := by
  nomatch h

private theorem pt_band_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (pt_false_ne_true h)
  | true => rfl

private theorem pt_band_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (pt_false_ne_true h)
  | true => exact h

private theorem pt_band_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]
  rfl

private theorem pt_bor_false_elim {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => exact False.elim (pt_true_ne_false h)
  | false => exact ⟨rfl, h⟩

private theorem pt_bor_left {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]
  rfl

private theorem pt_bor_right {a b : Bool} (h : b = true) : (a || b) = true := by
  cases a <;> rw [h] <;> rfl

private theorem pt_ite_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem pt_ite_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem pt_ite_false_true {α : Type} (t e : α) :
    (if false = true then t else e) = e := rfl

private theorem pt_nat_beq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => pt_nat_beq_refl n

private theorem pt_nat_beq_symm : ∀ a b : Nat, Nat.beq a b = Nat.beq b a
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | a + 1, b + 1 => pt_nat_beq_symm a b

private theorem pt_nat_eq_of_beq : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => False.elim (pt_false_ne_true h)
  | _ + 1, 0, h => False.elim (pt_false_ne_true h)
  | _ + 1, _ + 1, h => congrArg Nat.succ (pt_nat_eq_of_beq h)

private theorem pt_nat_beq_of_eq {a b : Nat} (h : a = b) :
    Nat.beq a b = true := by
  subst h
  exact pt_nat_beq_refl a

private theorem pt_nat_ble_zero (n : Nat) : Nat.ble 0 n = true := by
  cases n <;> rfl

private theorem pt_nat_ble_zero_false_of_pos {n : Nat} (hPos : 0 < n) :
    Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hPos)
  | succ _ => rfl

private theorem pt_nat_ble_one_of_pos {n : Nat} (hPos : 0 < n) :
    Nat.ble 1 n = true := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hPos)
  | succ k => cases k <;> rfl

private theorem pt_nat_ble_trans :
    ∀ a b c : Nat, Nat.ble a b = true → Nat.ble b c = true →
      Nat.ble a c = true
  | 0, _, c, _, _ => pt_nat_ble_zero c
  | _ + 1, 0, _, hab, _ => False.elim (pt_false_ne_true hab)
  | _ + 1, _ + 1, 0, _, hbc => False.elim (pt_false_ne_true hbc)
  | a + 1, b + 1, c + 1, hab, hbc => pt_nat_ble_trans a b c hab hbc

private theorem pt_nat_mod_one (n : Nat) : Nat.mod n 1 = 0 :=
  Nat.mod_one n

private theorem pt_nat_pow_add (b m : Nat) :
    ∀ n : Nat, Nat.pow b (m + n) = Nat.pow b m * Nat.pow b n
  | 0 => by
    rw [Nat.add_zero]
    change Nat.pow b m = Nat.pow b m * 1
    rw [Nat.mul_one]
  | n + 1 => by
    change Nat.pow b (m + n) * b = Nat.pow b m * (Nat.pow b n * b)
    rw [pt_nat_pow_add b m n, Nat.mul_assoc]

private theorem pt_isAligned_zero (a : Allocation) (offset : Nat) :
    isAligned a offset 0 = true := by
  unfold isAligned
  rw [pt_nat_ble_zero a.alignLog2]
  change (true && Nat.beq (Nat.mod offset 1) 0) = true
  rw [pt_nat_mod_one offset]
  rfl

private theorem pt_mod_pow_le {src dst off : Nat} (hLe : dst ≤ src)
    (hMod : Nat.mod off (Nat.pow 2 src) = 0) :
    Nat.mod off (Nat.pow 2 dst) = 0 := by
  have hDecomp : src = dst + (src - dst) := (Nat.add_sub_of_le hLe).symm
  have hDivMod :
      Nat.pow 2 src * Nat.div off (Nat.pow 2 src) +
        Nat.mod off (Nat.pow 2 src) = off :=
    Nat.div_add_mod off (Nat.pow 2 src)
  rw [hMod, Nat.add_zero] at hDivMod
  have hPow : Nat.pow 2 src = Nat.pow 2 dst * Nat.pow 2 (src - dst) :=
    Eq.trans (congrArg (Nat.pow 2) hDecomp) (pt_nat_pow_add 2 dst (src - dst))
  have hEq :
      off = Nat.pow 2 dst *
        (Nat.pow 2 (src - dst) * Nat.div off (Nat.pow 2 src)) :=
    Eq.trans hDivMod.symm
      (Eq.trans
        (congrArg (fun x => x * Nat.div off (Nat.pow 2 src)) hPow)
        (Nat.mul_assoc (Nat.pow 2 dst) (Nat.pow 2 (src - dst))
          (Nat.div off (Nat.pow 2 src))))
  rw [hEq]
  exact Nat.mul_mod_right (Nat.pow 2 dst) _

private theorem pt_isAligned_mono {a : Allocation} {offset src dst : Nat}
    (hLe : dst ≤ src) (hAl : isAligned a offset src = true) :
    isAligned a offset dst = true := by
  unfold isAligned at hAl
  have hLogSrc : Nat.ble src a.alignLog2 = true := pt_band_left hAl
  have hModSrc : Nat.beq (Nat.mod offset (Nat.pow 2 src)) 0 = true :=
    pt_band_right hAl
  have hLogDst : Nat.ble dst a.alignLog2 = true :=
    Nat.ble_eq.mpr (Nat.le_trans hLe (Nat.ble_eq.mp hLogSrc))
  have hModDst : Nat.beq (Nat.mod offset (Nat.pow 2 dst)) 0 = true :=
    pt_nat_beq_of_eq (pt_mod_pow_le hLe (pt_nat_eq_of_beq hModSrc))
  unfold isAligned
  exact pt_band_intro hLogDst hModDst

private theorem pt_list_take_append_left {α : Type} :
    ∀ xs ys : List α, (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => congrArg (List.cons x) (pt_list_take_append_left xs ys)

private theorem pt_list_drop_append_left {α : Type} :
    ∀ xs ys : List α, (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => pt_list_drop_append_left xs ys

private theorem pt_list_take_length_of_le {α : Type} :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length → (xs.take n).length = n
  | 0, _, _ => rfl
  | n + 1, [], h => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, _ :: rest, h =>
    congrArg Nat.succ (pt_list_take_length_of_le n rest (Nat.le_of_succ_le_succ h))

private theorem pt_list_drop_length {α : Type} :
    ∀ (n : Nat) (xs : List α), (xs.drop n).length = xs.length - n
  | 0, xs => by rw [List.drop_zero, Nat.sub_zero]
  | _ + 1, [] => by rw [List.drop_nil, List.length_nil, Nat.zero_sub]
  | n + 1, _ :: rest => by
    change (rest.drop n).length = (rest.length + 1) - (n + 1)
    rw [pt_list_drop_length n rest, Nat.succ_sub_succ]

private theorem pt_list_drop_take_length_of_ble {α : Type} (off sz : Nat)
    (xs : List α) (h : Nat.ble (off + sz) xs.length = true) :
    ((xs.drop off).take sz).length = sz := by
  have hLe : off + sz ≤ xs.length := Nat.ble_eq.mp h
  apply pt_list_take_length_of_le
  rw [pt_list_drop_length]
  exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hLe)

private theorem pt_list_take_drop_add {α : Type} :
    ∀ (off sz : Nat) (xs : List α),
      xs.take off ++ (xs.drop off).take sz = xs.take (off + sz)
  | 0, _, _ => by
    rw [Nat.zero_add, List.take_zero, List.drop_zero, List.nil_append]
  | _ + 1, _, [] => by
    rw [List.drop_nil, List.take_nil, List.take_nil, List.nil_append,
        List.take_nil]
  | off + 1, sz, x :: xs => by
    rw [Nat.add_right_comm off 1 sz, List.take_succ_cons, List.take_succ_cons,
        List.drop_succ_cons, List.cons_append, pt_list_take_drop_add off sz xs]

private theorem pt_list_take_append_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), xs.take n ++ xs.drop n = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => congrArg (List.cons x) (pt_list_take_append_drop n xs)

private theorem pt_splice_length {α : Type} (off : Nat) (bs xs : List α)
    (hB : Nat.ble (off + bs.length) xs.length = true) :
    (xs.take off ++ bs ++ xs.drop (off + bs.length)).length = xs.length := by
  have hLe : off + bs.length ≤ xs.length := Nat.ble_eq.mp hB
  have hOffLe : off ≤ xs.length := Nat.le_trans (Nat.le_add_right off _) hLe
  rw [List.length_append, List.length_append,
      pt_list_take_length_of_le off xs hOffLe, pt_list_drop_length]
  exact Nat.add_sub_of_le hLe

private theorem pt_drop_take_splice_same (off n : Nat)
    (bs xs : List AllocByte) (hLen : bs.length = n)
    (hB : Nat.ble (off + bs.length) xs.length = true) :
    ((xs.take off ++ bs ++ xs.drop (off + bs.length)).drop off).take n =
      bs := by
  have hOffLe : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off _) (Nat.ble_eq.mp hB)
  have hTakeLen : (xs.take off).length = off :=
    pt_list_take_length_of_le off xs hOffLe
  have hDrop :
      (xs.take off ++ (bs ++ xs.drop (off + bs.length))).drop
        (xs.take off).length =
      bs ++ xs.drop (off + bs.length) :=
    pt_list_drop_append_left (xs.take off) (bs ++ xs.drop (off + bs.length))
  rw [hTakeLen] at hDrop
  rw [List.append_assoc, hDrop, ← hLen]
  exact pt_list_take_append_left bs _

private theorem pt_take_of_le_take_append {α : Type} (off sz : Nat)
    (xs ys : List α) (hLe : off + sz ≤ xs.length) :
    ((xs ++ ys).drop off).take sz = (xs.drop off).take sz := by
  revert off sz ys
  induction xs with
  | nil =>
    intro off sz ys hLe
    have hZ : off + sz = 0 := Nat.eq_zero_of_le_zero hLe
    have hSzZ : sz = 0 := Nat.eq_zero_of_le_zero (by rw [← hZ]; exact Nat.le_add_left _ _)
    subst hSzZ
    rfl
  | cons x rest ih =>
    intro off sz ys hLe
    cases off with
    | zero =>
      cases sz with
      | zero => rfl
      | succ sz' =>
        change x :: ((rest ++ ys).take sz') = x :: (rest.take sz')
        have h' : 0 + sz' ≤ rest.length := by
          rw [Nat.zero_add] at hLe
          rw [Nat.zero_add]
          exact Nat.le_of_succ_le_succ hLe
        have hSub := ih 0 sz' ys h'
        rw [List.drop_zero, List.drop_zero] at hSub
        exact congrArg (List.cons x) hSub
    | succ off' =>
      have h' : off' + sz ≤ rest.length := by
        rw [Nat.succ_add] at hLe
        exact Nat.le_of_succ_le_succ hLe
      exact ih off' sz ys h'

private theorem pt_drop_take_append_right {α : Type} (off sz : Nat)
    (pre suf : List α) (hLen : pre.length ≤ off) :
    ((pre ++ suf).drop off).take sz = (suf.drop (off - pre.length)).take sz := by
  revert off
  induction pre with
  | nil =>
    intro off _
    rw [List.nil_append, List.length_nil, Nat.sub_zero]
  | cons _ rest ih =>
    intro off hLen
    cases off with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hLen)
    | succ off' =>
      have hSub : off' + 1 - (rest.length + 1) = off' - rest.length :=
        Nat.succ_sub_succ off' rest.length
      rw [List.cons_append, List.drop_succ_cons, List.length_cons, hSub]
      exact ih off' (Nat.le_of_succ_le_succ hLen)

private theorem pt_drop_take_drop_shift {α : Type} (m off sz : Nat)
    (xs : List α) (hLe : m ≤ off) :
    ((xs.drop m).drop (off - m)).take sz = (xs.drop off).take sz := by
  revert off
  induction m generalizing xs with
  | zero =>
    intro off _
    rw [List.drop_zero, Nat.sub_zero]
  | succ m' ih =>
    intro off hLe
    cases xs with
    | nil =>
      rw [List.drop_nil, List.drop_nil, List.drop_nil]
    | cons _ rest =>
      cases off with
      | zero => exact False.elim (Nat.not_succ_le_zero _ hLe)
      | succ off' =>
        have hSub : off' + 1 - (m' + 1) = off' - m' :=
          Nat.succ_sub_succ off' m'
        rw [List.drop_succ_cons, hSub]
        exact ih rest off' (Nat.le_of_succ_le_succ hLe)

private theorem pt_drop_take_splice_disjoint (off1 off2 sz2 : Nat)
    (bs1 xs : List AllocByte)
    (hB1 : Nat.ble (off1 + bs1.length) xs.length = true)
    (hDisj : (Nat.ble (off1 + bs1.length) off2 ||
      Nat.ble (off2 + sz2) off1) = true) :
    (((xs.take off1 ++ bs1 ++ xs.drop (off1 + bs1.length)).drop off2).take sz2) =
      (xs.drop off2).take sz2 := by
  have hLe1 : off1 + bs1.length ≤ xs.length := Nat.ble_eq.mp hB1
  have hOff1Le : off1 ≤ xs.length := Nat.le_trans (Nat.le_add_right off1 _) hLe1
  revert hDisj
  cases hLeft : Nat.ble (off1 + bs1.length) off2 with
  | true =>
    intro hDisj; have hLeOff2 : off1 + bs1.length ≤ off2 := Nat.ble_eq.mp hLeft
    have hPreLen : (xs.take off1 ++ bs1).length = off1 + bs1.length := by
      rw [List.length_append, pt_list_take_length_of_le off1 xs hOff1Le]
    rw [pt_drop_take_append_right off2 sz2 (xs.take off1 ++ bs1)
          (xs.drop (off1 + bs1.length)) (by rw [hPreLen]; exact hLeOff2),
        hPreLen]
    exact pt_drop_take_drop_shift (off1 + bs1.length) off2 sz2 xs hLeOff2
  | false =>
    intro hDisj
    have hRight : Nat.ble (off2 + sz2) off1 = true := hDisj
    have hLeRight : off2 + sz2 ≤ off1 := Nat.ble_eq.mp hRight
    have hTakeLen : (xs.take off1).length = off1 :=
      pt_list_take_length_of_le off1 xs hOff1Le
    rw [List.append_assoc,
        pt_take_of_le_take_append off2 sz2 (xs.take off1)
          (bs1 ++ xs.drop (off1 + bs1.length))
          (by rw [hTakeLen]; exact hLeRight)]
    have hSplit :
        ((xs.take off1 ++ xs.drop off1).drop off2).take sz2 =
          ((xs.take off1).drop off2).take sz2 :=
      pt_take_of_le_take_append off2 sz2 (xs.take off1)
        (xs.drop off1) (by rw [hTakeLen]; exact hLeRight)
    rw [pt_list_take_append_drop off1 xs] at hSplit
    exact hSplit.symm

/-! ## 1. Pointer Invariant Partial Order (`AliasingInv`, `AlignInv`,
`ValidityInv`, `PtrInv`) -/

/-- Two-tier aliasing capability axis mirroring `zerocopy::invariant::Aliasing`
(`Exclusive` vs `Shared`). -/
inductive AliasingInv : Type where
  | exclusive : AliasingInv
  | shared : AliasingInv

/-- Alignment invariant axis ordered from `.aligned` to `.unaligned`. -/
inductive AlignInv : Type where
  | aligned : AlignInv
  | unaligned : AlignInv

/-- Byte-slice validity axis (`safe`, `initialized`, `asInitialized`,
`uninit`). -/
inductive ValidityInv : Type where
  | safe : ValidityInv
  | initialized : ValidityInv
  | asInitialized : ValidityInv
  | uninit : ValidityInv

/-- Combined three-axis `zerocopy::Ptr` invariant descriptor. -/
structure PtrInv : Type where
  aliasing : AliasingInv
  align : AlignInv
  validity : ValidityInv

/-- Computable subtyping order on `AliasingInv` (`exclusive ≤ shared`). -/
@[expose] def aliasingLeBool : AliasingInv → AliasingInv → Bool
  | .exclusive, _ => true
  | .shared, .shared => true
  | .shared, .exclusive => false

/-- Propositional subtyping order on `AliasingInv`. -/
@[expose] def AliasingLe (a b : AliasingInv) : Prop :=
  aliasingLeBool a b = true

theorem AliasingLe.refl (a : AliasingInv) : AliasingLe a a := by
  cases a <;> rfl

theorem AliasingLe.trans {a b c : AliasingInv}
    (hab : AliasingLe a b) (hbc : AliasingLe b c) : AliasingLe a c := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact False.elim (pt_false_ne_true hab) |
      exact False.elim (pt_false_ne_true hbc)

theorem AliasingLe.antisymm {a b : AliasingInv}
    (hab : AliasingLe a b) (hba : AliasingLe b a) : a = b := by
  cases a <;> cases b <;>
    first | rfl | exact False.elim (pt_false_ne_true hab) |
      exact False.elim (pt_false_ne_true hba)

theorem aliasingLe_shared_exclusive_false : ¬ AliasingLe .shared .exclusive :=
  fun h => pt_false_ne_true h

/-- Computable subtyping order on `AlignInv` (`aligned ≤ unaligned`). -/
@[expose] def alignLeBool : AlignInv → AlignInv → Bool
  | .aligned, _ => true
  | .unaligned, .unaligned => true
  | .unaligned, .aligned => false

/-- Propositional subtyping order on `AlignInv`. -/
@[expose] def AlignLe (a b : AlignInv) : Prop :=
  alignLeBool a b = true

theorem AlignLe.refl (a : AlignInv) : AlignLe a a := by
  cases a <;> rfl

theorem AlignLe.trans {a b c : AlignInv}
    (hab : AlignLe a b) (hbc : AlignLe b c) : AlignLe a c := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact False.elim (pt_false_ne_true hab) |
      exact False.elim (pt_false_ne_true hbc)

theorem AlignLe.antisymm {a b : AlignInv}
    (hab : AlignLe a b) (hba : AlignLe b a) : a = b := by
  cases a <;> cases b <;>
    first | rfl | exact False.elim (pt_false_ne_true hab) |
      exact False.elim (pt_false_ne_true hba)

theorem alignLe_unaligned_aligned_false : ¬ AlignLe .unaligned .aligned :=
  fun h => pt_false_ne_true h

/-- Computable partial order on `ValidityInv` (`safe ≤ asInitialized ≤
uninit` and `initialized ≤ asInitialized ≤ uninit`, with `.safe` and
`.initialized` incomparable). Codec-specific transitions between `.safe` and
`.initialized` use `ptrRecallValidity_safe_to_initialized` (`AllDecodableInit`)
and `ptrRecallValidity_initialized_to_safe` (`IsSurjectiveInitDecoder`). -/
@[expose] def validityLeBool : ValidityInv → ValidityInv → Bool
  | .safe, .safe => true
  | .safe, .asInitialized => true
  | .safe, .uninit => true
  | .safe, .initialized => false
  | .initialized, .initialized => true
  | .initialized, .asInitialized => true
  | .initialized, .uninit => true
  | .initialized, .safe => false
  | .asInitialized, .asInitialized => true
  | .asInitialized, .uninit => true
  | .asInitialized, _ => false
  | .uninit, .uninit => true
  | .uninit, _ => false

/-- Propositional order on `ValidityInv`. -/
@[expose] def ValidityLe (a b : ValidityInv) : Prop :=
  validityLeBool a b = true

theorem ValidityLe.refl (a : ValidityInv) : ValidityLe a a := by
  cases a <;> rfl

theorem ValidityLe.trans {a b c : ValidityInv}
    (hab : ValidityLe a b) (hbc : ValidityLe b c) : ValidityLe a c := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact False.elim (pt_false_ne_true hab) |
      exact False.elim (pt_false_ne_true hbc)

theorem ValidityLe.antisymm {a b : ValidityInv}
    (hab : ValidityLe a b) (hba : ValidityLe b a) : a = b := by
  cases a <;> cases b <;>
    first | rfl | exact False.elim (pt_false_ne_true hab) |
      exact False.elim (pt_false_ne_true hba)

theorem validityLe_safe_initialized_false :
    ¬ ValidityLe .safe .initialized :=
  fun h => pt_false_ne_true h

theorem validityLe_initialized_safe_false :
    ¬ ValidityLe .initialized .safe :=
  fun h => pt_false_ne_true h

theorem validityLe_asInitialized_initialized_false :
    ¬ ValidityLe .asInitialized .initialized :=
  fun h => pt_false_ne_true h

theorem validityLe_asInitialized_safe_false :
    ¬ ValidityLe .asInitialized .safe :=
  fun h => pt_false_ne_true h

theorem validityLe_uninit_asInitialized_false :
    ¬ ValidityLe .uninit .asInitialized :=
  fun h => pt_false_ne_true h

/-- Product partial order on `PtrInv`. -/
@[expose] def PtrInvLe (p q : PtrInv) : Prop :=
  AliasingLe p.aliasing q.aliasing ∧
    AlignLe p.align q.align ∧
    ValidityLe p.validity q.validity

theorem PtrInvLe.refl (p : PtrInv) : PtrInvLe p p :=
  ⟨AliasingLe.refl p.aliasing, AlignLe.refl p.align,
   ValidityLe.refl p.validity⟩

theorem PtrInvLe.trans {p q r : PtrInv}
    (hpq : PtrInvLe p q) (hqr : PtrInvLe q r) : PtrInvLe p r :=
  ⟨AliasingLe.trans hpq.1 hqr.1,
   AlignLe.trans hpq.2.1 hqr.2.1,
   ValidityLe.trans hpq.2.2 hqr.2.2⟩

theorem PtrInvLe.antisymm {p q : PtrInv}
    (hpq : PtrInvLe p q) (hqp : PtrInvLe q p) : p = q := by
  cases p with
  | mk pa pl pv =>
    cases q with
    | mk qa ql qv =>
      have ha : pa = qa := AliasingLe.antisymm hpq.1 hqp.1
      have hl : pl = ql := AlignLe.antisymm hpq.2.1 hqp.2.1
      have hv : pv = qv := ValidityLe.antisymm hpq.2.2 hqp.2.2
      subst ha
      subst hl
      subst hv
      rfl

/-! ## 2. Slice Validity, Codec Initialization, and `PtrHolds` -/

/-- Byte position `i` of an `n`-byte slice whose first `i` bytes are `pre` must
be initialized under `zerocopy`'s `AsInitialized` relative to codec `c`. This is
the codec analog of `Core.BitValidity.InitRequiredAt`, with buffers that `c`
decodes as the valid instances: either every decodable `n`-byte buffer is
initialized at `i` (first clause), or some decodable `n`-byte buffer starts
with `pre` and every such buffer is initialized at `i` (second clause). -/
@[expose] def CodecRequiresInitAt {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre : List AllocByte) (i : Nat) : Prop :=
  (∀ (bs : List AllocByte) (x : α),
      bs.length = n → c.decode bs = some x → ByteInitAt bs i) ∨
    ((∃ (bs : List AllocByte) (x : α),
        bs.length = n ∧ bs.take i = pre ∧ c.decode bs = some x) ∧
      ∀ (bs : List AllocByte) (x : α),
        bs.length = n → bs.take i = pre → c.decode bs = some x →
        ByteInitAt bs i)

/-- `bs` is at least as initialized as codec `c` requires (`zerocopy`'s
`AsInitialized`, both clauses): `bs.length = n` and every byte position
`i < n` that `CodecRequiresInitAt c (bs.take i) i` requires is `.init` in `bs`.
-/
@[expose] def AsInitFor {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (bs : List AllocByte) : Prop :=
  bs.length = n ∧
    ∀ i : Nat, i < n → CodecRequiresInitAt c (bs.take i) i → ByteInitAt bs i

/-- Every buffer accepted by `c.decode` consists solely of initialized bytes
(`AllBytesInit`). Holds for all unpadded `IntoBytes` codecs and fails whenever
`0 < pad` under `padRight`/`padLeft`. -/
@[expose] def AllDecodableInit {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ ⦃bs : List AllocByte⦄ ⦃x : α⦄, c.decode bs = some x → AllBytesInit bs

theorem allDecodableInit_implies_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hDec : AllDecodableInit c) :
    c.IsInitCodec :=
  fun x => hDec (c.decode_encode x)

/-- Semantic validity invariant for slice `bs` relative to `c : FixedByteCodec α
n`. Every level enforces exact slice length `n`. -/
@[expose] def ValidityHolds {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (v : ValidityInv) (bs : List AllocByte) : Prop :=
  bs.length = n ∧
    match v with
    | .uninit => True
    | .asInitialized => AsInitFor c bs
    | .initialized => AllBytesInit bs
    | .safe => ∃ x : α, c.decode bs = some x

theorem validityHolds_to_uninit {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (v : ValidityInv) (bs : List AllocByte)
    (h : ValidityHolds c v bs) : ValidityHolds c .uninit bs :=
  ⟨h.1, trivial⟩

theorem validityHolds_safe_to_asInitialized {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (bs : List AllocByte)
    (h : ValidityHolds c .safe bs) : ValidityHolds c .asInitialized bs := by
  let ⟨x, hDec⟩ := h.2
  refine ⟨h.1, ⟨h.1, fun i _ hReq => ?_⟩⟩
  cases hReq with
  | inl hAll => exact hAll bs x h.1 hDec
  | inr hS => exact hS.2 bs x h.1 rfl hDec

theorem validityHolds_initialized_to_asInitialized {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (bs : List AllocByte)
    (h : ValidityHolds c .initialized bs) : ValidityHolds c .asInitialized bs :=
  ⟨h.1, ⟨h.1, fun i hi _ =>
    byteInitAt_of_allBytesInit i bs (by rw [h.1]; exact hi) h.2⟩⟩

theorem validityHolds_safe_to_initialized_of_allDecodableInit {α : Type}
    {n : Nat} {c : FixedByteCodec α n} (hDecInit : AllDecodableInit c)
    (bs : List AllocByte) (h : ValidityHolds c .safe bs) :
    ValidityHolds c .initialized bs := by
  let ⟨_, hDec⟩ := h.2
  exact ⟨h.1, hDecInit hDec⟩

theorem validityHolds_initialized_to_safe_of_surjective {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hSurj : c.IsSurjectiveInitDecoder)
    (bs : List AllocByte) (h : ValidityHolds c .initialized bs) :
    ValidityHolds c .safe bs :=
  ⟨h.1, hSurj bs h.1 h.2⟩

/-- Unconditional monotonicity of `ValidityHolds` under the `ValidityLe`
partial order (`safe, initialized ≤ asInitialized ≤ uninit`). -/
theorem validityHolds_weaken {α : Type} {n : Nat}
    (c : FixedByteCodec α n) {v1 v2 : ValidityInv} {bs : List AllocByte}
    (hLe : ValidityLe v1 v2)
    (hV : ValidityHolds c v1 bs) : ValidityHolds c v2 bs := by
  cases v1 with
  | safe =>
    cases v2 with
    | safe => exact hV
    | initialized => exact False.elim (pt_false_ne_true hLe)
    | asInitialized => exact validityHolds_safe_to_asInitialized c bs hV
    | uninit => exact validityHolds_to_uninit c .safe bs hV
  | initialized =>
    cases v2 with
    | safe => exact False.elim (pt_false_ne_true hLe)
    | initialized => exact hV
    | asInitialized => exact validityHolds_initialized_to_asInitialized c bs hV
    | uninit => exact validityHolds_to_uninit c .initialized bs hV
  | asInitialized =>
    cases v2 with
    | safe | initialized => exact False.elim (pt_false_ne_true hLe)
    | asInitialized => exact hV
    | uninit => exact validityHolds_to_uninit c .asInitialized bs hV
  | uninit =>
    cases v2 with
    | safe | initialized | asInitialized => exact False.elim (pt_false_ne_true hLe)
    | uninit => exact hV

theorem unitCodec_allDecodableInit : AllDecodableInit unitCodec := by
  intro bs _ hDec
  cases bs with
  | nil => rfl
  | cons _ _ => nomatch hDec

theorem boolCodec_allDecodableInit : AllDecodableInit boolCodec := by
  intro bs _ hDec
  cases bs with
  | nil => nomatch hDec
  | cons b0 rest =>
    cases b0 with
    | uninit => nomatch hDec
    | init _ _ =>
      cases rest with
      | nil => rfl
      | cons _ _ => nomatch hDec

private theorem pt_allBytesInit_of_rawBytes?_some (bs : List AllocByte) :
    ∀ {raw : List UInt8}, rawBytes? bs = some raw → AllBytesInit bs := by
  induction bs with
  | nil =>
    intro _ _
    rfl
  | cons ab rest ih =>
    intro raw h
    cases ab with
    | uninit => nomatch h
    | init b _ =>
      change (match rawBytes? rest with
        | some tl => some (b :: tl)
        | none => none) = some raw at h
      revert h
      cases hRest : rawBytes? rest with
      | none =>
        intro h
        nomatch h
      | some _rawRest => intro h; exact ih hRest

theorem uintBvCodec_allDecodableInit (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : AllDecodableInit (uintBvCodec endian sz hPos) := by
  intro bs _ hDec
  unfold uintBvCodec FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length sz with
  | false =>
    rw [pt_ite_false hLen] at hDec
    nomatch hDec
  | true =>
    rw [pt_ite_true hLen] at hDec
    revert hDec
    cases hRaw : rawBytes? bs with
    | none =>
      intro hDec
      nomatch hDec
    | some _raw =>
      intro hDec; exact pt_allBytesInit_of_rawBytes?_some bs hRaw

theorem prod_allDecodableInit {α β : Type} {m n : Nat}
    {c1 : FixedByteCodec α m} {c2 : FixedByteCodec β n}
    (h1 : AllDecodableInit c1) (h2 : AllDecodableInit c2) :
    AllDecodableInit (FixedByteCodec.prod c1 c2) := by
  intro bs _ hDec
  unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length (m + n) with
  | false =>
    rw [pt_ite_false hLen] at hDec
    nomatch hDec
  | true =>
    rw [pt_ite_true hLen] at hDec
    revert hDec
    cases hD1 : c1.decode (bs.take m) with
    | none =>
      intro hDec
      nomatch hDec
    | some a =>
      intro hDec
      revert hDec
      cases hD2 : c2.decode (bs.drop m) with
      | none =>
        intro hDec
        nomatch hDec
      | some b =>
        intro hDec; rw [← pt_list_take_append_drop m bs]
        exact AllBytesInit_append (h1 hD1) (h2 hD2)

theorem array_allDecodableInit {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hc : AllDecodableInit c) :
    ∀ k : Nat, AllDecodableInit (FixedByteCodec.array k c)
  | 0 => by
    intro bs _ hDec
    cases bs with
    | nil => rfl
    | cons _ _ => nomatch hDec
  | k + 1 => by
    intro bs _ hDec
    change FixedByteCodec.decodeChunks c (k + 1) bs = some _ at hDec
    rw [FixedByteCodec.decodeChunks_succ] at hDec
    cases hBle : Nat.ble n bs.length with
    | false =>
      rw [pt_ite_false hBle] at hDec
      nomatch hDec
    | true =>
      rw [pt_ite_true hBle] at hDec
      revert hDec
      cases hD1 : c.decode (bs.take n) with
      | none =>
        intro hDec
        nomatch hDec
      | some x =>
        intro hDec
        revert hDec
        cases hD2 : FixedByteCodec.decodeChunks c k (bs.drop n) with
        | none =>
          intro hDec
          nomatch hDec
        | some xs =>
          intro hDec; rw [← pt_list_take_append_drop n bs]
          exact AllBytesInit_append (hc hD1) (array_allDecodableInit hc k hD2)

theorem padRight_not_allDecodableInit {α : Type} {n pad : Nat}
    (hPos : 0 < pad) (c0 : FixedByteCodec α n) (x0 : α) :
    ¬ AllDecodableInit (FixedByteCodec.padRight c0 pad) := by
  intro hDecInit
  have hFalse :
      allBytesInit ((FixedByteCodec.padRight c0 pad).encode x0) = false :=
    FixedByteCodec.allBytesInit_padRight_encode_eq_false c0 hPos x0
  have hTrue :
      AllBytesInit ((FixedByteCodec.padRight c0 pad).encode x0) :=
    hDecInit ((FixedByteCodec.padRight c0 pad).decode_encode x0)
  rw [hTrue] at hFalse
  exact pt_true_ne_false hFalse

theorem padRight_not_isInitCodec {α : Type} {n pad : Nat}
    (hPos : 0 < pad) (c0 : FixedByteCodec α n) (x0 : α) :
    ¬ (FixedByteCodec.padRight c0 pad).IsInitCodec := by
  intro hInit
  have hFalse :
      allBytesInit ((FixedByteCodec.padRight c0 pad).encode x0) = false :=
    FixedByteCodec.allBytesInit_padRight_encode_eq_false c0 hPos x0
  have hTrue : AllBytesInit ((FixedByteCodec.padRight c0 pad).encode x0) :=
    hInit x0
  rw [hTrue] at hFalse
  exact pt_true_ne_false hFalse

/-- Effective alignment exponent enforced against `MemoryState` (`sub.alignLog2`
when `.aligned`, `0` when `.unaligned`). -/
@[expose] def ptrEffectiveAlignLog2 (sub : ByteSubLens) (inv : PtrInv) : Nat :=
  match inv.align with
  | .aligned => sub.alignLog2
  | .unaligned => 0

/-- `zerocopy::Ptr`'s byte-range invariant (`zerocopy/src/pointer/ptr.rs`):

> "- It must derive from a valid allocation.
> - It must reference a byte range which is contained inside the
>   allocation from which it derives.
>   - As a consequence, the byte range it references must have a size
>     which does not overflow `isize`."

The `n` bytes at `off` lie inside `a` (`isInBounds`), and `a` itself fits in
`isize` (`a.bytes.length < isizeMaxBytes`, the per-allocation bound that
`Trusted.MirSemantics.allocIdsValid` enforces on caller memory). -/
@[expose] def PtrSpanInBounds (a : Allocation) (off n : Nat) : Prop :=
  isInBounds a off n = true ∧ a.bytes.length < isizeMaxBytes

/-- `PtrSpanInBounds` depends on `a` only through `a.bytes.length`, so it
survives in-place byte updates. -/
theorem ptrSpanInBounds_of_length_eq {a a' : Allocation} {off n : Nat}
    (hLen : a'.bytes.length = a.bytes.length)
    (h : PtrSpanInBounds a off n) : PtrSpanInBounds a' off n := by
  refine ⟨?_, ?_⟩
  · unfold isInBounds
    rw [hLen]
    exact h.1
  · rw [hLen]
    exact h.2

/-- Every in-bounds span ends strictly below `isize::MAX + 1`. -/
theorem ptrSpanInBounds_end_lt_isize {a : Allocation} {off n : Nat}
    (h : PtrSpanInBounds a off n) : off + n < isizeMaxBytes :=
  Nat.lt_of_le_of_lt (Nat.ble_eq.mp h.1) h.2

/-- Heap-grounded `zerocopy::Ptr` invariant judgment over non-ZST (`0 < n`)
slices of `Trusted.MirSemantics.MemoryState`.

Notes:
- Restricted to non-zero byte counts (`0 < n`), excluding 0-byte codecs such
  as `unitCodec` and `FixedByteCodec.array 0 c`.
- The referenced span lies inside a live allocation that fits in `isize`
  (`PtrSpanInBounds`), so every span is shorter than `isizeMaxBytes`.
- `.exclusive` requires `a.mutability = .mut` (and permits `ptrWrite` /
  `canAsMut`), whereas `.shared` permits either `.shared` or `.mut` allocations
  (`ptrRead` uses `readBytes`, unlike `&mut`-only `byteSubLensGet`).
  Cross-pointer exclusivity is stated explicitly via `DisjointPtrWrites` /
  `MemDisjointFrame`, not embedded inside `PtrHolds`.
- `containsUnsafeCell` is an abstract caller-supplied model flag unused here and
  checked at read and cast boundaries (`canPtrRead`, `canAsRef`,
  `castReadCompat`). -/
@[expose] def PtrHolds {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (containsUnsafeCell : Bool)
    (mem : MemoryState) : Prop :=
  let _ := containsUnsafeCell
  0 < n ∧
  sub.size = n ∧
  ∃ a : Allocation,
    findAllocation sub.allocId mem.allocations = some a ∧
    a.live = true ∧
    PtrSpanInBounds a sub.offset n ∧
    (inv.aliasing = .exclusive → a.mutability = .mut) ∧
    (inv.align = .aligned → isAligned a sub.offset sub.alignLog2 = true) ∧
    ValidityHolds c inv.validity ((a.bytes.drop sub.offset).take n)

/-- Inductively lifts a contiguous byte slice `bs` starting at
`(allocId, offset)` into a `SepProp ByteHeaplet`. -/
@[expose] def bytesHeapletPred (allocId offset : Nat) (bs : List AllocByte) :
    SepProp ByteHeaplet :=
  (@List.rec AllocByte (fun _ => Nat → SepProp ByteHeaplet)
    (fun _ => sepEmp byteHeapletPCM)
    (fun b _ ih off =>
      sepConj byteHeapletPCM
        (bytePointsTo ⟨allocId, off⟩ b)
        (ih (off + 1)))
    bs) offset

/-- Separation-logic assertion on `ByteHeaplet` expressing exclusive ownership
and validity of the non-ZST (`0 < n`) region focused by `sub` (without
distinguishing shared fractional permissions or alignment). -/
@[expose] def ptrHeapletPred {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) : SepProp ByteHeaplet :=
  fun h =>
    0 < n ∧
    sub.size = n ∧
    ∃ bs : List AllocByte,
      ValidityHolds c inv.validity bs ∧
      bytesHeapletPred sub.allocId sub.offset bs h

private theorem pt_framePreserving_trans {M : Type} {pcm : ExplPCM M}
    {P Q R : SepProp M}
    (hpq : FramePreserving pcm P Q) (hqr : FramePreserving pcm Q R) :
    FramePreserving pcm P R := by
  intro h1 hf hComb hP hop1
  let ⟨h2, hComb2, hop2, hQ⟩ := hpq h1 hf hComb hP hop1
  exact hqr h2 hf hComb2 hQ hop2

private theorem pt_framePreserving_conj {M : Type} {pcm : ExplPCM M}
    {P1 Q1 P2 Q2 : SepProp M}
    (h1 : FramePreserving pcm P1 Q1) (h2 : FramePreserving pcm P2 Q2) :
    FramePreserving pcm (sepConj pcm P1 P2) (sepConj pcm Q1 Q2) := by
  have step1 := FramePreserving.frame P2 h1
  have step2 : FramePreserving pcm (sepConj pcm Q1 P2) (sepConj pcm Q1 Q2) := by
    intro hm hf hComb hQP hop
    have hPQ : sepConj pcm P2 Q1 hm := (sepConj_comm pcm Q1 P2 hm).mp hQP
    let ⟨hm', hComb', hop', hQ2Q1⟩ := FramePreserving.frame Q1 h2 hm hf hComb hPQ hop
    exact ⟨hm', hComb', hop', (sepConj_comm pcm Q2 Q1 hm').mp hQ2Q1⟩
  exact pt_framePreserving_trans step1 step2

theorem bytesHeapletPred_framePreserving_update (aid : AllocId) :
    ∀ (off : Nat) (bs1 bs2 : List AllocByte),
      bs1.length = bs2.length →
      FramePreserving byteHeapletPCM
        (bytesHeapletPred aid off bs1)
        (bytesHeapletPred aid off bs2)
  | _, [], [], _ => fun h1 _ hComb hp hop => ⟨h1, hComb, hop, hp⟩
  | _, [], _ :: _, hLen => by nomatch hLen
  | _, _ :: _, [], hLen => by nomatch hLen
  | off, b1 :: rest1, b2 :: rest2, hLen =>
    pt_framePreserving_conj
      (bytePointsTo_framePreserving_update ⟨aid, off⟩ b1 b2)
      (bytesHeapletPred_framePreserving_update aid (off + 1) rest1 rest2
        (Nat.succ.inj hLen))

theorem bytesHeapletPred_append (aid : AllocId) :
    ∀ (off : Nat) (bs1 bs2 : List AllocByte),
      SepEquiv (bytesHeapletPred aid off (bs1 ++ bs2))
        (sepConj byteHeapletPCM
          (bytesHeapletPred aid off bs1)
          (bytesHeapletPred aid (off + bs1.length) bs2))
  | off, [], bs2 => by
    intro h
    have hEmp := sepConj_emp_left byteHeapletPCM (bytesHeapletPred aid off bs2) h
    have hZ : off + ([] : List AllocByte).length = off := Nat.add_zero off
    rw [List.nil_append, hZ]
    exact hEmp.symm
  | off, b1 :: rest1, bs2 => by
    intro h
    have ih := bytesHeapletPred_append aid (off + 1) rest1 bs2
    have hCong :
        SepEquiv
          (sepConj byteHeapletPCM (bytePointsTo ⟨aid, off⟩ b1)
            (bytesHeapletPred aid (off + 1) (rest1 ++ bs2)))
          (sepConj byteHeapletPCM (bytePointsTo ⟨aid, off⟩ b1)
            (sepConj byteHeapletPCM (bytesHeapletPred aid (off + 1) rest1)
              (bytesHeapletPred aid ((off + 1) + rest1.length) bs2))) := by
      intro h'
      constructor
      · exact sepConj_mono byteHeapletPCM (SepEntails.refl _)
          (fun m hm => (ih m).mp hm) h'
      · exact sepConj_mono byteHeapletPCM (SepEntails.refl _)
          (fun m hm => (ih m).mpr hm) h'
    have hAssoc := sepConj_assoc byteHeapletPCM
      (bytePointsTo ⟨aid, off⟩ b1)
      (bytesHeapletPred aid (off + 1) rest1)
      (bytesHeapletPred aid (off + (rest1.length + 1)) bs2) h
    have hShift : (off + 1) + rest1.length = off + (rest1.length + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 rest1.length]
    change (bytesHeapletPred aid off ((b1 :: rest1) ++ bs2)) h ↔ _
    rw [List.cons_append]
    change sepConj byteHeapletPCM (bytePointsTo ⟨aid, off⟩ b1)
      (bytesHeapletPred aid (off + 1) (rest1 ++ bs2)) h ↔ _
    have hStep1 := hCong h
    rw [hShift] at hStep1
    exact hStep1.trans hAssoc.symm

theorem ptrHeapletPred_weaken {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv1 inv2 : PtrInv)
    (hValLe : ValidityLe inv1.validity inv2.validity) :
    SepEntails (ptrHeapletPred sub c inv1) (ptrHeapletPred sub c inv2) := by
  intro h ⟨hPos, hSize, bs, hV, hBytes⟩
  exact ⟨hPos, hSize, bs, validityHolds_weaken c hValLe hV, hBytes⟩

theorem ptrHeapletPred_write_framePreserving {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv) (x : α) :
    FramePreserving byteHeapletPCM
      (ptrHeapletPred sub c inv)
      (ptrHeapletPred sub c { inv with validity := .safe }) := by
  intro h1 hf hComb ⟨hPos, hSize, bs, hV, hBytes⟩ hop
  have hLen : bs.length = (c.encode x).length := by
    rw [hV.1, c.encode_length x]
  let ⟨h1', hComb', hop', hBytes'⟩ :=
    bytesHeapletPred_framePreserving_update sub.allocId sub.offset bs
      (c.encode x) hLen h1 hf hComb hBytes hop
  have hSafe : ValidityHolds c ValidityInv.safe (c.encode x) :=
    ⟨c.encode_length x, ⟨x, c.decode_encode x⟩⟩
  exact ⟨h1', hComb', hop', ⟨hPos, hSize, c.encode x, hSafe, hBytes'⟩⟩

theorem ptrHeapletPred_write_framed {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv) (x : α)
    (F : SepProp ByteHeaplet) :
    FramePreserving byteHeapletPCM
      (sepConj byteHeapletPCM (ptrHeapletPred sub c inv) F)
      (sepConj byteHeapletPCM
        (ptrHeapletPred sub c { inv with validity := .safe }) F) :=
  FramePreserving.frame F (ptrHeapletPred_write_framePreserving sub c inv x)

/-! ### 2a. Memory Framing Under `writeBytes` and `byteLensDisjoint` -/

/-- Pointer-region disjointness over `Anneal.ByteSubLens.byteLensDisjoint`. -/
@[expose] def DisjointPtrWrites (l1 l2 : ByteSubLens) : Prop :=
  byteLensDisjoint l1 l2 = true

private theorem pt_isInBoundsComp_eq (a : Allocation) (off sz : Nat) :
    isInBoundsComp a off sz = isInBounds a off sz := rfl

private theorem pt_isAlignedComp_eq (a : Allocation) (off al : Nat) :
    isAlignedComp a off al = isAligned a off al := rfl

private theorem pt_readBytesComp_ok {m : MemoryState}
    {id : AllocId} {off sz al : Nat} {a : Allocation} (hPos : 0 < sz)
    (hFind : findAllocation id m.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a off sz = true)
    (hAlign : isAligned a off al = true) :
    readBytesComp m ⟨id, off⟩ sz al = .ok ((a.bytes.drop off).take sz) := by
  have hFindComp : findAllocationComp id m.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  have hG : (!a.live || !isInBoundsComp a off sz || !isAlignedComp a off al) =
      false := by
    rw [hLive, pt_isInBoundsComp_eq, hBounds, pt_isAlignedComp_eq, hAlign]
    rfl
  unfold readBytesComp
  rw [pt_nat_ble_zero_false_of_pos hPos, hFindComp]
  dsimp only [pt_ite_false_true]
  rw [hG]
  rfl

private theorem pt_writeBytesComp_ok {m : MemoryState}
    {id : AllocId} {off al : Nat} {bs : List AllocByte} {a : Allocation}
    (hPos : 0 < bs.length)
    (hFind : findAllocation id m.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a off bs.length = true)
    (hAlign : isAligned a off al = true)
    (hMut : a.mutability = .mut) :
    writeBytesComp m ⟨id, off⟩ al bs =
      .ok { m with
        allocations := replaceAllocationComp
          { allocId := a.allocId, alignLog2 := a.alignLog2, mutability := .mut,
            bytes := a.bytes.take off ++ bs ++ a.bytes.drop (off + bs.length),
            live := a.live }
          m.allocations } := by
  have hFindComp : findAllocationComp id m.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  have hG : (!a.live || !isInBoundsComp a off bs.length ||
      !isAlignedComp a off al) = false := by
    rw [hLive, pt_isInBoundsComp_eq, hBounds, pt_isAlignedComp_eq, hAlign]
    rfl
  unfold writeBytesComp
  rw [pt_nat_ble_zero_false_of_pos hPos, hFindComp]
  dsimp only [pt_ite_false_true]
  rw [hG, pt_ite_false rfl, hMut]

private theorem pt_mutability_eq_shared_of_not_isMut {m : Mutability}
    (h : mutabilityIsMut m = false) : m = .shared := by
  cases m <;> first | rfl | exact False.elim (pt_true_ne_false h)

private theorem pt_mutability_eq_mut_of_isMut {m : Mutability}
    (h : mutabilityIsMut m = true) : m = .mut := by
  cases m <;> first | rfl | exact False.elim (pt_false_ne_true h)

theorem ptrHolds_frame_writeBytes {α : Type} {n : Nat}
    (subWrite subOther : ByteSubLens) (alignW : Nat) (bsWrite : List AllocByte)
    (hNz : 0 < bsWrite.length) (hSzW : bsWrite.length = subWrite.size)
    (hDisj : DisjointPtrWrites subWrite subOther)
    {c : FixedByteCodec α n} {inv : PtrInv} {uc : Bool}
    {mem1 mem2 : MemoryState}
    (hWrite : writeBytes mem1 ⟨subWrite.allocId, subWrite.offset⟩ alignW
      bsWrite = .ok mem2)
    (hOther : PtrHolds subOther c inv uc mem1) :
    PtrHolds subOther c inv uc mem2 := by
  rw [← writeBytesComp_eq] at hWrite
  unfold writeBytesComp at hWrite
  rw [pt_nat_ble_zero_false_of_pos hNz] at hWrite
  dsimp only [pt_ite_false_true] at hWrite
  revert hWrite
  cases hFindW : findAllocationComp subWrite.allocId mem1.allocations with
  | none =>
    intro hWrite
    nomatch hWrite
  | some aW =>
    intro hWrite
    dsimp only at hWrite
    cases hGuard : (!aW.live ||
        !isInBoundsComp aW subWrite.offset bsWrite.length ||
        !isAlignedComp aW subWrite.offset alignW) with
    | true =>
      rw [pt_ite_true hGuard] at hWrite
      nomatch hWrite
    | false =>
      rw [pt_ite_false hGuard] at hWrite
      cases hMutB : mutabilityIsMut aW.mutability with
      | false =>
        have hSh : aW.mutability = .shared :=
          pt_mutability_eq_shared_of_not_isMut hMutB
        rw [hSh] at hWrite
        nomatch hWrite
      | true =>
        have hMutW : aW.mutability = .mut :=
          pt_mutability_eq_mut_of_isMut hMutB
        rw [hMutW] at hWrite
        dsimp only at hWrite
        injection hWrite with hMem2
        subst hMem2
        have hG1 := pt_bor_false_elim hGuard
        have hG2 := pt_bor_false_elim hG1.1
        have hBoundsW :
            Nat.ble (subWrite.offset + bsWrite.length) aW.bytes.length = true := by
          revert hG2
          cases hb : isInBoundsComp aW subWrite.offset bsWrite.length with
          | true => intro hG2; exact hb
          | false => intro hG2; exact False.elim (pt_true_ne_false hG2.2)
        have hAllocIdW : aW.allocId = subWrite.allocId :=
          findAllocationComp_allocId subWrite.allocId mem1.allocations aW hFindW
        let bytesW :=
          aW.bytes.take subWrite.offset ++ bsWrite ++
            aW.bytes.drop (subWrite.offset + bsWrite.length)
        let aWNew : Allocation :=
          { allocId := aW.allocId, alignLog2 := aW.alignLog2, mutability := .mut,
            bytes := bytesW, live := aW.live }
        have hAWNewId : aWNew.allocId = subWrite.allocId := hAllocIdW
        let ⟨hPosO, hSizeO, aO, hFindO, hLiveO, hBoundsO, hMutO, hAlignO, hValO⟩ :=
          hOther
        have hFindOComp :
            findAllocationComp subOther.allocId mem1.allocations = some aO := by
          rw [findAllocationComp_eq]
          exact hFindO
        dsimp only [DisjointPtrWrites, byteLensDisjoint] at hDisj
        cases hIdEq : Nat.beq subWrite.allocId subOther.allocId with
        | false =>
          have hNe : Nat.beq aWNew.allocId subOther.allocId = false := by
            rw [hAWNewId]
            exact hIdEq
          have hFindAfter :
              findAllocation subOther.allocId
                (replaceAllocationComp aWNew mem1.allocations) = some aO := by
            rw [← findAllocationComp_eq,
                findAllocationComp_replace_ne subOther.allocId mem1.allocations
                  aWNew hNe,
                hFindOComp]
          exact ⟨hPosO, hSizeO, aO, hFindAfter, hLiveO, hBoundsO, hMutO,
            hAlignO, hValO⟩
        | true =>
          have hIdSame : subWrite.allocId = subOther.allocId :=
            pt_nat_eq_of_beq hIdEq
          rw [hIdEq] at hDisj
          have hDisjRange :
              rangesDisjoint subWrite.offset subWrite.size
                subOther.offset subOther.size = true := hDisj
          have hFindWSame :
              findAllocationComp subOther.allocId mem1.allocations = some aW := by
            rw [← hIdSame]
            exact hFindW
          rw [hFindWSame] at hFindOComp
          injection hFindOComp with hAOEq
          subst hAOEq
          have hFindAfter :
              findAllocation subOther.allocId
                (replaceAllocationComp aWNew mem1.allocations) = some aWNew := by
            rw [← findAllocationComp_eq, ← hIdSame, ← hAllocIdW]
            exact findAllocationComp_replace_same mem1.allocations aW aWNew
              (by rw [hAllocIdW]; exact hFindW) rfl
          have hLenNew : aWNew.bytes.length = aW.bytes.length :=
            pt_splice_length subWrite.offset bsWrite aW.bytes hBoundsW
          have hBoundsNew : PtrSpanInBounds aWNew subOther.offset n :=
            ptrSpanInBounds_of_length_eq hLenNew hBoundsO
          have hDisjBs :
              (Nat.ble (subWrite.offset + bsWrite.length) subOther.offset ||
                Nat.ble (subOther.offset + n) subWrite.offset) = true := by
            rw [hSzW]
            rw [hSizeO] at hDisjRange
            exact hDisjRange
          have hSliceEq :
              (aWNew.bytes.drop subOther.offset).take n =
                (aW.bytes.drop subOther.offset).take n :=
            pt_drop_take_splice_disjoint subWrite.offset subOther.offset n
              bsWrite aW.bytes hBoundsW hDisjBs
          refine ⟨hPosO, hSizeO, aWNew, hFindAfter, hLiveO, hBoundsNew, ?_, ?_, ?_⟩
          · intro _
            rfl
          · intro hAl
            exact hAlignO hAl
          · rw [hSliceEq]
            exact hValO

private theorem pt_mir_getElem?_cons_zero {α : Type} (x : α) (xs : List α) :
    Trusted.MirSemantics.getElem? (x :: xs) 0 = some x := rfl

private theorem pt_mir_getElem?_cons_succ {α : Type} (x : α) (xs : List α)
    (n : Nat) :
    Trusted.MirSemantics.getElem? (x :: xs) (n + 1) =
      Trusted.MirSemantics.getElem? xs n := rfl

private theorem pt_take_eq_of_mir_getElem?_eq {α : Type} :
    ∀ (sz : Nat) (xs ys : List α),
      sz ≤ xs.length → sz ≤ ys.length →
      (∀ i : Nat, i < sz →
        Trusted.MirSemantics.getElem? xs i =
          Trusted.MirSemantics.getElem? ys i) →
      xs.take sz = ys.take sz
  | 0, _, _, _, _, _ => rfl
  | _ + 1, [], _, hX, _, _ => False.elim (Nat.not_succ_le_zero _ hX)
  | _ + 1, _, [], _, hY, _ => False.elim (Nat.not_succ_le_zero _ hY)
  | sz + 1, x :: xr, y :: yr, hX, hY, hPt => by
    have h0 : Trusted.MirSemantics.getElem? (x :: xr) 0 =
        Trusted.MirSemantics.getElem? (y :: yr) 0 :=
      hPt 0 (Nat.zero_lt_succ sz)
    rw [pt_mir_getElem?_cons_zero, pt_mir_getElem?_cons_zero] at h0
    injection h0 with hHead
    subst hHead
    have hTail : xr.take sz = yr.take sz :=
      pt_take_eq_of_mir_getElem?_eq sz xr yr
        (Nat.le_of_succ_le_succ hX) (Nat.le_of_succ_le_succ hY)
        (fun i hi => by
          have hi1 := hPt (i + 1) (Nat.succ_lt_succ hi)
          rw [pt_mir_getElem?_cons_succ, pt_mir_getElem?_cons_succ] at hi1
          exact hi1)
    exact congrArg (List.cons x) hTail

private theorem pt_drop_take_eq_of_mir_getElem?_eq {α : Type} :
    ∀ (off sz : Nat) (xs ys : List α),
      off + sz ≤ xs.length → off + sz ≤ ys.length →
      (∀ i : Nat, i < sz →
        Trusted.MirSemantics.getElem? xs (off + i) =
          Trusted.MirSemantics.getElem? ys (off + i)) →
      (xs.drop off).take sz = (ys.drop off).take sz
  | 0, sz, xs, ys, hX, hY, hPt => by
    rw [List.drop_zero, List.drop_zero]
    rw [Nat.zero_add] at hX
    rw [Nat.zero_add] at hY
    exact pt_take_eq_of_mir_getElem?_eq sz xs ys hX hY (fun i hi => by
      have hi0 := hPt i hi
      rw [Nat.zero_add] at hi0
      exact hi0)
  | _ + 1, _, [], _, hX, _, _ => by
    rw [Nat.succ_add] at hX
    exact False.elim (Nat.not_succ_le_zero _ hX)
  | _ + 1, _, _, [], _, hY, _ => by
    rw [Nat.succ_add] at hY
    exact False.elim (Nat.not_succ_le_zero _ hY)
  | off + 1, sz, _ :: xr, _ :: yr, hX, hY, hPt => by
    rw [List.drop_succ_cons, List.drop_succ_cons]
    have hX' : off + sz ≤ xr.length := by
      rw [Nat.succ_add] at hX
      exact Nat.le_of_succ_le_succ hX
    have hY' : off + sz ≤ yr.length := by
      rw [Nat.succ_add] at hY
      exact Nat.le_of_succ_le_succ hY
    exact pt_drop_take_eq_of_mir_getElem?_eq off sz xr yr hX' hY' (fun i hi => by
      have hi1 := hPt i hi
      rw [Nat.succ_add, pt_mir_getElem?_cons_succ,
          pt_mir_getElem?_cons_succ] at hi1
      exact hi1)

/-- Any `MemDisjointFrame W m1 m2` memory transition preserves `PtrHolds` for
every live pointer `sub` whose `allocId < m1.nextAllocId` and whose byte span
`[sub.offset, sub.offset + n)` lies completely outside footprint `W`. -/
theorem ptrHolds_of_memDisjointFrame {α : Type} {n : Nat}
    (W : ByteFootprint) (sub : ByteSubLens) (c : FixedByteCodec α n)
    (inv : PtrInv) (uc : Bool) (m1 m2 : MemoryState)
    (hLt : sub.allocId < m1.nextAllocId)
    (hFrame : MemDisjointFrame W m1 m2)
    (hOut : ∀ i : Nat, i < n →
      ByteFootprint.contains W ⟨sub.allocId, sub.offset + i⟩ = false)
    (hHolds : PtrHolds sub c inv uc m1) :
    PtrHolds sub c inv uc m2 := by
  let ⟨hPos, hSz, a1, hFind1, hLive1, hBounds1, hMut1, hAlign1, hVal1⟩ :=
    hHolds
  let ⟨_, hAlloc⟩ := hFrame
  have hSpec := hAlloc sub.allocId hLt
  rw [hFind1] at hSpec
  revert hSpec
  cases hFind2 : findAllocation sub.allocId m2.allocations with
  | none =>
    intro hSpec
    exact False.elim hSpec
  | some a2 =>
    intro hSpec
    dsimp only at hSpec
    let ⟨_, hAlEq, hMutEq, hLiveEq, hLenEq, hByteEq⟩ := hSpec
    have hLive2 : a2.live = true := by rw [hLiveEq]; exact hLive1
    have hBounds2 : PtrSpanInBounds a2 sub.offset n :=
      ptrSpanInBounds_of_length_eq hLenEq hBounds1
    have hMut2 : inv.aliasing = .exclusive → a2.mutability = .mut := by
      intro hEx
      rw [hMutEq]
      exact hMut1 hEx
    have hAlign2 :
        inv.align = .aligned → isAligned a2 sub.offset sub.alignLog2 = true := by
      intro hAl
      unfold isAligned
      rw [hAlEq]
      exact hAlign1 hAl
    have hLe1 : sub.offset + n ≤ a1.bytes.length := Nat.ble_eq.mp hBounds1.1
    have hLe2 : sub.offset + n ≤ a2.bytes.length := by
      rw [hLenEq]
      exact hLe1
    have hSliceEq :
        (a2.bytes.drop sub.offset).take n =
          (a1.bytes.drop sub.offset).take n :=
      pt_drop_take_eq_of_mir_getElem?_eq sub.offset n a2.bytes a1.bytes
        hLe2 hLe1 (fun i hi => hByteEq (sub.offset + i) (hOut i hi))
    refine ⟨hPos, hSz, a2, hFind2, hLive2, hBounds2, hMut2, hAlign2, ?_⟩
    rw [hSliceEq]
    exact hVal1

/-! ## 3. Verified `zerocopy::Ptr` and Cast Typestate Transitions -/

/-! ### 3a. Aliasing Transitions (`into_shared`, `reborrow_shared`, `as_ref`,
`as_mut`) -/

/-- Weakens any `AliasingInv` pointer (`.exclusive` or `.shared`) to
`.shared`, preserving physical bytes, alignment, and validity in `mem`. -/
theorem ptrHolds_intoShared {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem) :
    PtrHolds sub c { inv with aliasing := .shared } uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, _, hAlign, hVal⟩ := hHolds
  exact ⟨hPos, hSz, a, hFind, hLive, hBounds,
    (fun hEx => by nomatch hEx), hAlign, hVal⟩

/-- Reborrows any pointer as a `.shared` view of the same allocation and byte
slice without modifying `mem`. -/
theorem ptrHolds_reborrowShared {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem) :
    PtrHolds sub c { inv with aliasing := .shared } uc mem :=
  ptrHolds_intoShared sub c inv uc mem hHolds

/-- Shared-reference (`&T`) read guard: requires `.aligned`, `.safe`, and
`containsUnsafeCell = false`. Note: this is conservatively stricter than
`zerocopy::Ptr::as_ref` (which accepts `.shared`/`.exclusive` `Reference`
pointers even when `T` contains `UnsafeCell`). -/
@[expose] def canAsRef (inv : PtrInv) (containsUnsafeCell : Bool) : Bool :=
  (match inv.align with
   | .aligned => true
   | .unaligned => false) &&
  (match inv.validity with
   | .safe => true
   | _ => false) &&
  !containsUnsafeCell

/-- Mutable-reference (`&mut T`) guard: requires `.exclusive` aliasing,
`.aligned`, and `.safe`. -/
@[expose] def canAsMut (inv : PtrInv) : Bool :=
  (match inv.aliasing with
   | .exclusive => true
   | _ => false) &&
  (match inv.align with
   | .aligned => true
   | .unaligned => false) &&
  (match inv.validity with
   | .safe => true
   | _ => false)

/-- Capable of reading through this pointer (`exclusive` always; `shared` iff
`containsUnsafeCell = false`). -/
@[expose] def canPtrRead (aliasing : AliasingInv) (containsUnsafeCell : Bool) : Bool :=
  match aliasing with
  | .exclusive => true
  | .shared => !containsUnsafeCell

/-- Shared read / `&T` projection via `Trusted.MirSemantics.readBytesComp`.
Works on both `.shared` and `.mut` allocations in `MemoryState`. Models
`as_ref`: the result is the value denoted by the borrowed referent (an `&T`),
not an owned copy moved out of it, so unlike `ptrRead` it needs no `Copy`
flag. -/
@[expose] def ptrAsRefRead {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool)
    (mem : MemoryState) : Option α :=
  if canAsRef inv uc && Nat.ble 1 n && Nat.beq sub.size n then
    match readBytesComp mem ⟨sub.allocId, sub.offset⟩ n sub.alignLog2 with
    | .ok bs => c.decode bs
    | .error _ => none
  else
    none

theorem ptrAsRefRead_sound {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hCan : canAsRef inv uc = true) (hHolds : PtrHolds sub c inv uc mem) :
    ∃ x : α,
      ptrAsRefRead sub c inv uc mem = some x ∧
      PtrHolds sub c { inv with aliasing := .shared } uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hVal⟩ := hHolds
  have hCan12 := pt_band_left hCan
  have hCanAl := pt_band_left hCan12
  have hCanVal := pt_band_right hCan12
  have hCanAlEq : inv.align = .aligned := by
    revert hCanAl
    cases hA : inv.align with
    | aligned => intro hCanAl; rfl
    | unaligned => intro hCanAl; exact False.elim (pt_false_ne_true hCanAl)
  have hCanValEq : inv.validity = .safe := by
    revert hCanVal
    cases hV : inv.validity with
    | safe => intro hCanVal; rfl
    | initialized | asInitialized | uninit =>
      intro hCanVal
      exact False.elim (pt_false_ne_true hCanVal)
  rw [hCanValEq] at hVal
  let ⟨x, hDec⟩ := hVal.2
  have hAlTrue : isAligned a sub.offset sub.alignLog2 = true := hAlign hCanAlEq
  have hRB :
      readBytesComp mem ⟨sub.allocId, sub.offset⟩ n sub.alignLog2 =
        .ok ((a.bytes.drop sub.offset).take n) :=
    pt_readBytesComp_ok hPos hFind hLive hBounds.1 hAlTrue
  have hCond : (canAsRef inv uc && Nat.ble 1 n && Nat.beq sub.size n) = true :=
    pt_band_intro (pt_band_intro hCan (pt_nat_ble_one_of_pos hPos))
      (pt_nat_beq_of_eq hSz)
  refine ⟨x, ?_, ⟨hPos, hSz, a, hFind, hLive, hBounds,
    (fun hEx => by nomatch hEx), hAlign, by rw [hCanValEq]; exact hVal⟩⟩
  unfold ptrAsRefRead
  rw [pt_ite_true hCond, hRB]
  exact hDec

theorem ptrAsRefRead_rejected_of_unsafeCell {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv)
    (mem : MemoryState) :
    canAsRef inv true = false ∧ ptrAsRefRead sub c inv true mem = none := by
  have hFalse : canAsRef inv true = false := by
    unfold canAsRef
    exact Bool.and_false _
  refine ⟨hFalse, ?_⟩
  unfold ptrAsRefRead
  rw [hFalse]
  rfl

theorem ptrAsRefRead_rejected_of_unaligned {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool)
    (mem : MemoryState) (hUn : inv.align = .unaligned) :
    canAsRef inv uc = false ∧ ptrAsRefRead sub c inv uc mem = none := by
  have hFalse : canAsRef inv uc = false := by
    unfold canAsRef
    rw [hUn]
    rfl
  refine ⟨hFalse, ?_⟩
  unfold ptrAsRefRead
  rw [hFalse]
  rfl

theorem ptrAsRefRead_rejected_of_uninit {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool)
    (mem : MemoryState) (hUninit : inv.validity = .uninit) :
    canAsRef inv uc = false ∧ ptrAsRefRead sub c inv uc mem = none := by
  have hFalse : canAsRef inv uc = false := by
    unfold canAsRef
    rw [hUninit]
    cases (match inv.align with
      | .aligned => true
      | .unaligned => false) <;> rfl
  refine ⟨hFalse, ?_⟩
  unfold ptrAsRefRead
  rw [hFalse]
  rfl

theorem canAsMut_rejected_of_shared (inv : PtrInv)
    (hShared : inv.aliasing = .shared) : canAsMut inv = false := by
  unfold canAsMut
  rw [hShared]
  rfl

/-- Mutable reference (`&mut T`) read-and-update law backed by `byteSubLensGet`
and `byteSubLensPut`. Requires `canAsMut inv = true` (`.exclusive`, `.aligned`,
`.safe`). -/
theorem ptrAsMut_access_sound {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hCan : canAsMut inv = true) (hHolds : PtrHolds sub c inv uc mem) (y : α) :
    ∃ (oldX : α) (bsOld : List AllocByte) (mem' : MemoryState),
      byteSubLensGet sub mem = some bsOld ∧
      c.decode bsOld = some oldX ∧
      byteSubLensPut sub mem (c.encode y) = some mem' ∧
      PtrHolds sub c inv uc mem' ∧
      (byteSubLensGet sub mem').bind c.decode = some y := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hVal⟩ := hHolds
  have hCan12 := pt_band_left hCan
  have hCanAlias := pt_band_left hCan12
  have hCanAl := pt_band_right hCan12
  have hCanVal := pt_band_right hCan
  have hAliasEq : inv.aliasing = .exclusive := by
    revert hCanAlias
    cases hE : inv.aliasing with
    | exclusive => intro hCanAlias; rfl
    | shared =>
      intro hCanAlias; exact False.elim (pt_false_ne_true hCanAlias)
  have hAlignEq : inv.align = .aligned := by
    revert hCanAl
    cases hA : inv.align with
    | aligned => intro hCanAl; rfl
    | unaligned => intro hCanAl; exact False.elim (pt_false_ne_true hCanAl)
  have hValEq : inv.validity = .safe := by
    revert hCanVal
    cases hV : inv.validity with
    | safe => intro hCanVal; rfl
    | initialized | asInitialized | uninit =>
      intro hCanVal; exact False.elim (pt_false_ne_true hCanVal)
  rw [hValEq] at hVal
  let ⟨oldX, hDecOld⟩ := hVal.2
  have hMutA : a.mutability = .mut := hMut hAliasEq
  have hAlignA : isAligned a sub.offset sub.alignLog2 = true := hAlign hAlignEq
  have hFindComp : findAllocationComp sub.allocId mem.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  have hGetSome :
      byteSubLensGet sub mem = some ((a.bytes.drop sub.offset).take n) := by
    unfold byteSubLensGet
    have hPosSz : Nat.blt 0 sub.size = true := by
      rw [hSz]; exact pt_nat_ble_one_of_pos hPos
    rw [hPosSz]
    rw [hFindComp]
    dsimp only
    rw [hMutA]
    dsimp only [mutabilityIsMut]
    rw [hSz, pt_readBytesComp_ok hPos hFind hLive hBounds.1 hAlignA]
  let bytes' :=
    a.bytes.take sub.offset ++ c.encode y ++
      a.bytes.drop (sub.offset + (c.encode y).length)
  let a' : Allocation :=
    { allocId := a.allocId, alignLog2 := a.alignLog2, mutability := .mut,
      bytes := bytes', live := a.live }
  let mem' : MemoryState :=
    { nextAllocId := mem.nextAllocId
      allocations := replaceAllocationComp a' mem.allocations }
  have hPutLen : (c.encode y).length = sub.size := by
    rw [c.encode_length y, hSz]
  have hPosEnc : 0 < (c.encode y).length := by
    rw [c.encode_length y]; exact hPos
  have hBoundsEnc : isInBounds a sub.offset (c.encode y).length = true := by
    rw [c.encode_length y]; exact hBounds.1
  have hWB :
      writeBytesComp mem ⟨sub.allocId, sub.offset⟩ sub.alignLog2 (c.encode y) =
        .ok mem' :=
    pt_writeBytesComp_ok hPosEnc hFind hLive hBoundsEnc hAlignA hMutA
  have hPutSome : byteSubLensPut sub mem (c.encode y) = some mem' := by
    unfold byteSubLensPut
    have hConj : (Nat.blt 0 sub.size &&
        Nat.beq (c.encode y).length sub.size) = true :=
      pt_band_intro (by rw [hSz]; exact pt_nat_ble_one_of_pos hPos)
        (pt_nat_beq_of_eq hPutLen)
    rw [hConj]
    rw [hWB]
  have hGetAfter : byteSubLensGet sub mem' = some (c.encode y) :=
    byteSubLens_put_get sub mem mem' (c.encode y) hPutSome
  have hAllocIdA : a.allocId = sub.allocId :=
    findAllocationComp_allocId sub.allocId mem.allocations a hFindComp
  have hFindAfter :
      findAllocation sub.allocId mem'.allocations = some a' := by
    rw [← findAllocationComp_eq, ← hAllocIdA]
    exact findAllocationComp_replace_same mem.allocations a a'
      (by rw [hAllocIdA]; exact hFindComp) rfl
  have hLenBytes' : a'.bytes.length = a.bytes.length :=
    pt_splice_length sub.offset (c.encode y) a.bytes hBoundsEnc
  have hBoundsAfter : PtrSpanInBounds a' sub.offset n :=
    ptrSpanInBounds_of_length_eq hLenBytes' hBounds
  have hSliceAfter : (a'.bytes.drop sub.offset).take n = c.encode y := by
    dsimp only [a', bytes']
    exact pt_drop_take_splice_same sub.offset n (c.encode y) a.bytes
      (c.encode_length y) hBoundsEnc
  have hValAfter : ValidityHolds c inv.validity ((a'.bytes.drop sub.offset).take n) := by
    rw [hValEq, hSliceAfter]
    exact ⟨c.encode_length y, ⟨y, c.decode_encode y⟩⟩
  refine ⟨oldX, (a.bytes.drop sub.offset).take n, mem',
    hGetSome, hDecOld, hPutSome,
    ⟨hPos, hSz, a', hFindAfter, hLive, hBoundsAfter, (fun _ => rfl), hAlign,
     hValAfter⟩, ?_⟩
  rw [hGetAfter]
  exact c.decode_encode y

/-! ### 3b. Alignment Transitions (`forget_aligned`, `try_into_aligned`,
`assume_alignment`, alignment shrinking) -/

/-- Unconditionally forgets `.aligned` to `.unaligned`. -/
theorem ptrHolds_forgetAligned {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem) :
    PtrHolds sub c { inv with align := .unaligned } uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, _, hVal⟩ := hHolds
  exact ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut,
    (fun hAl => by nomatch hAl), hVal⟩

/-- Runtime alignment check `isAligned a sub.offset sub.alignLog2` against
`mem.allocations`. -/
@[expose] def ptrCheckAligned (sub : ByteSubLens) (mem : MemoryState) : Bool :=
  match findAllocationComp sub.allocId mem.allocations with
  | none => false
  | some a => isAlignedComp a sub.offset sub.alignLog2

theorem ptrTryIntoAligned_iff {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem) :
    ptrCheckAligned sub mem = true ↔
      PtrHolds sub c { inv with align := .aligned } uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, _, hVal⟩ := hHolds
  have hFindComp : findAllocationComp sub.allocId mem.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  constructor
  · intro hChk
    unfold ptrCheckAligned at hChk
    rw [hFindComp] at hChk
    exact ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, (fun _ => hChk), hVal⟩
  · intro ⟨_, _, a', hFind', _, _, _, hAlign', _⟩
    rw [hFind] at hFind'
    injection hFind' with hAEq
    subst hAEq
    unfold ptrCheckAligned
    rw [hFindComp]
    exact hAlign' rfl

theorem ptrTryIntoAligned_sound {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem)
    (hChk : ptrCheckAligned sub mem = true) :
    PtrHolds sub c { inv with align := .aligned } uc mem :=
  (ptrTryIntoAligned_iff sub c inv uc mem hHolds).mp hChk

theorem ptrTryIntoAligned_rejected {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem)
    (hFail : ptrCheckAligned sub mem = false) :
    ¬ PtrHolds sub c { inv with align := .aligned } uc mem := by
  intro hAligned
  have hTrue := (ptrTryIntoAligned_iff sub c inv uc mem hHolds).mpr hAligned
  rw [hFail] at hTrue
  exact pt_false_ne_true hTrue

/-- Promotes `.unaligned` to `.aligned` given an explicit alignment proof
obligation `∀ a, findAllocation sub.allocId mem.allocations = some a →
isAligned a sub.offset sub.alignLog2 = true`. -/
theorem ptrHolds_assumeAlignment {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState)
    (hHolds : PtrHolds sub c inv uc mem)
    (hAlignOblig : ∀ a : Allocation,
      findAllocation sub.allocId mem.allocations = some a →
      isAligned a sub.offset sub.alignLog2 = true) :
    PtrHolds sub c { inv with align := .aligned } uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, _, hVal⟩ := hHolds
  exact ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut,
    (fun _ => hAlignOblig a hFind), hVal⟩

/-- Retargets the alignment exponent: decreasing it (`dstAlignLog2 ≤
sub.alignLog2`) preserves `.aligned` `PtrHolds` invariants, and `.unaligned`
invariants accept any exponent (e.g. after transmuting to a more-aligned
destination type). -/
theorem ptrHolds_shrinkAlign {α : Type} {n : Nat} (sub : ByteSubLens)
    (dstAlignLog2 : Nat) (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool)
    (mem : MemoryState)
    (hLe : inv.align = .aligned → dstAlignLog2 ≤ sub.alignLog2)
    (hHolds : PtrHolds sub c inv uc mem) :
    PtrHolds { sub with alignLog2 := dstAlignLog2 } c inv uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hVal⟩ := hHolds
  refine ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, ?_, hVal⟩
  intro hAl
  exact pt_isAligned_mono (hLe hAl) (hAlign hAl)

/-! ### 3c. Validity Inclusion and Conversion Compatibility

`PtrHolds` is a duplicable state predicate, not an ownership token: the
aliasing discipline `zerocopy` enforces by typing (an `Exclusive` source is
inaccessible while a derived pointer lives, and accessible again afterward)
appears here as premises of conversion theorems, made load-bearing by
write-back clauses (`PtrWriteBack`).

`zerocopy::pointer::TryTransmuteFromPtr` (`zerocopy/src/pointer/transmute.rs`)
lists three obligations for viewing `src : Ptr<Src, (A, _, SV)>` as
`dst : Ptr<Dst, (A, _, DV)>`:

> "- Preserve destination validity: Either of the following hold:
>   - So long as `dst` is active, no mutation of `dst`'s referent is allowed
>     except via `dst` itself
>   - The set of `DV`-valid referents of `dst` is a superset of the set of
>     `SV`-valid referents of `src` [...]
> - Preserve source validity: Either of the following hold:
>   - `dst` does not permit mutation of its referent
>   - The set of `DV`-valid referents of `dst` is a subset of the set of
>     `SV`-valid referents of `src` [...]
> - No safe code, given access to `src` and `dst`, can cause undefined
>   behavior: Any of the following hold:
>   - `A` is `Exclusive`
>   - `Src: Immutable` and `Dst: Immutable`
>   - It is sound for shared code to operate on a `&Src` and `&Dst` which
>     reference the same byte range at the same time"

`ValidityIncl` from source to destination models the first obligation's
superset alternative and `MutationCompat` the second (triggered when the
destination permits mutation, `ptrPermitsMutation`). For the third,
`castReadCompat` models the first two alternatives; same-type conversions
(`recall_validity`, `ptrWrite`, `ptrHolds_weaken`) satisfy the last one, so
they need only the validity obligations. `zerocopy`'s `recall_validity` is
itself a same-type transmute (`transmute_with::<T, V, IdCast, R>`), and
every validity change below (`ptrWrite`, `ptrRecallValidity_sound`,
`ptrHolds_weaken`, `ptrTransmute_sound`, `ptrTryCastInto_sound`) carries
`MutationCompat` and a write-back clause. -/

/-- Every buffer satisfying `ValidityHolds cSrc vSrc` also satisfies
`ValidityHolds cDst vDst`: the `vDst`-valid referents of `cDst` include the
`vSrc`-valid referents of `cSrc`. -/
@[expose] def ValidityIncl {α β : Type} {n : Nat} (cSrc : FixedByteCodec α n)
    (vSrc : ValidityInv) (cDst : FixedByteCodec β n) (vDst : ValidityInv) :
    Prop :=
  ∀ bs : List AllocByte, ValidityHolds cSrc vSrc bs → ValidityHolds cDst vDst bs

theorem validityIncl_refl {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (v : ValidityInv) : ValidityIncl c v c v :=
  fun _ h => h

/-- Same-codec weakening along `ValidityLe`. -/
theorem validityIncl_of_validityLe {α : Type} {n : Nat}
    (c : FixedByteCodec α n) {v1 v2 : ValidityInv} (hLe : ValidityLe v1 v2) :
    ValidityIncl c v1 c v2 :=
  fun _ h => validityHolds_weaken c hLe h

/-- Unpadded `IntoBytes` (`AllDecodableInit`): `.safe` slices are
`.initialized`. -/
theorem validityIncl_safe_initialized_of_allDecodableInit {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hDecInit : AllDecodableInit c) :
    ValidityIncl c .safe c .initialized :=
  fun bs h =>
    validityHolds_safe_to_initialized_of_allDecodableInit hDecInit bs h

/-- Initialized bytes of any source (even a padded one) are valid for a
`FromBytes` destination (`IsSurjectiveInitDecoder`). -/
theorem validityIncl_initialized_fromBytes {α β : Type} {n : Nat}
    (cSrc : FixedByteCodec α n) {cDst : FixedByteCodec β n}
    (hDstFrom : cDst.IsSurjectiveInitDecoder) :
    ValidityIncl cSrc .initialized cDst .safe :=
  fun _ h => ⟨h.1, hDstFrom _ h.1 h.2⟩

/-- Unpadded `IntoBytes` source (`AllDecodableInit`) into `FromBytes`
destination (`IsSurjectiveInitDecoder`). -/
theorem validityIncl_intoBytes_fromBytes {α β : Type} {n : Nat}
    {cSrc : FixedByteCodec α n} {cDst : FixedByteCodec β n}
    (hSrcInit : AllDecodableInit cSrc)
    (hDstFrom : cDst.IsSurjectiveInitDecoder) :
    ValidityIncl cSrc .safe cDst .safe :=
  fun bs h =>
    validityIncl_initialized_fromBytes cSrc hDstFrom bs
      (validityIncl_safe_initialized_of_allDecodableInit hSrcInit bs h)

/-- `.asInitialized` transfers when, after every prefix, each byte position the
destination requires initialized is also required by the source (this holds
across padded representations). -/
theorem validityIncl_asInitialized {α β : Type} {n : Nat}
    {cSrc : FixedByteCodec α n} {cDst : FixedByteCodec β n}
    (hReqSub : ∀ (pre : List AllocByte) (i : Nat), i < n →
      CodecRequiresInitAt cDst pre i → CodecRequiresInitAt cSrc pre i) :
    ValidityIncl cSrc .asInitialized cDst .asInitialized :=
  fun _ h => ⟨h.1, ⟨h.1, fun i hi hReqDst =>
    h.2.2 i hi (hReqSub _ i hi hReqDst)⟩⟩

/-- Both endpoints of a cast satisfy `zerocopy::invariant::Read<A>`
(`.exclusive`, or `.shared` without `UnsafeCell`), as `try_cast_into` requires
of its destination (`U: Read<I::Aliasing, R>`). Under `.shared`, this is
`zerocopy`'s "`Src: Immutable` and `Dst: Immutable`" transmute alternative. -/
@[expose] def castReadCompat (aliasing : AliasingInv) (ucSrc ucDst : Bool) :
    Bool :=
  canPtrRead aliasing ucSrc && canPtrRead aliasing ucDst

/-- Whether a pointer permits mutation of its referent: `.exclusive`, or
`.shared` over a referent containing an `UnsafeCell`. (No operation in this
module writes through `.shared`; the `UnsafeCell` case keeps the obligations
faithful to `zerocopy`.) -/
@[expose] def ptrPermitsMutation (aliasing : AliasingInv) (uc : Bool) : Bool :=
  match aliasing with
  | .exclusive => true
  | .shared => uc

/-- Source-validity preservation: when the destination permits mutation, every
`vDst`-valid `cDst` buffer must be a `vSrc`-valid `cSrc` buffer, so writes
through the destination cannot invalidate the source. -/
@[expose] def MutationCompat {α β : Type} {n : Nat} (aliasing : AliasingInv)
    (ucDst : Bool) (cSrc : FixedByteCodec α n) (vSrc : ValidityInv)
    (cDst : FixedByteCodec β n) (vDst : ValidityInv) : Prop :=
  ptrPermitsMutation aliasing ucDst = true → ValidityIncl cDst vDst cSrc vSrc

/-- All three `TryTransmuteFromPtr` obligations for an infallible transmute
between possibly different types (see the section comment). -/
@[expose] def TransmuteCompat {α β : Type} {n : Nat} (aliasing : AliasingInv)
    (ucSrc ucDst : Bool) (cSrc : FixedByteCodec α n) (vSrc : ValidityInv)
    (cDst : FixedByteCodec β n) (vDst : ValidityInv) : Prop :=
  castReadCompat aliasing ucSrc ucDst = true ∧
    ValidityIncl cSrc vSrc cDst vDst ∧
    MutationCompat aliasing ucDst cSrc vSrc cDst vDst

/-- A shared transmute between `UnsafeCell`-free endpoints needs only forward
inclusion: neither endpoint permits mutation. -/
theorem transmuteCompat_shared {α β : Type} {n : Nat}
    {cSrc : FixedByteCodec α n} {vSrc : ValidityInv}
    {cDst : FixedByteCodec β n} {vDst : ValidityInv}
    (hIncl : ValidityIncl cSrc vSrc cDst vDst) :
    TransmuteCompat .shared false false cSrc vSrc cDst vDst :=
  ⟨rfl, hIncl, fun hPM => nomatch hPM⟩

/-- An exclusive transmute needs inclusion in both directions. -/
theorem transmuteCompat_exclusive {α β : Type} {n : Nat} (ucSrc ucDst : Bool)
    {cSrc : FixedByteCodec α n} {vSrc : ValidityInv}
    {cDst : FixedByteCodec β n} {vDst : ValidityInv}
    (hIncl : ValidityIncl cSrc vSrc cDst vDst)
    (hRev : ValidityIncl cDst vDst cSrc vSrc) :
    TransmuteCompat .exclusive ucSrc ucDst cSrc vSrc cDst vDst :=
  ⟨rfl, hIncl, fun _ => hRev⟩

/-- Re-reading the same span through another codec: `PtrHolds` constrains the
codec only through slice validity. Aliasing permissions are the caller's
obligation. -/
private theorem pt_ptrHolds_recodec {α β : Type} {n : Nat} (sub : ByteSubLens)
    (c1 : FixedByteCodec α n) (c2 : FixedByteCodec β n) (inv : PtrInv)
    (v1 v2 : ValidityInv) (uc1 uc2 : Bool) (mem : MemoryState)
    (hIncl : ValidityIncl c1 v1 c2 v2)
    (hHolds : PtrHolds sub c1 { inv with validity := v1 } uc1 mem) :
    PtrHolds sub c2 { inv with validity := v2 } uc2 mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hVal⟩ := hHolds
  exact ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hIncl _ hVal⟩

/-- Write-back for a pointer conversion: every state in which the destination
view `(sub, cDst, invDst)` holds (for example after `ptrWrite` through it) also
satisfies the source codec `cSrc` and validity `vSrc` at that view, so the
source invariant survives mutation through the destination. -/
@[expose] def PtrWriteBack {α β : Type} {n : Nat} (sub : ByteSubLens)
    (cDst : FixedByteCodec β n) (invDst : PtrInv) (ucDst : Bool)
    (cSrc : FixedByteCodec α n) (vSrc : ValidityInv) (ucSrc : Bool) : Prop :=
  ∀ mem' : MemoryState,
    PtrHolds sub cDst invDst ucDst mem' →
    PtrHolds sub cSrc { invDst with validity := vSrc } ucSrc mem'

theorem ptrWriteBack_of_validityIncl {α β : Type} {n : Nat}
    (sub : ByteSubLens) (cDst : FixedByteCodec β n) (invDst : PtrInv)
    (ucDst : Bool) (cSrc : FixedByteCodec α n) (vSrc : ValidityInv)
    (ucSrc : Bool) (hIncl : ValidityIncl cDst invDst.validity cSrc vSrc) :
    PtrWriteBack sub cDst invDst ucDst cSrc vSrc ucSrc :=
  fun mem' hDst =>
    pt_ptrHolds_recodec sub cDst cSrc invDst invDst.validity vSrc ucDst ucSrc
      mem' hIncl hDst

/-! ### 3d. Typed `ptrRead`, `ptrWrite`, and `recall_validity` -/

/-- Boolean check for `.safe` validity. -/
@[expose] def validityIsSafe : ValidityInv → Bool
  | .safe => true
  | _ => false

/-- By-value typed pointer read (`zerocopy::Ptr::read`, which requires
`T: Copy`, `T: Read<I::Aliasing, R>`, and `Valid` validity) via
`readBytesComp` using `ptrEffectiveAlignLog2`. `isCopy` is an abstract
caller-supplied flag for `T: Copy`, like `containsUnsafeCell`: the read
returns an owned value while the pointer stays usable, which duplicates the
referent unless it is `Copy`. Succeeds on both `.shared` (with
`containsUnsafeCell = false`) and `.mut` allocations when
`inv.validity = .safe`, and fails closed otherwise. -/
@[expose] def ptrRead {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc isCopy : Bool)
    (mem : MemoryState) : Option α :=
  if isCopy && canPtrRead inv.aliasing uc && validityIsSafe inv.validity &&
      Nat.ble 1 n && Nat.beq sub.size n then
    match readBytesComp mem ⟨sub.allocId, sub.offset⟩ n
        (ptrEffectiveAlignLog2 sub inv) with
    | .ok bs => c.decode bs
    | .error _ => none
  else
    none

theorem ptrRead_sound {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc isCopy : Bool)
    (mem : MemoryState) (hCopy : isCopy = true)
    (hCan : canPtrRead inv.aliasing uc = true)
    (hSafe : inv.validity = .safe)
    (hHolds : PtrHolds sub c inv uc mem) :
    ∃ x : α, ptrRead sub c inv uc isCopy mem = some x ∧
      PtrHolds sub c inv uc mem := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hVal⟩ := hHolds
  rw [hSafe] at hVal
  let ⟨x, hDec⟩ := hVal.2
  have hEffAl :
      isAligned a sub.offset (ptrEffectiveAlignLog2 sub inv) = true := by
    cases hAl : inv.align with
    | aligned =>
      unfold ptrEffectiveAlignLog2
      rw [hAl]
      exact hAlign hAl
    | unaligned =>
      unfold ptrEffectiveAlignLog2
      rw [hAl]
      exact pt_isAligned_zero a sub.offset
  have hRB :
      readBytesComp mem ⟨sub.allocId, sub.offset⟩ n
          (ptrEffectiveAlignLog2 sub inv) =
        .ok ((a.bytes.drop sub.offset).take n) :=
    pt_readBytesComp_ok hPos hFind hLive hBounds.1 hEffAl
  have hValFlag : validityIsSafe inv.validity = true := by
    rw [hSafe]; rfl
  have hCond : (isCopy && canPtrRead inv.aliasing uc &&
      validityIsSafe inv.validity && Nat.ble 1 n && Nat.beq sub.size n) =
      true :=
    pt_band_intro
      (pt_band_intro (pt_band_intro (pt_band_intro hCopy hCan) hValFlag)
        (pt_nat_ble_one_of_pos hPos))
      (pt_nat_beq_of_eq hSz)
  refine ⟨x, ?_, ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign,
    by rw [hSafe]; exact hVal⟩⟩
  unfold ptrRead
  rw [pt_ite_true hCond, hRB]
  exact hDec

theorem ptrRead_agrees_with_byteSubLensGet {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool)
    (mem : MemoryState) (hExcl : inv.aliasing = .exclusive)
    (hAl : inv.align = .aligned) (hSafe : inv.validity = .safe)
    (hHolds : PtrHolds sub c inv uc mem) :
    ptrRead sub c inv uc true mem = (byteSubLensGet sub mem).bind c.decode := by
  let ⟨hPos, hSz, a, hFind, _, _, hMut, _, _⟩ := hHolds
  have hCan : canPtrRead inv.aliasing uc = true := by rw [hExcl]; rfl
  have hValFlag : validityIsSafe inv.validity = true := by
    rw [hSafe]; rfl
  have hCond : (true && canPtrRead inv.aliasing uc &&
      validityIsSafe inv.validity && Nat.ble 1 n && Nat.beq sub.size n) =
      true :=
    pt_band_intro
      (pt_band_intro (pt_band_intro (pt_band_intro rfl hCan) hValFlag)
        (pt_nat_ble_one_of_pos hPos))
      (pt_nat_beq_of_eq hSz)
  have hFindComp : findAllocationComp sub.allocId mem.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  have hMutA : a.mutability = .mut := hMut hExcl
  have hPosSz : Nat.blt 0 sub.size = true := by
    rw [hSz]; exact pt_nat_ble_one_of_pos hPos
  have hEff : ptrEffectiveAlignLog2 sub inv = sub.alignLog2 := by
    unfold ptrEffectiveAlignLog2
    rw [hAl]
  unfold ptrRead
  rw [pt_ite_true hCond, hEff]
  unfold byteSubLensGet
  rw [hPosSz]
  rw [hFindComp]
  dsimp only
  rw [hMutA]
  dsimp only [mutabilityIsMut]
  rw [hSz]
  cases readBytesComp mem ⟨sub.allocId, sub.offset⟩ n sub.alignLog2 <;> rfl

theorem ptrRead_rejected_of_not_copy {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (mem : MemoryState) :
    ptrRead sub c inv uc false mem = none := by
  unfold ptrRead
  rfl

theorem ptrRead_rejected_of_uninit {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc isCopy : Bool)
    (mem : MemoryState) (hUninit : inv.validity = .uninit) :
    ptrRead sub c inv uc isCopy mem = none := by
  unfold ptrRead
  rw [hUninit]
  cases isCopy <;> cases canPtrRead inv.aliasing uc <;> rfl

theorem ptrRead_rejected_of_shared_unsafeCell {α : Type} {n : Nat}
    (sub : ByteSubLens) (c : FixedByteCodec α n) (inv : PtrInv) (isCopy : Bool)
    (mem : MemoryState) (hShared : inv.aliasing = .shared) :
    ptrRead sub c inv true isCopy mem = none := by
  unfold ptrRead canPtrRead
  rw [hShared]
  cases isCopy <;> rfl

/-- Boolean check for `.exclusive` aliasing. -/
@[expose] def aliasingIsExclusive : AliasingInv → Bool
  | .exclusive => true
  | _ => false

/-- Typed pointer write via `writeBytesComp` using `ptrEffectiveAlignLog2`,
modeling a by-value store of `x` through an `.exclusive` pointer (as through
`as_mut` or `core::ptr::write`). The referent becomes `c.encode x`. -/
@[expose] def ptrWrite {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (x : α)
    (mem : MemoryState) : Option MemoryState :=
  if aliasingIsExclusive inv.aliasing &&
      Nat.ble 1 n && Nat.beq sub.size n then
    match writeBytesComp mem ⟨sub.allocId, sub.offset⟩
        (ptrEffectiveAlignLog2 sub inv) (c.encode x) with
    | .ok mem' => some mem'
    | .error _ => none
  else
    none

/-- `ptrWrite` soundness. Writing stores `c.encode x`, a `.safe` slice for `c`,
so the pointer's own validity survives only if every `.safe` slice satisfies it
(`hMut : ValidityIncl c .safe c inv.validity`). This holds for `.uninit`,
`.asInitialized`, and `.safe`, and for `.initialized` exactly when `.safe`
slices are initialized (e.g. `AllDecodableInit c`); it fails for padded
`.initialized` pointers. After the write, both the original invariant and
`.safe` hold, and a `Copy` read returns `x`. -/
theorem ptrWrite_sound {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (uc : Bool) (x : α)
    (mem : MemoryState) (hExcl : inv.aliasing = .exclusive)
    (hMutCompat : ValidityIncl c .safe c inv.validity)
    (hHolds : PtrHolds sub c inv uc mem) :
    ∃ mem' : MemoryState,
      ptrWrite sub c inv x mem = some mem' ∧
      PtrHolds sub c inv uc mem' ∧
      PtrHolds sub c { inv with validity := .safe } uc mem' ∧
      ptrRead sub c { inv with validity := .safe } uc true mem' = some x := by
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, _⟩ := hHolds
  have hMutA : a.mutability = .mut := hMut hExcl
  have hFindComp : findAllocationComp sub.allocId mem.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  have hEffAl :
      isAligned a sub.offset (ptrEffectiveAlignLog2 sub inv) = true := by
    cases hAl : inv.align with
    | aligned =>
      unfold ptrEffectiveAlignLog2
      rw [hAl]
      exact hAlign hAl
    | unaligned =>
      unfold ptrEffectiveAlignLog2
      rw [hAl]
      exact pt_isAligned_zero a sub.offset
  let bytes' :=
    a.bytes.take sub.offset ++ c.encode x ++
      a.bytes.drop (sub.offset + (c.encode x).length)
  let a' : Allocation :=
    { allocId := a.allocId, alignLog2 := a.alignLog2, mutability := .mut,
      bytes := bytes', live := a.live }
  let mem' : MemoryState :=
    { nextAllocId := mem.nextAllocId
      allocations := replaceAllocationComp a' mem.allocations }
  have hPosEnc : 0 < (c.encode x).length := by
    rw [c.encode_length x]; exact hPos
  have hBoundsEnc : isInBounds a sub.offset (c.encode x).length = true := by
    rw [c.encode_length x]; exact hBounds.1
  have hWB :
      writeBytesComp mem ⟨sub.allocId, sub.offset⟩
          (ptrEffectiveAlignLog2 sub inv) (c.encode x) = .ok mem' :=
    pt_writeBytesComp_ok hPosEnc hFind hLive hBoundsEnc hEffAl hMutA
  have hCond : (aliasingIsExclusive inv.aliasing &&
      Nat.ble 1 n && Nat.beq sub.size n) = true := by
    rw [hExcl]
    exact pt_band_intro (pt_band_intro rfl (pt_nat_ble_one_of_pos hPos))
      (pt_nat_beq_of_eq hSz)
  have hAllocIdA : a.allocId = sub.allocId :=
    findAllocationComp_allocId sub.allocId mem.allocations a hFindComp
  have hFindAfter :
      findAllocation sub.allocId mem'.allocations = some a' := by
    rw [← findAllocationComp_eq, ← hAllocIdA]
    exact findAllocationComp_replace_same mem.allocations a a'
      (by rw [hAllocIdA]; exact hFindComp) rfl
  have hLenBytes' : a'.bytes.length = a.bytes.length :=
    pt_splice_length sub.offset (c.encode x) a.bytes hBoundsEnc
  have hBoundsAfter : PtrSpanInBounds a' sub.offset n :=
    ptrSpanInBounds_of_length_eq hLenBytes' hBounds
  have hSliceAfter : (a'.bytes.drop sub.offset).take n = c.encode x := by
    dsimp only [a', bytes']
    exact pt_drop_take_splice_same sub.offset n (c.encode x) a.bytes
      (c.encode_length x) hBoundsEnc
  have hValAfter :
      ValidityHolds c .safe ((a'.bytes.drop sub.offset).take n) := by
    rw [hSliceAfter]
    exact ⟨c.encode_length x, ⟨x, c.decode_encode x⟩⟩
  have hSafeAfter :
      PtrHolds sub c { inv with validity := .safe } uc mem' :=
    ⟨hPos, hSz, a', hFindAfter, hLive, hBoundsAfter, (fun _ => rfl), hAlign,
      hValAfter⟩
  refine ⟨mem', ?_, ?_, hSafeAfter, ?_⟩
  · unfold ptrWrite
    rw [pt_ite_true hCond, hWB]
  · exact ptrWriteBack_of_validityIncl sub c { inv with validity := .safe } uc
      c inv.validity uc hMutCompat mem' hSafeAfter
  · have hCanR : canPtrRead ({ inv with validity := .safe }.aliasing) uc =
        true := by
      rw [hExcl]
      rfl
    have hValR : validityIsSafe ({ inv with validity := .safe }.validity) =
        true := rfl
    have hCondR : (true &&
        canPtrRead ({ inv with validity := .safe }.aliasing) uc &&
        validityIsSafe ({ inv with validity := .safe }.validity) &&
        Nat.ble 1 n && Nat.beq sub.size n) = true :=
      pt_band_intro
        (pt_band_intro (pt_band_intro (pt_band_intro rfl hCanR) hValR)
          (pt_nat_ble_one_of_pos hPos))
        (pt_nat_beq_of_eq hSz)
    have hEffSafe :
        isAligned a' sub.offset
          (ptrEffectiveAlignLog2 sub { inv with validity := .safe }) = true :=
      hEffAl
    have hRB' :
        readBytesComp mem' ⟨sub.allocId, sub.offset⟩ n
            (ptrEffectiveAlignLog2 sub { inv with validity := .safe }) =
          .ok ((a'.bytes.drop sub.offset).take n) :=
      pt_readBytesComp_ok hPos hFindAfter hLive hBoundsAfter.1 hEffSafe
    unfold ptrRead
    rw [pt_ite_true hCondR, hRB', hSliceAfter]
    exact c.decode_encode x

theorem ptrWrite_rejected_of_shared {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (x : α) (mem : MemoryState)
    (hShared : inv.aliasing = .shared) :
    ptrWrite sub c inv x mem = none := by
  unfold ptrWrite
  rw [hShared]
  rfl

theorem ptrWrite_preserves_disjoint_ptrHolds {α β : Type} {n m : Nat}
    (subW : ByteSubLens) (cW : FixedByteCodec α n) (invW : PtrInv) (x : α)
    (subO : ByteSubLens) (cO : FixedByteCodec β m) (invO : PtrInv)
    (ucO : Bool) (mem1 mem2 : MemoryState)
    (hDisj : DisjointPtrWrites subW subO)
    (hWrite : ptrWrite subW cW invW x mem1 = some mem2)
    (hOther : PtrHolds subO cO invO ucO mem1) :
    PtrHolds subO cO invO ucO mem2 := by
  unfold ptrWrite at hWrite
  cases hCond :
      (aliasingIsExclusive invW.aliasing &&
        Nat.ble 1 n && Nat.beq subW.size n) with
  | false =>
    rw [pt_ite_false hCond] at hWrite
    nomatch hWrite
  | true =>
    rw [pt_ite_true hCond] at hWrite
    have hSzEq : subW.size = n :=
      pt_nat_eq_of_beq (pt_band_right hCond)
    have hNz : 0 < (cW.encode x).length := by
      rw [cW.encode_length x]
      exact Nat.ble_eq.mp (pt_band_right (pt_band_left hCond))
    have hSzLen : (cW.encode x).length = subW.size := by
      rw [cW.encode_length x, hSzEq]
    revert hWrite
    cases hWB :
        writeBytesComp mem1 ⟨subW.allocId, subW.offset⟩
          (ptrEffectiveAlignLog2 subW invW) (cW.encode x) with
    | error _ =>
      intro hWrite
      nomatch hWrite
    | ok memOut =>
      intro hWrite
      injection hWrite with hMemEq
      rw [← hMemEq]
      rw [writeBytesComp_eq] at hWB
      exact ptrHolds_frame_writeBytes subW subO
        (ptrEffectiveAlignLog2 subW invW) (cW.encode x) hNz hSzLen hDisj hWB
        hOther

/-- `zerocopy::Ptr::recall_validity`, a same-type transmute
(`transmute_with::<T, V, IdCast, R>`) that keeps aliasing and alignment:
changes validity from `inv.validity` to `vDst` given forward inclusion and, when
the pointer permits mutation, reverse inclusion (`MutationCompat`). For
example, `.initialized -> .safe` needs `IsSurjectiveInitDecoder c`
(`validityIncl_initialized_fromBytes`) and, under `.exclusive`, also
`AllDecodableInit c`; padded codecs are rejected because a `.safe` write could
leave uninitialized padding behind. Weakenings use
`validityIncl_of_validityLe`. -/
theorem ptrRecallValidity_sound {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv : PtrInv) (vDst : ValidityInv) (uc : Bool)
    (mem : MemoryState) (hIncl : ValidityIncl c inv.validity c vDst)
    (hMutCompat : MutationCompat inv.aliasing uc c inv.validity c vDst)
    (hHolds : PtrHolds sub c inv uc mem) :
    PtrHolds sub c { inv with validity := vDst } uc mem ∧
      (ptrPermitsMutation inv.aliasing uc = true →
        PtrWriteBack sub c { inv with validity := vDst } uc c inv.validity
          uc) :=
  ⟨pt_ptrHolds_recodec sub c c inv inv.validity vDst uc uc mem hIncl hHolds,
   fun hPM =>
    ptrWriteBack_of_validityIncl sub c { inv with validity := vDst } uc c
      inv.validity uc (hMutCompat hPM)⟩

/-- `PtrInvLe` weakening of aliasing, alignment, and validity. Weakening
validity is a `recall_validity`, so a result that permits mutation needs
`MutationCompat` (e.g. an `.exclusive` `.safe` pointer cannot weaken to
`.uninit` unless every `c`-buffer is `.safe`). -/
theorem ptrHolds_weaken {α : Type} {n : Nat} (sub : ByteSubLens)
    (c : FixedByteCodec α n) (inv1 inv2 : PtrInv) (uc : Bool)
    (mem : MemoryState) (hLe : PtrInvLe inv1 inv2)
    (hMutCompat : MutationCompat inv2.aliasing uc c inv1.validity c
      inv2.validity)
    (hHolds : PtrHolds sub c inv1 uc mem) :
    PtrHolds sub c inv2 uc mem ∧
      (ptrPermitsMutation inv2.aliasing uc = true →
        PtrWriteBack sub c inv2 uc c inv1.validity uc) := by
  refine ⟨?_, fun hPM =>
    ptrWriteBack_of_validityIncl sub c inv2 uc c inv1.validity uc
      (hMutCompat hPM)⟩
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, hAlign, hVal⟩ := hHolds
  refine ⟨hPos, hSz, a, hFind, hLive, hBounds, ?_, ?_, ?_⟩
  · intro hEx2
    have hEx1 : inv1.aliasing = .exclusive := by
      cases ha : inv1.aliasing with
      | exclusive => rfl
      | shared =>
        have hBad : AliasingLe inv1.aliasing .exclusive := by
          have hA1 : AliasingLe inv1.aliasing inv2.aliasing := hLe.1
          rw [hEx2] at hA1
          exact hA1
        rw [ha] at hBad
        exact False.elim (pt_false_ne_true hBad)
    exact hMut hEx1
  · intro hAl2
    have hAl1 : inv1.align = .aligned := by
      cases hl : inv1.align with
      | aligned => rfl
      | unaligned =>
        have hBad : AlignLe inv1.align .aligned := by
          have hL1 : AlignLe inv1.align inv2.align := hLe.2.1
          rw [hAl2] at hL1
          exact hL1
        rw [hl] at hBad
        exact False.elim (pt_false_ne_true hBad)
    exact hAlign hAl1
  · exact validityHolds_weaken c hLe.2.2 hVal

/-! ### 3e. Transmute and `try_cast_into` -/

/-- `zerocopy::Ptr::transmute` soundness (`TryTransmuteFromPtr` with an
infallible validity relation): reinterprets the span as `cDst` with validity
`vDst` and the destination type's alignment exponent `dstAlignLog2`. Like
`transmute`, it conservatively forgets alignment (`.unaligned`), since the
destination type may require stricter alignment; regain it with
`ptrTryIntoAligned_sound` or `ptrHolds_assumeAlignment`.

The second conjunct is the write-back clause: when the destination permits
mutation, every state in which it holds also satisfies the source codec and
validity. `castReadCompat` rules out shared-access interleavings that
`PtrHolds` does not model, so this proof does not consume it. -/
theorem ptrTransmute_sound {α β : Type} {n : Nat}
    (sub : ByteSubLens) (dstAlignLog2 : Nat)
    (cSrc : FixedByteCodec α n) (cDst : FixedByteCodec β n)
    (inv : PtrInv) (vDst : ValidityInv) (ucSrc ucDst : Bool)
    (mem : MemoryState)
    (hCompat :
      TransmuteCompat inv.aliasing ucSrc ucDst cSrc inv.validity cDst vDst)
    (hHolds : PtrHolds sub cSrc inv ucSrc mem) :
    PtrHolds { sub with alignLog2 := dstAlignLog2 } cDst
        { inv with align := .unaligned, validity := vDst } ucDst mem ∧
      (ptrPermitsMutation inv.aliasing ucDst = true →
        PtrWriteBack { sub with alignLog2 := dstAlignLog2 } cDst
          { inv with align := .unaligned, validity := vDst } ucDst cSrc
          inv.validity ucSrc) := by
  refine ⟨?_, fun hPM =>
    ptrWriteBack_of_validityIncl { sub with alignLog2 := dstAlignLog2 } cDst
      { inv with align := .unaligned, validity := vDst } ucDst cSrc
      inv.validity ucSrc (hCompat.2.2 hPM)⟩
  have hUnal := ptrHolds_forgetAligned sub cSrc inv ucSrc mem hHolds
  have hRetarget :=
    ptrHolds_shrinkAlign sub dstAlignLog2 cSrc { inv with align := .unaligned }
      ucSrc mem (fun hAl => by nomatch hAl) hUnal
  exact pt_ptrHolds_recodec { sub with alignLog2 := dstAlignLog2 } cSrc cDst
    { inv with align := .unaligned } inv.validity vDst ucSrc ucDst mem
    hCompat.2.1 hRetarget

/-- Boolean check for `.safe` or `.initialized` validity. -/
@[expose] def validityIsInitOrSafe : ValidityInv → Bool
  | .safe | .initialized => true
  | _ => false

/-- Fallible `TryFromBytes` + alignment checked cast (`try_cast_into` followed
by a validity check): requires both endpoints to be readable under
`inv.aliasing` (`castReadCompat`, mirroring `U: Read<I::Aliasing, R>`), checks
target alignment at `dstAlignLog2` via `ptrCheckAligned`, and checks target
bit-validity via `readBytesComp` + `cDst.decode`. -/
@[expose] def ptrTryCastInto {β : Type} {n : Nat}
    (sub : ByteSubLens) (dstAlignLog2 : Nat) (cDst : FixedByteCodec β n)
    (inv : PtrInv) (ucSrc ucDst : Bool) (mem : MemoryState) : Option β :=
  if castReadCompat inv.aliasing ucSrc ucDst &&
      validityIsInitOrSafe inv.validity &&
      Nat.ble 1 n && Nat.beq sub.size n &&
      ptrCheckAligned { sub with alignLog2 := dstAlignLog2 } mem then
    match readBytesComp mem ⟨sub.allocId, sub.offset⟩ n dstAlignLog2 with
    | .ok bs => cDst.decode bs
    | .error _ => none
  else
    none

/-- `ptrTryCastInto` soundness. The runtime decode check replaces
`TransmuteCompat`'s forward inclusion, and `castReadCompat` and alignment at
`dstAlignLog2` are checked at runtime, but source-validity preservation remains
a static obligation (`MutationCompat`) with the same write-back clause as
`ptrTransmute_sound`. -/
theorem ptrTryCastInto_sound {α β : Type} {n : Nat}
    (sub : ByteSubLens) (dstAlignLog2 : Nat)
    (cSrc : FixedByteCodec α n) (cDst : FixedByteCodec β n)
    (inv : PtrInv) (ucSrc ucDst : Bool) (mem : MemoryState) (y : β)
    (hMutCompat :
      MutationCompat inv.aliasing ucDst cSrc inv.validity cDst .safe)
    (hHolds : PtrHolds sub cSrc inv ucSrc mem)
    (hCast :
      ptrTryCastInto sub dstAlignLog2 cDst inv ucSrc ucDst mem = some y) :
    PtrHolds { sub with alignLog2 := dstAlignLog2 } cDst
        { inv with align := .aligned, validity := .safe } ucDst mem ∧
      (ptrPermitsMutation inv.aliasing ucDst = true →
        PtrWriteBack { sub with alignLog2 := dstAlignLog2 } cDst
          { inv with align := .aligned, validity := .safe } ucDst cSrc
          inv.validity ucSrc) := by
  refine ⟨?_, fun hPM =>
    ptrWriteBack_of_validityIncl { sub with alignLog2 := dstAlignLog2 } cDst
      { inv with align := .aligned, validity := .safe } ucDst cSrc
      inv.validity ucSrc (hMutCompat hPM)⟩
  let ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut, _, _⟩ := hHolds
  unfold ptrTryCastInto at hCast
  cases hCond :
      (castReadCompat inv.aliasing ucSrc ucDst &&
        validityIsInitOrSafe inv.validity &&
        Nat.ble 1 n && Nat.beq sub.size n &&
        ptrCheckAligned { sub with alignLog2 := dstAlignLog2 } mem) with
  | false =>
    rw [pt_ite_false hCond] at hCast
    nomatch hCast
  | true =>
    rw [pt_ite_true hCond] at hCast
    have hChkAl :
        ptrCheckAligned { sub with alignLog2 := dstAlignLog2 } mem = true :=
      pt_band_right hCond
    have hFindComp : findAllocationComp sub.allocId mem.allocations = some a := by
      rw [findAllocationComp_eq]
      exact hFind
    unfold ptrCheckAligned at hChkAl
    dsimp only at hChkAl
    rw [hFindComp] at hChkAl
    have hAlDst : isAligned a sub.offset dstAlignLog2 = true := hChkAl
    have hRB :
        readBytesComp mem ⟨sub.allocId, sub.offset⟩ n dstAlignLog2 =
          .ok ((a.bytes.drop sub.offset).take n) :=
      pt_readBytesComp_ok hPos hFind hLive hBounds.1 hAlDst
    rw [hRB] at hCast
    have hLenSlice : ((a.bytes.drop sub.offset).take n).length = n :=
      pt_list_drop_take_length_of_ble sub.offset n a.bytes hBounds.1
    exact ⟨hPos, hSz, a, hFind, hLive, hBounds, hMut,
      (fun _ => hAlDst), ⟨hLenSlice, ⟨y, hCast⟩⟩⟩

/-- Soundness-boundary theorem: padding (`padRight (u16Codec .little) 2`)
refutes `AllDecodableInit` and `IsInitCodec`, and admits a valid `.safe`
4-byte `.mut` aligned allocation slice whose bytes fail `AllBytesInit` and fail
`u32Codec .little`'s `.safe` invariant (`u32Codec.decode = none`). -/
theorem padding_refutes_intoBytes_and_unpadded_transmute :
    ¬ (FixedByteCodec.padRight (u16Codec .little) 2).IsInitCodec ∧
    ¬ AllDecodableInit (FixedByteCodec.padRight (u16Codec .little) 2) ∧
    ∃ (sub : ByteSubLens) (mem : MemoryState),
      PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
        ⟨.exclusive, .aligned, .safe⟩ false mem ∧
      PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
        ⟨.exclusive, .aligned, .asInitialized⟩ false mem ∧
      ¬ PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
        ⟨.exclusive, .aligned, .initialized⟩ false mem ∧
      ¬ PtrHolds sub (u32Codec .little)
        ⟨.exclusive, .aligned, .safe⟩ false mem := by
  have hNotInit :
      ¬ (FixedByteCodec.padRight (u16Codec .little) 2).IsInitCodec :=
    padRight_not_isInitCodec (by decide) (u16Codec .little) (BitVec.ofNat 16 0)
  have hNotDecInit :
      ¬ AllDecodableInit (FixedByteCodec.padRight (u16Codec .little) 2) :=
    padRight_not_allDecodableInit (by decide) (u16Codec .little)
      (BitVec.ofNat 16 0)
  let sub : ByteSubLens := ⟨0, 0, 4, 2⟩
  let bs :=
    (FixedByteCodec.padRight (u16Codec .little) 2).encode (BitVec.ofNat 16 0)
  let mem : MemoryState :=
    { nextAllocId := 1
      allocations := [{ allocId := 0, alignLog2 := 2, mutability := .mut,
                        bytes := bs, live := true }] }
  have hSafe :
      PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
        ⟨.exclusive, .aligned, .safe⟩ false mem :=
    ⟨by decide, rfl,
     ⟨0, 2, .mut, bs, true⟩, rfl, rfl, ⟨rfl, by decide⟩, (fun _ => rfl),
     (fun _ => rfl),
     ⟨rfl, ⟨BitVec.ofNat 16 0, rfl⟩⟩⟩
  have hAsInit :
      PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
        ⟨.exclusive, .aligned, .asInitialized⟩ false mem := by
    cases hSafe.2.2 with
    | intro a ha =>
      exact ⟨hSafe.1, hSafe.2.1, a, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1,
        ha.2.2.2.2.1, validityHolds_safe_to_asInitialized _ _ ha.2.2.2.2.2⟩
  refine ⟨hNotInit, hNotDecInit, sub, mem, hSafe, hAsInit, ?_, ?_⟩
  · intro h
    cases h.2.2 with
    | intro a ha =>
      injection ha.1 with hEq
      subst hEq
      have hBad : allBytesInit bs = true := ha.2.2.2.2.2.2
      nomatch hBad
  · intro h
    cases h.2.2 with
    | intro a ha =>
      injection ha.1 with hEq
      subst hEq
      cases ha.2.2.2.2.2.2 with
      | intro _ hDec => nomatch hDec

end Anneal.Core

end
