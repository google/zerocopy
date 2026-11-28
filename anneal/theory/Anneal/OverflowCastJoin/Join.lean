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
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.Core.BlockTree
public import Anneal.Core.StageCut

public section

namespace Anneal.OverflowCastJoin

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp Anneal.MirTotal Anneal.Core

/-!
# Stage-Cut Interval Joins for `*WithOverflow` and `intToInt` (`Join`)

Provides LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`), `omega`-free
step laws and an elaborator-irreducible (`@[irreducible]`), zero-`Prop`-argument
affine-interval stage-cut barrier (`OvfCastStageCut`) for multi-diamond MIR
pipelines combining:
1. `CastKind.intToInt` narrowing and widening casts (`u32 <-> u16`),
2. Overflowing tuple arithmetic (`BinOp.mulWithOverflow` and
   `BinOp.addWithOverflow` producing `MirTy.tuple [u16, bool]`), and
3. Paired unchecked arithmetic (`BinOp.mulUnchecked`, `BinOp.addUnchecked`)
   guarded by interval bounds (`acc < 65536`).

Unlike hardcoded fixed-arity local tables, `StageIntervalStateInv` and
`OvfCastStageCut` parameterize over an arbitrary baseline local frame
(`baseLocals : List LocalSlot`) and an arbitrary quartet of distinct local
indices (`StageLocalIds`), collapsing $2^m$ unjoined diamond paths to $O(m)$
stage-cut proofs (`ovfCastStageCut_compose`) backed by `BlockTree` basic
block indexing (`ValidBlockTree`) with zero local-type-support side conditions.
-/

/-! ## Constructive Total Slot-Update Algebra (`listSetAt`) -/

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α} (hb : b = true) :
    (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) :
    (if b then t else e) = e := by
  subst hb
  rfl

private def listSetAtAux {α : Type} (xs : List α) (v : α) :
    List α × (Nat → List α) :=
  List.foldr
    (fun (x : α) (acc : List α × (Nat → List α)) =>
      (x :: acc.1,
       fun n =>
         match n with
         | 0 => v :: acc.1
         | k + 1 => x :: acc.2 k))
    ([], fun _ => [])
    xs

private theorem listSetAtAux_fst {α : Type} (xs : List α) (v : α) :
    (listSetAtAux xs v).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

/-- Total computable list update via `List.foldr` (`0` `noncomputable`):
replaces index `idx` with `v` when `idx < xs.length` and leaves `xs` unchanged
when `xs.length ≤ idx`. -/
@[expose] def listSetAt {α : Type} (xs : List α) (idx : Nat) (v : α) : List α :=
  (List.foldr
    (fun (x : α) (acc : List α × (Nat → List α)) =>
      (x :: acc.1,
       fun n =>
         match n with
         | 0 => v :: acc.1
         | k + 1 => x :: acc.2 k))
    ([], fun _ => [])
    xs).2 idx

/-- Empty-list equation for `listSetAt`. -/
theorem listSetAt_nil {α : Type} (idx : Nat) (v : α) :
    listSetAt ([] : List α) idx v = [] := rfl

/-- Zero-index equation for `listSetAt` on `x :: tl`. -/
theorem listSetAt_cons_zero {α : Type} (x : α) (tl : List α) (v : α) :
    listSetAt (x :: tl) 0 v = v :: tl :=
  congrArg (List.cons v) (listSetAtAux_fst tl v)

/-- Successor-index equation for `listSetAt` on `x :: tl`. -/
theorem listSetAt_cons_succ {α : Type} (x : α) (tl : List α) (k : Nat) (v : α) :
    listSetAt (x :: tl) (k + 1) v = x :: listSetAt tl k v := rfl

/-- `listSetAt` preserves `List.length`. -/
theorem listSetAt_length {α : Type} (xs : List α) (idx : Nat) (v : α) :
    (listSetAt xs idx v).length = xs.length := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero]
      rfl
    | succ k =>
      rw [listSetAt_cons_succ]
      exact congrArg Nat.succ (ih k)

/-- Same-index lookup law for `listSetAt` when `idx < xs.length`. -/
theorem compGetElem?_listSetAt_same {α : Type} {xs : List α} {idx : Nat}
    (v : α) (hLt : idx < xs.length) :
    compGetElem? (listSetAt xs idx v) idx = some v := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hLt)
  | cons x tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero]
      rfl
    | succ k =>
      rw [listSetAt_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ hLt)

/-- Distinct-index frame law for `listSetAt` (`j ≠ idx`). -/
theorem compGetElem?_listSetAt_ne {α : Type} (xs : List α) {idx j : Nat}
    (v : α) (hNe : j ≠ idx) :
    compGetElem? (listSetAt xs idx v) j = compGetElem? xs j := by
  induction xs generalizing idx j with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero =>
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ =>
        rw [listSetAt_cons_zero]
        rfl
    | succ k =>
      cases j with
      | zero =>
        rw [listSetAt_cons_succ]
        rfl
      | succ m =>
        rw [listSetAt_cons_succ]
        exact ih (fun hEq => hNe (congrArg Nat.succ hEq))

/-- Agreement between `compSetElem?` and `some (listSetAt xs idx v)` when
`idx < xs.length`. -/
theorem compSetElem?_eq_some_listSetAt {α : Type} {xs : List α} {idx : Nat}
    (v : α) (hLt : idx < xs.length) :
    compSetElem? xs idx v = some (listSetAt xs idx v) := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hLt)
  | cons x tl ih =>
    cases idx with
    | zero =>
      rw [compSetElem?_eq, listSetAt_cons_zero]
      rfl
    | succ k =>
      rw [listSetAt_cons_succ]
      have hSub := ih (Nat.lt_of_succ_lt_succ hLt)
      change (match compSetElem? tl k v with
          | some xs' => some (x :: xs')
          | none => none) =
        some (x :: listSetAt tl k v)
      rw [hSub]

/-- Overwriting the same index `idx` twice collapses to a single `listSetAt`. -/
theorem listSetAt_overwrite {α : Type} (xs : List α) (idx : Nat) (v₁ v₂ : α) :
    listSetAt (listSetAt xs idx v₁) idx v₂ = listSetAt xs idx v₂ := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero, listSetAt_cons_zero, listSetAt_cons_zero]
    | succ k =>
      rw [listSetAt_cons_succ, listSetAt_cons_succ, listSetAt_cons_succ]
      exact congrArg (List.cons x) (ih k)

/-- Updates at distinct indices `i ≠ j` commute under `listSetAt`. -/
theorem listSetAt_comm {α : Type} (xs : List α) {i j : Nat} (v₁ v₂ : α)
    (hNe : i ≠ j) :
    listSetAt (listSetAt xs i v₁) j v₂ =
      listSetAt (listSetAt xs j v₂) i v₁ := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x tl ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ m =>
        rw [listSetAt_cons_zero, listSetAt_cons_succ, listSetAt_cons_succ,
          listSetAt_cons_zero]
    | succ k =>
      cases j with
      | zero =>
        rw [listSetAt_cons_succ, listSetAt_cons_zero, listSetAt_cons_zero,
          listSetAt_cons_succ]
      | succ m =>
        rw [listSetAt_cons_succ, listSetAt_cons_succ, listSetAt_cons_succ,
          listSetAt_cons_succ]
        exact congrArg (List.cons x)
          (ih (fun hEq => hNe (congrArg Nat.succ hEq)))

/-! ## Unsigned `u16` / `u32` Scalar, `*WithOverflow`, and `intToInt` Laws -/

/-- Unsigned 32-bit integer `MirTy` (`u32`). -/
@[expose] def ocjU32Ty : MirTy := .int .i32 false

/-- Unsigned 16-bit integer `MirTy` (`u16`). -/
@[expose] def ocjU16Ty : MirTy := .int .i16 false

/-- Overflowing 16-bit arithmetic result tuple `MirTy` (`(u16, bool)`). -/
@[expose] def ocjOvf16Ty : MirTy := .tuple [.int .i16 false, .bool]

/-- Unsigned `u32` scalar `Val` wrapping `BitVec.ofNat 128 n`. -/
@[expose] def ocjU32Val (n : Nat) : Val := .scalar ⟨.i32, false, BitVec.ofNat
    128 n⟩

/-- Unsigned `u16` scalar `Val` wrapping `BitVec.ofNat 128 n`. -/
@[expose] def ocjU16Val (n : Nat) : Val := .scalar ⟨.i16, false, BitVec.ofNat
    128 n⟩

private theorem lt_pow128_of_lt_65536 {n : Nat} (hn : n < 65536) :
    n < Nat.pow 2 128 :=
  Nat.lt_of_lt_of_le hn (Nat.le_of_ble_eq_true rfl)

private theorem bvToNat_ofNat128_lt {n : Nat} (hn : n < Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n := by
  change Nat.mod n (Nat.pow 2 128) = n
  exact Nat.mod_eq_of_lt hn

private theorem nat_ble_false_of_lt {a b : Nat} (h : b < a) :
    Nat.ble a b = false := by
  cases hB : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hB) h)

/-- `truncateBitsComp .i16` is the identity on `BitVec.ofNat 128 n` when
`n < 65536`. -/
theorem truncateBitsComp_i16_of_lt {n : Nat} (hn : n < 65536) :
    truncateBitsComp .i16 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  rw [truncateBitsComp_eq]
  apply truncateBits_of_toNat_lt
  change (BitVec.ofNat 128 n).toNat < 65536
  rw [bvToNat_ofNat128_lt (lt_pow128_of_lt_65536 hn)]
  exact hn

/-- `truncateBitsComp .i32` is the identity on `BitVec.ofNat 128 n` when
`n < 65536`. -/
theorem truncateBitsComp_i32_of_lt {n : Nat} (hn : n < 65536) :
    truncateBitsComp .i32 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  rw [truncateBitsComp_eq]
  apply truncateBits_of_toNat_lt
  change (BitVec.ofNat 128 n).toNat < Nat.pow 2 32
  rw [bvToNat_ofNat128_lt (lt_pow128_of_lt_65536 hn)]
  exact Nat.lt_of_lt_of_le hn (Nat.le_of_ble_eq_true rfl)

private theorem bvOfIntComp_128_ofNat_lt {n : Nat} (hn : n < Nat.pow 2 128) :
    bvOfIntComp 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  unfold bvOfIntComp intEmodComp
  have hMod : Nat.mod n (Int.natAbs (Int.ofNat (Nat.pow 2 128))) = n :=
    Nat.mod_eq_of_lt hn
  change
    BitVec.ofNat 128
      (Int.ofNat (Nat.mod n (Int.natAbs (Int.ofNat (Nat.pow 2 128))))).toNat =
    BitVec.ofNat 128 n
  rw [hMod]
  rfl

/-- `decodeScalarComp` on an in-range unsigned `u16` (`n < 65536`) yields
`Int.ofNat n`. -/
theorem decodeScalarComp_u16_of_lt {n : Nat} (hn : n < 65536) :
    decodeScalarComp ⟨.i16, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalarComp
  dsimp only
  rw [ite_bool_false rfl, truncateBitsComp_i16_of_lt hn,
    bvToNat_ofNat128_lt (lt_pow128_of_lt_65536 hn)]

/-- `truncateScalarComp .i16 false (Int.ofNat n)` succeeds with `lossy = false`
when `n < 65536`. -/
theorem truncateScalarComp_u16_of_lt {n : Nat} (hn : n < 65536) :
    truncateScalarComp .i16 false (Int.ofNat n) =
      .ok (⟨.i16, false, BitVec.ofNat 128 n⟩, false) := by
  unfold truncateScalarComp
  rw [ite_bool_false rfl]
  dsimp only
  rw [bvOfIntComp_128_ofNat_lt (lt_pow128_of_lt_65536 hn),
    truncateBitsComp_i16_of_lt hn,
    (bv128BeqComp_iff (BitVec.ofNat 128 n) (BitVec.ofNat 128 n)).mpr rfl]
  rfl

/-- Narrowing `CastKind.intToInt` from `ocjU32Val n` to `ocjU16Ty` preserves
`n` when `n < 65536`. -/
theorem evalIntToIntCastComp_u32_to_u16 {n : Nat} (hn : n < 65536) :
    evalIntToIntCastComp (ocjU32Val n) ocjU16Ty = .ok (ocjU16Val n) := by
  unfold evalIntToIntCastComp intLikeBitsComp
  dsimp only [ocjU32Val, ocjU16Ty, ocjU16Val]
  rw [ite_bool_false rfl, truncateBitsComp_i32_of_lt hn,
    bvToNat_ofNat128_lt (lt_pow128_of_lt_65536 hn)]
  dsimp only
  rw [truncateBitsComp_i16_of_lt hn]

/-- Widening `CastKind.intToInt` from `ocjU16Val n` to `ocjU32Ty` preserves `n`
when `n < 65536`. -/
theorem evalIntToIntCastComp_u16_to_u32 {n : Nat} (hn : n < 65536) :
    evalIntToIntCastComp (ocjU16Val n) ocjU32Ty = .ok (ocjU32Val n) := by
  unfold evalIntToIntCastComp intLikeBitsComp
  dsimp only [ocjU16Val, ocjU32Ty, ocjU32Val]
  rw [ite_bool_false rfl, truncateBitsComp_i16_of_lt hn,
    bvToNat_ofNat128_lt (lt_pow128_of_lt_65536 hn)]
  dsimp only
  rw [truncateBitsComp_i32_of_lt hn]

/-- `checkValBy MirTy.beq (ocjU16Val n) ocjU16Ty = true` when `n < 65536`. -/
theorem checkVal_u16_lt {n : Nat} (hn : n < 65536) :
    checkValBy MirTy.beq (ocjU16Val n) ocjU16Ty = true := by
  unfold checkValBy valTy?Comp scalarWfComp ocjU16Val ocjU16Ty
  dsimp only
  rw [truncateBitsComp_i16_of_lt hn,
    (bv128BeqComp_iff (BitVec.ofNat 128 n) (BitVec.ofNat 128 n)).mpr rfl]
  rfl

/-- `checkValBy MirTy.beq (ocjU32Val n) ocjU32Ty = true` when `n < 65536`. -/
theorem checkVal_u32_lt {n : Nat} (hn : n < 65536) :
    checkValBy MirTy.beq (ocjU32Val n) ocjU32Ty = true := by
  unfold checkValBy valTy?Comp scalarWfComp ocjU32Val ocjU32Ty
  dsimp only
  rw [truncateBitsComp_i32_of_lt hn,
    (bv128BeqComp_iff (BitVec.ofNat 128 n) (BitVec.ofNat 128 n)).mpr rfl]
  rfl

/-- `checkValBy MirTy.beq (.tuple [ocjU16Val n, .bool b]) ocjOvf16Ty = true`
when `n < 65536`. -/
theorem checkVal_ovf16_lt {n : Nat} (hn : n < 65536) (b : Bool) :
    checkValBy MirTy.beq (.tuple [ocjU16Val n, .bool b]) ocjOvf16Ty = true := by
  unfold checkValBy valTy?Comp scalarWfComp ocjU16Val ocjOvf16Ty
  dsimp only
  rw [truncateBitsComp_i16_of_lt hn,
    (bv128BeqComp_iff (BitVec.ofNat 128 n) (BitVec.ofNat 128 n)).mpr rfl]
  rfl

/-- `evalConstLitComp ocjU16Ty (.scalar (BitVec.ofNat 128 n)) =
.ok (ocjU16Val n)` when `n < 65536`. -/
theorem evalConstLitComp_u16_lt {n : Nat} (hn : n < 65536) :
    evalConstLitComp ocjU16Ty (.scalar (BitVec.ofNat 128 n)) =
      .ok (ocjU16Val n) := by
  unfold evalConstLitComp ocjU16Ty ocjU16Val
  dsimp only
  rw [truncateBitsComp_i16_of_lt hn,
    (bv128BeqComp_iff (BitVec.ofNat 128 n) (BitVec.ofNat 128 n)).mpr rfl]
  rfl

private theorem evalArithOpComp_u16_add_noovf (op : BinOp) {a b : Nat}
    (hSum : a + b < 65536)
    (hOpEq : op = .addWithOverflow ∨ op = .addUnchecked) :
    evalArithOpComp op .i16 false (Int.ofNat a) (Int.ofNat b) =
      if binOpIsOverflowingComp op then
        .ok (.tuple [ocjU16Val (a + b), .bool false])
      else .ok (ocjU16Val (a + b)) := by
  have hBle128 : Nat.ble (Nat.pow 2 128) (a + b) = false :=
    nat_ble_false_of_lt (lt_pow128_of_lt_65536 hSum)
  cases hOpEq with
  | inl hEq =>
    subst hEq
    change (match truncateScalarComp .i16 false (Int.ofNat (a + b)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if (Nat.ble (Nat.pow 2 128) (a + b) || lossy) && false then
          Except.error FaultKind.undefined
        else
          Except.ok
            (Val.tuple
              [Val.scalar val,
               Val.bool (Nat.ble (Nat.pow 2 128) (a + b) || lossy)])) =
      Except.ok (Val.tuple [ocjU16Val (a + b), Val.bool false])
    rw [truncateScalarComp_u16_of_lt hSum, hBle128]
    rfl
  | inr hEq =>
    subst hEq
    change (match truncateScalarComp .i16 false (Int.ofNat (a + b)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if (Nat.ble (Nat.pow 2 128) (a + b) || lossy) && true then
          Except.error FaultKind.undefined
        else
          Except.ok (Val.scalar val)) =
      Except.ok (ocjU16Val (a + b))
    rw [truncateScalarComp_u16_of_lt hSum, hBle128]
    rfl

private theorem evalArithOpComp_u16_mul_noovf (op : BinOp) {a b : Nat}
    (hProd : a * b < 65536)
    (hOpEq : op = .mulWithOverflow ∨ op = .mulUnchecked) :
    evalArithOpComp op .i16 false (Int.ofNat a) (Int.ofNat b) =
      if binOpIsOverflowingComp op then
        .ok (.tuple [ocjU16Val (a * b), .bool false])
      else .ok (ocjU16Val (a * b)) := by
  have hBle128 : Nat.ble (Nat.pow 2 128) (a * b) = false :=
    nat_ble_false_of_lt (lt_pow128_of_lt_65536 hProd)
  cases hOpEq with
  | inl hEq =>
    subst hEq
    change (match truncateScalarComp .i16 false (Int.ofNat (a * b)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if (Nat.ble (Nat.pow 2 128) (a * b) || lossy) && false then
          Except.error FaultKind.undefined
        else
          Except.ok
            (Val.tuple
              [Val.scalar val,
               Val.bool (Nat.ble (Nat.pow 2 128) (a * b) || lossy)])) =
      Except.ok (Val.tuple [ocjU16Val (a * b), Val.bool false])
    rw [truncateScalarComp_u16_of_lt hProd, hBle128]
    rfl
  | inr hEq =>
    subst hEq
    change (match truncateScalarComp .i16 false (Int.ofNat (a * b)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if (Nat.ble (Nat.pow 2 128) (a * b) || lossy) && true then
          Except.error FaultKind.undefined
        else
          Except.ok (Val.scalar val)) =
      Except.ok (ocjU16Val (a * b))
    rw [truncateScalarComp_u16_of_lt hProd, hBle128]
    rfl

/-- Exact `BinOp.mulWithOverflow` step law on `u16` when `a * b < 65536`. -/
theorem evalBinOpComp_u16_mulWithOverflow {a b : Nat}
    (ha : a < 65536) (hb : b < 65536) (hProd : a * b < 65536) :
    evalBinOpComp .mulWithOverflow (ocjU16Val a) (ocjU16Val b) =
      .ok (.tuple [ocjU16Val (a * b), .bool false]) := by
  unfold evalBinOpComp
  dsimp only [ocjU16Val]
  rw [ite_bool_false (rfl : binOpIsShiftComp .mulWithOverflow = false)]
  rw [ite_bool_false
    (rfl : (!(intWidthBeqComp .i16 .i16 && boolBeqComp false false)) = false)]
  rw [decodeScalarComp_u16_of_lt ha, decodeScalarComp_u16_of_lt hb]
  exact evalArithOpComp_u16_mul_noovf .mulWithOverflow hProd (Or.inl rfl)

/-- Exact `BinOp.mulUnchecked` step law on `u16` when `a * b < 65536`. -/
theorem evalBinOpComp_u16_mulUnchecked {a b : Nat}
    (ha : a < 65536) (hb : b < 65536) (hProd : a * b < 65536) :
    evalBinOpComp .mulUnchecked (ocjU16Val a) (ocjU16Val b) =
      .ok (ocjU16Val (a * b)) := by
  unfold evalBinOpComp
  dsimp only [ocjU16Val]
  rw [ite_bool_false (rfl : binOpIsShiftComp .mulUnchecked = false)]
  rw [ite_bool_false
    (rfl : (!(intWidthBeqComp .i16 .i16 && boolBeqComp false false)) = false)]
  rw [decodeScalarComp_u16_of_lt ha, decodeScalarComp_u16_of_lt hb]
  exact evalArithOpComp_u16_mul_noovf .mulUnchecked hProd (Or.inr rfl)

/-- Exact `BinOp.addWithOverflow` step law on `u16` when `a + b < 65536`. -/
theorem evalBinOpComp_u16_addWithOverflow {a b : Nat}
    (ha : a < 65536) (hb : b < 65536) (hSum : a + b < 65536) :
    evalBinOpComp .addWithOverflow (ocjU16Val a) (ocjU16Val b) =
      .ok (.tuple [ocjU16Val (a + b), .bool false]) := by
  unfold evalBinOpComp
  dsimp only [ocjU16Val]
  rw [ite_bool_false (rfl : binOpIsShiftComp .addWithOverflow = false)]
  rw [ite_bool_false
    (rfl : (!(intWidthBeqComp .i16 .i16 && boolBeqComp false false)) = false)]
  rw [decodeScalarComp_u16_of_lt ha, decodeScalarComp_u16_of_lt hb]
  exact evalArithOpComp_u16_add_noovf .addWithOverflow hSum (Or.inl rfl)

/-- Exact `BinOp.addUnchecked` step law on `u16` when `a + b < 65536`. -/
theorem evalBinOpComp_u16_addUnchecked {a b : Nat}
    (ha : a < 65536) (hb : b < 65536) (hSum : a + b < 65536) :
    evalBinOpComp .addUnchecked (ocjU16Val a) (ocjU16Val b) =
      .ok (ocjU16Val (a + b)) := by
  unfold evalBinOpComp
  dsimp only [ocjU16Val]
  rw [ite_bool_false (rfl : binOpIsShiftComp .addUnchecked = false)]
  rw [ite_bool_false
    (rfl : (!(intWidthBeqComp .i16 .i16 && boolBeqComp false false)) = false)]
  rw [decodeScalarComp_u16_of_lt ha, decodeScalarComp_u16_of_lt hb]
  exact evalArithOpComp_u16_add_noovf .addUnchecked hSum (Or.inr rfl)

/-! ## `BlockTree`-Accelerated Single-Body Statement & Terminator Step Laws -/

/-- Entry `switchInt` basic block branching on `flagLocal == 1` to `trueBlk` and
otherwise to `falseBlk`. -/
@[expose] def mkOverflowCastEntryBlock (flagLocal : LocalId)
    (trueBlk falseBlk : BasicBlockId) : BasicBlock :=
  {
    statements := []
    terminator := .switchInt (.copy ⟨flagLocal, []⟩)
      ⟨[(BitVec.ofNat 128 1, trueBlk)], falseBlk⟩
    cleanup := false
  }

/-- Four local-variable indices (`accId`, `tmpId`, `ovfMulId`, `ovfAddId`)
used by a single overflow-cast diamond stage; `stageLocalIdsWf` requires all
four to be in bounds and pairwise distinct. -/
structure StageLocalIds where
  /-- Accumulator local (`u32`). -/
  accId : LocalId
  /-- Narrowed `u16` scratch local. -/
  tmpId : LocalId
  /-- `mulWithOverflow` `(u16, bool)` tuple local. -/
  ovfMulId : LocalId
  /-- `addWithOverflow` `(u16, bool)` tuple local. -/
  ovfAddId : LocalId

/-- Constructs the 6-statement `*WithOverflow` + `*Unchecked` + `intToInt` arm
block over arbitrary `ids : StageLocalIds`. -/
@[expose] def mkOverflowCastArmBlock (ids : StageLocalIds) (mulK addC joinBlk :
    Nat) :
    BasicBlock :=
  {
    statements := [
      .assign ⟨ids.tmpId, []⟩
        (.cast .intToInt (.copy ⟨ids.accId, []⟩) ocjU16Ty),
      .assign ⟨ids.ovfMulId, []⟩ (.binaryOp .mulWithOverflow
        (.copy ⟨ids.tmpId, []⟩)
        (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 mulK)⟩)),
      .assign ⟨ids.tmpId, []⟩ (.binaryOp .mulUnchecked
        (.copy ⟨ids.tmpId, []⟩)
        (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 mulK)⟩)),
      .assign ⟨ids.ovfAddId, []⟩ (.binaryOp .addWithOverflow
        (.copy ⟨ids.tmpId, []⟩)
        (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 addC)⟩)),
      .assign ⟨ids.tmpId, []⟩ (.binaryOp .addUnchecked
        (.copy ⟨ids.tmpId, []⟩)
        (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 addC)⟩)),
      .assign ⟨ids.accId, []⟩ (.cast .intToInt (.copy ⟨ids.tmpId, []⟩) ocjU32Ty)
    ]
    terminator := .goto joinBlk
    cleanup := false
  }

private theorem evalOperandToSlotComp_copy_imm
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {tyOk : MirTy → Bool} {localId : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : compGetElem? bodyLocals localId = some ty)
    (hSlot : compGetElem? locals localId = some (.immediate optVal)) :
    evalOperandToSlotComp bodyLocals locals mem tyOk (.copy ⟨localId, []⟩) =
      .ok (ty, optVal, locals, mem) := by
  unfold evalOperandToSlotComp
  dsimp only
  rw [hTy, hSlot]
  rfl

private theorem evalPrimitiveOperandComp_copy_imm
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {localId : LocalId} {ty : MirTy} {v : Val}
    (hTy : compGetElem? bodyLocals localId = some ty)
    (hSlot : compGetElem? locals localId = some (.immediate (some v)))
    (hOk : isPrimitiveReadableTyComp ty = true) :
    evalPrimitiveOperandComp bodyLocals locals mem (.copy ⟨localId, []⟩) =
      .ok (v, locals, mem) := by
  unfold evalPrimitiveOperandComp
  rw [evalOperandToSlotComp_copy_imm hTy hSlot]
  dsimp only
  rw [hOk]
  rfl

private theorem evalPrimitiveOperandComp_const_ok
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {ty : MirTy} {lit : ConstLit} {v : Val}
    (hConst : evalConstLitComp ty lit = .ok v)
    (hOk : isPrimitiveReadableTyComp ty = true) :
    evalPrimitiveOperandComp bodyLocals locals mem (.constant ⟨ty, lit⟩) =
      .ok (v, locals, mem) := by
  unfold evalPrimitiveOperandComp evalOperandToSlotComp
  dsimp only
  rw [hConst]
  dsimp only
  rw [hOk]
  rfl

/-- Evaluates `Rvalue.use (.copy ⟨srcId, []⟩)` on an initialized `.immediate`
slot. -/
theorem evalRvalue_use_copy_imm
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {srcId : LocalId} {srcTy dstTy : MirTy} {v : Val}
    (hTy : compGetElem? bodyLocals srcId = some srcTy)
    (hSlot : compGetElem? locals srcId = some (.immediate (some v)))
    (hEq : MirTy.beq srcTy dstTy = true) :
    evalRvalueBy MirTy.beq bodyLocals locals mem dstTy
        (.use (.copy ⟨srcId, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueBy
  dsimp only
  rw [evalOperandToSlotComp_copy_imm hTy hSlot]
  dsimp only
  rw [hEq, ite_bool_false (rfl : (!true) = false)]

/-- Evaluates `Rvalue.cast .intToInt (.copy ⟨srcId, []⟩) castTy` on an
initialized `.immediate` slot. -/
theorem evalRvalue_cast_intToInt_copy_imm
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {srcId : LocalId} {srcTy castTy dstTy : MirTy} {v res : Val}
    (hTy : compGetElem? bodyLocals srcId = some srcTy)
    (hSlot : compGetElem? locals srcId = some (.immediate (some v)))
    (hInt : isIntLikeTyComp srcTy = true)
    (hCast : evalIntToIntCastComp v castTy = .ok res) :
    evalRvalueBy MirTy.beq bodyLocals locals mem dstTy
        (.cast .intToInt (.copy ⟨srcId, []⟩) castTy) =
      .ok (res, locals, mem) := by
  unfold evalRvalueBy
  dsimp only
  rw [evalOperandToSlotComp_copy_imm hTy hSlot]
  dsimp only
  rw [hInt, ite_bool_false (rfl : (!true) = false), hCast]

/-- Evaluates `Rvalue.binaryOp op lhs rhs` on memory-preserving primitive
operands. -/
theorem evalRvalue_binaryOp_prim
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {dstTy : MirTy} {op : BinOp} {lhs rhs : Operand} {vl vr res : Val}
    (hLhs : evalPrimitiveOperandComp bodyLocals locals mem lhs =
      .ok (vl, locals, mem))
    (hRhs : evalPrimitiveOperandComp bodyLocals locals mem rhs =
      .ok (vr, locals, mem))
    (hBin : evalBinOpComp op vl vr = .ok res) :
    evalRvalueBy MirTy.beq bodyLocals locals mem dstTy (.binaryOp op lhs rhs) =
      .ok (res, locals, mem) := by
  unfold evalRvalueBy
  dsimp only
  rw [hLhs]
  dsimp only
  rw [hRhs]
  dsimp only
  rw [hBin]

/-- Writes `val` to an `.immediate` local slot via `listSetAt` when
`dstLocalId < locals.length`. -/
theorem writePlace_imm_listSetAt
    {locals : List LocalSlot} (mem : MemoryState)
    {dstLocalId : LocalId} {dstTy : MirTy} {old : Option Val} {val : Val}
    (hChk : checkValBy MirTy.beq val dstTy = true)
    (hSlot : compGetElem? locals dstLocalId = some (.immediate old))
    (hLt : dstLocalId < locals.length) :
    writePlaceBy MirTy.beq locals mem dstLocalId dstTy val =
      .ok (listSetAt locals dstLocalId (.immediate (some val)), mem) := by
  unfold writePlaceBy
  rw [hChk, ite_bool_false (rfl : (!true) = false), hSlot]
  dsimp only
  rw [compSetElem?_eq_some_listSetAt (.immediate (some val)) hLt]

/-- Single-step `evalStep (bodyProg body) 0` transition for an immediate-slot
assignment indexed through any valid `BlockTree BasicBlock`. -/
theorem evalStep_bodyProg_block_assign {body : Body} {bt : BlockTree BasicBlock}
    {bb : BasicBlock} {blockIdx stmtIdx : Nat}
    {locals locals' locals'' : List LocalSlot}
    {cm : CallerMemory} {mem mem' mem'' : MemoryState}
    {dstId : LocalId} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hBlk : bt.lookup blockIdx = some bb)
    (hStmt : compGetElem? bb.statements stmtIdx = some (.assign ⟨dstId, []⟩ rv))
    (hTy : compGetElem? body.locals dstId = some dstTy)
    (hRv : evalRvalueBy MirTy.beq body.locals locals mem dstTy rv =
      .ok (v, locals', mem'))
    (hWr : writePlaceBy MirTy.beq locals' mem' dstId dstTy v =
      .ok (locals'', mem'')) :
    evalStep (bodyProg body) 0
        { frames := [{ defId := 0, blockIdx := blockIdx, stmtIdx := stmtIdx,
                       locals := locals }],
          callerMem := cm, mem := mem } =
      .step {
        frames := [{ defId := 0, blockIdx := blockIdx, stmtIdx := stmtIdx + 1,
                     locals := locals'' }]
        callerMem := cm
        mem := mem''
      } := by
  rw [← evalMirStepBlockTreeBy_eq_evalStep MirTy.beq (fun _ _ => rfl) hValid]
  unfold evalMirStepBlockTreeBy
  dsimp only
  rw [ite_bool_false (rfl : (!Nat.beq 0 0) = false), hBlk]
  dsimp only
  rw [hStmt]
  unfold evalStatementBy
  dsimp only
  rw [ite_bool_false (rfl : (![].isEmpty) = false), hTy]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hWr]

/-- Single-step `evalStep (bodyProg body) 0` transition at the end of a basic
block (`stmtIdx = bb.statements.length`), reducing to `evalTerminatorComp`. -/
theorem evalStep_bodyProg_block_term {body : Body} {bt : BlockTree BasicBlock}
    {bb : BasicBlock} {blockIdx stmtIdx : Nat} {locals : List LocalSlot}
    {cm : CallerMemory} {mem : MemoryState}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hBlk : bt.lookup blockIdx = some bb)
    (hNone : compGetElem? bb.statements stmtIdx = none)
    (hLen : stmtIdx = bb.statements.length)
    (hNoCall : (match bb.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => false
      | _ => true) = true := by rfl) :
    evalStep (bodyProg body) 0
        { frames := [{ defId := 0, blockIdx := blockIdx, stmtIdx := stmtIdx,
                       locals := locals }],
          callerMem := cm, mem := mem } =
      evalTerminatorComp body bb
        { defId := 0, blockIdx := blockIdx, stmtIdx := stmtIdx,
          locals := locals } mem cm := by
  subst hLen
  rw [← evalMirStepBlockTreeBy_eq_evalStep MirTy.beq (fun _ _ => rfl) hValid]
  unfold evalMirStepBlockTreeBy
  dsimp only
  rw [ite_bool_false (rfl : (!Nat.beq 0 0) = false), hBlk]
  dsimp only
  rw [hNone]
  dsimp only
  rw [ite_bool_true (Nat.beq_refl bb.statements.length)]
  cases hTerm : bb.terminator with
  | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
    rw [hTerm] at hNoCall
    cases hNoCall
  | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
  | assert _ _ _ _ _ | coreCall _ _ _ _ _ | callNe _ _ _ _ _ | drop _ _ _
  | unsupported => rfl

/-- Single-step `evalStep (bodyProg body) 0` transition for
`mkOverflowCastEntryBlock flagLocal targetTrue targetFalse`. -/
theorem evalStep_bodyProg_switchBool {body : Body} {bt : BlockTree BasicBlock}
    {bb : BasicBlock} {blockIdx targetTrue targetFalse : Nat}
    {flagLocal : LocalId} {locals : List LocalSlot}
    {cm : CallerMemory} {mem : MemoryState} {flagVal : Bool}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hBlk : bt.lookup blockIdx = some bb)
    (hTerm : bb = mkOverflowCastEntryBlock flagLocal targetTrue targetFalse)
    (hTy : compGetElem? body.locals flagLocal = some .bool)
    (hSlot : compGetElem? locals flagLocal =
      some (.immediate (some (.bool flagVal)))) :
    evalStep (bodyProg body) 0
        { frames := [{ defId := 0, blockIdx := blockIdx, stmtIdx := 0,
                       locals := locals }],
          callerMem := cm, mem := mem } =
      .step {
        frames := [{ defId := 0,
                     blockIdx := if flagVal then targetTrue else targetFalse,
                     stmtIdx := 0, locals := locals }]
        callerMem := cm
        mem := mem
      } := by
  subst hTerm
  rw [evalStep_bodyProg_block_term (stmtIdx := 0) hValid hBlk rfl rfl]
  unfold mkOverflowCastEntryBlock evalTerminatorComp
  dsimp only
  rw [evalPrimitiveOperandComp_copy_imm hTy hSlot rfl]
  cases flagVal <;> rfl

/-! ## Parametric `OvfCastStageCut` & Linear Interval-Hull Join -/

/-- Cutpoint node pairing a CFG `blockIdx` with closed unsigned accumulator
bounds `[lo, hi]`. -/
structure OverflowCastCutNode where
  /-- Basic-block index at the stage entry or join cutpoint (`stmtIdx = 0`). -/
  blockIdx : BasicBlockId
  /-- Inclusive lower bound on the `u32` accumulator `acc`. -/
  lo : Nat
  /-- Inclusive upper bound on the `u32` accumulator `acc` (`hi < 65536`). -/
  hi : Nat

/-- Decidable well-formedness check ensuring the four stage local indices lie
in bounds (`< numLocals`) and are pairwise distinct. -/
@[expose] def stageLocalIdsWf (ids : StageLocalIds) (numLocals : Nat) : Bool :=
  Nat.blt ids.accId numLocals &&
    Nat.blt ids.tmpId numLocals &&
    Nat.blt ids.ovfMulId numLocals &&
    Nat.blt ids.ovfAddId numLocals &&
    !Nat.beq ids.accId ids.tmpId &&
    !Nat.beq ids.accId ids.ovfMulId &&
    !Nat.beq ids.accId ids.ovfAddId &&
    !Nat.beq ids.tmpId ids.ovfMulId &&
    !Nat.beq ids.tmpId ids.ovfAddId &&
    !Nat.beq ids.ovfMulId ids.ovfAddId

private theorem and_eq_true_elim {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem ne_of_not_beq {a b : Nat} (h : (!Nat.beq a b) = true) :
    a ≠ b := by
  intro hEq
  subst hEq
  rw [Nat.beq_refl a] at h
  cases h

private structure StageIdsUnpacked (ids : StageLocalIds)
    (numLocals : Nat) : Prop where
  accLt : ids.accId < numLocals
  tmpLt : ids.tmpId < numLocals
  mulLt : ids.ovfMulId < numLocals
  addLt : ids.ovfAddId < numLocals
  accNeTmp : ids.accId ≠ ids.tmpId
  accNeMul : ids.accId ≠ ids.ovfMulId
  accNeAdd : ids.accId ≠ ids.ovfAddId
  tmpNeMul : ids.tmpId ≠ ids.ovfMulId
  tmpNeAdd : ids.tmpId ≠ ids.ovfAddId
  mulNeAdd : ids.ovfMulId ≠ ids.ovfAddId

private theorem unpack_stageLocalIdsWf {ids : StageLocalIds} {numLocals : Nat}
    (h : stageLocalIdsWf ids numLocals = true) :
    StageIdsUnpacked ids numLocals := by
  unfold stageLocalIdsWf at h
  let ⟨h1, hMulNeAdd⟩ := and_eq_true_elim h
  let ⟨h2, hTmpNeAdd⟩ := and_eq_true_elim h1
  let ⟨h3, hTmpNeMul⟩ := and_eq_true_elim h2
  let ⟨h4, hAccNeAdd⟩ := and_eq_true_elim h3
  let ⟨h5, hAccNeMul⟩ := and_eq_true_elim h4
  let ⟨h6, hAccNeTmp⟩ := and_eq_true_elim h5
  let ⟨h7, hAddLt⟩ := and_eq_true_elim h6
  let ⟨h8, hMulLt⟩ := and_eq_true_elim h7
  let ⟨hAccLt, hTmpLt⟩ := and_eq_true_elim h8
  exact {
    accLt := Nat.blt_eq.mp hAccLt
    tmpLt := Nat.blt_eq.mp hTmpLt
    mulLt := Nat.blt_eq.mp hMulLt
    addLt := Nat.blt_eq.mp hAddLt
    accNeTmp := ne_of_not_beq hAccNeTmp
    accNeMul := ne_of_not_beq hAccNeMul
    accNeAdd := ne_of_not_beq hAccNeAdd
    tmpNeMul := ne_of_not_beq hTmpNeMul
    tmpNeAdd := ne_of_not_beq hTmpNeAdd
    mulNeAdd := ne_of_not_beq hMulNeAdd
  }

/-- Updates `(accId, tmpId, ovfMulId, ovfAddId)` on top of `baseLocals` while
preserving every other local slot in `baseLocals`. -/
@[expose] def applyStageSlots (baseLocals : List LocalSlot) (ids :
    StageLocalIds)
    (acc : Nat) (oTmp oMul oAdd : Option Val) : List LocalSlot :=
  listSetAt
    (listSetAt
      (listSetAt
        (listSetAt baseLocals ids.accId (.immediate (some (ocjU32Val acc))))
        ids.tmpId (.immediate oTmp))
      ids.ovfMulId (.immediate oMul))
    ids.ovfAddId (.immediate oAdd)

/-- Constructs a single-frame MIR state at `(blockIdx, stmtIdx)` with
`applyStageSlots baseLocals ids acc oTmp oMul oAdd`. -/
@[expose] def mkStageState (blockIdx stmtIdx : Nat) (baseLocals : List
    LocalSlot)
    (ids : StageLocalIds) (acc : Nat) (oTmp oMul oAdd : Option Val)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  {
    frames := [{
      defId := 0
      blockIdx := blockIdx
      stmtIdx := stmtIdx
      locals := applyStageSlots baseLocals ids acc oTmp oMul oAdd
    }]
    callerMem := cm
    mem := mem
  }

private theorem applyStageSlots_length (baseLocals : List LocalSlot)
    (ids : StageLocalIds) (acc : Nat) (oTmp oMul oAdd : Option Val) :
    (applyStageSlots baseLocals ids acc oTmp oMul oAdd).length =
      baseLocals.length := by
  unfold applyStageSlots
  rw [listSetAt_length, listSetAt_length, listSetAt_length, listSetAt_length]

private theorem applyStageSlots_get_acc {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc : Nat) (oTmp oMul oAdd : Option Val) :
    compGetElem? (applyStageSlots baseLocals ids acc oTmp oMul oAdd) ids.accId =
      some (.immediate (some (ocjU32Val acc))) := by
  unfold applyStageSlots
  rw [compGetElem?_listSetAt_ne _ _ u.accNeAdd,
    compGetElem?_listSetAt_ne _ _ u.accNeMul,
    compGetElem?_listSetAt_ne _ _ u.accNeTmp,
    compGetElem?_listSetAt_same _ u.accLt]

private theorem applyStageSlots_get_tmp {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc : Nat) (oTmp oMul oAdd : Option Val) :
    compGetElem? (applyStageSlots baseLocals ids acc oTmp oMul oAdd) ids.tmpId =
      some (.immediate oTmp) := by
  unfold applyStageSlots
  rw [compGetElem?_listSetAt_ne _ _ u.tmpNeAdd,
    compGetElem?_listSetAt_ne _ _ u.tmpNeMul]
  have hLen1 :
      (listSetAt baseLocals ids.accId
        (.immediate (some (ocjU32Val acc)))).length =
        baseLocals.length := listSetAt_length _ _ _
  exact compGetElem?_listSetAt_same _ (by rw [hLen1]; exact u.tmpLt)

private theorem applyStageSlots_get_mul {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc : Nat) (oTmp oMul oAdd : Option Val) :
    compGetElem? (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
        ids.ovfMulId =
      some (.immediate oMul) := by
  unfold applyStageSlots
  rw [compGetElem?_listSetAt_ne _ _ u.mulNeAdd]
  have hLen2 :
      (listSetAt
        (listSetAt baseLocals ids.accId (.immediate (some (ocjU32Val acc))))
        ids.tmpId (.immediate oTmp)).length = baseLocals.length := by
    rw [listSetAt_length, listSetAt_length]
  exact compGetElem?_listSetAt_same _ (by rw [hLen2]; exact u.mulLt)

private theorem applyStageSlots_get_add {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc : Nat) (oTmp oMul oAdd : Option Val) :
    compGetElem? (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
        ids.ovfAddId =
      some (.immediate oAdd) := by
  unfold applyStageSlots
  have hLen3 :
      (listSetAt
        (listSetAt
          (listSetAt baseLocals ids.accId (.immediate (some (ocjU32Val acc))))
          ids.tmpId (.immediate oTmp))
        ids.ovfMulId (.immediate oMul)).length = baseLocals.length := by
    rw [listSetAt_length, listSetAt_length, listSetAt_length]
  exact compGetElem?_listSetAt_same _ (by rw [hLen3]; exact u.addLt)

/-- Any local index distinct from `(accId, tmpId, ovfMulId, ovfAddId)` retains
its baseline slot across `applyStageSlots`. -/
theorem applyStageSlots_get_other (baseLocals : List LocalSlot)
    (ids : StageLocalIds) (acc : Nat) (oTmp oMul oAdd : Option Val)
    {j : LocalId} (h1 : j ≠ ids.accId) (h2 : j ≠ ids.tmpId)
    (h3 : j ≠ ids.ovfMulId) (h4 : j ≠ ids.ovfAddId) :
    compGetElem? (applyStageSlots baseLocals ids acc oTmp oMul oAdd) j =
      compGetElem? baseLocals j := by
  unfold applyStageSlots
  rw [compGetElem?_listSetAt_ne _ _ h4,
    compGetElem?_listSetAt_ne _ _ h3,
    compGetElem?_listSetAt_ne _ _ h2,
    compGetElem?_listSetAt_ne _ _ h1]

private theorem applyStageSlots_set_tmp {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc : Nat) (oTmp oTmp' oMul oAdd : Option Val) :
    listSetAt (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
        ids.tmpId (.immediate oTmp') =
      applyStageSlots baseLocals ids acc oTmp' oMul oAdd := by
  unfold applyStageSlots
  rw [listSetAt_comm _ _ _ u.tmpNeAdd.symm,
    listSetAt_comm
      (listSetAt
        (listSetAt baseLocals ids.accId (.immediate (some (ocjU32Val acc))))
        ids.tmpId (.immediate oTmp)) _ _ u.tmpNeMul.symm,
    listSetAt_overwrite]

private theorem applyStageSlots_set_mul {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc : Nat) (oTmp oMul oMul' oAdd : Option Val) :
    listSetAt (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
        ids.ovfMulId (.immediate oMul') =
      applyStageSlots baseLocals ids acc oTmp oMul' oAdd := by
  unfold applyStageSlots
  rw [listSetAt_comm _ _ _ u.mulNeAdd.symm, listSetAt_overwrite]

private theorem applyStageSlots_set_add (baseLocals : List LocalSlot)
    (ids : StageLocalIds) (acc : Nat) (oTmp oMul oAdd oAdd' : Option Val) :
    listSetAt (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
        ids.ovfAddId (.immediate oAdd') =
      applyStageSlots baseLocals ids acc oTmp oMul oAdd' := by
  unfold applyStageSlots
  exact listSetAt_overwrite _ _ _ _

private theorem applyStageSlots_set_acc {baseLocals : List LocalSlot}
    {ids : StageLocalIds} (u : StageIdsUnpacked ids baseLocals.length)
    (acc acc' : Nat) (oTmp oMul oAdd : Option Val) :
    listSetAt (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
        ids.accId (.immediate (some (ocjU32Val acc'))) =
      applyStageSlots baseLocals ids acc' oTmp oMul oAdd := by
  unfold applyStageSlots
  rw [listSetAt_comm _ _ _ u.accNeAdd.symm,
    listSetAt_comm
      (listSetAt
        (listSetAt baseLocals ids.accId (.immediate (some (ocjU32Val acc))))
        ids.tmpId (.immediate oTmp)) _ _ u.accNeMul.symm,
    listSetAt_comm
      (listSetAt baseLocals ids.accId (.immediate (some (ocjU32Val acc))))
      _ _ u.accNeTmp.symm,
    listSetAt_overwrite]

/-- Executes all 6 statements + `goto joinBlk` of `mkOverflowCastArmBlock` in
`7` deterministic `wpUntilCutStep` transitions over any valid `BlockTree`. -/
theorem step_overflowCast_arm
    {body : Body} {bt : BlockTree BasicBlock} {baseLocals : List LocalSlot}
    {ids : StageLocalIds} {armBlk joinBlk mulK addC : Nat}
    {acc : Nat} {oTmp oMul oAdd : Option Val}
    {cm : CallerMemory} {mem : MemoryState}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hIdsWf : stageLocalIdsWf ids baseLocals.length = true)
    (hLocAcc : compGetElem? body.locals ids.accId = some ocjU32Ty)
    (hLocTmp : compGetElem? body.locals ids.tmpId = some ocjU16Ty)
    (hLocMul : compGetElem? body.locals ids.ovfMulId = some ocjOvf16Ty)
    (hLocAdd : compGetElem? body.locals ids.ovfAddId = some ocjOvf16Ty)
    (hTree : bt.lookup armBlk =
      some (mkOverflowCastArmBlock ids mulK addC joinBlk))
    (hAcc : acc < 65536) (hMulK : mulK < 65536) (hAddC : addC < 65536)
    (hProd : acc * mulK < 65536) (hRes : acc * mulK + addC < 65536)
    {P : State → Prop}
    (hPost : P (mkStageState joinBlk 0 baseLocals ids
      (acc * mulK + addC)
      (some (ocjU16Val (acc * mulK + addC)))
      (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
      (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false])) cm mem)) :
    wpUntilCutStep (evalStep (bodyProg body) 0) P 7
      (mkStageState armBlk 0 baseLocals ids acc oTmp oMul oAdd cm mem) := by
  have u := unpack_stageLocalIdsWf hIdsWf
  have hLenEq (a : Nat) (t m d : Option Val) :
      (applyStageSlots baseLocals ids a t m d).length = baseLocals.length :=
    applyStageSlots_length baseLocals ids a t m d
  -- Step 1 (stmt 0): `tmpId := Cast(.intToInt, copy accId, ocjU16Ty)`
  have hS0 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 0 baseLocals ids acc oTmp oMul oAdd cm mem) =
      .step (mkStageState armBlk 1 baseLocals ids acc
        (some (ocjU16Val acc)) oMul oAdd cm mem) := by
    unfold mkStageState
    have hWr := writePlace_imm_listSetAt mem (checkVal_u16_lt hAcc)
      (applyStageSlots_get_tmp u acc oTmp oMul oAdd)
      (by rw [hLenEq]; exact u.tmpLt)
    rw [applyStageSlots_set_tmp u] at hWr
    exact evalStep_bodyProg_block_assign hValid hTree rfl hLocTmp
      (evalRvalue_cast_intToInt_copy_imm hLocAcc
        (applyStageSlots_get_acc u acc oTmp oMul oAdd) rfl
        (evalIntToIntCastComp_u32_to_u16 hAcc))
      hWr
  -- Step 2 (stmt 1): `ovfMulId := mulWithOverflow(copy tmpId, const mulK)`
  have hS1 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 1 baseLocals ids acc
          (some (ocjU16Val acc)) oMul oAdd cm mem) =
      .step (mkStageState armBlk 2 baseLocals ids acc
        (some (ocjU16Val acc))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd cm mem) := by
    unfold mkStageState
    have hWr := writePlace_imm_listSetAt mem (checkVal_ovf16_lt hProd false)
      (applyStageSlots_get_mul u acc (some (ocjU16Val acc)) oMul oAdd)
      (by rw [hLenEq]; exact u.mulLt)
    rw [applyStageSlots_set_mul u] at hWr
    exact evalStep_bodyProg_block_assign hValid hTree rfl hLocMul
      (evalRvalue_binaryOp_prim
        (evalPrimitiveOperandComp_copy_imm hLocTmp
          (applyStageSlots_get_tmp u acc (some (ocjU16Val acc)) oMul oAdd) rfl)
        (evalPrimitiveOperandComp_const_ok (evalConstLitComp_u16_lt hMulK) rfl)
        (evalBinOpComp_u16_mulWithOverflow hAcc hMulK hProd))
      hWr
  -- Step 3 (stmt 2): `tmpId := mulUnchecked(copy tmpId, const mulK)`
  have hS2 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 2 baseLocals ids acc
          (some (ocjU16Val acc))
          (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd cm mem) =
      .step (mkStageState armBlk 3 baseLocals ids acc
        (some (ocjU16Val (acc * mulK)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd cm mem) := by
    unfold mkStageState
    have hWr := writePlace_imm_listSetAt mem (checkVal_u16_lt hProd)
      (applyStageSlots_get_tmp u acc (some (ocjU16Val acc))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd)
      (by rw [hLenEq]; exact u.tmpLt)
    rw [applyStageSlots_set_tmp u] at hWr
    exact evalStep_bodyProg_block_assign hValid hTree rfl hLocTmp
      (evalRvalue_binaryOp_prim
        (evalPrimitiveOperandComp_copy_imm hLocTmp
          (applyStageSlots_get_tmp u acc (some (ocjU16Val acc))
            (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd) rfl)
        (evalPrimitiveOperandComp_const_ok (evalConstLitComp_u16_lt hMulK) rfl)
        (evalBinOpComp_u16_mulUnchecked hAcc hMulK hProd))
      hWr
  -- Step 4 (stmt 3): `ovfAddId := addWithOverflow(copy tmpId, const addC)`
  have hS3 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 3 baseLocals ids acc
          (some (ocjU16Val (acc * mulK)))
          (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd cm mem) =
      .step (mkStageState armBlk 4 baseLocals ids acc
        (some (ocjU16Val (acc * mulK)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
        (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false]))
        cm mem) := by
    unfold mkStageState
    have hWr := writePlace_imm_listSetAt mem (checkVal_ovf16_lt hRes false)
      (applyStageSlots_get_add u acc (some (ocjU16Val (acc * mulK)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd)
      (by rw [hLenEq]; exact u.addLt)
    rw [applyStageSlots_set_add] at hWr
    exact evalStep_bodyProg_block_assign hValid hTree rfl hLocAdd
      (evalRvalue_binaryOp_prim
        (evalPrimitiveOperandComp_copy_imm hLocTmp
          (applyStageSlots_get_tmp u acc (some (ocjU16Val (acc * mulK)))
            (some (.tuple [ocjU16Val (acc * mulK), .bool false])) oAdd) rfl)
        (evalPrimitiveOperandComp_const_ok (evalConstLitComp_u16_lt hAddC) rfl)
        (evalBinOpComp_u16_addWithOverflow hProd hAddC hRes))
      hWr
  -- Step 5 (stmt 4): `tmpId := addUnchecked(copy tmpId, const addC)`
  have hS4 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 4 baseLocals ids acc
          (some (ocjU16Val (acc * mulK)))
          (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
          (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false])) cm mem) =
      .step (mkStageState armBlk 5 baseLocals ids acc
        (some (ocjU16Val (acc * mulK + addC)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
        (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false]))
        cm mem) := by
    unfold mkStageState
    have hWr := writePlace_imm_listSetAt mem (checkVal_u16_lt hRes)
      (applyStageSlots_get_tmp u acc (some (ocjU16Val (acc * mulK)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
        (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false])))
      (by rw [hLenEq]; exact u.tmpLt)
    rw [applyStageSlots_set_tmp u] at hWr
    exact evalStep_bodyProg_block_assign hValid hTree rfl hLocTmp
      (evalRvalue_binaryOp_prim
        (evalPrimitiveOperandComp_copy_imm hLocTmp
          (applyStageSlots_get_tmp u acc (some (ocjU16Val (acc * mulK)))
            (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
            (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false]))) rfl)
        (evalPrimitiveOperandComp_const_ok (evalConstLitComp_u16_lt hAddC) rfl)
        (evalBinOpComp_u16_addUnchecked hProd hAddC hRes))
      hWr
  -- Step 6 (stmt 5): `accId := Cast(.intToInt, copy tmpId, ocjU32Ty)`
  have hS5 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 5 baseLocals ids acc
          (some (ocjU16Val (acc * mulK + addC)))
          (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
          (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false])) cm mem) =
      .step (mkStageState armBlk 6 baseLocals ids (acc * mulK + addC)
        (some (ocjU16Val (acc * mulK + addC)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
        (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false]))
        cm mem) := by
    unfold mkStageState
    have hWr := writePlace_imm_listSetAt mem (checkVal_u32_lt hRes)
      (applyStageSlots_get_acc u acc (some (ocjU16Val (acc * mulK + addC)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
        (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false])))
      (by rw [hLenEq]; exact u.accLt)
    rw [applyStageSlots_set_acc u] at hWr
    exact evalStep_bodyProg_block_assign hValid hTree rfl hLocAcc
      (evalRvalue_cast_intToInt_copy_imm hLocTmp
        (applyStageSlots_get_tmp u acc (some (ocjU16Val (acc * mulK + addC)))
          (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
          (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false]))) rfl
        (evalIntToIntCastComp_u16_to_u32 hRes))
      hWr
  -- Step 7 (terminator): `goto joinBlk`
  have hS6 :
      evalStep (bodyProg body) 0
        (mkStageState armBlk 6 baseLocals ids (acc * mulK + addC)
          (some (ocjU16Val (acc * mulK + addC)))
          (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
          (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false])) cm mem) =
      .step (mkStageState joinBlk 0 baseLocals ids (acc * mulK + addC)
        (some (ocjU16Val (acc * mulK + addC)))
        (some (.tuple [ocjU16Val (acc * mulK), .bool false]))
        (some (.tuple [ocjU16Val (acc * mulK + addC), .bool false]))
        cm mem) := by
    unfold mkStageState
    rw [evalStep_bodyProg_block_term (stmtIdx := 6) hValid hTree rfl rfl]
    rfl
  exact wpUntilCutStep_step hS0
    (wpUntilCutStep_step hS1
      (wpUntilCutStep_step hS2
        (wpUntilCutStep_step hS3
          (wpUntilCutStep_step hS4
            (wpUntilCutStep_step hS5
              (wpUntilCutStep_step hS6
                (wpUntilCutStep_here 0 hPost)))))))

/-- Cutpoint state invariant asserting `s` sits at a single `defId := 0` frame
at `(node.blockIdx, 0)` with `callerMem = ⟨[]⟩` and `applyStageSlots baseLocals
ids acc oTmp oMul oAdd` for some `acc ∈ [node.lo, node.hi]` (`node.hi < 65536`),
existentially abstracting `mem`, `oTmp`, `oMul`, and `oAdd`. -/
@[expose] def StageIntervalStateInv (baseLocals : List LocalSlot) (ids :
    StageLocalIds)
    (node : OverflowCastCutNode) (s : State) : Prop :=
  ∃ (acc : Nat) (oTmp oMul oAdd : Option Val) (mem : MemoryState),
    s = mkStageState node.blockIdx 0 baseLocals ids acc oTmp oMul oAdd
      ⟨[]⟩ mem ∧
    node.lo ≤ acc ∧ acc ≤ node.hi ∧ node.hi < 65536

/-- Underlying unsealed specification of `OvfCastStageCut`: every state
satisfying `StageIntervalStateInv baseLocals ids srcNode` reaches
`StageIntervalStateInv baseLocals ids dstNode` within `stepFuel` steps of
`evalStep (bodyProg body) 0` whenever `ValidBlockTree body.basicBlocks bt`. -/
@[expose] def denoteOvfCastStageCut (body : Body) (bt : BlockTree BasicBlock)
    (baseLocals : List LocalSlot) (ids : StageLocalIds)
    (srcNode dstNode : OverflowCastCutNode) (stepFuel : Nat) : Prop :=
  ValidBlockTree body.basicBlocks bt →
  ∀ s : State,
    StageIntervalStateInv baseLocals ids srcNode s →
    wpUntilCutStep (evalStep (bodyProg body) 0)
      (StageIntervalStateInv baseLocals ids dstNode) stepFuel s

/-- Zero-`Prop`-argument Hoare-style stage-cut barrier for affine-interval
`*WithOverflow` + `CastKind.intToInt` diamond stages, marked
elaborator-irreducible (`@[irreducible]`) below so `rw`, `simp`, and `dsimp` do
not traverse interior symbolic states when chaining stages via
`ovfCastStageCut_compose`. End-to-end non-vacuity is anchored by `hValid` and
`hEntry` in `wpOutcomeState_of_ovfCastStageCut_and_exit`. -/
@[expose] def OvfCastStageCut (body : Body) (bt : BlockTree BasicBlock)
    (baseLocals : List LocalSlot) (ids : StageLocalIds)
    (srcNode dstNode : OverflowCastCutNode) (stepFuel : Nat) : Prop :=
  denoteOvfCastStageCut body bt baseLocals ids srcNode dstNode stepFuel

/-- Seals a `denoteOvfCastStageCut` proof into `OvfCastStageCut`. -/
theorem seal_ovfCastStageCut {body : Body} {bt : BlockTree BasicBlock}
    {baseLocals : List LocalSlot} {ids : StageLocalIds}
    {srcNode dstNode : OverflowCastCutNode} {stepFuel : Nat}
    (h : denoteOvfCastStageCut body bt baseLocals ids srcNode dstNode
      stepFuel) :
    OvfCastStageCut body bt baseLocals ids srcNode dstNode stepFuel :=
  h

/-- Unseals `OvfCastStageCut` into `denoteOvfCastStageCut`. -/
theorem open_ovfCastStageCut {body : Body} {bt : BlockTree BasicBlock}
    {baseLocals : List LocalSlot} {ids : StageLocalIds}
    {srcNode dstNode : OverflowCastCutNode} {stepFuel : Nat}
    (h : OvfCastStageCut body bt baseLocals ids srcNode dstNode stepFuel) :
    denoteOvfCastStageCut body bt baseLocals ids srcNode dstNode
      stepFuel :=
  h

/-- Sequential composition of `OvfCastStageCut` segments (`f₁ + f₂` steps)
in $O(1)$ kernel inference steps. -/
theorem ovfCastStageCut_compose {body : Body} {bt : BlockTree BasicBlock}
    {baseLocals : List LocalSlot} {ids : StageLocalIds}
    {n0 n1 n2 : OverflowCastCutNode} {f1 f2 : Nat}
    (h1 : OvfCastStageCut body bt baseLocals ids n0 n1 f1)
    (h2 : OvfCastStageCut body bt baseLocals ids n1 n2 f2) :
    OvfCastStageCut body bt baseLocals ids n0 n2 (f1 + f2) :=
  seal_ovfCastStageCut (fun hValid s hInv0 =>
    wpUntilCutStep_trans
      (open_ovfCastStageCut h1 hValid s hInv0)
      (fun st hInv1 => open_ovfCastStageCut h2 hValid st hInv1))

/-- Joins an entry `wpUntilCutStep` prefix, a composed `OvfCastStageCut`
chain, and an exit `wpOutcomeState` suffix into a single `wpOutcomeState
(bodyProg body)` derivation. -/
theorem wpOutcomeState_of_ovfCastStageCut_and_exit
    {body : Body} {bt : BlockTree BasicBlock}
    {baseLocals : List LocalSlot} {ids : StageLocalIds}
    {n0 nEnd : OverflowCastCutNode} {fEntry fChain fExit : Nat}
    {s0 : State} {post : TerminalOut → Prop}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hEntry : wpUntilCutStep (evalStep (bodyProg body) 0)
      (StageIntervalStateInv baseLocals ids n0) fEntry s0)
    (hChain : OvfCastStageCut body bt baseLocals ids n0 nEnd fChain)
    (hExit : ∀ st : State, StageIntervalStateInv baseLocals ids nEnd st →
      wpOutcomeState (bodyProg body) post (fun _ => False) fExit st) :
    wpOutcomeState (bodyProg body) post (fun _ => False)
      (fEntry + fChain + fExit) s0 :=
  wpOutcomeState_of_wpUntilCutMir
    (wpUntilCutStep_trans hEntry
      (fun st hInv0 => open_ovfCastStageCut hChain hValid st hInv0))
    hExit

attribute [irreducible] OvfCastStageCut

/-- Proves and seals a single 8-step diamond stage (`switchInt` on `flagLocal`
branching to `mkOverflowCastArmBlock ids tMul tAdd joinBlk` vs.
`mkOverflowCastArmBlock ids fMul fAdd joinBlk`) into an `OvfCastStageCut`
establishing `[lo, hi] -> [loNext, hiNext]` across both boolean branch outcomes.
-/
theorem seal_ovfCast_stage
    {body : Body} {bt : BlockTree BasicBlock}
    {baseLocals : List LocalSlot} {ids : StageLocalIds}
    {entryBlk flagLocal tBlk fBlk joinBlk tMul tAdd fMul fAdd : Nat}
    {lo hi loNext hiNext : Nat} {flagVal : Bool}
    (hIdsWf : stageLocalIdsWf ids baseLocals.length = true)
    (hLocAcc : compGetElem? body.locals ids.accId = some ocjU32Ty)
    (hLocTmp : compGetElem? body.locals ids.tmpId = some ocjU16Ty)
    (hLocMul : compGetElem? body.locals ids.ovfMulId = some ocjOvf16Ty)
    (hLocAdd : compGetElem? body.locals ids.ovfAddId = some ocjOvf16Ty)
    (hEntryTree : bt.lookup entryBlk =
      some (mkOverflowCastEntryBlock flagLocal tBlk fBlk))
    (hTrueTree : bt.lookup tBlk =
      some (mkOverflowCastArmBlock ids tMul tAdd joinBlk))
    (hFalseTree : bt.lookup fBlk =
      some (mkOverflowCastArmBlock ids fMul fAdd joinBlk))
    (hFlagTy : compGetElem? body.locals flagLocal = some .bool)
    (hFlagDisj :
      (!Nat.beq flagLocal ids.accId &&
        !Nat.beq flagLocal ids.tmpId &&
        !Nat.beq flagLocal ids.ovfMulId &&
        !Nat.beq flagLocal ids.ovfAddId) = true)
    (hFlagBase : compGetElem? baseLocals flagLocal =
      some (.immediate (some (.bool flagVal))))
    (hTMul : tMul < 65536) (hTAdd : tAdd < 65536)
    (hFMul : fMul < 65536) (hFAdd : fAdd < 65536)
    (hTMulBound : hi * tMul < 65536)
    (hTHi : hi * tMul + tAdd ≤ hiNext)
    (hTLo : loNext ≤ lo * tMul + tAdd)
    (hFMulBound : hi * fMul < 65536)
    (hFHi : hi * fMul + fAdd ≤ hiNext)
    (hFLo : loNext ≤ lo * fMul + fAdd)
    (hHiNext : hiNext < 65536) :
    OvfCastStageCut body bt baseLocals ids
      { blockIdx := entryBlk, lo := lo, hi := hi }
      { blockIdx := joinBlk, lo := loNext, hi := hiNext } 8 := by
  apply seal_ovfCastStageCut
  intro hValid s hInv
  let ⟨acc, oTmp, oMul, oAdd, mem, hEqS, hLoAcc, hAccHi, hHi⟩ := hInv
  subst hEqS
  let ⟨hd1, hdAdd⟩ := and_eq_true_elim hFlagDisj
  let ⟨hd2, hdMul⟩ := and_eq_true_elim hd1
  let ⟨hdAcc, hdTmp⟩ := and_eq_true_elim hd2
  have hFlagGet :
      compGetElem? (applyStageSlots baseLocals ids acc oTmp oMul oAdd)
          flagLocal =
        some (.immediate (some (.bool flagVal))) := by
    rw [applyStageSlots_get_other baseLocals ids acc oTmp oMul oAdd
      (ne_of_not_beq hdAcc) (ne_of_not_beq hdTmp)
      (ne_of_not_beq hdMul) (ne_of_not_beq hdAdd)]
    exact hFlagBase
  have hAccLt : acc < 65536 := Nat.lt_of_le_of_lt hAccHi hHi
  have hSwitch :
      evalStep (bodyProg body) 0
        (mkStageState entryBlk 0 baseLocals ids acc oTmp oMul oAdd ⟨[]⟩ mem) =
      .step (mkStageState (if flagVal then tBlk else fBlk)
        0 baseLocals ids acc oTmp oMul oAdd ⟨[]⟩ mem) := by
    unfold mkStageState
    exact evalStep_bodyProg_switchBool hValid hEntryTree rfl hFlagTy hFlagGet
  cases flagVal with
  | true =>
    have hProd : acc * tMul < 65536 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right tMul hAccHi) hTMulBound
    have hNewHi : acc * tMul + tAdd ≤ hiNext :=
      Nat.le_trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right tMul hAccHi) tAdd) hTHi
    have hNewLo : loNext ≤ acc * tMul + tAdd :=
      Nat.le_trans hTLo
        (Nat.add_le_add_right (Nat.mul_le_mul_right tMul hLoAcc) tAdd)
    have hNewLt : acc * tMul + tAdd < 65536 :=
      Nat.lt_of_le_of_lt hNewHi hHiNext
    exact wpUntilCutStep_step hSwitch
      (step_overflowCast_arm hValid hIdsWf hLocAcc hLocTmp hLocMul hLocAdd
        hTrueTree hAccLt hTMul hTAdd hProd hNewLt
        ⟨acc * tMul + tAdd, _, _, _, mem, rfl, hNewLo, hNewHi, hHiNext⟩)
  | false =>
    have hProd : acc * fMul < 65536 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right fMul hAccHi) hFMulBound
    have hNewHi : acc * fMul + fAdd ≤ hiNext :=
      Nat.le_trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right fMul hAccHi) fAdd) hFHi
    have hNewLo : loNext ≤ acc * fMul + fAdd :=
      Nat.le_trans hFLo
        (Nat.add_le_add_right (Nat.mul_le_mul_right fMul hLoAcc) fAdd)
    have hNewLt : acc * fMul + fAdd < 65536 :=
      Nat.lt_of_le_of_lt hNewHi hHiNext
    exact wpUntilCutStep_step hSwitch
      (step_overflowCast_arm hValid hIdsWf hLocAcc hLocTmp hLocMul hLocAdd
        hFalseTree hAccLt hFMul hFAdd hProd hNewLt
        ⟨acc * fMul + fAdd, _, _, _, mem, rfl, hNewLo, hNewHi, hHiNext⟩)

end Anneal.OverflowCastJoin

end
