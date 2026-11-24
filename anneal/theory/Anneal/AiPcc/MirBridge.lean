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
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirTotal.Ops
public import Anneal.AiPcc.BitArith
public import Anneal.AiPcc.Tnum
public import Anneal.AiPcc.WrappedInterval
public import Anneal.AiPcc.ReducedProduct

public section

namespace Anneal.AiPcc

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# MIR Abstract State and Scalar Bridge (`Anneal.AiPcc.MirBridge`)

Connects the Pass-1 reduced-product value domain `AbsVal` (`InitDom` x `Tnum` x
`WrappedInterval` x `StridedCong`) to `Trusted.MirAst.Body` and
`Trusted.MirSemantics.{evalBinOp, evalIntToIntCast}` over unsigned integer,
boolean, and unit immediate locals. Defines relational boolean comparison guards
(`RelGuard`, `BoolAbs`), abstract local frames (`MirAbsSlot`, `MirAbsEnv`),
guard-clearing writes (`setMirAbsSlot`), and branch guard refinements
(`refineEnvByGuard`) consumed by `Anneal.AiPcc.MirTransfer`.
-/

/-! ## 1. Unsigned `IntWidth`, `BitVec 128`, and `MirSemantics` Bridge -/

universe u

private theorem ite_bool_false {α : Sort u} {c : Bool} {d : Decidable (c = true)}
    (hc : c = false) (a b : α) : @ite α (c = true) d a b = b := by
  cases d with
  | isTrue h => rw [hc] at h; nomatch h
  | isFalse _ => rfl

private theorem ite_bool_true {α : Sort u} {c : Bool} {d : Decidable (c = true)}
    (hc : c = true) (a b : α) : @ite α (c = true) d a b = a := by
  cases d with
  | isTrue _ => rfl
  | isFalse h => exact False.elim (h hc)

private theorem nat_add_sub_cancel_left {a b : Nat} (h : a ≤ b) :
    a + (b - a) = b := by
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel h

private theorem nat_le_or_gt (a b : Nat) : a ≤ b ∨ b < a := by
  cases hBle : Nat.ble a b with
  | true => exact Or.inl (Nat.le_of_ble_eq_true hBle)
  | false =>
    exact Or.inr (Nat.lt_of_not_le (fun hLe => by
      rw [Nat.ble_eq_true_of_le hLe] at hBle
      nomatch hBle))

private theorem int_ofNat_sub_eq_subNatNat (a b : Nat) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero =>
    dsimp only [Int.subNatNat]
    rw [Nat.zero_sub a, Nat.sub_zero]
    change Int.add (Int.ofNat a) (Int.ofNat 0) = Int.ofNat a
    change Int.ofNat (a + 0) = Int.ofNat a
    rw [Nat.add_zero]
  | succ _ => rfl

private theorem int_ofNat_sub_of_le {a b : Nat} (h : b ≤ a) :
    Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) := by
  rw [int_ofNat_sub_eq_subNatNat]
  dsimp only [Int.subNatNat]
  have hZero : b - a = 0 := Nat.sub_eq_zero_of_le h
  rw [hZero]

private theorem int_ofNat_sub_of_lt {a b : Nat} (h : a < b) :
    Int.ofNat a - Int.ofNat b = Int.negSucc (b - a - 1) := by
  rw [int_ofNat_sub_eq_subNatNat]
  dsimp only [Int.subNatNat]
  have hPos : 0 < b - a := Nat.sub_pos_of_lt h
  cases hD : b - a with
  | zero => rw [hD] at hPos; nomatch hPos
  | succ k => rfl

private theorem int_ofNat_le_iff {a b : Nat} :
    (Int.ofNat a ≤ Int.ofNat b) ↔ (a ≤ b) := by
  constructor
  · intro hLe
    have hNonNeg : Int.NonNeg (Int.ofNat b - Int.ofNat a) := hLe
    cases nat_le_or_gt a b with
    | inl h => exact h
    | inr hGt =>
      rw [int_ofNat_sub_of_lt hGt] at hNonNeg
      nomatch hNonNeg
  · intro hLe
    change Int.NonNeg (Int.ofNat b - Int.ofNat a)
    rw [int_ofNat_sub_of_le hLe]
    exact Int.NonNeg.mk (b - a)

private theorem int_ofNat_lt_iff {a b : Nat} :
    (Int.ofNat a < Int.ofNat b) ↔ (a < b) := by
  change (Int.ofNat a + 1 ≤ Int.ofNat b) ↔ (Nat.succ a ≤ b)
  have hAdd : Int.ofNat a + (1 : Int) = Int.ofNat (Nat.succ a) := rfl
  rw [hAdd]
  exact int_ofNat_le_iff

private theorem int_pow_ofNat (a n : Nat) :
    HPow.hPow (Int.ofNat a) n = Int.ofNat (Nat.pow a n) := rfl

private theorem intWidthBeqComp_refl (w : IntWidth) :
    intWidthBeqComp w w = true := by
  cases w <;> rfl

/-- Every captured `IntWidth` satisfies `validWidth (bitWidthComp w) = true`. -/
theorem bitWidthComp_valid (w : IntWidth) :
    validWidth (bitWidthComp w) = true := by
  cases w <;> rfl

/-- Every captured `IntWidth` has bit-width at most 128. -/
theorem bitWidthComp_le_128 (w : IntWidth) : bitWidthComp w ≤ 128 := by
  cases w <;> exact Nat.le_of_ble_eq_true rfl

/-- `modPow2 (bitWidthComp w) ≤ Nat.pow 2 128`. -/
theorem modPow2_bitWidth_le_128 (w : IntWidth) :
    modPow2 (bitWidthComp w) ≤ Nat.pow 2 128 := by
  rw [← modPow2_eq_pow 128]
  exact modPow2_mono (bitWidthComp_le_128 w)

/-- Reflexivity of `IntWidth.beq`. -/
theorem intWidth_beq_refl (w : IntWidth) : IntWidth.beq w w = true := by
  cases w <;> rfl

/-- Decidable equality soundness for `intWidthBeqComp`. -/
theorem intWidth_eq_of_beqComp {w1 w2 : IntWidth}
    (h : intWidthBeqComp w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | nomatch h

/-- `BitVec.ofNat n x` has `toNat = x` whenever `x < Nat.pow 2 n`. -/
theorem bitVec_toNat_ofNat_lt {n x : Nat} (h : x < Nat.pow 2 n) :
    (BitVec.ofNat n x).toNat = x := by
  change Nat.mod x (Nat.pow 2 n) = x
  exact nat_mod_eq_of_lt h

/-- `BitVec.ofNat 128 b.toNat = b`. -/
theorem bitVec128_ofNat_toNat (b : BitVec 128) :
    BitVec.ofNat 128 b.toNat = b := by
  cases b with
  | ofFin f =>
    cases f with
    | mk v hv =>
      have hMod : Nat.mod v (Nat.pow 2 128) = v := nat_mod_eq_of_lt hv
      have hFin :
          ∀ (a : Nat) (ha : a < Nat.pow 2 128),
            a = v → (Fin.mk a ha : Fin (Nat.pow 2 128)) = Fin.mk v hv := by
        intro a _ hEq
        subst hEq
        rfl
      exact congrArg BitVec.ofFin
        (hFin (Nat.mod v (Nat.pow 2 128))
          (Nat.mod_lt v (Nat.pow_pos (Nat.zero_lt_succ 1))) hMod)

/-- Explicit arithmetic characterization of `(truncateBits w b).toNat`. -/
theorem truncateBits_toNat (w : IntWidth) (b : BitVec 128) :
    (truncateBits w b).toNat = wrapVal (bitWidthComp w) b.toNat := by
  have hModLt : Nat.mod b.toNat (modPow2 (bitWidthComp w)) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (nat_mod_lt b.toNat (modPow2_pos (bitWidthComp w)))
      (modPow2_bitWidth_le_128 w)
  have hStep :
      ∀ (k : Nat), k = bitWidthComp w →
        (BitVec.ofNat 128 (BitVec.ofNat k (Nat.shiftRight b.toNat 0)).toNat).toNat =
          Nat.mod b.toNat (modPow2 (bitWidthComp w)) := by
    intro k hk
    subst hk
    have hSh0 : Nat.shiftRight b.toNat 0 = b.toNat := rfl
    rw [hSh0]
    change Nat.mod (Nat.mod b.toNat (Nat.pow 2 (bitWidthComp w))) (Nat.pow 2 128) =
      Nat.mod b.toNat (modPow2 (bitWidthComp w))
    rw [← modPow2_eq_pow (bitWidthComp w)]
    exact nat_mod_eq_of_lt hModLt
  dsimp only [truncateBits, bvZeroExtend, bvExtractLsb, bvExtractLsb', wrapVal]
  cases w with
  | i8 => exact hStep 8 rfl
  | i16 => exact hStep 16 rfl
  | i32 => exact hStep 32 rfl
  | i64 => exact hStep 64 rfl
  | i128 => exact hStep 128 rfl
  | isize => exact hStep 64 rfl

/-- `truncateBits w b = BitVec.ofNat 128 (wrapVal (bitWidthComp w) b.toNat)`. -/
theorem truncateBits_eq_ofNat_wrapVal (w : IntWidth) (b : BitVec 128) :
    truncateBits w b = BitVec.ofNat 128 (wrapVal (bitWidthComp w) b.toNat) := by
  have h1 := bitVec128_ofNat_toNat (truncateBits w b)
  rw [truncateBits_toNat w b] at h1
  exact h1.symm

/-- `truncateBits w b = b` whenever `b.toNat < modPow2 (bitWidthComp w)`. -/
theorem truncateBits_of_lt {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    truncateBits w b = b := by
  rw [truncateBits_eq_ofNat_wrapVal w b]
  dsimp only [wrapVal]
  rw [nat_mod_eq_of_lt hLt, bitVec128_ofNat_toNat b]

/-- `truncateBits w (BitVec.ofNat 128 x) = BitVec.ofNat 128 x` for
`x < modPow2 (bitWidthComp w)`. -/
theorem truncateBits_ofNat_lt {w : IntWidth} {x : Nat}
    (hLt : x < modPow2 (bitWidthComp w)) :
    truncateBits w (BitVec.ofNat 128 x) = BitVec.ofNat 128 x := by
  have h128 : x < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hLt (modPow2_bitWidth_le_128 w)
  apply truncateBits_of_lt
  rw [bitVec_toNat_ofNat_lt h128]
  exact hLt

/-- `decodeScalar` of an in-range unsigned scalar equals `Int.ofNat b.toNat`. -/
theorem decodeScalar_uint_of_lt {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    decodeScalar ⟨w, false, b⟩ = Int.ofNat b.toNat := by
  dsimp only [decodeScalar]
  rw [ite_bool_false rfl, truncateBits_of_lt hLt]

/-- `checkVal` accepts every in-range unsigned scalar at its declared width. -/
theorem checkVal_uint_of_lt {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    checkVal (.scalar ⟨w, false, b⟩) (.int w false) = true := by
  have hWf : ScalarVal.wf ⟨w, false, b⟩ = true := by
    dsimp only [ScalarVal.wf]
    rw [truncateBits_of_lt hLt]
    dsimp only [BEq.beq]
    exact decide_eq_true rfl
  dsimp only [checkVal, Val.ty?]
  rw [ite_bool_true hWf]
  dsimp only [MirTy.beq]
  rw [intWidth_beq_refl w]
  rfl

/-- `bvOfInt 128 (Int.ofNat x) = BitVec.ofNat 128 x` for all `x : Nat`. -/
theorem bvOfInt_ofNat_128 {x : Nat} :
    bvOfInt 128 (Int.ofNat x) = BitVec.ofNat 128 x := by
  dsimp only [bvOfInt, intEmod, Int.natAbs, Int.toNat]
  change BitVec.ofNat 128 (Nat.mod x (Nat.pow 2 128)) = BitVec.ofNat 128 x
  have hMod :
      (BitVec.ofNat 128 (Nat.mod x (Nat.pow 2 128))).toNat =
        (BitVec.ofNat 128 x).toNat := by
    change Nat.mod (Nat.mod x (Nat.pow 2 128)) (Nat.pow 2 128) =
      Nat.mod x (Nat.pow 2 128)
    exact nat_mod_eq_of_lt (Nat.mod_lt x (Nat.pow_pos (Nat.zero_lt_succ 1)))
  have h1 := bitVec128_ofNat_toNat (BitVec.ofNat 128 (Nat.mod x (Nat.pow 2 128)))
  have h2 := bitVec128_ofNat_toNat (BitVec.ofNat 128 x)
  rw [← h1, ← h2, hMod]

/-- `truncateScalar w false (Int.ofNat x)` characterization on `Nat`. -/
theorem truncateScalar_uint_ofNat (w : IntWidth) (x : Nat) :
    truncateScalar w false (Int.ofNat x) =
      .ok (⟨w, false, BitVec.ofNat 128 (wrapVal (bitWidthComp w) x)⟩,
           BitVec.ofNat 128 (wrapVal (bitWidthComp w) x) != BitVec.ofNat 128 x) := by
  dsimp only [truncateScalar]
  rw [ite_bool_false rfl, bvOfInt_ofNat_128, truncateBits_eq_ofNat_wrapVal]
  have hWrap :
      wrapVal (bitWidthComp w) (BitVec.ofNat 128 x).toNat =
        wrapVal (bitWidthComp w) x := by
    dsimp only [wrapVal]
    change Nat.mod (Nat.mod x (Nat.pow 2 128)) (modPow2 (bitWidthComp w)) =
      Nat.mod x (modPow2 (bitWidthComp w))
    rw [← modPow2_eq_pow 128]
    exact mod_modPow2_of_le (bitWidthComp_le_128 w) x
  rw [hWrap]

/-- `truncateScalar w false (Int.ofNat x)` has `lossy = false` whenever
`x < modPow2 (bitWidthComp w)`. -/
theorem truncateScalar_uint_of_lt {w : IntWidth} {x : Nat}
    (hLt : x < modPow2 (bitWidthComp w)) :
    truncateScalar w false (Int.ofNat x) =
      .ok (⟨w, false, BitVec.ofNat 128 x⟩, false) := by
  rw [truncateScalar_uint_ofNat w x]
  have hW : wrapVal (bitWidthComp w) x = x := nat_mod_eq_of_lt hLt
  rw [hW]
  have hNe : (BitVec.ofNat 128 x != BitVec.ofNat 128 x) = false := by
    dsimp only [bne, BEq.beq]
    rw [decide_eq_true rfl]
    rfl
  rw [hNe]

private theorem bvOfInt_negSucc_mod_eq {k m d : Nat}
    (hM : 0 < m)
    (hDvd : Nat.mod (Nat.pow 2 k) m = 0)
    (hDiffPos : 0 < d) (hDiffLtM : d < m) (hMleN : m ≤ Nat.pow 2 k) :
    Nat.mod (bvOfInt k (Int.negSucc (d - 1))).toNat m = m - d := by
  let N := Nat.pow 2 k
  have hDiffLtN : d < N := Nat.lt_of_lt_of_le hDiffLtM hMleN
  have hPred : d = (d - 1) + 1 := (Nat.sub_add_cancel hDiffPos).symm
  dsimp only [bvOfInt, intEmod]
  have hPredLtN : d - 1 < N :=
    Nat.lt_of_le_of_lt (Nat.sub_le d 1) hDiffLtN
  have hAbsN : (Int.ofNat N).natAbs = N := rfl
  rw [hAbsN, nat_mod_eq_of_lt hPredLtN]
  have hSuccEq : Nat.succ (d - 1) = d := hPred.symm
  rw [hSuccEq]
  have hSubNat : Int.subNatNat N d = Int.ofNat (N - d) := by
    dsimp only [Int.subNatNat]
    have hZero : d - N = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hDiffLtN)
    rw [hZero]
  rw [hSubNat]
  have hToNat : (Int.ofNat (N - d)).toNat = N - d := rfl
  rw [hToNat]
  have hNPos : 0 < N := Nat.pow_pos (Nat.zero_lt_succ 1)
  have hNSubLt : N - d < N := Nat.sub_lt hNPos hDiffPos
  rw [bitVec_toNat_ofNat_lt hNSubLt]
  have hNDecomp : N = m * Nat.div N m := by
    have h := nat_div_add_mod N m
    rw [hDvd, Nat.add_zero] at h
    exact h.symm
  have hQPos : 0 < Nat.div N m := by
    cases hq : Nat.div N m with
    | zero =>
      rw [hq, Nat.mul_zero] at hNDecomp
      rw [hNDecomp] at hNPos
      nomatch hNPos
    | succ _ => exact Nat.zero_lt_succ _
  have hNSubEq : N - d = (m - d) + m * (Nat.div N m - 1) := by
    have hQ1 : Nat.div N m = 1 + (Nat.div N m - 1) := by
      rw [Nat.add_comm]; exact (Nat.sub_add_cancel hQPos).symm
    have hN2 : N = m + m * (Nat.div N m - 1) := by
      have hStep := congrArg (fun z => m * z) hQ1
      rw [Nat.mul_add m 1 _, Nat.mul_one] at hStep
      exact Eq.trans hNDecomp hStep
    have h1 : N - d = (m + m * (Nat.div N m - 1)) - d :=
      congrArg (fun z => z - d) hN2
    rw [h1, Nat.add_comm m _, Nat.add_sub_assoc (Nat.le_of_lt hDiffLtM),
        Nat.add_comm]
  rw [hNSubEq, nat_add_mul_mod_self_left]
  exact nat_mod_eq_of_lt (Nat.sub_lt hM hDiffPos)

/-- Modular subtraction on `Int` matches `wrapVal w (modPow2 w + x - y)` for
`x, y < modPow2 (bitWidthComp w)`. -/
theorem truncateScalar_uint_sub {w : IntWidth} {x y : Nat}
    (hx : x < modPow2 (bitWidthComp w)) (hy : y < modPow2 (bitWidthComp w)) :
    ∃ lossy : Bool,
      truncateScalar w false (Int.ofNat x - Int.ofNat y) =
        .ok (⟨w, false, BitVec.ofNat 128
          (wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) + x - y))⟩,
          lossy) := by
  let M := modPow2 (bitWidthComp w)
  have hM : 0 < M := modPow2_pos (bitWidthComp w)
  have hMleN : M ≤ Nat.pow 2 128 := modPow2_bitWidth_le_128 w
  have hDvd : Nat.mod (Nat.pow 2 128) M = 0 := by
    have hPowEq : Nat.pow 2 128 = modPow2 128 := (modPow2_eq_pow 128).symm
    have hSplit : 128 = bitWidthComp w + (128 - bitWidthComp w) :=
      (nat_add_sub_cancel_left (bitWidthComp_le_128 w)).symm
    rw [hPowEq, hSplit, modPow2_add]
    exact Nat.mul_mod_right M (modPow2 (128 - bitWidthComp w))
  dsimp only [truncateScalar]
  rw [ite_bool_false rfl]
  let lossyVal : Bool :=
    truncateBits w (bvOfInt 128 (Int.ofNat x - Int.ofNat y)) !=
      bvOfInt 128 (Int.ofNat x - Int.ofNat y)
  refine ⟨lossyVal, ?_⟩
  apply congrArg Except.ok
  apply congrArg (fun (bv : BitVec 128) =>
    (({ width := w, signed := false, bits := bv } : ScalarVal), lossyVal))
  rw [truncateBits_eq_ofNat_wrapVal]
  apply congrArg (BitVec.ofNat 128)
  cases nat_le_or_gt y x with
  | inl hLe =>
    have hSubInt : Int.ofNat x - Int.ofNat y = Int.ofNat (x - y) :=
      int_ofNat_sub_of_le hLe
    rw [hSubInt, bvOfInt_ofNat_128]
    have hSubLt : x - y < M := Nat.lt_of_le_of_lt (Nat.sub_le x y) hx
    have hSubLtN : x - y < Nat.pow 2 128 := Nat.lt_of_lt_of_le hSubLt hMleN
    rw [bitVec_toNat_ofNat_lt hSubLtN]
    dsimp only [wrapVal]
    have hAddSub : M + x - y = M + (x - y) := Nat.add_sub_assoc hLe M
    rw [hAddSub, nat_add_mod_self_left]
  | inr hGt =>
    have hDiffPos : 0 < y - x := Nat.sub_pos_of_lt hGt
    have hDiffLtM : y - x < M := Nat.lt_of_le_of_lt (Nat.sub_le y x) hy
    rw [int_ofNat_sub_of_lt hGt]
    dsimp only [wrapVal]
    have hLhs := bvOfInt_negSucc_mod_eq (k := 128) (m := M) (d := y - x)
      hM hDvd hDiffPos hDiffLtM hMleN
    have hMSubEq : M + x - y = M - (y - x) := by
      have hAdd : M + x - y + y = M - (y - x) + y := by
        have hLe1 : y ≤ M + x := Nat.le_trans (Nat.le_of_lt hy) (Nat.le_add_right M x)
        rw [Nat.sub_add_cancel hLe1]
        have hYDecomp : (y - x) + x = y := Nat.sub_add_cancel (Nat.le_of_lt hGt)
        have hRhs : M - (y - x) + y = M + x := by
          have h1 := congrArg (fun z => M - (y - x) + z) hYDecomp.symm
          rw [← Nat.add_assoc,
              Nat.sub_add_cancel (Nat.le_of_lt hDiffLtM)] at h1
          exact h1
        exact hRhs.symm
      exact Nat.add_right_cancel hAdd
    rw [hLhs, hMSubEq, nat_mod_eq_of_lt (Nat.sub_lt hM hDiffPos)]

/-- Helper turning `hostOverflow` to `false` when `n < Nat.pow 2 128`. -/
private theorem hostOverflow_false_of_lt_128 {n : Nat} (h : n < Nat.pow 2 128) :
    (decide (Int.ofNat n < 0) ||
     decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128)) = false := by
  have h1 : decide (Int.ofNat n < 0) = false := by
    apply decide_eq_false
    intro hNeg
    exact Nat.not_lt_zero n (int_ofNat_lt_iff.mp hNeg)
  have hPowInt : HPow.hPow (2 : Int) 128 = Int.ofNat (Nat.pow 2 128) :=
    int_pow_ofNat 2 128
  have h2 : decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) = false := by
    apply decide_eq_false
    rw [hPowInt]
    intro hGe
    exact Nat.not_le_of_gt h (int_ofNat_le_iff.mp hGe)
  rw [h1, h2]
  rfl

private theorem same_uint_guard_false (w : IntWidth) :
    (!(IntWidth.beq w w && (false == false))) = false := by
  rw [intWidth_beq_refl w]
  rfl

/-- Unsigned wrapping `.add` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_add {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .add (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128 (wrapVal (bitWidthComp w) (b1.toNat + b2.toNat))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.add.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && (Int.ofNat b2.toNat == 0))) rfl,
      ite_bool_false (c := (false && false && _)) rfl]
  have hSumInt : Int.ofNat b1.toNat + Int.ofNat b2.toNat =
      Int.ofNat (b1.toNat + b2.toNat) := rfl
  rw [hSumInt, truncateScalar_uint_ofNat w (b1.toNat + b2.toNat)]
  dsimp only
  rw [ite_bool_false (c := (_ && BinOp.add.isUnchecked)) (Bool.and_false _),
      ite_bool_false (c := BinOp.add.isOverflowing) rfl]

/-- Unsigned `.addUnchecked` soundness when
`b1.toNat + b2.toNat < modPow2 w`. -/
theorem evalBinOp_uint_addUnchecked {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hNoOv : b1.toNat + b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .addUnchecked (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128 (wrapVal (bitWidthComp w) (b1.toNat + b2.toNat))⟩) := by
  have hSum128 : b1.toNat + b2.toNat < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hNoOv (modPow2_bitWidth_le_128 w)
  have hWrapEq : wrapVal (bitWidthComp w) (b1.toNat + b2.toNat) =
      b1.toNat + b2.toNat := nat_mod_eq_of_lt hNoOv
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.addUnchecked.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && (Int.ofNat b2.toNat == 0))) rfl,
      ite_bool_false (c := (false && false && _)) rfl]
  have hSumInt : Int.ofNat b1.toNat + Int.ofNat b2.toNat =
      Int.ofNat (b1.toNat + b2.toNat) := rfl
  rw [hSumInt, truncateScalar_uint_of_lt hNoOv, hWrapEq]
  dsimp only
  rw [ite_bool_false (c := false) rfl]
  have hNoFail :
      (((decide (Int.ofNat (b1.toNat + b2.toNat) < 0) ||
         decide (Int.ofNat (b1.toNat + b2.toNat) ≥ HPow.hPow (2 : Int) 128)) ||
        false) && BinOp.addUnchecked.isUnchecked) = false := by
    rw [hostOverflow_false_of_lt_128 hSum128]
    rfl
  rw [ite_bool_false hNoFail,
      ite_bool_false (c := BinOp.addUnchecked.isOverflowing) rfl]

/-- Unsigned wrapping `.sub` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_sub {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .sub (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128
          (wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) + b1.toNat - b2.toNat))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.sub.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && (Int.ofNat b2.toNat == 0))) rfl,
      ite_bool_false (c := (false && false && _)) rfl]
  have hSub := truncateScalar_uint_sub h1 h2
  cases hSub with
  | intro lossy hEq =>
    rw [hEq]
    dsimp only
    rw [ite_bool_false (c := (_ && BinOp.sub.isUnchecked)) (Bool.and_false _),
        ite_bool_false (c := BinOp.sub.isOverflowing) rfl]

/-- Unsigned `.subUnchecked` soundness when `b2.toNat ≤ b1.toNat`. -/
theorem evalBinOp_uint_subUnchecked {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hGe : b2.toNat ≤ b1.toNat) :
    evalBinOp .subUnchecked (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128
          (wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) + b1.toNat - b2.toNat))⟩) := by
  have hDiffLt : b1.toNat - b2.toNat < modPow2 (bitWidthComp w) :=
    Nat.lt_of_le_of_lt (Nat.sub_le b1.toNat b2.toNat) h1
  have hDiff128 : b1.toNat - b2.toNat < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hDiffLt (modPow2_bitWidth_le_128 w)
  have hSubInt : Int.ofNat b1.toNat - Int.ofNat b2.toNat =
      Int.ofNat (b1.toNat - b2.toNat) := int_ofNat_sub_of_le hGe
  have hWrapEq :
      wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) + b1.toNat - b2.toNat) =
        b1.toNat - b2.toNat := by
    dsimp only [wrapVal]
    rw [Nat.add_sub_assoc hGe (modPow2 (bitWidthComp w)),
        nat_add_mod_self_left, nat_mod_eq_of_lt hDiffLt]
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.subUnchecked.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && (Int.ofNat b2.toNat == 0))) rfl,
      ite_bool_false (c := (false && false && _)) rfl]
  rw [hSubInt, truncateScalar_uint_of_lt hDiffLt, hWrapEq]
  dsimp only
  rw [ite_bool_false (c := false) rfl]
  have hNoFail :
      (((decide (Int.ofNat (b1.toNat - b2.toNat) < 0) ||
         decide (Int.ofNat (b1.toNat - b2.toNat) ≥ HPow.hPow (2 : Int) 128)) ||
        false) && BinOp.subUnchecked.isUnchecked) = false := by
    rw [hostOverflow_false_of_lt_128 hDiff128]
    rfl
  rw [ite_bool_false hNoFail,
      ite_bool_false (c := BinOp.subUnchecked.isOverflowing) rfl]

/-- Unsigned `.bitAnd` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_bitAnd {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .bitAnd (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false, BitVec.ofNat 128 (Nat.land b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.land b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_land, bitAt_zero_ge_of_lt_modPow2 h1 k hk]; rfl)
  dsimp only [evalBinOp, bvAnd]
  rw [ite_bool_false (c := BinOp.bitAnd.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      truncateBits_of_lt h1, truncateBits_of_lt h2,
      truncateBits_ofNat_lt hLt]

/-- Unsigned `.bitOr` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_bitOr {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .bitOr (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false, BitVec.ofNat 128 (Nat.lor b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.lor b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_lor, bitAt_zero_ge_of_lt_modPow2 h1 k hk,
          bitAt_zero_ge_of_lt_modPow2 h2 k hk]; rfl)
  dsimp only [evalBinOp, bvOr]
  rw [ite_bool_false (c := BinOp.bitOr.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      truncateBits_of_lt h1, truncateBits_of_lt h2,
      truncateBits_ofNat_lt hLt]

/-- Unsigned `.bitXor` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_bitXor {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .bitXor (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false, BitVec.ofNat 128 (Nat.xor b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.xor b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_xor, bitAt_zero_ge_of_lt_modPow2 h1 k hk,
          bitAt_zero_ge_of_lt_modPow2 h2 k hk]; rfl)
  dsimp only [evalBinOp, bvXor]
  rw [ite_bool_false (c := BinOp.bitXor.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      truncateBits_of_lt h1, truncateBits_of_lt h2,
      truncateBits_ofNat_lt hLt]

/-- Helper collapsing `intEmod` on non-negative integers. -/
private theorem intEmod_ofNat (a b : Nat) :
    intEmod (Int.ofNat a) (Int.ofNat b) = Int.ofNat (Nat.mod a b) := rfl

/-- Unsigned wrapping `.shl` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_shl {w rw_ : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp rw_)) :
    evalBinOp .shl (.scalar ⟨w, false, b1⟩) (.scalar ⟨rw_, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128
          (wrapVal (bitWidthComp w)
            (Nat.shiftLeft b1.toNat (Nat.mod b2.toNat (bitWidthComp w))))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_true (c := BinOp.shl.isShift) rfl,
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalShiftOp, intShiftLeft]
  rw [← bitWidthComp_eq w, intEmod_ofNat]
  have hToNat :
      (Int.ofNat (Nat.mod b2.toNat (bitWidthComp w))).toNat =
        Nat.mod b2.toNat (bitWidthComp w) := rfl
  rw [hToNat, truncateScalar_uint_ofNat]
  dsimp only
  have hF :
      ((Int.ofNat (Nat.mod b2.toNat (bitWidthComp w)) != Int.ofNat b2.toNat) &&
       BinOp.shl.isUnchecked) = false := Bool.and_false _
  rw [ite_bool_false hF]

/-- Unsigned `.shlUnchecked` soundness when `b2.toNat < bitWidthComp w`. -/
theorem evalBinOp_uint_shlUnchecked {w rw_ : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp rw_))
    (hInB : b2.toNat < bitWidthComp w) :
    evalBinOp .shlUnchecked (.scalar ⟨w, false, b1⟩) (.scalar ⟨rw_, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128 (wrapVal (bitWidthComp w) (Nat.shiftLeft b1.toNat b2.toNat))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_true (c := BinOp.shlUnchecked.isShift) rfl,
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalShiftOp, intShiftLeft]
  rw [← bitWidthComp_eq w, intEmod_ofNat, nat_mod_eq_of_lt hInB]
  have hToNat : (Int.ofNat b2.toNat).toNat = b2.toNat := rfl
  rw [hToNat, truncateScalar_uint_ofNat]
  dsimp only
  have hCond :
      ((Int.ofNat b2.toNat != Int.ofNat b2.toNat) &&
       BinOp.shlUnchecked.isUnchecked) = false := by
    dsimp only [bne, BEq.beq, BinOp.isUnchecked]
    rw [decide_eq_true rfl]
    rfl
  rw [ite_bool_false hCond]

/-- Unsigned wrapping `.shr` soundness on `evalBinOp`. -/
theorem evalBinOp_uint_shr {w rw_ : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp rw_)) :
    evalBinOp .shr (.scalar ⟨w, false, b1⟩) (.scalar ⟨rw_, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128
          (Nat.shiftRight b1.toNat (Nat.mod b2.toNat (bitWidthComp w)))⟩) := by
  have hLt :
      Nat.shiftRight b1.toNat (Nat.mod b2.toNat (bitWidthComp w)) <
        modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_shiftRight]
      exact bitAt_zero_ge_of_lt_modPow2 h1 _ (Nat.le_trans hk (Nat.le_add_right _ _)))
  dsimp only [evalBinOp]
  rw [ite_bool_true (c := BinOp.shr.isShift) rfl,
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalShiftOp, intShiftRight]
  rw [← bitWidthComp_eq w, intEmod_ofNat]
  have hToNat :
      (Int.ofNat (Nat.mod b2.toNat (bitWidthComp w))).toNat =
        Nat.mod b2.toNat (bitWidthComp w) := rfl
  rw [hToNat, truncateScalar_uint_of_lt hLt]
  dsimp only
  have hF :
      ((Int.ofNat (Nat.mod b2.toNat (bitWidthComp w)) != Int.ofNat b2.toNat) &&
       BinOp.shr.isUnchecked) = false := Bool.and_false _
  rw [ite_bool_false hF]

/-- Unsigned `.shrUnchecked` soundness when `b2.toNat < bitWidthComp w`. -/
theorem evalBinOp_uint_shrUnchecked {w rw_ : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp rw_))
    (hInB : b2.toNat < bitWidthComp w) :
    evalBinOp .shrUnchecked (.scalar ⟨w, false, b1⟩) (.scalar ⟨rw_, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128 (Nat.shiftRight b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.shiftRight b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_shiftRight]
      exact bitAt_zero_ge_of_lt_modPow2 h1 _ (Nat.le_trans hk (Nat.le_add_right _ _)))
  dsimp only [evalBinOp]
  rw [ite_bool_true (c := BinOp.shrUnchecked.isShift) rfl,
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalShiftOp, intShiftRight]
  rw [← bitWidthComp_eq w, intEmod_ofNat, nat_mod_eq_of_lt hInB]
  have hToNat : (Int.ofNat b2.toNat).toNat = b2.toNat := rfl
  rw [hToNat, truncateScalar_uint_of_lt hLt]
  dsimp only
  have hCond :
      ((Int.ofNat b2.toNat != Int.ofNat b2.toNat) &&
       BinOp.shrUnchecked.isUnchecked) = false := by
    dsimp only [bne, BEq.beq, BinOp.isUnchecked]
    rw [decide_eq_true rfl]
    rfl
  rw [ite_bool_false hCond]

/-- Unsigned `.div` soundness when `0 < b2.toNat`. -/
theorem evalBinOp_uint_div {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hPos : 0 < b2.toNat) :
    evalBinOp .div (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false, BitVec.ofNat 128 (Nat.div b1.toNat b2.toNat)⟩) := by
  have hNe0 : (Int.ofNat b2.toNat == 0) = false := by
    dsimp only [BEq.beq]
    apply decide_eq_false
    intro hEq
    have hZ : b2.toNat = 0 := Int.ofNat.inj hEq
    rw [hZ] at hPos
    nomatch hPos
  have hLt : Nat.div b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self b1.toNat b2.toNat) h1
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.div.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalArithOp, intTdiv]
  have hDivZ : (true && (Int.ofNat b2.toNat == 0)) = false := by
    rw [hNe0]; rfl
  rw [ite_bool_false hDivZ,
      ite_bool_false (c := (false && true && _)) rfl,
      truncateScalar_uint_of_lt hLt]
  dsimp only
  rw [ite_bool_false (c := (_ && BinOp.div.isUnchecked)) (Bool.and_false _),
      ite_bool_false (c := BinOp.div.isOverflowing) rfl]

/-- Unsigned `.rem` soundness when `0 < b2.toNat`. -/
theorem evalBinOp_uint_rem {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hPos : 0 < b2.toNat) :
    evalBinOp .rem (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false, BitVec.ofNat 128 (Nat.mod b1.toNat b2.toNat)⟩) := by
  have hNe0 : (Int.ofNat b2.toNat == 0) = false := by
    dsimp only [BEq.beq]
    apply decide_eq_false
    intro hEq
    have hZ : b2.toNat = 0 := Int.ofNat.inj hEq
    rw [hZ] at hPos
    nomatch hPos
  have hLt : Nat.mod b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    Nat.lt_trans (nat_mod_lt b1.toNat hPos) h2
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.rem.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [evalArithOp, intTmod]
  have hDivZ : (true && (Int.ofNat b2.toNat == 0)) = false := by
    rw [hNe0]; rfl
  rw [ite_bool_false hDivZ,
      ite_bool_false (c := (false && true && _)) rfl,
      truncateScalar_uint_of_lt hLt]
  dsimp only
  rw [ite_bool_false (c := (_ && BinOp.rem.isUnchecked)) (Bool.and_false _),
      ite_bool_false (c := BinOp.rem.isOverflowing) rfl]

/-- Unsigned integer comparison soundness on `evalBinOp`. -/
theorem evalBinOp_uint_eq {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .eq (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (Nat.beq b1.toNat b2.toNat)) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.eq.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [BEq.beq]
  cases hB : Nat.beq b1.toNat b2.toNat with
  | true =>
    have hE : Int.ofNat b1.toNat = Int.ofNat b2.toNat :=
      congrArg Int.ofNat (Nat.eq_of_beq_eq_true hB)
    rw [decide_eq_true hE]
  | false =>
    have hN : Int.ofNat b1.toNat ≠ Int.ofNat b2.toNat := by
      intro hE
      have hNat := Int.ofNat.inj hE
      rw [nat_beq_of_eq hNat] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Exact `Trusted.MirSemantics.evalBinOp .ne` characterization on unsigned
scalars. -/
theorem evalBinOp_uint_ne {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .ne (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (!Nat.beq b1.toNat b2.toNat)) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.ne.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  dsimp only [bne, BEq.beq]
  cases hB : Nat.beq b1.toNat b2.toNat with
  | true =>
    have hE : Int.ofNat b1.toNat = Int.ofNat b2.toNat :=
      congrArg Int.ofNat (Nat.eq_of_beq_eq_true hB)
    rw [decide_eq_true hE]
  | false =>
    have hN : Int.ofNat b1.toNat ≠ Int.ofNat b2.toNat := by
      intro hE
      have hNat := Int.ofNat.inj hE
      rw [nat_beq_of_eq hNat] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Exact `Trusted.MirSemantics.evalBinOp .lt` characterization on unsigned
scalars. -/
theorem evalBinOp_uint_lt {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .lt (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (Nat.blt b1.toNat b2.toNat)) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.lt.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  cases hB : Nat.blt b1.toNat b2.toNat with
  | true =>
    rw [decide_eq_true (int_ofNat_lt_iff.mpr (lt_of_blt_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat b1.toNat < Int.ofNat b2.toNat) := by
      intro hLt
      rw [blt_true_of_lt (int_ofNat_lt_iff.mp hLt)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Exact `Trusted.MirSemantics.evalBinOp .le` characterization on unsigned
scalars. -/
theorem evalBinOp_uint_le {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .le (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (Nat.ble b1.toNat b2.toNat)) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.le.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  cases hB : Nat.ble b1.toNat b2.toNat with
  | true =>
    rw [decide_eq_true (int_ofNat_le_iff.mpr (Nat.le_of_ble_eq_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat b1.toNat ≤ Int.ofNat b2.toNat) := by
      intro hLe
      rw [Nat.ble_eq_true_of_le (int_ofNat_le_iff.mp hLe)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Exact `Trusted.MirSemantics.evalBinOp .gt` characterization on unsigned
scalars. -/
theorem evalBinOp_uint_gt {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .gt (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (Nat.blt b2.toNat b1.toNat)) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.gt.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  cases hB : Nat.blt b2.toNat b1.toNat with
  | true =>
    rw [decide_eq_true (int_ofNat_lt_iff.mpr (lt_of_blt_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat b1.toNat > Int.ofNat b2.toNat) := by
      intro hGt
      rw [blt_true_of_lt (int_ofNat_lt_iff.mp hGt)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Exact `Trusted.MirSemantics.evalBinOp .ge` characterization on unsigned
scalars. -/
theorem evalBinOp_uint_ge {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .ge (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (Nat.ble b2.toNat b1.toNat)) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.ge.isShift) rfl,
      ite_bool_false (same_uint_guard_false w),
      decodeScalar_uint_of_lt h1, decodeScalar_uint_of_lt h2]
  cases hB : Nat.ble b2.toNat b1.toNat with
  | true =>
    rw [decide_eq_true (int_ofNat_le_iff.mpr (Nat.le_of_ble_eq_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat b1.toNat ≥ Int.ofNat b2.toNat) := by
      intro hGe
      rw [Nat.ble_eq_true_of_le (int_ofNat_le_iff.mp hGe)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Unsigned `CastKind.intToInt` cast soundness on `evalIntToIntCast`. -/
theorem evalIntToIntCast_uint {wSrc wDst : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp wSrc)) :
    evalIntToIntCast (.scalar ⟨wSrc, false, b⟩) (.int wDst false) =
      .ok (.scalar ⟨wDst, false,
        BitVec.ofNat 128 (wrapVal (bitWidthComp wDst) b.toNat)⟩) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  rw [ite_bool_false rfl, truncateBits_of_lt hLt]
  dsimp only
  rw [bitVec128_ofNat_toNat b, truncateBits_eq_ofNat_wrapVal wDst b]

/-! ## 2. Relational Boolean Guards, `MirAbsSlot`, and `MirAbsEnv` -/

/-- Relational predicate attached to a `bool` local recording the integer
comparison that produced it, enabling path-sensitive refinement at `switchInt`
without requiring fused compare-and-branch MIR instructions. -/
inductive RelGuard where
  | none
  | uleConst (reg : LocalId) (w : IntWidth) (bound : Nat)
  | ugtConst (reg : LocalId) (w : IntWidth) (bound : Nat)
  | ultReg (lhs rhs : LocalId) (w : IntWidth)
  | ugeReg (lhs rhs : LocalId) (w : IntWidth)
  | ueqConst (reg : LocalId) (w : IntWidth) (val : Nat)
  | uneConst (reg : LocalId) (w : IntWidth) (val : Nat)

/-- Structural equality on `RelGuard`. -/
@[expose] def RelGuard.beq : RelGuard → RelGuard → Bool
  | .none, .none => true
  | .uleConst r1 w1 b1, .uleConst r2 w2 b2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq b1 b2
  | .ugtConst r1 w1 b1, .ugtConst r2 w2 b2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq b1 b2
  | .ultReg l1 r1 w1, .ultReg l2 r2 w2 =>
    Nat.beq l1 l2 && Nat.beq r1 r2 && intWidthBeqComp w1 w2
  | .ugeReg l1 r1 w1, .ugeReg l2 r2 w2 =>
    Nat.beq l1 l2 && Nat.beq r1 r2 && intWidthBeqComp w1 w2
  | .ueqConst r1 w1 v1, .ueqConst r2 w2 v2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq v1 v2
  | .uneConst r1 w1 v1, .uneConst r2 w2 v2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq v1 v2
  | _, _ => false

/-- Soundness of `RelGuard.beq`. -/
theorem relGuard_eq_of_beq {g1 g2 : RelGuard} (h : RelGuard.beq g1 g2 = true) :
    g1 = g2 := by
  cases g1 with
  | none => cases g2 <;> first | rfl | nomatch h
  | uleConst _ _ _ =>
    cases g2 with
    | uleConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h
  | ugtConst _ _ _ =>
    cases g2 with
    | ugtConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h
  | ultReg _ _ _ =>
    cases g2 with
    | ultReg _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h12),
          intWidth_eq_of_beqComp (bool_and_true_right h)]
    | _ => nomatch h
  | ugeReg _ _ _ =>
    cases g2 with
    | ugeReg _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h12),
          intWidth_eq_of_beqComp (bool_and_true_right h)]
    | _ => nomatch h
  | ueqConst _ _ _ =>
    cases g2 with
    | ueqConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h
  | uneConst _ _ _ =>
    cases g2 with
    | uneConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h

/-- Logical negation of a `RelGuard`. -/
@[expose] def RelGuard.negate : RelGuard → RelGuard
  | .none => .none
  | .uleConst r w b => .ugtConst r w b
  | .ugtConst r w b => .uleConst r w b
  | .ultReg l r w => .ugeReg l r w
  | .ugeReg l r w => .ultReg l r w
  | .ueqConst r w v => .uneConst r w v
  | .uneConst r w v => .ueqConst r w v

/-- True iff `g` references local `id`. -/
@[expose] def RelGuard.mentions (id : LocalId) : RelGuard → Bool
  | .none => false
  | .uleConst r _ _ => Nat.beq r id
  | .ugtConst r _ _ => Nat.beq r id
  | .ultReg l r _ => Nat.beq l id || Nat.beq r id
  | .ugeReg l r _ => Nat.beq l id || Nat.beq r id
  | .ueqConst r _ _ => Nat.beq r id
  | .uneConst r _ _ => Nat.beq r id

/-- Concrete extraction of an initialized unsigned scalar at local `r`. -/
@[expose] def localUintNat? (locals : List LocalSlot) (r : LocalId) (w :
    IntWidth) :
    Option Nat :=
  match compGetElem? locals r with
  | some (.immediate (some (.scalar sv))) =>
    if intWidthBeqComp sv.width w && !sv.signed then some sv.bits.toNat else none
  | _ => none

/-- Concrete meaning of `RelGuard` on boolean value `b` in `locals`. -/
@[expose] def RelGuard.denote (locals : List LocalSlot) (g : RelGuard) (b :
    Bool) : Prop :=
  match g with
  | .none => True
  | .uleConst r w bound =>
    ∀ x, localUintNat? locals r w = some x → (b = true ↔ x ≤ bound)
  | .ugtConst r w bound =>
    ∀ x, localUintNat? locals r w = some x → (b = true ↔ bound < x)
  | .ultReg l r w =>
    ∀ x y, localUintNat? locals l w = some x →
      localUintNat? locals r w = some y → (b = true ↔ x < y)
  | .ugeReg l r w =>
    ∀ x y, localUintNat? locals l w = some x →
      localUintNat? locals r w = some y → (b = true ↔ y ≤ x)
  | .ueqConst r w val =>
    ∀ x, localUintNat? locals r w = some x → (b = true ↔ x = val)
  | .uneConst r w val =>
    ∀ x, localUintNat? locals r w = some x → (b = true ↔ x ≠ val)

/-- Soundness of `RelGuard.negate`. -/
theorem relGuard_negate_sound {locals : List LocalSlot} {g : RelGuard} {b : Bool}
    (h : g.denote locals b) : g.negate.denote locals (!b) := by
  cases g with
  | none => exact True.intro
  | uleConst r w bound =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hLe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hGt => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      have hNotLe : ¬ (x ≤ bound) := fun hLe => nomatch (hIff.mpr hLe)
      exact ⟨(fun _ => Nat.lt_of_not_le hNotLe), (fun _ => rfl)⟩
  | ugtConst r w bound =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hGt := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hLe => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      have hNotGt : ¬ (bound < x) := fun hGt => nomatch (hIff.mpr hGt)
      exact ⟨(fun _ => Nat.le_of_not_lt hNotGt), (fun _ => rfl)⟩
  | ultReg l r w =>
    intro x y hx hy
    have hIff := h x y hx hy
    cases b with
    | true =>
      have hLt := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hGe => False.elim (Nat.not_le_of_gt hLt hGe))⟩
    | false =>
      have hNotLt : ¬ (x < y) := fun hLt => nomatch (hIff.mpr hLt)
      exact ⟨(fun _ => Nat.le_of_not_lt hNotLt), (fun _ => rfl)⟩
  | ugeReg l r w =>
    intro x y hx hy
    have hIff := h x y hx hy
    cases b with
    | true =>
      have hGe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hLt => False.elim (Nat.not_le_of_gt hLt hGe))⟩
    | false =>
      have hNotGe : ¬ (y ≤ x) := fun hGe => nomatch (hIff.mpr hGe)
      exact ⟨(fun _ => Nat.lt_of_not_le hNotGe), (fun _ => rfl)⟩
  | ueqConst r w val =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hEq := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hNe => False.elim (hNe hEq))⟩
    | false =>
      have hNe : x ≠ val := fun hEq => nomatch (hIff.mpr hEq)
      exact ⟨(fun _ => hNe), (fun _ => rfl)⟩
  | uneConst r w val =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hNe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hEq => False.elim (hNe hEq))⟩
    | false =>
      have hEq : x = val := by
        cases hB : Nat.beq x val with
        | true => exact Nat.eq_of_beq_eq_true hB
        | false =>
          have hNe : x ≠ val := fun hE => by rw [nat_beq_of_eq hE] at hB; nomatch hB
          nomatch (hIff.mpr hNe)
      exact ⟨(fun _ => hEq), (fun _ => rfl)⟩

/-- Abstract boolean local with optional attached `RelGuard`. -/
inductive BoolAbs where
  | bot
  | uninit
  | top (guard : RelGuard)
  | exact (val : Bool) (guard : RelGuard)

/-- Concrete denotation of `BoolAbs` on `Option Val` in `locals`. -/
@[expose] def BoolAbs.denote (locals : List LocalSlot) (ba : BoolAbs) :
    Option Val → Prop
  | none =>
    match ba with
    | .uninit => True
    | _ => False
  | some (.bool b) =>
    match ba with
    | .bot => False
    | .uninit => True
    | .top g => g.denote locals b
    | .exact v g => b = v ∧ g.denote locals b
  | some _ => False

/-- Lattice inclusion on `BoolAbs`. -/
@[expose] def BoolAbs.le (a b : BoolAbs) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .uninit => true
  | .top g1, .top g2 =>
    match g2 with
    | .none => true
    | _ => RelGuard.beq g1 g2
  | .exact _ g1, .top g2 =>
    match g2 with
    | .none => true
    | _ => RelGuard.beq g1 g2
  | .exact v1 g1, .exact v2 g2 =>
    boolBeqComp v1 v2 &&
    match g2 with
    | .none => true
    | _ => RelGuard.beq g1 g2
  | _, _ => false

/-- Soundness of `BoolAbs.le`. -/
theorem boolAbs_le_sound {locals : List LocalSlot} {a b : BoolAbs}
    {opt : Option Val} (hLe : BoolAbs.le a b = true) (ha : a.denote locals opt) :
    b.denote locals opt := by
  cases opt with
  | none =>
    cases a with
    | bot => exact False.elim ha
    | uninit =>
      cases b <;> dsimp only [BoolAbs.le] at hLe <;> first | exact True.intro | nomatch hLe
    | top _ => exact False.elim ha
    | exact _ _ => exact False.elim ha
  | some v =>
    cases v with
    | bool bv =>
      cases a with
      | bot => exact False.elim ha
      | uninit =>
        cases b <;> dsimp only [BoolAbs.le] at hLe <;> first | exact True.intro | nomatch hLe
      | top g1 =>
        cases b with
        | bot => nomatch hLe
        | uninit => exact True.intro
        | exact _ _ => nomatch hLe
        | top g2 =>
          dsimp only [BoolAbs.le] at hLe
          cases g2 with
          | none => exact True.intro
          | uleConst _ _ _ | ugtConst _ _ _ | ultReg _ _ _
          | ugeReg _ _ _ | ueqConst _ _ _ | uneConst _ _ _ =>
            rw [← relGuard_eq_of_beq hLe]; exact ha
      | exact v1 g1 =>
        cases b with
        | bot => nomatch hLe
        | uninit => exact True.intro
        | top g2 =>
          dsimp only [BoolAbs.le] at hLe
          cases g2 with
          | none => exact True.intro
          | uleConst _ _ _ | ugtConst _ _ _ | ultReg _ _ _
          | ugeReg _ _ _ | ueqConst _ _ _ | uneConst _ _ _ =>
            rw [← relGuard_eq_of_beq hLe]; exact ha.2
        | exact v2 g2 =>
          dsimp only [BoolAbs.le] at hLe
          have hv : v1 = v2 := by
            have h1 := bool_and_true_left hLe
            cases v1 <;> cases v2 <;> first | rfl | nomatch h1
          have hg := bool_and_true_right hLe
          refine ⟨Eq.trans ha.1 hv, ?_⟩
          cases g2 with
          | none => exact True.intro
          | uleConst _ _ _ | ugtConst _ _ _ | ultReg _ _ _
          | ugeReg _ _ _ | ueqConst _ _ _ | uneConst _ _ _ =>
            rw [← relGuard_eq_of_beq hg]; exact ha.2
    | scalar _ | ptr _ | char _ | ordering _ | unit
    | enumVal _ _ | tuple _ | bytes _ => exact False.elim ha

/-- Lattice join on `BoolAbs`. -/
@[expose] def BoolAbs.join (a b : BoolAbs) : BoolAbs :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | .uninit, _ => .uninit
  | _, .uninit => .uninit
  | .exact v1 g1, .exact v2 g2 =>
    let g := if RelGuard.beq g1 g2 then g1 else .none
    if boolBeqComp v1 v2 then .exact v1 g else .top g
  | .exact _ g1, .top g2 =>
    .top (if RelGuard.beq g1 g2 then g1 else .none)
  | .top g1, .exact _ g2 =>
    .top (if RelGuard.beq g1 g2 then g1 else .none)
  | .top g1, .top g2 =>
    .top (if RelGuard.beq g1 g2 then g1 else .none)

/-- Left join soundness for `BoolAbs`. -/
theorem boolAbs_join_sound_left {locals : List LocalSlot} {a b : BoolAbs}
    {opt : Option Val} (ha : a.denote locals opt) :
    (BoolAbs.join a b).denote locals opt := by
  cases opt with
  | none =>
    cases a with
    | bot => exact False.elim ha
    | uninit => cases b <;> exact True.intro
    | top _ | exact _ _ => exact False.elim ha
  | some v =>
    cases v with
    | bool bv =>
      cases a with
      | bot => exact False.elim ha
      | uninit => cases b <;> exact True.intro
      | top g1 =>
        cases b with
        | bot => exact ha
        | uninit => exact True.intro
        | top g2 | exact _ g2 =>
          dsimp only [BoolAbs.join]
          cases hG : RelGuard.beq g1 g2 <;> first | exact ha | exact True.intro
      | exact v1 g1 =>
        cases b with
        | bot => exact ha
        | uninit => exact True.intro
        | top g2 =>
          dsimp only [BoolAbs.join]
          cases hG : RelGuard.beq g1 g2 <;> first | exact ha.2 | exact True.intro
        | exact v2 g2 =>
          dsimp only [BoolAbs.join]
          cases hV : boolBeqComp v1 v2 with
          | true =>
            cases hG : RelGuard.beq g1 g2 with
            | true => exact ha
            | false => exact ⟨ha.1, True.intro⟩
          | false =>
            cases hG : RelGuard.beq g1 g2 with
            | true => exact ha.2
            | false => exact True.intro
    | scalar _ | ptr _ | char _ | ordering _ | unit
    | enumVal _ _ | tuple _ | bytes _ => exact False.elim ha

/-- Right join soundness for `BoolAbs`. -/
theorem boolAbs_join_sound_right {locals : List LocalSlot} {a b : BoolAbs}
    {opt : Option Val} (hb : b.denote locals opt) :
    (BoolAbs.join a b).denote locals opt := by
  cases opt with
  | none =>
    cases b with
    | bot => exact False.elim hb
    | uninit => cases a <;> exact True.intro
    | top _ | exact _ _ => exact False.elim hb
  | some v =>
    cases v with
    | bool bv =>
      cases b with
      | bot => exact False.elim hb
      | uninit => cases a <;> exact True.intro
      | top g2 =>
        cases a with
        | bot => exact hb
        | uninit => exact True.intro
        | top g1 | exact _ g1 =>
          dsimp only [BoolAbs.join]
          cases hG : RelGuard.beq g1 g2 with
          | true => rw [relGuard_eq_of_beq hG]; exact hb
          | false => exact True.intro
      | exact v2 g2 =>
        cases a with
        | bot => exact hb
        | uninit => exact True.intro
        | top g1 =>
          dsimp only [BoolAbs.join]
          cases hG : RelGuard.beq g1 g2 with
          | true => rw [relGuard_eq_of_beq hG]; exact hb.2
          | false => exact True.intro
        | exact v1 g1 =>
          dsimp only [BoolAbs.join]
          cases hV : boolBeqComp v1 v2 with
          | true =>
            have hvEq : v1 = v2 := by
              cases v1 <;> cases v2 <;> first | rfl | nomatch hV
            subst hvEq
            cases hG : RelGuard.beq g1 g2 with
            | true => rw [relGuard_eq_of_beq hG]; exact hb
            | false => exact ⟨hb.1, True.intro⟩
          | false =>
            cases hG : RelGuard.beq g1 g2 with
            | true => rw [relGuard_eq_of_beq hG]; exact hb.2
            | false => exact True.intro
    | scalar _ | ptr _ | char _ | ordering _ | unit
    | enumVal _ _ | tuple _ | bytes _ => exact False.elim hb

/-- Drop any `RelGuard` mentioning `id`. -/
@[expose] def BoolAbs.clearGuardIf (id : LocalId) : BoolAbs → BoolAbs
  | .bot => .bot
  | .uninit => .uninit
  | .top g => if g.mentions id then .top .none else .top g
  | .exact v g => if g.mentions id then .exact v .none else .exact v g

/-- Abstract local slot in `MirAbsEnv`. -/
inductive MirAbsSlot where
  | dead
  | uint (w : IntWidth) (a : AbsVal)
  | bool (b : BoolAbs)
  | unit

/-- Abstract MIR local frame (`MirAbsEnv`). -/
abbrev MirAbsEnv := List MirAbsSlot

/-- Initial uninitialized live abstract slot for a supported MIR local type. -/
@[expose] def liveUninitAbsSlot? : MirTy → Option MirAbsSlot
  | .int w false => some (.uint w (AbsVal.uninit (bitWidthComp w)))
  | .bool => some (.bool .uninit)
  | .unit => some .unit
  | _ => none

/-- Concrete denotation of one `MirAbsSlot` against `ty` and `LocalSlot`. -/
@[expose] def MirAbsSlot.denote (ty : MirTy) (locals : List LocalSlot)
    (slot : MirAbsSlot) (cslot : LocalSlot) : Prop :=
  match slot with
  | .dead => cslot = .dead
  | .uint w a =>
    ty = .int w false ∧
    match cslot with
    | .immediate none => a.denote (bitWidthComp w) none
    | .immediate (some (.scalar sv)) =>
      sv.width = w ∧ sv.signed = false ∧
      sv.bits.toNat < modPow2 (bitWidthComp w) ∧
      a.denote (bitWidthComp w) (some sv.bits.toNat)
    | _ => False
  | .bool ba =>
    ty = .bool ∧
    match cslot with
    | .immediate opt => ba.denote locals opt
    | _ => False
  | .unit => ty = .unit ∧ cslot = .immediate (some .unit)

/-- True iff `slot` carries no frame-relative `RelGuard` (required on return
postcondition slots `retInv`, which describe a standalone returned `Val` after
frame exit). -/
@[expose] def MirAbsSlot.noRelGuard : MirAbsSlot → Bool
  | .bool (.top g) => RelGuard.beq g .none
  | .bool (.exact _ g) => RelGuard.beq g .none
  | _ => true

/-- Frame-independent concrete value denotation of a guard-free `MirAbsSlot`
against `(ty, v)`. -/
@[expose] def MirAbsSlot.valDenote (ty : MirTy) (slot : MirAbsSlot) (v : Val) :
    Prop :=
  slot.denote ty [] (.immediate (some v))

/-- Any guard-free `MirAbsSlot` denoting `.immediate (some v)` in `locals`
satisfies the frame-independent `valDenote ty v`. -/
theorem mirAbsSlot_valDenote_of_denote {ty : MirTy} {locals : List LocalSlot}
    {slot : MirAbsSlot} {v : Val}
    (hNoG : slot.noRelGuard = true)
    (hDen : slot.denote ty locals (.immediate (some v))) :
    slot.valDenote ty v := by
  cases slot with
  | dead => exact False.elim (by nomatch hDen)
  | uint _ _ => exact hDen
  | unit => exact hDen
  | bool ba =>
    refine ⟨hDen.1, ?_⟩
    cases v with
    | bool bv =>
      cases ba with
      | bot => exact False.elim hDen.2
      | uninit => exact True.intro
      | top g =>
        dsimp only [MirAbsSlot.noRelGuard] at hNoG
        rw [relGuard_eq_of_beq hNoG]
        exact True.intro
      | exact b g =>
        dsimp only [MirAbsSlot.noRelGuard] at hNoG
        rw [relGuard_eq_of_beq hNoG]
        exact ⟨hDen.2.1, True.intro⟩
    | scalar _ | ptr _ | char _ | ordering _ | unit
    | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2

/-- Concrete denotation of `MirAbsEnv` on a concrete MIR local frame. -/
@[expose] def mirAbsEnvDenote (tys : List MirTy) (env : MirAbsEnv)
    (locals : List LocalSlot) : Prop :=
  env.length = tys.length ∧
  locals.length = tys.length ∧
  ∀ (i : Nat) (ty : MirTy) (s : MirAbsSlot) (cs : LocalSlot),
    compGetElem? tys i = some ty →
    compGetElem? env i = some s →
    compGetElem? locals i = some cs →
    s.denote ty locals cs

/-- Pointwise lattice inclusion on `MirAbsSlot`. -/
@[expose] def MirAbsSlot.le (a b : MirAbsSlot) : Bool :=
  match a, b with
  | .dead, .dead => true
  | .uint w1 a1, .uint w2 a2 =>
    intWidthBeqComp w1 w2 && AbsVal.le (bitWidthComp w1) a1 a2
  | .bool b1, .bool b2 => BoolAbs.le b1 b2
  | .unit, .unit => true
  | _, _ => false

/-- Soundness of `MirAbsSlot.le`. -/
theorem mirAbsSlot_le_sound {ty : MirTy} {locals : List LocalSlot}
    {a b : MirAbsSlot} {cs : LocalSlot}
    (hLe : MirAbsSlot.le a b = true) (ha : a.denote ty locals cs) :
    b.denote ty locals cs := by
  cases a with
  | dead =>
    cases b <;> dsimp only [MirAbsSlot.le] at hLe <;> first | exact ha | nomatch hLe
  | unit =>
    cases b <;> dsimp only [MirAbsSlot.le] at hLe <;> first | exact ha | nomatch hLe
  | bool b1 =>
    cases b with
    | bool b2 =>
      refine ⟨ha.1, ?_⟩
      cases cs with
      | dead | indirect _ => exact False.elim ha.2
      | immediate opt => exact boolAbs_le_sound hLe ha.2
    | dead | uint _ _ | unit => nomatch hLe
  | uint w1 a1 =>
    cases b with
    | uint w2 a2 =>
      dsimp only [MirAbsSlot.le] at hLe
      have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hLe)
      have hAle := bool_and_true_right hLe
      subst hwEq
      refine ⟨ha.1, ?_⟩
      cases cs with
      | dead | indirect _ => exact False.elim ha.2
      | immediate opt =>
        cases opt with
        | none => exact absVal_le_sound hAle ha.2
        | some v =>
          cases v with
          | scalar sv =>
            exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.1,
              absVal_le_sound hAle ha.2.2.2.2⟩
          | ptr _ | bool _ | char _ | ordering _ | unit
          | enumVal _ _ | tuple _ | bytes _ => exact False.elim ha.2
    | dead | bool _ | unit => nomatch hLe

/-- Pointwise inclusion on `MirAbsEnv`. -/
@[expose] def mirAbsEnvLe (e1 e2 : MirAbsEnv) : Bool :=
  e1.foldr
    (fun a ih ys =>
      match ys with
      | [] => false
      | b :: bs => MirAbsSlot.le a b && ih bs)
    (fun ys =>
      match ys with
      | [] => true
      | _ :: _ => false)
    e2

/-- Length equality implied by `mirAbsEnvLe`. -/
theorem mirAbsEnvLe_length :
    ∀ {e1 e2 : MirAbsEnv}, mirAbsEnvLe e1 e2 = true → e1.length = e2.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h =>
    congrArg Nat.succ (mirAbsEnvLe_length (bool_and_true_right h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem mirAbsEnvLe_get :
    ∀ {e1 e2 : MirAbsEnv} {i : Nat} {a b : MirAbsSlot},
      mirAbsEnvLe e1 e2 = true →
      compGetElem? e1 i = some a →
      compGetElem? e2 i = some b →
      MirAbsSlot.le a b = true
  | [], [], _, _, _, _, h1, _ => nomatch h1
  | [], _ :: _, _, _, _, h, _, _ => nomatch h
  | _ :: _, [], _, _, _, h, _, _ => nomatch h
  | x :: xs, y :: ys, 0, a, b, h, h1, h2 => by
    injection h1 with ha; injection h2 with hb; subst ha; subst hb
    exact bool_and_true_left h
  | _ :: xs, _ :: ys, i + 1, a, b, h, h1, h2 =>
    mirAbsEnvLe_get (e1 := xs) (e2 := ys) (bool_and_true_right h) h1 h2

/-- Soundness of `mirAbsEnvLe`. -/
theorem mirAbsEnvLe_sound {tys : List MirTy} {e1 e2 : MirAbsEnv}
    {locals : List LocalSlot}
    (hLe : mirAbsEnvLe e1 e2 = true) (h1 : mirAbsEnvDenote tys e1 locals) :
    mirAbsEnvDenote tys e2 locals := by
  refine ⟨Eq.trans (mirAbsEnvLe_length hLe).symm h1.1, h1.2.1, ?_⟩
  intro i ty s2 cs hTy h2 hCs
  have hEx1 : ∃ s1, compGetElem? e1 i = some s1 := by
    have hGen : ∀ (xs ys : List MirAbsSlot) (k : Nat) (y : MirAbsSlot),
        xs.length = ys.length → compGetElem? ys k = some y →
        ∃ x, compGetElem? xs k = some x := by
      intro xs
      induction xs with
      | nil =>
        intro ys k y hL hY
        cases ys with
        | nil => nomatch hY
        | cons _ _ => nomatch hL
      | cons x xs ih =>
        intro ys k y hL hY
        cases ys with
        | nil => nomatch hL
        | cons _ ys =>
          cases k with
          | zero => exact ⟨x, rfl⟩
          | succ k' =>
            injection hL with hL'
            exact ih ys k' y hL' hY
    exact hGen e1 e2 i s2 (mirAbsEnvLe_length hLe) h2
  cases hEx1 with
  | intro s1 hs1 =>
    exact mirAbsSlot_le_sound (mirAbsEnvLe_get hLe hs1 h2)
      (h1.2.2 i ty s1 cs hTy hs1 hCs)

/-- Pointwise join on `MirAbsSlot` (fails closed on incompatible tags). -/
@[expose] def MirAbsSlot.join (a b : MirAbsSlot) : Option MirAbsSlot :=
  match a, b with
  | .dead, .dead => some .dead
  | .uint w1 a1, .uint w2 a2 =>
    if intWidthBeqComp w1 w2 then
      some (.uint w1 (AbsVal.join (bitWidthComp w1) a1 a2))
    else
      none
  | .bool b1, .bool b2 => some (.bool (BoolAbs.join b1 b2))
  | .unit, .unit => some .unit
  | _, _ => none

/-- Pointwise join on `MirAbsEnv`. -/
@[expose] def mirAbsEnvJoin (e1 e2 : MirAbsEnv) : Option MirAbsEnv :=
  e1.foldr
    (fun a ih ys =>
      match ys with
      | [] => none
      | b :: bs =>
        match MirAbsSlot.join a b, ih bs with
        | some c, some cs => some (c :: cs)
        | _, _ => none)
    (fun ys =>
      match ys with
      | [] => some []
      | _ :: _ => none)
    e2

private theorem mirAbsEnvJoin_cons (a b : MirAbsSlot) (as bs : MirAbsEnv) :
    mirAbsEnvJoin (a :: as) (b :: bs) =
      match MirAbsSlot.join a b, mirAbsEnvJoin as bs with
      | some c, some cs => some (c :: cs)
      | _, _ => none := rfl

private theorem mirAbsEnvJoin_len :
    ∀ {e1 e2 e3 : MirAbsEnv},
      mirAbsEnvJoin e1 e2 = some e3 →
      e1.length = e3.length ∧ e2.length = e3.length
  | [], [], _, h => by injection h with hE; subst hE; exact ⟨rfl, rfl⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: as, b :: bs, e3, h => by
    rw [mirAbsEnvJoin_cons] at h
    cases hj : MirAbsSlot.join a b with
    | none => rw [hj] at h; nomatch h
    | some c =>
      cases hRest : mirAbsEnvJoin as bs with
      | none => rw [hj, hRest] at h; nomatch h
      | some cs =>
        rw [hj, hRest] at h
        injection h with hEq
        subst hEq
        have ih := mirAbsEnvJoin_len hRest
        exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

private theorem mirAbsEnvJoin_get :
    ∀ {e1 e2 e3 : MirAbsEnv} {i : Nat} {a b c : MirAbsSlot},
      mirAbsEnvJoin e1 e2 = some e3 →
      compGetElem? e1 i = some a →
      compGetElem? e2 i = some b →
      compGetElem? e3 i = some c →
      MirAbsSlot.join a b = some c
  | [], [], _, _, _, _, _, _, h1, _, _ => nomatch h1
  | [], _ :: _, _, _, _, _, _, h, _, _, _ => nomatch h
  | _ :: _, [], _, _, _, _, _, h, _, _, _ => nomatch h
  | x :: xs, y :: ys, e3, i, a, b, c, h, h1, h2, h3 => by
    rw [mirAbsEnvJoin_cons] at h
    cases hj : MirAbsSlot.join x y with
    | none => rw [hj] at h; nomatch h
    | some z =>
      cases hRest : mirAbsEnvJoin xs ys with
      | none => rw [hj, hRest] at h; nomatch h
      | some zs =>
        rw [hj, hRest] at h
        injection h with hEq
        subst hEq
        cases i with
        | zero =>
          injection h1 with ha; injection h2 with hb; injection h3 with hc
          subst ha; subst hb; subst hc
          exact hj
        | succ k =>
          exact mirAbsEnvJoin_get (e1 := xs) (e2 := ys) (e3 := zs) hRest h1 h2 h3

/-- Left join soundness on `MirAbsSlot`. -/
theorem mirAbsSlot_join_sound_left {ty : MirTy} {locals : List LocalSlot}
    {a b c : MirAbsSlot} {cs : LocalSlot}
    (hJ : MirAbsSlot.join a b = some c) (ha : a.denote ty locals cs) :
    c.denote ty locals cs := by
  cases a with
  | dead =>
    cases b with
    | dead => injection hJ with hc; subst hc; exact ha
    | uint _ _ | bool _ | unit => nomatch hJ
  | unit =>
    cases b with
    | unit => injection hJ with hc; subst hc; exact ha
    | dead | uint _ _ | bool _ => nomatch hJ
  | bool b1 =>
    cases b with
    | bool b2 =>
      injection hJ with hc; subst hc
      refine ⟨ha.1, ?_⟩
      cases cs with
      | dead | indirect _ => exact False.elim ha.2
      | immediate opt => exact boolAbs_join_sound_left ha.2
    | dead | uint _ _ | unit => nomatch hJ
  | uint w1 a1 =>
    cases b with
    | uint w2 a2 =>
      dsimp only [MirAbsSlot.join] at hJ
      cases hw : intWidthBeqComp w1 w2 with
      | false => rw [hw] at hJ; nomatch hJ
      | true =>
        rw [hw] at hJ
        injection hJ with hc; subst hc
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead | indirect _ => exact False.elim ha.2
        | immediate opt =>
          cases opt with
          | none => exact absVal_join_sound_left (bitWidthComp_valid w1) a1 a2 ha.2
          | some v =>
            cases v with
            | scalar sv =>
              exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.1,
                absVal_join_sound_left (bitWidthComp_valid w1) a1 a2 ha.2.2.2.2⟩
            | ptr _ | bool _ | char _ | ordering _ | unit
            | enumVal _ _ | tuple _ | bytes _ => exact False.elim ha.2
    | dead | bool _ | unit => nomatch hJ

/-- Right join soundness on `MirAbsSlot`. -/
theorem mirAbsSlot_join_sound_right {ty : MirTy} {locals : List LocalSlot}
    {a b c : MirAbsSlot} {cs : LocalSlot}
    (hJ : MirAbsSlot.join a b = some c) (hb : b.denote ty locals cs) :
    c.denote ty locals cs := by
  cases a with
  | dead =>
    cases b with
    | dead => injection hJ with hc; subst hc; exact hb
    | uint _ _ | bool _ | unit => nomatch hJ
  | unit =>
    cases b with
    | unit => injection hJ with hc; subst hc; exact hb
    | dead | uint _ _ | bool _ => nomatch hJ
  | bool b1 =>
    cases b with
    | bool b2 =>
      injection hJ with hc; subst hc
      refine ⟨hb.1, ?_⟩
      cases cs with
      | dead | indirect _ => exact False.elim hb.2
      | immediate opt => exact boolAbs_join_sound_right hb.2
    | dead | uint _ _ | unit => nomatch hJ
  | uint w1 a1 =>
    cases b with
    | uint w2 a2 =>
      dsimp only [MirAbsSlot.join] at hJ
      cases hw : intWidthBeqComp w1 w2 with
      | false => rw [hw] at hJ; nomatch hJ
      | true =>
        have hwEq := intWidth_eq_of_beqComp hw
        rw [hw] at hJ
        injection hJ with hc; subst hc; subst hwEq
        refine ⟨hb.1, ?_⟩
        cases cs with
        | dead | indirect _ => exact False.elim hb.2
        | immediate opt =>
          cases opt with
          | none => exact absVal_join_sound_right (bitWidthComp_valid w1) a1 a2 hb.2
          | some v =>
            cases v with
            | scalar sv =>
              exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2.1,
                absVal_join_sound_right (bitWidthComp_valid w1) a1 a2 hb.2.2.2.2⟩
            | ptr _ | bool _ | char _ | ordering _ | unit
            | enumVal _ _ | tuple _ | bytes _ => exact False.elim hb.2
    | dead | bool _ | unit => nomatch hJ

private theorem compGetElem?_exists_of_len {α β : Type} :
    ∀ (xs : List α) (ys : List β) (i : Nat) (y : β),
      xs.length = ys.length → compGetElem? ys i = some y →
      ∃ x, compGetElem? xs i = some x
  | [], [], _, _, _, hY => nomatch hY
  | [], _ :: _, _, _, hL, _ => nomatch hL
  | _ :: _, [], _, _, hL, _ => nomatch hL
  | x :: _, _ :: _, 0, _, _, _ => ⟨x, rfl⟩
  | _ :: xs, _ :: ys, i + 1, y, hL, hY => by
    injection hL with hL'
    exact compGetElem?_exists_of_len xs ys i y hL' hY

/-- Left join soundness on `MirAbsEnv`. -/
theorem mirAbsEnvJoin_sound_left {tys : List MirTy} {e1 e2 e3 : MirAbsEnv}
    {locals : List LocalSlot}
    (hJ : mirAbsEnvJoin e1 e2 = some e3) (h1 : mirAbsEnvDenote tys e1 locals) :
    mirAbsEnvDenote tys e3 locals := by
  have hLens := mirAbsEnvJoin_len hJ
  refine ⟨Eq.trans hLens.1.symm h1.1, h1.2.1, ?_⟩
  intro i ty s3 cs hTy h3 hCs
  have hEx1 := compGetElem?_exists_of_len e1 e3 i s3 hLens.1 h3
  have hEx2 := compGetElem?_exists_of_len e2 e3 i s3 hLens.2 h3
  cases hEx1 with
  | intro s1 hs1 =>
    cases hEx2 with
    | intro s2 hs2 =>
      exact mirAbsSlot_join_sound_left (mirAbsEnvJoin_get hJ hs1 hs2 h3)
        (h1.2.2 i ty s1 cs hTy hs1 hCs)

/-- Right join soundness on `MirAbsEnv`. -/
theorem mirAbsEnvJoin_sound_right {tys : List MirTy} {e1 e2 e3 : MirAbsEnv}
    {locals : List LocalSlot}
    (hJ : mirAbsEnvJoin e1 e2 = some e3) (h2 : mirAbsEnvDenote tys e2 locals) :
    mirAbsEnvDenote tys e3 locals := by
  have hLens := mirAbsEnvJoin_len hJ
  refine ⟨Eq.trans hLens.2.symm h2.1, h2.2.1, ?_⟩
  intro i ty s3 cs hTy h3 hCs
  have hEx1 := compGetElem?_exists_of_len e1 e3 i s3 hLens.1 h3
  have hEx2 := compGetElem?_exists_of_len e2 e3 i s3 hLens.2 h3
  cases hEx1 with
  | intro s1 hs1 =>
    cases hEx2 with
    | intro s2 hs2 =>
      exact mirAbsSlot_join_sound_right (mirAbsEnvJoin_get hJ hs1 hs2 h3)
        (h2.2.2 i ty s2 cs hTy hs2 hCs)

/-! ## 3. Environment Updates, Guard Invalidation, and Branch Refinement -/

private theorem setElem?_length {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      Trusted.MirSemantics.setElem? xs i v = some xs' → xs'.length = xs.length
  | [], _, _, _, h => nomatch h
  | _ :: _, _, 0, _, h => by injection h with hEq; subst hEq; rfl
  | _ :: xs, _, i + 1, v, h => by
    dsimp only [Trusted.MirSemantics.setElem?] at h
    cases hR : Trusted.MirSemantics.setElem? xs i v with
    | none => rw [hR] at h; nomatch h
    | some tl =>
      rw [hR] at h
      injection h with hEq
      subst hEq
      exact congrArg Nat.succ (setElem?_length hR)

/-- `compSetElem?` preserves list length. -/
theorem compSetElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : compSetElem? xs i v = some xs') : xs'.length = xs.length := by
  rw [compSetElem?_eq] at h
  exact setElem?_length h

private theorem getElem?_setElem_same {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      Trusted.MirSemantics.setElem? xs i v = some xs' →
      Trusted.MirSemantics.getElem? xs' i = some v
  | [], _, _, _, h => nomatch h
  | _ :: _, _, 0, _, h => by injection h with hEq; subst hEq; rfl
  | _ :: xs, _, i + 1, v, h => by
    dsimp only [Trusted.MirSemantics.setElem?] at h
    cases hR : Trusted.MirSemantics.setElem? xs i v with
    | none => rw [hR] at h; nomatch h
    | some tl =>
      rw [hR] at h
      injection h with hEq
      subst hEq
      dsimp only [Trusted.MirSemantics.getElem?]
      exact getElem?_setElem_same hR

/-- `compGetElem?` at the updated index after `compSetElem?`. -/
theorem compGetElem?_setElem_same {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : compSetElem? xs i v = some xs') : compGetElem? xs' i = some v := by
  rw [compSetElem?_eq] at h
  rw [compGetElem?_eq]
  exact getElem?_setElem_same h

private theorem getElem?_setElem_ne {α : Type} :
    ∀ {xs xs' : List α} {i j : Nat} {v : α},
      Trusted.MirSemantics.setElem? xs i v = some xs' → i ≠ j →
      Trusted.MirSemantics.getElem? xs' j = Trusted.MirSemantics.getElem? xs j
  | [], _, _, _, _, h, _ => nomatch h
  | _ :: _, _, 0, 0, _, _, hNe => False.elim (hNe rfl)
  | _ :: _, _, 0, _ + 1, _, h, _ => by injection h with hEq; subst hEq; rfl
  | _ :: xs, _, i + 1, 0, v, h, _ => by
    dsimp only [Trusted.MirSemantics.setElem?] at h
    cases hR : Trusted.MirSemantics.setElem? xs i v with
    | none => rw [hR] at h; nomatch h
    | some tl => rw [hR] at h; injection h with hEq; subst hEq; rfl
  | _ :: xs, _, i + 1, j + 1, v, h, hNe => by
    dsimp only [Trusted.MirSemantics.setElem?] at h
    cases hR : Trusted.MirSemantics.setElem? xs i v with
    | none => rw [hR] at h; nomatch h
    | some tl =>
      rw [hR] at h
      injection h with hEq
      subst hEq
      dsimp only [Trusted.MirSemantics.getElem?]
      exact getElem?_setElem_ne hR (fun hEq => hNe (congrArg Nat.succ hEq))

/-- `compGetElem?` at any distinct index after `compSetElem?`. -/
theorem compGetElem?_setElem_ne {α : Type} {xs xs' : List α} {i j : Nat} {v : α}
    (h : compSetElem? xs i v = some xs') (hNe : i ≠ j) :
    compGetElem? xs' j = compGetElem? xs j := by
  rw [compSetElem?_eq] at h
  rw [compGetElem?_eq, compGetElem?_eq]
  exact getElem?_setElem_ne h hNe

private theorem setElem?_exists_of_get {α : Type} :
    ∀ (xs : List α) (i : Nat) {old : α} (v : α),
      Trusted.MirSemantics.getElem? xs i = some old →
      ∃ xs', Trusted.MirSemantics.setElem? xs i v = some xs'
  | [], _, _, _, h => nomatch h
  | _ :: xs, 0, _, v, _ => ⟨v :: xs, rfl⟩
  | x :: xs, i + 1, _, v, h => by
    cases setElem?_exists_of_get xs i v h with
    | intro tl htl =>
      refine ⟨x :: tl, ?_⟩
      dsimp only [Trusted.MirSemantics.setElem?]
      rw [htl]

/-- `compSetElem?` succeeds whenever `compGetElem?` succeeds at `i`. -/
theorem compSetElem?_exists_of_get {α : Type} (xs : List α) (i : Nat) {old : α}
    (v : α) (h : compGetElem? xs i = some old) :
    ∃ xs', compSetElem? xs i v = some xs' := by
  rw [compGetElem?_eq] at h
  cases setElem?_exists_of_get xs i v h with
  | intro xs' hxs' =>
    exact ⟨xs', Eq.trans (compSetElem?_eq xs i v) hxs'⟩

/-- Clears all `RelGuard`s in `env` mentioning `id`. -/
@[expose] def clearGuardsFor (id : LocalId) (env : MirAbsEnv) : MirAbsEnv :=
  env.map (fun s =>
    match s with
    | .bool ba => .bool (ba.clearGuardIf id)
    | other => other)

/-- Update `env[id] := newSlot` while clearing `RelGuard`s mentioning `id`. -/
@[expose] def setMirAbsSlot (id : LocalId) (newSlot : MirAbsSlot) (env :
    MirAbsEnv) :
    Option MirAbsEnv :=
  match compSetElem? (clearGuardsFor id env) id newSlot with
  | some env' => some env'
  | none => none

private theorem compGetElem?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat),
      compGetElem? (xs.map f) i = (compGetElem? xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => compGetElem?_map f xs i

private theorem listLength_map_local {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (listLength_map_local f xs)

private theorem relGuard_preserved_on_update {locals locals' : List LocalSlot}
    {id : LocalId} {newCs : LocalSlot} {g : RelGuard} {b : Bool}
    (hSet : compSetElem? locals id newCs = some locals')
    (hNoMent : g.mentions id = false)
    (hDen : g.denote locals b) :
    g.denote locals' b := by
  have hLocEq : ∀ r w, Nat.beq r id = false →
      localUintNat? locals' r w = localUintNat? locals r w := by
    intro r w hNeB
    have hNe : id ≠ r := fun hE => by
      rw [← hE, nat_beq_refl id] at hNeB; nomatch hNeB
    dsimp only [localUintNat?]
    rw [compGetElem?_setElem_ne hSet hNe]
  cases g with
  | none => exact True.intro
  | uleConst r w bound =>
    intro x hx
    rw [hLocEq r w hNoMent] at hx
    exact hDen x hx
  | ugtConst r w bound =>
    intro x hx
    rw [hLocEq r w hNoMent] at hx
    exact hDen x hx
  | ultReg l r w =>
    intro x y hx hy
    dsimp only [RelGuard.mentions] at hNoMent
    rw [hLocEq l w (bool_or_false_left hNoMent)] at hx
    rw [hLocEq r w (bool_or_false_right hNoMent)] at hy
    exact hDen x y hx hy
  | ugeReg l r w =>
    intro x y hx hy
    dsimp only [RelGuard.mentions] at hNoMent
    rw [hLocEq l w (bool_or_false_left hNoMent)] at hx
    rw [hLocEq r w (bool_or_false_right hNoMent)] at hy
    exact hDen x y hx hy
  | ueqConst r w val =>
    intro x hx
    rw [hLocEq r w hNoMent] at hx
    exact hDen x hx
  | uneConst r w val =>
    intro x hx
    rw [hLocEq r w hNoMent] at hx
    exact hDen x hx

/-- Updating both concrete `locals[id] := newCs` and abstract
`setMirAbsSlot id newSlot env` preserves `mirAbsEnvDenote` whenever `newSlot`
denotes `newCs` in `locals'`. -/
theorem setMirAbsSlot_sound {tys : List MirTy} {env env' : MirAbsEnv}
    {locals locals' : List LocalSlot} {id : LocalId}
    {newSlot : MirAbsSlot} {newCs : LocalSlot} {tyId : MirTy}
    (hEnv : mirAbsEnvDenote tys env locals)
    (hTyId : compGetElem? tys id = some tyId)
    (hSetAbs : setMirAbsSlot id newSlot env = some env')
    (hSetConc : compSetElem? locals id newCs = some locals')
    (hNewDen : newSlot.denote tyId locals' newCs) :
    mirAbsEnvDenote tys env' locals' := by
  dsimp only [setMirAbsSlot] at hSetAbs
  cases hS : compSetElem? (clearGuardsFor id env) id newSlot with
  | none => rw [hS] at hSetAbs; nomatch hSetAbs
  | some res =>
    rw [hS] at hSetAbs
    injection hSetAbs with hEq
    subst hEq
    have hLenClr : (clearGuardsFor id env).length = env.length :=
      listLength_map_local _ env
    refine ⟨Eq.trans (compSetElem?_length hS) (Eq.trans hLenClr hEnv.1),
            Eq.trans (compSetElem?_length hSetConc) hEnv.2.1, ?_⟩
    intro i ty s cs hTy hAbs hCs
    cases hEqId : Nat.beq id i with
    | true =>
      have hI := Nat.eq_of_beq_eq_true hEqId
      subst hI
      rw [compGetElem?_setElem_same hS] at hAbs
      rw [compGetElem?_setElem_same hSetConc] at hCs
      rw [hTyId] at hTy
      injection hAbs with hs; injection hCs with hcs; injection hTy with ht
      subst hs; subst hcs; subst ht
      exact hNewDen
    | false =>
      have hNe : id ≠ i := fun hE => by
        rw [hE, nat_beq_refl i] at hEqId; nomatch hEqId
      rw [compGetElem?_setElem_ne hS hNe] at hAbs
      rw [compGetElem?_setElem_ne hSetConc hNe] at hCs
      dsimp only [clearGuardsFor] at hAbs
      rw [compGetElem?_map] at hAbs
      cases hOld : compGetElem? env i with
      | none => rw [hOld] at hAbs; nomatch hAbs
      | some oldSlot =>
        rw [hOld] at hAbs
        injection hAbs with hs
        subst hs
        have hOldDen := hEnv.2.2 i ty oldSlot cs hTy hOld hCs
        cases oldSlot with
        | dead => exact hOldDen
        | unit => exact hOldDen
        | uint w a => exact hOldDen
        | bool ba =>
          refine ⟨hOldDen.1, ?_⟩
          cases cs with
          | dead | indirect _ => exact False.elim hOldDen.2
          | immediate opt =>
            cases opt with
            | none =>
              cases ba with
              | bot | top _ | exact _ _ => exact False.elim hOldDen.2
              | uninit => exact True.intro
            | some v =>
              cases v with
              | bool bv =>
                cases ba with
                | bot => exact False.elim hOldDen.2
                | uninit => exact True.intro
                | top g =>
                  dsimp only [BoolAbs.clearGuardIf]
                  cases hM : g.mentions id with
                  | true => exact True.intro
                  | false => exact relGuard_preserved_on_update hSetConc hM hOldDen.2
                | exact ev g =>
                  dsimp only [BoolAbs.clearGuardIf]
                  cases hM : g.mentions id with
                  | true => exact ⟨hOldDen.2.1, True.intro⟩
                  | false =>
                    exact ⟨hOldDen.2.1,
                      relGuard_preserved_on_update hSetConc hM hOldDen.2.2⟩
              | scalar _ | ptr _ | char _ | ordering _ | unit
              | enumVal _ _ | tuple _ | bytes _ => exact False.elim hOldDen.2

/-- Refines `env` using `RelGuard` `g` assuming boolean value `branchVal`. -/
@[expose] def refineEnvByGuard (env : MirAbsEnv) (g : RelGuard) (branchVal :
    Bool) :
    MirAbsEnv :=
  let eff := if branchVal then g else g.negate
  match eff with
  | .none => env
  | .uleConst r w bound =>
    match compGetElem? env r with
    | some (.uint w' a) =>
      if intWidthBeqComp w w' && a.isInit then
        let a' := AbsVal.refineUleConst (bitWidthComp w) a bound
        match compSetElem? env r (.uint w a') with
        | some env' => env'
        | none => env
      else env
    | _ => env
  | .ugtConst r w bound =>
    match compGetElem? env r with
    | some (.uint w' a) =>
      if intWidthBeqComp w w' && a.isInit then
        let a' := AbsVal.refineUgtConst (bitWidthComp w) a bound
        match compSetElem? env r (.uint w a') with
        | some env' => env'
        | none => env
      else env
    | _ => env
  | .ultReg l r w =>
    match compGetElem? env l, compGetElem? env r with
    | some (.uint wl al), some (.uint wr ar) =>
      if intWidthBeqComp w wl && intWidthBeqComp w wr &&
         al.isInit && ar.isInit then
        let al' := AbsVal.refineBltReg (bitWidthComp w) al ar
        match compSetElem? env l (.uint w al') with
        | some env' => env'
        | none => env
      else env
    | _, _ => env
  | .ugeReg l r w =>
    match compGetElem? env l, compGetElem? env r with
    | some (.uint wl al), some (.uint wr ar) =>
      if intWidthBeqComp w wl && intWidthBeqComp w wr &&
         al.isInit && ar.isInit then
        let al' := AbsVal.refineBgeReg (bitWidthComp w) al ar
        match compSetElem? env l (.uint w al') with
        | some env' => env'
        | none => env
      else env
    | _, _ => env
  | .ueqConst r w val =>
    match compGetElem? env r with
    | some (.uint w' a) =>
      if intWidthBeqComp w w' && a.isInit then
        let a' := AbsVal.refineEqConst (bitWidthComp w) a val
        match compSetElem? env r (.uint w a') with
        | some env' => env'
        | none => env
      else env
    | _ => env
  | .uneConst _ _ _ => env

/-- Helper for in-place slot refinement at a single local without modifying
`locals`. -/
private theorem refineSingleSlot_sound {tys : List MirTy} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {r : LocalId} {newSlot : MirAbsSlot}
    (hEnv : mirAbsEnvDenote tys env locals)
    (hSet : compSetElem? env r newSlot = some env')
    (hRef : ∀ ty cs, compGetElem? tys r = some ty →
      compGetElem? locals r = some cs → newSlot.denote ty locals cs) :
    mirAbsEnvDenote tys env' locals := by
  refine ⟨Eq.trans (compSetElem?_length hSet) hEnv.1, hEnv.2.1, ?_⟩
  intro i ty s cs hTy hAbs hCs
  cases hEq : Nat.beq r i with
  | true =>
    have hI := Nat.eq_of_beq_eq_true hEq
    subst hI
    rw [compGetElem?_setElem_same hSet] at hAbs
    injection hAbs with hs; subst hs
    exact hRef ty cs hTy hCs
  | false =>
    have hNe : r ≠ i := fun hE => by rw [hE, nat_beq_refl i] at hEq; nomatch hEq
    rw [compGetElem?_setElem_ne hSet hNe] at hAbs
    exact hEnv.2.2 i ty s cs hTy hAbs hCs

/-- Soundness of `refineEnvByGuard`. -/
theorem refineEnvByGuard_sound {tys : List MirTy} {env : MirAbsEnv}
    {locals : List LocalSlot} {g : RelGuard} {b : Bool}
    (hEnv : mirAbsEnvDenote tys env locals) (hGuard : g.denote locals b) :
    mirAbsEnvDenote tys (refineEnvByGuard env g b) locals := by
  have hEff : (if b then g else g.negate).denote locals true := by
    cases b with
    | true => exact hGuard
    | false => exact relGuard_negate_sound hGuard
  dsimp only [refineEnvByGuard]
  cases hG : (if b then g else g.negate) with
  | none | uneConst _ _ _ => exact hEnv
  | uleConst r w bound =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | bool _ | unit => exact hEnv
      | uint w' a =>
        dsimp only
        cases hC : intWidthBeqComp w w' && a.isInit with
        | false => exact hEnv
        | true =>
          have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
          have hInit := bool_and_true_right hC
          subst hwEq
          rw [ite_bool_true rfl]
          cases hSet : compSetElem? env r
              (.uint w (AbsVal.refineUleConst (bitWidthComp w) a bound)) with
          | none => exact hEnv
          | some env' =>
            apply refineSingleSlot_sound hEnv hSet
            intro ty cs hTy hCs
            have hDen := hEnv.2.2 r ty (.uint w a) cs hTy hGet hCs
            refine ⟨hDen.1, ?_⟩
            cases cs with
            | dead | indirect _ => exact False.elim hDen.2
            | immediate opt =>
              cases opt with
              | none =>
                have hEx := absVal_init_of_isInit hInit hDen.2
                cases hEx with | intro _ hx => nomatch hx.1
              | some v =>
                cases v with
                | scalar sv =>
                  have hLoc : localUintNat? locals r w = some sv.bits.toNat := by
                    dsimp only [localUintNat?]
                    rw [hCs]
                    dsimp only
                    rw [hDen.2.1, hDen.2.2.1, intWidthBeqComp_refl w]
                    rfl
                  have hLe : sv.bits.toNat ≤ bound := (hEff sv.bits.toNat hLoc).mp rfl
                  exact ⟨hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                    absVal_refineUleConst_sound (bitWidthComp_valid w)
                      hDen.2.2.2.2 hInit hLe⟩
                | ptr _ | bool _ | char _ | ordering _ | unit
                | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2
  | ugtConst r w bound =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | bool _ | unit => exact hEnv
      | uint w' a =>
        dsimp only
        cases hC : intWidthBeqComp w w' && a.isInit with
        | false => exact hEnv
        | true =>
          have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
          have hInit := bool_and_true_right hC
          subst hwEq
          rw [ite_bool_true rfl]
          cases hSet : compSetElem? env r
              (.uint w (AbsVal.refineUgtConst (bitWidthComp w) a bound)) with
          | none => exact hEnv
          | some env' =>
            apply refineSingleSlot_sound hEnv hSet
            intro ty cs hTy hCs
            have hDen := hEnv.2.2 r ty (.uint w a) cs hTy hGet hCs
            refine ⟨hDen.1, ?_⟩
            cases cs with
            | dead | indirect _ => exact False.elim hDen.2
            | immediate opt =>
              cases opt with
              | none =>
                have hEx := absVal_init_of_isInit hInit hDen.2
                cases hEx with | intro _ hx => nomatch hx.1
              | some v =>
                cases v with
                | scalar sv =>
                  have hLoc : localUintNat? locals r w = some sv.bits.toNat := by
                    dsimp only [localUintNat?]
                    rw [hCs]
                    dsimp only
                    rw [hDen.2.1, hDen.2.2.1, intWidthBeqComp_refl w]
                    rfl
                  have hGt : bound < sv.bits.toNat := (hEff sv.bits.toNat hLoc).mp rfl
                  exact ⟨hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                    absVal_refineUgtConst_sound (bitWidthComp_valid w)
                      hDen.2.2.2.2 hInit hGt⟩
                | ptr _ | bool _ | char _ | ordering _ | unit
                | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2
  | ultReg l r w =>
    rw [hG] at hEff
    dsimp only
    cases hGetL : compGetElem? env l with
    | none => exact hEnv
    | some sl =>
      cases sl with
      | dead | bool _ | unit => exact hEnv
      | uint wl al =>
        cases hGetR : compGetElem? env r with
        | none => exact hEnv
        | some sr =>
          cases sr with
          | dead | bool _ | unit => exact hEnv
          | uint wr ar =>
            dsimp only
            cases hC : intWidthBeqComp w wl && intWidthBeqComp w wr &&
                al.isInit && ar.isInit with
            | false => exact hEnv
            | true =>
              have h123 := bool_and_true_left hC
              have h12 := bool_and_true_left h123
              have hwl := intWidth_eq_of_beqComp (bool_and_true_left h12)
              have hwr := intWidth_eq_of_beqComp (bool_and_true_right h12)
              have hInitL := bool_and_true_right h123
              have hInitR := bool_and_true_right hC
              subst hwl; subst hwr
              rw [ite_bool_true rfl]
              cases hSet : compSetElem? env l
                  (.uint w (AbsVal.refineBltReg (bitWidthComp w) al ar)) with
              | none => exact hEnv
              | some env' =>
                apply refineSingleSlot_sound hEnv hSet
                intro tyL csL hTyL hCsL
                have hDenL := hEnv.2.2 l tyL (.uint w al) csL hTyL hGetL hCsL
                have hExTyR := compGetElem?_exists_of_len tys env r (.uint w ar) hEnv.1.symm hGetR
                have hExCsR := compGetElem?_exists_of_len locals env r (.uint w ar)
                  (Eq.trans hEnv.2.1 hEnv.1.symm) hGetR
                cases hExTyR with | intro tyR hTyR =>
                cases hExCsR with | intro csR hCsR =>
                have hDenR := hEnv.2.2 r tyR (.uint w ar) csR hTyR hGetR hCsR
                refine ⟨hDenL.1, ?_⟩
                cases csL with
                | dead | indirect _ => exact False.elim hDenL.2
                | immediate optL =>
                  cases optL with
                  | none =>
                    cases absVal_init_of_isInit hInitL hDenL.2 with
                    | intro _ hx => nomatch hx.1
                  | some vL =>
                    cases vL with
                    | scalar svL =>
                      cases csR with
                      | dead | indirect _ => exact False.elim hDenR.2
                      | immediate optR =>
                        cases optR with
                        | none =>
                          cases absVal_init_of_isInit hInitR hDenR.2 with
                          | intro _ hy => nomatch hy.1
                        | some vR =>
                          cases vR with
                          | scalar svR =>
                            have hLocL : localUintNat? locals l w = some svL.bits.toNat := by
                              dsimp only [localUintNat?]
                              rw [hCsL]; dsimp only
                              rw [hDenL.2.1, hDenL.2.2.1, intWidthBeqComp_refl w]; rfl
                            have hLocR : localUintNat? locals r w = some svR.bits.toNat := by
                              dsimp only [localUintNat?]
                              rw [hCsR]; dsimp only
                              rw [hDenR.2.1, hDenR.2.2.1, intWidthBeqComp_refl w]; rfl
                            have hLt := (hEff svL.bits.toNat svR.bits.toNat hLocL hLocR).mp rfl
                            exact ⟨hDenL.2.1, hDenL.2.2.1, hDenL.2.2.2.1,
                              absVal_refineBltReg_sound (bitWidthComp_valid w)
                                hDenL.2.2.2.2 hDenR.2.2.2.2 hInitL hInitR hLt⟩
                          | ptr _ | bool _ | char _ | ordering _ | unit
                          | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenR.2
                    | ptr _ | bool _ | char _ | ordering _ | unit
                    | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenL.2
  | ugeReg l r w =>
    rw [hG] at hEff
    dsimp only
    cases hGetL : compGetElem? env l with
    | none => exact hEnv
    | some sl =>
      cases sl with
      | dead | bool _ | unit => exact hEnv
      | uint wl al =>
        cases hGetR : compGetElem? env r with
        | none => exact hEnv
        | some sr =>
          cases sr with
          | dead | bool _ | unit => exact hEnv
          | uint wr ar =>
            dsimp only
            cases hC : intWidthBeqComp w wl && intWidthBeqComp w wr &&
                al.isInit && ar.isInit with
            | false => exact hEnv
            | true =>
              have h123 := bool_and_true_left hC
              have h12 := bool_and_true_left h123
              have hwl := intWidth_eq_of_beqComp (bool_and_true_left h12)
              have hwr := intWidth_eq_of_beqComp (bool_and_true_right h12)
              have hInitL := bool_and_true_right h123
              have hInitR := bool_and_true_right hC
              subst hwl; subst hwr
              rw [ite_bool_true rfl]
              cases hSet : compSetElem? env l
                  (.uint w (AbsVal.refineBgeReg (bitWidthComp w) al ar)) with
              | none => exact hEnv
              | some env' =>
                apply refineSingleSlot_sound hEnv hSet
                intro tyL csL hTyL hCsL
                have hDenL := hEnv.2.2 l tyL (.uint w al) csL hTyL hGetL hCsL
                have hExTyR := compGetElem?_exists_of_len tys env r (.uint w ar) hEnv.1.symm hGetR
                have hExCsR := compGetElem?_exists_of_len locals env r (.uint w ar)
                  (Eq.trans hEnv.2.1 hEnv.1.symm) hGetR
                cases hExTyR with | intro tyR hTyR =>
                cases hExCsR with | intro csR hCsR =>
                have hDenR := hEnv.2.2 r tyR (.uint w ar) csR hTyR hGetR hCsR
                refine ⟨hDenL.1, ?_⟩
                cases csL with
                | dead | indirect _ => exact False.elim hDenL.2
                | immediate optL =>
                  cases optL with
                  | none =>
                    cases absVal_init_of_isInit hInitL hDenL.2 with
                    | intro _ hx => nomatch hx.1
                  | some vL =>
                    cases vL with
                    | scalar svL =>
                      cases csR with
                      | dead | indirect _ => exact False.elim hDenR.2
                      | immediate optR =>
                        cases optR with
                        | none =>
                          cases absVal_init_of_isInit hInitR hDenR.2 with
                          | intro _ hy => nomatch hy.1
                        | some vR =>
                          cases vR with
                          | scalar svR =>
                            have hLocL : localUintNat? locals l w = some svL.bits.toNat := by
                              dsimp only [localUintNat?]
                              rw [hCsL]; dsimp only
                              rw [hDenL.2.1, hDenL.2.2.1, intWidthBeqComp_refl w]; rfl
                            have hLocR : localUintNat? locals r w = some svR.bits.toNat := by
                              dsimp only [localUintNat?]
                              rw [hCsR]; dsimp only
                              rw [hDenR.2.1, hDenR.2.2.1, intWidthBeqComp_refl w]; rfl
                            have hGe := (hEff svL.bits.toNat svR.bits.toNat hLocL hLocR).mp rfl
                            exact ⟨hDenL.2.1, hDenL.2.2.1, hDenL.2.2.2.1,
                              absVal_refineBgeReg_sound (bitWidthComp_valid w)
                                hDenL.2.2.2.2 hDenR.2.2.2.2 hInitL hInitR hGe⟩
                          | ptr _ | bool _ | char _ | ordering _ | unit
                          | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenR.2
                    | ptr _ | bool _ | char _ | ordering _ | unit
                    | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenL.2
  | ueqConst r w val =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | bool _ | unit => exact hEnv
      | uint w' a =>
        dsimp only
        cases hC : intWidthBeqComp w w' && a.isInit with
        | false => exact hEnv
        | true =>
          have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
          have hInit := bool_and_true_right hC
          subst hwEq
          rw [ite_bool_true rfl]
          cases hSet : compSetElem? env r
              (.uint w (AbsVal.refineEqConst (bitWidthComp w) a val)) with
          | none => exact hEnv
          | some env' =>
            apply refineSingleSlot_sound hEnv hSet
            intro ty cs hTy hCs
            have hDen := hEnv.2.2 r ty (.uint w a) cs hTy hGet hCs
            refine ⟨hDen.1, ?_⟩
            cases cs with
            | dead | indirect _ => exact False.elim hDen.2
            | immediate opt =>
              cases opt with
              | none =>
                cases absVal_init_of_isInit hInit hDen.2 with
                | intro _ hx => nomatch hx.1
              | some v =>
                cases v with
                | scalar sv =>
                  have hLoc : localUintNat? locals r w = some sv.bits.toNat := by
                    dsimp only [localUintNat?]
                    rw [hCs]; dsimp only
                    rw [hDen.2.1, hDen.2.2.1, intWidthBeqComp_refl w]; rfl
                  have hEq := (hEff sv.bits.toNat hLoc).mp rfl
                  exact ⟨hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                    absVal_refineEqConst_sound (bitWidthComp_valid w)
                      hDen.2.2.2.2 hInit hEq⟩
                | ptr _ | bool _ | char _ | ordering _ | unit
                | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2

end Anneal.AiPcc

end
