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
public import Anneal.MirWp.Scalars
public import Anneal.AiPcc.BitArith
public import Anneal.AiPcc.Tnum
public import Anneal.AiPcc.WrappedInterval
public import Anneal.AiPcc.ReducedProduct

public section

namespace Anneal.AiPcc

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal Anneal.MirWp

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

private theorem nat_pred_succ_of_pos {n : Nat} (h : 0 < n) :
    Nat.succ (n - 1) = n := Nat.sub_add_cancel h

private theorem int_negSucc_sub_ofNat (k d : Nat) :
    Int.negSucc k - Int.ofNat d = Int.negSucc (k + d) := by
  cases d with
  | zero =>
    change Int.subNatNat 0 (Nat.succ k) = Int.negSucc (k + 0)
    rw [Nat.add_zero]
    rfl
  | succ d' =>
    change Int.negSucc (Nat.succ (k + d')) = Int.negSucc (k + (d' + 1))
    rfl

private theorem nat_le_or_gt (a b : Nat) : a ≤ b ∨ b < a := by
  cases hBle : Nat.ble a b with
  | true => exact Or.inl (Nat.le_of_ble_eq_true hBle)
  | false =>
    exact Or.inr (Nat.lt_of_not_le (fun hLe => by
      rw [Nat.ble_eq_true_of_le hLe] at hBle
      nomatch hBle))

private theorem int_subNatNat_of_le (a b : Nat) (h : b ≤ a) :
    Int.subNatNat a b = Int.ofNat (a - b) := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]

private theorem int_subNatNat_of_lt (a b : Nat) (h : a < b) :
    Int.subNatNat a b = Int.negSucc (b - a - 1) := by
  unfold Int.subNatNat
  have hPos : 0 < b - a := Nat.sub_pos_of_lt h
  cases hSub : b - a with
  | zero => rw [hSub] at hPos; nomatch hPos
  | succ _ => rfl

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

/-! ### Signed Integer (`i8..i128`, `isize`) & General Scalar `MirSemantics` Bridge -/

/-- Agreement between `modPow2 (bitWidthComp w)` and `intWidthModulus w`. -/
theorem modPow2_bitWidthComp_eq_modulus (w : IntWidth) :
    modPow2 (bitWidthComp w) = intWidthModulus w := by
  cases w <;> decide

/-- `halfModPow2 (bitWidthComp w)` equals `intWidthHalfModulus w`. -/
theorem halfModPow2_bitWidthComp_eq_half (w : IntWidth) :
    halfModPow2 (bitWidthComp w) = intWidthHalfModulus w := by
  cases w <;> decide

/-- Every target shift width `bitWidthComp w ≤ 128` fits strictly below the
signed positive ceiling `halfModPow2 (bitWidthComp rw_) ≥ 128` of any RHS
integer width `rw_`. -/
theorem bitWidthComp_le_halfModPow2 (w rw_ : IntWidth) :
    bitWidthComp w ≤ halfModPow2 (bitWidthComp rw_) := by
  cases w <;> cases rw_ <;> decide

private theorem same_sint_guard_false (w : IntWidth) :
    (!(IntWidth.beq w w && (true == true))) = false := by
  rw [intWidth_beq_refl w]
  rfl

/-- `checkVal` accepts every in-range signed scalar at its declared width. -/
theorem checkVal_sint_of_lt {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    checkVal (.scalar ⟨w, true, b⟩) (.int w true) = true := by
  have hWf : ScalarVal.wf ⟨w, true, b⟩ = true := by
    dsimp only [ScalarVal.wf]
    rw [truncateBits_of_lt hLt]
    dsimp only [BEq.beq]
    exact decide_eq_true rfl
  dsimp only [checkVal, Val.ty?]
  rw [ite_bool_true hWf]
  dsimp only [MirTy.beq]
  rw [intWidth_beq_refl w]
  rfl

/-- Biased-coordinate characterization of `decodeScalar` on in-range signed
scalars: `decodeScalar ⟨w, true, b⟩ = signedBias(b) - 2^(w-1)`. -/
theorem decodeScalar_sint_eq_bias {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    decodeScalar ⟨w, true, b⟩ =
      Int.ofNat (signedBias (bitWidthComp w) b.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) := by
  have hw := bitWidthComp_valid w
  have hModEq := modPow2_bitWidthComp_eq_modulus w
  have hHalfEq := halfModPow2_bitWidthComp_eq_half w
  cases Nat.lt_or_ge b.toNat (halfModPow2 (bitWidthComp w)) with
  | inl hSmall =>
    rw [decodeScalar_signed_of_lt_half (by rw [← hHalfEq]; exact hSmall),
        signedBias_of_lt_half hw hSmall,
        int_ofNat_sub_of_le (Nat.le_add_left _ _),
        Nat.add_sub_cancel]
  | inr hBig =>
    rw [decodeScalar_signed_of_ge_half
          (by rw [← hHalfEq]; exact hBig)
          (by rw [← hModEq]; exact hLt),
        signedBias_of_ge_half hw hBig hLt]
    have hSubLtH : b.toNat - halfModPow2 (bitWidthComp w) <
        halfModPow2 (bitWidthComp w) := by
      have hM := modPow2_eq_half_add_half hw
      have h1 : (b.toNat - halfModPow2 (bitWidthComp w)) + halfModPow2 (bitWidthComp w) <
          halfModPow2 (bitWidthComp w) + halfModPow2 (bitWidthComp w) := by
        rw [Nat.sub_add_cancel hBig, ← hM]; exact hLt
      exact nat_lt_of_add_lt_add_right h1
    rw [int_ofNat_sub_of_lt hSubLtH, ← hModEq]
    have hDiffEq :
        halfModPow2 (bitWidthComp w) - (b.toNat - halfModPow2 (bitWidthComp w)) =
          modPow2 (bitWidthComp w) - b.toNat := by
      have hAdd :
          (halfModPow2 (bitWidthComp w) - (b.toNat - halfModPow2 (bitWidthComp w))) + b.toNat =
          (modPow2 (bitWidthComp w) - b.toNat) + b.toNat := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt hLt)]
        have hBDecomp : (b.toNat - halfModPow2 (bitWidthComp w)) + halfModPow2 (bitWidthComp w) =
            b.toNat := Nat.sub_add_cancel hBig
        have hStep := congrArg
          (fun z => (halfModPow2 (bitWidthComp w) -
            (b.toNat - halfModPow2 (bitWidthComp w))) + z) hBDecomp.symm
        rw [← Nat.add_assoc,
            Nat.sub_add_cancel (Nat.le_of_lt hSubLtH),
            ← modPow2_eq_half_add_half hw] at hStep
        exact hStep
      exact Nat.add_right_cancel hAdd
    rw [hDiffEq]

private theorem int_sub_eq_sub_iff {a b c : Nat} :
    (Int.ofNat a - Int.ofNat c = Int.ofNat b - Int.ofNat c) ↔ a = b := by
  constructor
  · intro h
    cases nat_le_or_gt c a with
    | inl hca =>
      cases nat_le_or_gt c b with
      | inl hcb =>
        rw [int_ofNat_sub_of_le hca, int_ofNat_sub_of_le hcb] at h
        have hSub := Int.ofNat.inj h
        have h1 := congrArg (fun z => z + c) hSub
        rw [Nat.sub_add_cancel hca, Nat.sub_add_cancel hcb] at h1
        exact h1
      | inr hbc =>
        rw [int_ofNat_sub_of_le hca, int_ofNat_sub_of_lt hbc] at h
        nomatch h
    | inr hac =>
      cases nat_le_or_gt c b with
      | inl hcb =>
        rw [int_ofNat_sub_of_lt hac, int_ofNat_sub_of_le hcb] at h
        nomatch h
      | inr hbc =>
        rw [int_ofNat_sub_of_lt hac, int_ofNat_sub_of_lt hbc] at h
        have hNeg := Int.negSucc.inj h
        have h1 := congrArg Nat.succ hNeg
        rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt hac),
            nat_pred_succ_of_pos (Nat.sub_pos_of_lt hbc)] at h1
        have hAdd : (c - a) + a = (c - b) + b := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hac), Nat.sub_add_cancel (Nat.le_of_lt hbc)]
        rw [h1] at hAdd
        exact Nat.add_left_cancel hAdd
  · intro h; subst h; rfl

private theorem int_sub_le_sub_iff {a b c : Nat} :
    (Int.ofNat a - Int.ofNat c ≤ Int.ofNat b - Int.ofNat c) ↔ a ≤ b := by
  have hDiff : (Int.ofNat b - Int.ofNat c) - (Int.ofNat a - Int.ofNat c) =
      Int.ofNat b - Int.ofNat a := by
    cases nat_le_or_gt c a with
    | inl hca =>
      cases nat_le_or_gt c b with
      | inl hcb =>
        rw [int_ofNat_sub_of_le hca, int_ofNat_sub_of_le hcb,
            int_ofNat_sub_eq_subNatNat, int_ofNat_sub_eq_subNatNat]
        cases nat_le_or_gt a b with
        | inl hab =>
          rw [int_subNatNat_of_le _ _ (Nat.sub_le_sub_right hab c),
              int_subNatNat_of_le _ _ hab]
          apply congrArg Int.ofNat
          have hAdd : (b - c) - (a - c) + a = (b - a) + a := by
            rw [Nat.sub_add_cancel hab]
            have hA : (a - c) + c = a := Nat.sub_add_cancel hca
            have h1 := congrArg (fun z => (b - c) - (a - c) + z) hA.symm
            rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.sub_le_sub_right hab c),
                Nat.sub_add_cancel hcb] at h1
            exact h1
          exact Nat.add_right_cancel hAdd
        | inr hba =>
          have hSubLt : b - c < a - c := by
            have h1 : (b - c) + c < (a - c) + c := by
              rw [Nat.sub_add_cancel hcb, Nat.sub_add_cancel hca]; exact hba
            exact nat_lt_of_add_lt_add_right h1
          rw [int_subNatNat_of_lt _ _ hSubLt, int_subNatNat_of_lt _ _ hba]
          apply congrArg (fun z => Int.negSucc (z - 1))
          have hAdd : (a - c) - (b - c) + b = (a - b) + b := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt hba)]
            have hB : (b - c) + c = b := Nat.sub_add_cancel hcb
            have h1 := congrArg (fun z => (a - c) - (b - c) + z) hB.symm
            rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hSubLt),
                Nat.sub_add_cancel hca] at h1
            exact h1
          exact Nat.add_right_cancel hAdd
      | inr hbc =>
        rw [int_ofNat_sub_of_le hca, int_ofNat_sub_of_lt hbc,
            int_ofNat_sub_of_lt (Nat.lt_of_lt_of_le hbc hca),
            int_negSucc_sub_ofNat]
        apply congrArg Int.negSucc
        have hPos1 : 0 < c - b := Nat.sub_pos_of_lt hbc
        have hAdd : ((c - b - 1) + (a - c)) + 1 + b = (a - b - 1) + 1 + b := by
          rw [Nat.sub_add_cancel (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le hbc hca)),
              Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_lt_of_le hbc hca)),
              Nat.add_comm (c - b - 1) (a - c), Nat.add_assoc (a - c) (c - b - 1) 1,
              Nat.sub_add_cancel hPos1, Nat.add_assoc (a - c) (c - b) b,
              Nat.sub_add_cancel (Nat.le_of_lt hbc), Nat.sub_add_cancel hca]
        exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)
    | inr hac =>
      cases nat_le_or_gt c b with
      | inl hcb =>
        rw [int_ofNat_sub_of_lt hac, int_ofNat_sub_of_le hcb,
            int_ofNat_sub_of_le (Nat.le_trans (Nat.le_of_lt hac) hcb)]
        change Int.ofNat ((b - c) + Nat.succ (c - a - 1)) = Int.ofNat (b - a)
        apply congrArg Int.ofNat
        rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt hac)]
        have hAdd : ((b - c) + (c - a)) + a = (b - a) + a := by
          rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_of_lt hac) hcb),
              Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hac),
              Nat.sub_add_cancel hcb]
        exact Nat.add_right_cancel hAdd
      | inr hbc =>
        rw [int_ofNat_sub_of_lt hac, int_ofNat_sub_of_lt hbc,
            int_ofNat_sub_eq_subNatNat]
        change Int.subNatNat (Nat.succ (c - a - 1)) (Nat.succ (c - b - 1)) =
          Int.subNatNat b a
        rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt hac),
            nat_pred_succ_of_pos (Nat.sub_pos_of_lt hbc)]
        cases nat_le_or_gt a b with
        | inl hab =>
          have hSubLe : c - b ≤ c - a := Nat.sub_le_sub_left hab c
          rw [int_subNatNat_of_le _ _ hSubLe, int_subNatNat_of_le _ _ hab]
          apply congrArg Int.ofNat
          have hAdd : ((c - a) - (c - b)) + (c - b) + b = (b - a) + (c - b) + b := by
            rw [Nat.sub_add_cancel hSubLe, Nat.add_assoc (b - a) (c - b) b,
                Nat.sub_add_cancel (Nat.le_of_lt hbc), Nat.add_comm (c - a) b]
            have h1 : b + (c - a) = (b - a) + c := by
              have h2 := congrArg (fun z => z + a)
                (rfl : b + (c - a) = b + (c - a))
              have h3 : (b + (c - a)) + a = ((b - a) + c) + a := by
                rw [Nat.add_assoc b (c - a) a, Nat.sub_add_cancel (Nat.le_of_lt hac),
                    Nat.add_comm (b - a) c, Nat.add_assoc c (b - a) a,
                    Nat.sub_add_cancel hab, Nat.add_comm b c]
              exact Nat.add_right_cancel h3
            exact h1
          exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)
        | inr hba =>
          have hSubLt : c - a < c - b := by
            have h1 : (c - a) + a = (c - b) + b := by
              rw [Nat.sub_add_cancel (Nat.le_of_lt hac), Nat.sub_add_cancel (Nat.le_of_lt hbc)]
            cases nat_le_or_gt (c - b) (c - a) with
            | inr h => exact h
            | inl hGe =>
              have h2 : (c - b) + b < (c - a) + a :=
                Nat.lt_of_le_of_lt (Nat.add_le_add_right hGe b) (Nat.add_lt_add_left hba (c - a))
              rw [h1] at h2
              exact False.elim (Nat.lt_irrefl _ h2)
          rw [int_subNatNat_of_lt _ _ hSubLt, int_subNatNat_of_lt _ _ hba]
          apply congrArg (fun z => Int.negSucc (z - 1))
          have hAdd : ((c - b) - (c - a)) + (c - a) + a = (a - b) + (c - a) + a := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt hSubLt), Nat.add_assoc (a - b) (c - a) a,
                Nat.sub_add_cancel (Nat.le_of_lt hac), Nat.add_comm (c - b) a]
            have h3 : (a + (c - b)) + b = ((a - b) + c) + b := by
              rw [Nat.add_assoc a (c - b) b, Nat.sub_add_cancel (Nat.le_of_lt hbc),
                  Nat.add_comm (a - b) c, Nat.add_assoc c (a - b) b,
                  Nat.sub_add_cancel (Nat.le_of_lt hba), Nat.add_comm a c]
            exact Nat.add_right_cancel h3
          exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)
  change Int.NonNeg ((Int.ofNat b - Int.ofNat c) - (Int.ofNat a - Int.ofNat c)) ↔ a ≤ b
  rw [hDiff]
  exact int_ofNat_le_iff

private theorem int_sub_lt_sub_iff {a b c : Nat} :
    (Int.ofNat a - Int.ofNat c < Int.ofNat b - Int.ofNat c) ↔ a < b := by
  have hL : (Int.ofNat a - Int.ofNat c) + 1 = Int.ofNat (a + 1) - Int.ofNat c := by
    cases nat_le_or_gt c a with
    | inl hca =>
      rw [int_ofNat_sub_of_le hca,
          int_ofNat_sub_of_le (Nat.le_trans hca (Nat.le_succ a))]
      change Int.ofNat ((a - c) + 1) = Int.ofNat ((a + 1) - c)
      apply congrArg Int.ofNat
      have hAdd : ((a - c) + 1) + c = ((a + 1) - c) + c := by
        rw [Nat.sub_add_cancel (Nat.le_trans hca (Nat.le_succ a)),
            Nat.add_assoc, Nat.add_comm 1 c, ← Nat.add_assoc, Nat.sub_add_cancel hca]
      exact Nat.add_right_cancel hAdd
    | inr hac =>
      rw [int_ofNat_sub_of_lt hac]
      have hPos : 0 < c - a := Nat.sub_pos_of_lt hac
      cases hD : c - a - 1 with
      | zero =>
        have hEq1 : c - a = 1 := by
          have h1 := Nat.sub_add_cancel hPos; rw [hD, Nat.zero_add] at h1; exact h1.symm
        have hCa1 : c = a + 1 := by
          have h2 := Nat.sub_add_cancel (Nat.le_of_lt hac)
          rw [hEq1, Nat.add_comm 1 a] at h2; exact h2.symm
        rw [hCa1, int_ofNat_sub_of_le (Nat.le_refl (a + 1)), Nat.sub_self]
        rfl
      | succ k =>
        have hLt1 : a + 1 < c := by
          have h1 := Nat.sub_add_cancel hPos; rw [hD] at h1
          have h2 := Nat.sub_add_cancel (Nat.le_of_lt hac)
          rw [← h1] at h2
          rw [← h2]
          have h3 : a + 1 < k + 2 + a := by
            rw [Nat.add_comm (k + 2) a]
            exact Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.zero_lt_succ k)) a
          exact h3
        rw [int_ofNat_sub_of_lt hLt1]
        have hSubEq : c - (a + 1) - 1 = k := by
          rw [Nat.sub_succ]
          change (c - a - 1) - 1 = k
          rw [hD]; rfl
        rw [hSubEq]; rfl
  change (Int.ofNat a - Int.ofNat c) + 1 ≤ Int.ofNat b - Int.ofNat c ↔ a + 1 ≤ b
  rw [hL]
  exact int_sub_le_sub_iff

private theorem signedBias_inj {w x y : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) (hy : y < modPow2 w)
    (hEq : signedBias w x = signedBias w y) : x = y := by
  have h1 := signedBias_inv hw hx
  have h2 := signedBias_inv hw hy
  rw [hEq] at h1
  exact h1.symm.trans h2

private theorem truncateBits_bvOfInt_sub_toNat {w : IntWidth} (a b : Nat) :
    (truncateBits w (bvOfInt 128 (Int.ofNat a - Int.ofNat b))).toNat =
      wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) +
        wrapVal (bitWidthComp w) a - wrapVal (bitWidthComp w) b) := by
  have hModEq := modPow2_bitWidthComp_eq_modulus w
  have hM : 0 < modPow2 (bitWidthComp w) := modPow2_pos (bitWidthComp w)
  cases nat_le_or_gt b a with
  | inl hLe =>
    rw [int_ofNat_sub_of_le hLe, truncateBits_bvOfInt_ofNat_toNat, ← hModEq]
    dsimp only [wrapVal]
    have hModSub :
        Nat.mod (a - b) (modPow2 (bitWidthComp w)) =
          Nat.mod (modPow2 (bitWidthComp w) + Nat.mod a (modPow2 (bitWidthComp w)) -
            Nat.mod b (modPow2 (bitWidthComp w))) (modPow2 (bitWidthComp w)) := by
      let M := modPow2 (bitWidthComp w)
      have hBModLe : Nat.mod b M ≤ M + Nat.mod a M :=
        Nat.le_trans (Nat.le_of_lt (nat_mod_lt b hM)) (Nat.le_add_right M _)
      have hCancel : ∀ u v : Nat, u < M → v < M →
          Nat.mod (u + Nat.mod b M) M = Nat.mod (v + Nat.mod b M) M → u = v := by
        intro u v hu hv hE
        have hStep := congrArg (fun z => Nat.mod (z + (M - Nat.mod b M)) M) hE
        have hSimp : ∀ z : Nat, z < M →
            Nat.mod (Nat.mod (z + Nat.mod b M) M + (M - Nat.mod b M)) M = z := by
          intro z hz
          rw [mod_add_mod_left (z + Nat.mod b M) (M - Nat.mod b M) M hM,
              Nat.add_assoc z (Nat.mod b M) (M - Nat.mod b M),
              Nat.add_comm (Nat.mod b M) (M - Nat.mod b M),
              Nat.sub_add_cancel (Nat.le_of_lt (nat_mod_lt b hM)),
              nat_add_mod_self_right, nat_mod_eq_of_lt hz]
        rw [hSimp u hu, hSimp v hv] at hStep
        exact hStep
      apply hCancel _ _ (nat_mod_lt _ hM) (nat_mod_lt _ hM)
      rw [mod_add_mod_left (a - b) (Nat.mod b M) M hM,
          mod_add_mod_right (a - b) b M hM, Nat.sub_add_cancel hLe,
          mod_add_mod_left (M + Nat.mod a M - Nat.mod b M) (Nat.mod b M) M hM,
          Nat.sub_add_cancel hBModLe, nat_add_mod_self_left,
          nat_mod_eq_of_lt (nat_mod_lt a hM)]
    exact hModSub
  | inr hGt =>
    rw [int_ofNat_sub_of_lt hGt, truncateBits_bvOfInt_negSucc_toNat, ← hModEq]
    dsimp only [wrapVal]
    let M := modPow2 (bitWidthComp w)
    have hDiffPos : 0 < b - a := Nat.sub_pos_of_lt hGt
    have hSubLt : M - (Nat.mod (b - a - 1) M + 1) < M :=
      Nat.sub_lt hM (Nat.zero_lt_succ _)
    have hBModLe : Nat.mod b M ≤ M + Nat.mod a M :=
      Nat.le_trans (Nat.le_of_lt (nat_mod_lt b hM)) (Nat.le_add_right M _)
    have hCancel : ∀ u v : Nat, u < M → v < M →
        Nat.mod (u + Nat.mod b M) M = Nat.mod (v + Nat.mod b M) M → u = v := by
      intro u v hu hv hE
      have hStep := congrArg (fun z => Nat.mod (z + (M - Nat.mod b M)) M) hE
      have hSimp : ∀ z : Nat, z < M →
          Nat.mod (Nat.mod (z + Nat.mod b M) M + (M - Nat.mod b M)) M = z := by
        intro z hz
        rw [mod_add_mod_left (z + Nat.mod b M) (M - Nat.mod b M) M hM,
            Nat.add_assoc z (Nat.mod b M) (M - Nat.mod b M),
            Nat.add_comm (Nat.mod b M) (M - Nat.mod b M),
            Nat.sub_add_cancel (Nat.le_of_lt (nat_mod_lt b hM)),
            nat_add_mod_self_right, nat_mod_eq_of_lt hz]
      rw [hSimp u hu, hSimp v hv] at hStep
      exact hStep
    apply hCancel _ _ hSubLt (nat_mod_lt _ hM)
    rw [mod_add_mod_left (M + Nat.mod a M - Nat.mod b M) (Nat.mod b M) M hM,
        Nat.sub_add_cancel hBModLe, nat_add_mod_self_left,
        nat_mod_eq_of_lt (nat_mod_lt a hM)]
    have hBMod : Nat.mod b M = Nat.mod (a + (Nat.mod (b - a - 1) M + 1)) M := by
      have hBDecomp : b = a + ((b - a - 1) + 1) := by
        rw [Nat.sub_add_cancel hDiffPos, Nat.add_comm a (b - a),
            Nat.sub_add_cancel (Nat.le_of_lt hGt)]
      have hStep := congrArg (fun z => Nat.mod z M) hBDecomp
      rw [← mod_add_mod_right a ((b - a - 1) + 1) M hM,
          ← mod_add_mod_left (b - a - 1) 1 M hM,
          mod_add_mod_right a (Nat.mod (b - a - 1) M + 1) M hM] at hStep
      exact hStep
    rw [hBMod, mod_add_mod_right _ (a + (Nat.mod (b - a - 1) M + 1)) M hM,
        Nat.add_comm a (Nat.mod (b - a - 1) M + 1),
        ← Nat.add_assoc (M - (Nat.mod (b - a - 1) M + 1)) (Nat.mod (b - a - 1) M + 1) a,
        Nat.sub_add_cancel (Nat.succ_le_of_lt (nat_mod_lt _ hM)),
        nat_add_mod_self_left]

private theorem signed_in_range_no_overflow {w : IntWidth} {u : Nat}
    (hu : u < modPow2 (bitWidthComp w)) :
    let H := halfModPow2 (bitWidthComp w)
    let value : Int := Int.ofNat u - Int.ofNat H
    (decide (value < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (value ≥ HPow.hPow (2 : Int) 127)) = false ∧
    (signExtendBits w (truncateBits w (bvOfInt 128 value)) !=
      bvToInt (bvOfInt 128 value)) = false := by
  have hw := bitWidthComp_valid w
  have hModEq := modPow2_bitWidthComp_eq_modulus w
  have hHalfEq := halfModPow2_bitWidthComp_eq_half w
  have hH127 : halfModPow2 (bitWidthComp w) ≤ Nat.pow 2 127 := by
    rw [hHalfEq]; exact intWidthHalfModulus_le_pow_127 w
  have hInt127 : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := by decide
  have hNeg127 : Neg.neg (HPow.hPow (2 : Int) 127) = Int.negSucc (Nat.pow 2 127 - 1) := by
    decide
  have hPow127Pos : 0 < Nat.pow 2 127 := Nat.pow_pos (Nat.zero_lt_succ 1)
  cases nat_le_or_gt (halfModPow2 (bitWidthComp w)) u with
  | inl hGe =>
    have hSubLtH : u - halfModPow2 (bitWidthComp w) < halfModPow2 (bitWidthComp w) := by
      have h1 : (u - halfModPow2 (bitWidthComp w)) + halfModPow2 (bitWidthComp w) <
          halfModPow2 (bitWidthComp w) + halfModPow2 (bitWidthComp w) := by
        rw [Nat.sub_add_cancel hGe, ← modPow2_eq_half_add_half hw]; exact hu
      exact nat_lt_of_add_lt_add_right h1
    have hSubLt127 : u - halfModPow2 (bitWidthComp w) < Nat.pow 2 127 :=
      Nat.lt_of_lt_of_le hSubLtH hH127
    have hVal : Int.ofNat u - Int.ofNat (halfModPow2 (bitWidthComp w)) =
        Int.ofNat (u - halfModPow2 (bitWidthComp w)) := int_ofNat_sub_of_le hGe
    dsimp only
    rw [hVal]
    refine ⟨?_, ?_⟩
    · rw [hNeg127, hInt127]
      have h1 : ¬ (Int.ofNat (u - halfModPow2 (bitWidthComp w)) <
          Int.negSucc (Nat.pow 2 127 - 1)) := fun h => nomatch h
      have h2 : ¬ (Int.ofNat (u - halfModPow2 (bitWidthComp w)) ≥
          Int.ofNat (Nat.pow 2 127)) := fun h =>
        Nat.not_le_of_gt hSubLt127 (int_ofNat_le_iff.mp h)
      rw [decide_eq_false h1, decide_eq_false h2]; rfl
    · have hSubLtM : u - halfModPow2 (bitWidthComp w) < intWidthModulus w := by
        rw [← hModEq]; exact Nat.lt_trans hSubLtH (halfModPow2_lt_modPow2 hw)
      have hTruncToNat :
          (truncateBits w (bvOfInt 128 (Int.ofNat (u - halfModPow2 (bitWidthComp w))))).toNat =
            u - halfModPow2 (bitWidthComp w) := by
        rw [truncateBits_bvOfInt_ofNat_toNat, nat_mod_eq_of_lt hSubLtM]
      have hSe : signExtendBits w
          (truncateBits w (bvOfInt 128 (Int.ofNat (u - halfModPow2 (bitWidthComp w))))) =
          Int.ofNat (u - halfModPow2 (bitWidthComp w)) := by
        rw [signExtendBits_eq_of_lt_half w _ (by
          rw [hTruncToNat, nat_mod_eq_of_lt hSubLtM, ← hHalfEq]; exact hSubLtH),
            hTruncToNat, nat_mod_eq_of_lt hSubLtM]
      have hWrap : bvToInt (bvOfInt 128 (Int.ofNat (u - halfModPow2 (bitWidthComp w)))) =
          Int.ofNat (u - halfModPow2 (bitWidthComp w)) := by
        have hSubLt128 : u - halfModPow2 (bitWidthComp w) < Nat.pow 2 128 :=
          Nat.lt_trans hSubLt127 (by decide)
        unfold bvToInt
        rw [bvOfInt_ofNat_toNat, nat_mod_eq_of_lt hSubLt128]
        have h2 : 2 * (u - halfModPow2 (bitWidthComp w)) < Nat.pow 2 128 := by
          have hP : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
          rw [hP]; exact Nat.mul_lt_mul_of_pos_left hSubLt127 (Nat.zero_lt_succ 1)
        rw [ite_prop_true h2]
      rw [hSe, hWrap]
      dsimp only [bne, BEq.beq]
      rw [decide_eq_true rfl]; rfl
  | inr hLtH =>
    have hVal : Int.ofNat u - Int.ofNat (halfModPow2 (bitWidthComp w)) =
        Int.negSucc (halfModPow2 (bitWidthComp w) - u - 1) :=
      int_ofNat_sub_of_lt hLtH
    let m := halfModPow2 (bitWidthComp w) - u - 1
    have hDiffPos : 0 < halfModPow2 (bitWidthComp w) - u := Nat.sub_pos_of_lt hLtH
    have hmLtH : m < halfModPow2 (bitWidthComp w) :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hDiffPos (Nat.zero_lt_succ 0))
        (Nat.sub_le (halfModPow2 (bitWidthComp w)) u)
    have hmLt127 : m < Nat.pow 2 127 := Nat.lt_of_lt_of_le hmLtH hH127
    have hmLtM : m < intWidthModulus w := by
      rw [← hModEq]; exact Nat.lt_trans hmLtH (halfModPow2_lt_modPow2 hw)
    dsimp only
    rw [hVal]
    refine ⟨?_, ?_⟩
    · rw [hNeg127, hInt127]
      have h1 : ¬ (Int.negSucc m < Int.negSucc (Nat.pow 2 127 - 1)) := by
        intro hLt
        cases hm : m with
        | zero =>
          rw [hm] at hLt
          have hZ : Int.negSucc 0 + 1 = Int.ofNat 0 := by decide
          change Int.NonNeg (Int.negSucc (Nat.pow 2 127 - 1) - (Int.negSucc 0 + 1)) at hLt
          rw [hZ] at hLt; nomatch hLt
        | succ m' =>
          rw [hm] at hLt
          change Int.NonNeg (Int.subNatNat (Nat.succ m') (Nat.succ (Nat.pow 2 127 - 1))) at hLt
          rw [nat_pred_succ_of_pos hPow127Pos] at hLt
          rw [int_subNatNat_of_lt _ _ (by change m' + 1 < Nat.pow 2 127; rw [← hm]; exact hmLt127)] at hLt
          nomatch hLt
      have h2 : ¬ (Int.negSucc m ≥ Int.ofNat (Nat.pow 2 127)) := by
        intro hGeI
        have hSucc : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) :=
          (nat_pred_succ_of_pos hPow127Pos).symm
        rw [hSucc] at hGeI
        nomatch hGeI
      rw [decide_eq_false h1, decide_eq_false h2]; rfl
    · have hTruncToNat :
          (truncateBits w (bvOfInt 128 (Int.negSucc m))).toNat =
            intWidthModulus w - (m + 1) := by
        rw [truncateBits_bvOfInt_negSucc_toNat, nat_mod_eq_of_lt hmLtM]
      have hGeHalf : intWidthHalfModulus w ≤ intWidthModulus w - (m + 1) := by
        have hLeH : m + 1 ≤ intWidthHalfModulus w := by
          rw [← hHalfEq]; exact Nat.succ_le_of_lt hmLtH
        have h1 : intWidthHalfModulus w + (m + 1) ≤ intWidthModulus w := by
          rw [intWidthModulus_eq_half_add_half w]
          exact Nat.add_le_add_left hLeH _
        have h2 := Nat.sub_le_sub_right h1 (m + 1)
        rw [Nat.add_sub_cancel] at h2
        exact h2
      have hSubLtM : intWidthModulus w - (m + 1) < intWidthModulus w :=
        Nat.sub_lt (intWidth_modulus_pos w) (Nat.zero_lt_succ m)
      have hSe : signExtendBits w (truncateBits w (bvOfInt 128 (Int.negSucc m))) =
          Int.negSucc m := by
        rw [signExtendBits_eq_of_ge_half w _ (by
          rw [hTruncToNat, nat_mod_eq_of_lt hSubLtM]; exact hGeHalf),
            hTruncToNat, nat_mod_eq_of_lt hSubLtM]
        have hSubSelf : intWidthModulus w - (intWidthModulus w - (m + 1)) = m + 1 := by
          have hAdd := Nat.sub_add_cancel (Nat.succ_le_of_lt hmLtM)
          have hStep := congrArg (fun z => z - (intWidthModulus w - (m + 1))) hAdd.symm
          rw [Nat.add_comm (intWidthModulus w - (m + 1)) (m + 1), Nat.add_sub_cancel] at hStep
          exact hStep
        rw [hSubSelf]; rfl
      have hWrap : bvToInt (bvOfInt 128 (Int.negSucc m)) = Int.negSucc m := by
        have hmLt128 : m < Nat.pow 2 128 := Nat.lt_trans hmLt127 (by decide)
        unfold bvToInt
        rw [bvOfInt_negSucc_toNat_of_lt 128 m hmLt128]
        have hPow128 : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
        have hGe127 : Nat.pow 2 127 ≤ Nat.pow 2 128 - (m + 1) := by
          have h1 : Nat.pow 2 127 + (m + 1) ≤ Nat.pow 2 128 := by
            rw [hPow128]; exact Nat.add_le_add_left (Nat.succ_le_of_lt hmLt127) _
          have h2 := Nat.sub_le_sub_right h1 (m + 1)
          rw [Nat.add_sub_cancel] at h2; exact h2
        have hGe2 : Nat.pow 2 128 ≤ 2 * (Nat.pow 2 128 - (m + 1)) := by
          have h2 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
          rw [h2]; exact Nat.mul_le_mul_left 2 hGe127
        rw [ite_prop_false (Nat.not_lt_of_ge hGe2)]
        have hLt128 : Nat.pow 2 128 - (m + 1) < Nat.pow 2 128 :=
          Nat.sub_lt (Nat.pow_pos (Nat.zero_lt_succ 1)) (Nat.zero_lt_succ m)
        rw [int_ofNat_sub_of_lt hLt128]
        have hSubSelf : Nat.pow 2 128 - (Nat.pow 2 128 - (m + 1)) = m + 1 := by
          have hAdd := Nat.sub_add_cancel (Nat.succ_le_of_lt hmLt128)
          have hStep := congrArg (fun z => z - (Nat.pow 2 128 - (m + 1))) hAdd.symm
          rw [Nat.add_comm (Nat.pow 2 128 - (m + 1)) (m + 1), Nat.add_sub_cancel] at hStep
          exact hStep
        rw [hSubSelf]; rfl
      rw [hSe, hWrap]
      dsimp only [bne, BEq.beq]
      rw [decide_eq_true rfl]; rfl

private theorem int_sub_add_int_sub (u1 u2 H : Nat) :
    (Int.ofNat u1 - Int.ofNat H) + (Int.ofNat u2 - Int.ofNat H) =
      Int.ofNat (u1 + u2) - Int.ofNat (H + H) := by
  have hCase : ∀ x y : Nat,
      (Int.ofNat x - Int.ofNat H) + (Int.ofNat y - Int.ofNat H) =
        Int.ofNat (x + y) - Int.ofNat (H + H) := by
    intro x y
    cases nat_le_or_gt H x with
    | inl hx =>
      cases nat_le_or_gt H y with
      | inl hy =>
        rw [int_ofNat_sub_of_le hx, int_ofNat_sub_of_le hy,
            int_ofNat_sub_of_le (Nat.add_le_add hx hy)]
        change Int.ofNat ((x - H) + (y - H)) = Int.ofNat ((x + y) - (H + H))
        apply congrArg Int.ofNat
        have hAdd : ((x - H) + (y - H)) + (H + H) = ((x + y) - (H + H)) + (H + H) := by
          rw [Nat.sub_add_cancel (Nat.add_le_add hx hy)]
          have hRe : ((x - H) + (y - H)) + (H + H) = ((x - H) + H) + ((y - H) + H) := by
            rw [Nat.add_assoc (x - H) (y - H) (H + H),
                ← Nat.add_assoc (y - H) H H,
                Nat.add_comm ((y - H) + H) H,
                ← Nat.add_assoc (x - H) H ((y - H) + H)]
          rw [hRe, Nat.sub_add_cancel hx, Nat.sub_add_cancel hy]
        exact Nat.add_right_cancel hAdd
      | inr hy =>
        rw [int_ofNat_sub_of_le hx, int_ofNat_sub_of_lt hy,
            int_ofNat_sub_eq_subNatNat]
        change Int.subNatNat (x - H) (Nat.succ (H - y - 1)) = Int.subNatNat (x + y) (H + H)
        rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt hy)]
        cases nat_le_or_gt (H + H) (x + y) with
        | inl hGe =>
          have hLe : H - y ≤ x - H := by
            have h1 : (H - y) + y + H ≤ (x - H) + y + H := by
              rw [Nat.sub_add_cancel (Nat.le_of_lt hy),
                  Nat.add_assoc (x - H) y H, Nat.add_comm y H,
                  ← Nat.add_assoc (x - H) H y, Nat.sub_add_cancel hx]
              exact hGe
            exact Nat.le_of_add_le_add_right (Nat.le_of_add_le_add_right h1)
          rw [int_subNatNat_of_le _ _ hLe, int_subNatNat_of_le _ _ hGe]
          apply congrArg Int.ofNat
          have hAdd : ((x - H) - (H - y)) + (H + H) = ((x + y) - (H + H)) + (H + H) := by
            rw [Nat.sub_add_cancel hGe]
            have hStep : ((x - H) - (H - y)) + (H + H) + y = (x + y) + y := by
              have hY : (H - y) + y = H := Nat.sub_add_cancel (Nat.le_of_lt hy)
              have hRe : ((x - H) - (H - y)) + (H + H) + y =
                  (((x - H) - (H - y)) + (H - y) + H) + (y + y) := by
                have hHH : (H + H) + y = ((H - y) + H) + (y + y) := by
                  rw [Nat.add_comm (H - y) H, Nat.add_assoc H (H - y) (y + y),
                      ← Nat.add_assoc (H - y) y y, hY, Nat.add_assoc H H y]
                rw [Nat.add_assoc _ (H + H) y, hHH,
                    ← Nat.add_assoc _ ((H - y) + H) (y + y),
                    ← Nat.add_assoc _ (H - y) H]
              rw [hRe, Nat.sub_add_cancel hLe, Nat.sub_add_cancel hx, ← Nat.add_assoc]
            exact Nat.add_right_cancel hStep
          exact Nat.add_right_cancel hAdd
        | inr hLt =>
          have hSubLt : x - H < H - y := by
            have h1 : (x - H) + H + y < (H - y) + H + y := by
              rw [Nat.sub_add_cancel hx, Nat.add_assoc (H - y) H y,
                  Nat.add_comm H y, ← Nat.add_assoc (H - y) y H,
                  Nat.sub_add_cancel (Nat.le_of_lt hy)]
              exact hLt
            exact nat_lt_of_add_lt_add_right (nat_lt_of_add_lt_add_right h1)
          rw [int_subNatNat_of_lt _ _ hSubLt, int_subNatNat_of_lt _ _ hLt]
          apply congrArg (fun z => Int.negSucc (z - 1))
          have hAdd : ((H - y) - (x - H)) + (x + y) = ((H + H) - (x + y)) + (x + y) := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt hLt)]
            have hRe : ((H - y) - (x - H)) + (x + y) + H = ((H + H) + H) := by
              have hX : (x - H) + H = x := Nat.sub_add_cancel hx
              have h1 : ((H - y) - (x - H)) + (x + y) + H =
                  (((H - y) - (x - H)) + (x - H) + y) + (H + H) := by
                have hXY : (x + y) + H = ((x - H) + y) + (H + H) := by
                  have hS := congrArg (fun z => (z + y) + H) hX.symm
                  rw [Nat.add_assoc (x - H) H y, Nat.add_comm H y,
                      ← Nat.add_assoc (x - H) y H, Nat.add_assoc ((x - H) + y) H H] at hS
                  exact hS
                rw [Nat.add_assoc _ (x + y) H, hXY,
                    ← Nat.add_assoc _ ((x - H) + y) (H + H),
                    ← Nat.add_assoc _ (x - H) y]
              rw [h1, Nat.sub_add_cancel (Nat.le_of_lt hSubLt),
                  Nat.sub_add_cancel (Nat.le_of_lt hy), Nat.add_comm H (H + H)]
            exact Nat.add_right_cancel hRe
          exact Nat.add_right_cancel hAdd
    | inr hx =>
      cases nat_le_or_gt H y with
      | inl hy =>
        rw [int_ofNat_sub_of_lt hx, int_ofNat_sub_of_le hy,
            int_ofNat_sub_eq_subNatNat]
        change Int.subNatNat (y - H) (Nat.succ (H - x - 1)) = Int.subNatNat (x + y) (H + H)
        rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt hx), Nat.add_comm x y]
        cases nat_le_or_gt (H + H) (y + x) with
        | inl hGe =>
          have hLe : H - x ≤ y - H := by
            have h1 : (H - x) + x + H ≤ (y - H) + x + H := by
              rw [Nat.sub_add_cancel (Nat.le_of_lt hx),
                  Nat.add_assoc (y - H) x H, Nat.add_comm x H,
                  ← Nat.add_assoc (y - H) H x, Nat.sub_add_cancel hy]
              exact hGe
            exact Nat.le_of_add_le_add_right (Nat.le_of_add_le_add_right h1)
          rw [int_subNatNat_of_le _ _ hLe, int_subNatNat_of_le _ _ hGe]
          apply congrArg Int.ofNat
          have hAdd : ((y - H) - (H - x)) + (H + H) = ((y + x) - (H + H)) + (H + H) := by
            rw [Nat.sub_add_cancel hGe]
            have hStep : ((y - H) - (H - x)) + (H + H) + x = (y + x) + x := by
              have hX : (H - x) + x = H := Nat.sub_add_cancel (Nat.le_of_lt hx)
              have hRe : ((y - H) - (H - x)) + (H + H) + x =
                  (((y - H) - (H - x)) + (H - x) + H) + (x + x) := by
                have hHH : (H + H) + x = ((H - x) + H) + (x + x) := by
                  rw [Nat.add_comm (H - x) H, Nat.add_assoc H (H - x) (x + x),
                      ← Nat.add_assoc (H - x) x x, hX, Nat.add_assoc H H x]
                rw [Nat.add_assoc _ (H + H) x, hHH,
                    ← Nat.add_assoc _ ((H - x) + H) (x + x),
                    ← Nat.add_assoc _ (H - x) H]
              rw [hRe, Nat.sub_add_cancel hLe, Nat.sub_add_cancel hy, ← Nat.add_assoc]
            exact Nat.add_right_cancel hStep
          exact Nat.add_right_cancel hAdd
        | inr hLt =>
          have hSubLt : y - H < H - x := by
            have h1 : (y - H) + H + x < (H - x) + H + x := by
              rw [Nat.sub_add_cancel hy, Nat.add_assoc (H - x) H x,
                  Nat.add_comm H x, ← Nat.add_assoc (H - x) x H,
                  Nat.sub_add_cancel (Nat.le_of_lt hx)]
              exact hLt
            exact nat_lt_of_add_lt_add_right (nat_lt_of_add_lt_add_right h1)
          rw [int_subNatNat_of_lt _ _ hSubLt, int_subNatNat_of_lt _ _ hLt]
          apply congrArg (fun z => Int.negSucc (z - 1))
          have hAdd : ((H - x) - (y - H)) + (y + x) = ((H + H) - (y + x)) + (y + x) := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt hLt)]
            have hRe : ((H - x) - (y - H)) + (y + x) + H = ((H + H) + H) := by
              have hY : (y - H) + H = y := Nat.sub_add_cancel hy
              have h1 : ((H - x) - (y - H)) + (y + x) + H =
                  (((H - x) - (y - H)) + (y - H) + x) + (H + H) := by
                have hYX : (y + x) + H = ((y - H) + x) + (H + H) := by
                  have hS := congrArg (fun z => (z + x) + H) hY.symm
                  rw [Nat.add_assoc (y - H) H x, Nat.add_comm H x,
                      ← Nat.add_assoc (y - H) x H, Nat.add_assoc ((y - H) + x) H H] at hS
                  exact hS
                rw [Nat.add_assoc _ (y + x) H, hYX,
                    ← Nat.add_assoc _ ((y - H) + x) (H + H),
                    ← Nat.add_assoc _ (y - H) x]
              rw [h1, Nat.sub_add_cancel (Nat.le_of_lt hSubLt),
                  Nat.sub_add_cancel (Nat.le_of_lt hx), Nat.add_comm H (H + H)]
            exact Nat.add_right_cancel hRe
          exact Nat.add_right_cancel hAdd
      | inr hy =>
        rw [int_ofNat_sub_of_lt hx, int_ofNat_sub_of_lt hy,
            int_ofNat_sub_of_lt (Nat.add_lt_add hx hy)]
        change Int.negSucc (Nat.succ ((H - x - 1) + (H - y - 1))) =
          Int.negSucc ((H + H) - (x + y) - 1)
        apply congrArg Int.negSucc
        have hPosX : 0 < H - x := Nat.sub_pos_of_lt hx
        have hPosY : 0 < H - y := Nat.sub_pos_of_lt hy
        have hAdd : (Nat.succ ((H - x - 1) + (H - y - 1)) + 1) + (x + y) =
            (((H + H) - (x + y) - 1) + 1) + (x + y) := by
          rw [Nat.sub_add_cancel (Nat.sub_pos_of_lt (Nat.add_lt_add hx hy)),
              Nat.sub_add_cancel (Nat.le_of_lt (Nat.add_lt_add hx hy))]
          have hLhs : Nat.succ ((H - x - 1) + (H - y - 1)) + 1 = (H - x) + (H - y) := by
            have h1 : (H - x - 1) + 1 = H - x := Nat.sub_add_cancel hPosX
            have h2 : (H - y - 1) + 1 = H - y := Nat.sub_add_cancel hPosY
            rw [← h1, ← h2]
            change ((H - x - 1) + (H - y - 1)) + 1 + 1 =
              ((H - x - 1) + 1) + ((H - y - 1) + 1)
            rw [Nat.add_assoc (H - x - 1) (H - y - 1) 1,
                Nat.add_assoc (H - x - 1) ((H - y - 1) + 1) 1,
                Nat.add_comm ((H - y - 1) + 1) 1,
                ← Nat.add_assoc (H - x - 1) 1 ((H - y - 1) + 1)]
          rw [hLhs]
          have hRe : ((H - x) + (H - y)) + (x + y) = ((H - x) + x) + ((H - y) + y) := by
            rw [Nat.add_assoc (H - x) (H - y) (x + y),
                ← Nat.add_assoc (H - y) x y, Nat.add_comm (H - y) x,
                Nat.add_assoc x (H - y) y, ← Nat.add_assoc (H - x) x ((H - y) + y)]
          rw [hRe, Nat.sub_add_cancel (Nat.le_of_lt hx),
              Nat.sub_add_cancel (Nat.le_of_lt hy)]
        exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)
  exact hCase u1 u2

private theorem int_sub_sub_int_sub (u1 u2 H : Nat) :
    (Int.ofNat u1 - Int.ofNat H) - (Int.ofNat u2 - Int.ofNat H) =
      Int.ofNat u1 - Int.ofNat u2 := by
  -- Direct case split on `H ≤ u1`, `H ≤ u2`
  cases nat_le_or_gt H u1 with
  | inl h1 =>
    cases nat_le_or_gt H u2 with
    | inl h2 =>
      rw [int_ofNat_sub_of_le h1, int_ofNat_sub_of_le h2,
          int_ofNat_sub_eq_subNatNat, int_ofNat_sub_eq_subNatNat]
      cases nat_le_or_gt u2 u1 with
      | inl hle =>
        rw [int_subNatNat_of_le _ _ (Nat.sub_le_sub_right hle H),
            int_subNatNat_of_le _ _ hle]
        apply congrArg Int.ofNat
        have hAdd : ((u1 - H) - (u2 - H)) + u2 = (u1 - u2) + u2 := by
          rw [Nat.sub_add_cancel hle]
          have hU2 : (u2 - H) + H = u2 := Nat.sub_add_cancel h2
          have hS := congrArg (fun z => ((u1 - H) - (u2 - H)) + z) hU2.symm
          rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.sub_le_sub_right hle H),
              Nat.sub_add_cancel h1] at hS
          exact hS
        exact Nat.add_right_cancel hAdd
      | inr hgt =>
        have hSubLt : u1 - H < u2 - H := by
          have hS : (u1 - H) + H < (u2 - H) + H := by
            rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]; exact hgt
          exact nat_lt_of_add_lt_add_right hS
        rw [int_subNatNat_of_lt _ _ hSubLt, int_subNatNat_of_lt _ _ hgt]
        apply congrArg (fun z => Int.negSucc (z - 1))
        have hAdd : ((u2 - H) - (u1 - H)) + u1 = (u2 - u1) + u1 := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hgt)]
          have hU1 : (u1 - H) + H = u1 := Nat.sub_add_cancel h1
          have hS := congrArg (fun z => ((u2 - H) - (u1 - H)) + z) hU1.symm
          rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hSubLt),
              Nat.sub_add_cancel h2] at hS
          exact hS
        exact Nat.add_right_cancel hAdd
    | inr h2 =>
      rw [int_ofNat_sub_of_le h1, int_ofNat_sub_of_lt h2,
          int_ofNat_sub_of_le (Nat.le_trans (Nat.le_of_lt h2) h1)]
      change Int.ofNat ((u1 - H) + Nat.succ (H - u2 - 1)) = Int.ofNat (u1 - u2)
      apply congrArg Int.ofNat
      rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt h2)]
      have hAdd : ((u1 - H) + (H - u2)) + u2 = (u1 - u2) + u2 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_of_lt h2) h1),
            Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt h2), Nat.sub_add_cancel h1]
      exact Nat.add_right_cancel hAdd
  | inr h1 =>
    cases nat_le_or_gt H u2 with
    | inl h2 =>
      rw [int_ofNat_sub_of_lt h1, int_ofNat_sub_of_le h2,
          int_ofNat_sub_of_lt (Nat.lt_of_lt_of_le h1 h2),
          int_negSucc_sub_ofNat]
      apply congrArg Int.negSucc
      have hAdd : ((H - u1 - 1) + (u2 - H)) + 1 + u1 = (u2 - u1 - 1) + 1 + u1 := by
        rw [Nat.sub_add_cancel (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le h1 h2)),
            Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_lt_of_le h1 h2)),
            Nat.add_comm (H - u1 - 1) (u2 - H), Nat.add_assoc (u2 - H) (H - u1 - 1) 1,
            Nat.sub_add_cancel (Nat.sub_pos_of_lt h1), Nat.add_assoc (u2 - H) (H - u1) u1,
            Nat.sub_add_cancel (Nat.le_of_lt h1), Nat.sub_add_cancel h2]
      exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)
    | inr h2 =>
      rw [int_ofNat_sub_of_lt h1, int_ofNat_sub_of_lt h2, int_ofNat_sub_eq_subNatNat]
      change Int.subNatNat (Nat.succ (H - u2 - 1)) (Nat.succ (H - u1 - 1)) =
        Int.subNatNat u1 u2
      rw [nat_pred_succ_of_pos (Nat.sub_pos_of_lt h1),
          nat_pred_succ_of_pos (Nat.sub_pos_of_lt h2)]
      cases nat_le_or_gt u2 u1 with
      | inl hle =>
        have hSubLe : H - u1 ≤ H - u2 := Nat.sub_le_sub_left hle H
        rw [int_subNatNat_of_le _ _ hSubLe, int_subNatNat_of_le _ _ hle]
        apply congrArg Int.ofNat
        have hAdd : ((H - u2) - (H - u1)) + (H - u1) + u1 = (u1 - u2) + (H - u1) + u1 := by
          rw [Nat.sub_add_cancel hSubLe, Nat.add_assoc (u1 - u2) (H - u1) u1,
              Nat.sub_add_cancel (Nat.le_of_lt h1), Nat.add_comm (H - u2) u1]
          have h3 : (u1 + (H - u2)) + u2 = ((u1 - u2) + H) + u2 := by
            rw [Nat.add_assoc u1 (H - u2) u2, Nat.sub_add_cancel (Nat.le_of_lt h2),
                Nat.add_comm (u1 - u2) H, Nat.add_assoc H (u1 - u2) u2,
                Nat.sub_add_cancel hle, Nat.add_comm u1 H]
          exact Nat.add_right_cancel h3
        exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)
      | inr hgt =>
        have hSubLt : H - u2 < H - u1 := by
          have hEq : (H - u2) + u2 = (H - u1) + u1 := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt h2), Nat.sub_add_cancel (Nat.le_of_lt h1)]
          cases nat_le_or_gt (H - u1) (H - u2) with
          | inr h => exact h
          | inl hGe =>
            have h3 : (H - u1) + u1 < (H - u2) + u2 :=
              Nat.lt_of_le_of_lt (Nat.add_le_add_right hGe u1) (Nat.add_lt_add_left hgt (H - u2))
            rw [hEq] at h3; exact False.elim (Nat.lt_irrefl _ h3)
        rw [int_subNatNat_of_lt _ _ hSubLt, int_subNatNat_of_lt _ _ hgt]
        apply congrArg (fun z => Int.negSucc (z - 1))
        have hAdd : ((H - u1) - (H - u2)) + (H - u2) + u2 = (u2 - u1) + (H - u2) + u2 := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hSubLt), Nat.add_assoc (u2 - u1) (H - u2) u2,
              Nat.sub_add_cancel (Nat.le_of_lt h2), Nat.add_comm (H - u1) u2]
          have h3 : (u2 + (H - u1)) + u1 = ((u2 - u1) + H) + u1 := by
            rw [Nat.add_assoc u2 (H - u1) u1, Nat.sub_add_cancel (Nat.le_of_lt h1),
                Nat.add_comm (u2 - u1) H, Nat.add_assoc H (u2 - u1) u1,
                Nat.sub_add_cancel (Nat.le_of_lt hgt), Nat.add_comm u2 H]
          exact Nat.add_right_cancel h3
        exact Nat.add_right_cancel (Nat.add_right_cancel hAdd)

/-- Signed wrapping `.add` produces the exact same modular bit-pattern as
unsigned `.add` (`wrapVal (bitWidthComp w) (b1.toNat + b2.toNat)`). -/
theorem evalBinOp_sint_add {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .add (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true,
        BitVec.ofNat 128 (wrapVal (bitWidthComp w) (b1.toNat + b2.toNat))⟩) := by
  have hw := bitWidthComp_valid w
  have hM : 0 < modPow2 (bitWidthComp w) := modPow2_pos (bitWidthComp w)
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.add.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && _)) rfl,
      ite_bool_false (c := (true && false && _)) rfl,
      int_sub_add_int_sub, truncateScalar_signed_eq]
  dsimp only
  rw [ite_bool_false (c := (_ && BinOp.add.isUnchecked)) (Bool.and_false _),
      ite_bool_false (c := BinOp.add.isOverflowing) rfl]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, true, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBits_bvOfInt_sub_toNat]
  have hHH : halfModPow2 (bitWidthComp w) + halfModPow2 (bitWidthComp w) =
      modPow2 (bitWidthComp w) := (modPow2_eq_half_add_half hw).symm
  rw [hHH]
  dsimp only [wrapVal]
  rw [nat_mod_self, Nat.sub_zero, nat_add_mod_self_left,
      nat_mod_eq_of_lt (nat_mod_lt _ hM)]
  have hBiasSum :
      Nat.mod (signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat)
        (modPow2 (bitWidthComp w)) =
      Nat.mod (b1.toNat + b2.toNat) (modPow2 (bitWidthComp w)) := by
    dsimp only [signedBias, wrapVal]
    rw [mod_add_mod_left (b1.toNat + halfModPow2 (bitWidthComp w)) _ _ hM,
        mod_add_mod_right (b1.toNat + halfModPow2 (bitWidthComp w))
          (b2.toNat + halfModPow2 (bitWidthComp w)) _ hM]
    have hRe : (b1.toNat + halfModPow2 (bitWidthComp w)) +
        (b2.toNat + halfModPow2 (bitWidthComp w)) =
        modPow2 (bitWidthComp w) + (b1.toNat + b2.toNat) := by
      rw [← hHH, Nat.add_assoc b1.toNat (halfModPow2 (bitWidthComp w)) _,
          ← Nat.add_assoc (halfModPow2 (bitWidthComp w)) b2.toNat _,
          Nat.add_comm (halfModPow2 (bitWidthComp w)) b2.toNat,
          Nat.add_assoc b2.toNat (halfModPow2 (bitWidthComp w)) _,
          ← Nat.add_assoc b1.toNat b2.toNat _, Nat.add_comm (b1.toNat + b2.toNat) _]
    rw [hRe, nat_add_mod_self_left]
  rw [hBiasSum]
  have h128 : Nat.mod (b1.toNat + b2.toNat) (modPow2 (bitWidthComp w)) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (nat_mod_lt _ hM) (modPow2_bitWidth_le_128 w)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt h128]

/-- Signed `.addUnchecked` soundness when
`H ≤ signedBias b1 + signedBias b2 < 3 * H`. -/
theorem evalBinOp_sint_addUnchecked {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hLo : halfModPow2 (bitWidthComp w) ≤
      signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat)
    (hHi : signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat <
      3 * halfModPow2 (bitWidthComp w)) :
    evalBinOp .addUnchecked (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true,
        BitVec.ofNat 128 (wrapVal (bitWidthComp w) (b1.toNat + b2.toNat))⟩) := by
  have hw := bitWidthComp_valid w
  have hM : 0 < modPow2 (bitWidthComp w) := modPow2_pos (bitWidthComp w)
  let H := halfModPow2 (bitWidthComp w)
  let u := signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat - H
  have huLt : u < modPow2 (bitWidthComp w) := by
    have h3 : 3 * H = modPow2 (bitWidthComp w) + H := by
      have hM2 := modPow2_eq_half_add_half hw
      have h3e : 3 * H = (H + H) + H := by
        rw [Nat.succ_mul 2 H, Nat.two_mul]
      rw [h3e, ← hM2]
    have hSum : u + H < modPow2 (bitWidthComp w) + H := by
      rw [Nat.sub_add_cancel hLo, ← h3]; exact hHi
    exact nat_lt_of_add_lt_add_right hSum
  have hValEq :
      Int.ofNat (signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (H + H) =
      Int.ofNat u - Int.ofNat H := by
    have hUAdd : u + H = signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat :=
      Nat.sub_add_cancel hLo
    rw [← hUAdd]
    have hSub : Int.ofNat (u + H) - Int.ofNat (H + H) = Int.ofNat u - Int.ofNat H := by
      cases nat_le_or_gt H u with
      | inl hGe =>
        rw [int_ofNat_sub_of_le (Nat.add_le_add_right hGe H), int_ofNat_sub_of_le hGe]
        apply congrArg Int.ofNat
        have hA : (u + H) - (H + H) = u - H := by
          have h2 : (u - H) + (H + H) = u + H := by
            rw [← Nat.add_assoc, Nat.sub_add_cancel hGe]
          have h3 := congrArg (fun z => z - (H + H)) h2.symm
          rw [Nat.add_sub_cancel] at h3
          exact h3
        exact hA
      | inr hLt =>
        rw [int_ofNat_sub_of_lt (Nat.add_lt_add_right hLt H), int_ofNat_sub_of_lt hLt]
        apply congrArg (fun z => Int.negSucc (z - 1))
        have h2 : (H - u) + (u + H) = H + H := by
          rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hLt)]
        have h3 := congrArg (fun z => z - (u + H)) h2.symm
        rw [Nat.add_sub_cancel] at h3
        exact h3
    exact hSub
  have hNoOv := signed_in_range_no_overflow (w := w) huLt
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.addUnchecked.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && _)) rfl,
      ite_bool_false (c := (true && false && _)) rfl,
      int_sub_add_int_sub, hValEq, truncateScalar_signed_eq]
  dsimp only
  rw [ite_bool_true (c := true) rfl]
  have hCondF :
      (((decide (Int.ofNat u - Int.ofNat H < Neg.neg (HPow.hPow (2 : Int) 127)) ||
         decide (Int.ofNat u - Int.ofNat H ≥ HPow.hPow (2 : Int) 127)) ||
        (signExtendBits w (truncateBits w (bvOfInt 128 (Int.ofNat u - Int.ofNat H))) !=
          bvToInt (bvOfInt 128 (Int.ofNat u - Int.ofNat H)))) &&
       BinOp.addUnchecked.isUnchecked) = false := by
    rw [hNoOv.1, hNoOv.2]; rfl
  rw [ite_bool_false hCondF,
      ite_bool_false (c := BinOp.addUnchecked.isOverflowing) rfl]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, true, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [← hValEq, truncateBits_bvOfInt_sub_toNat]
  have hHH : H + H = modPow2 (bitWidthComp w) := (modPow2_eq_half_add_half hw).symm
  rw [hHH]
  dsimp only [wrapVal]
  rw [nat_mod_self, Nat.sub_zero, nat_add_mod_self_left,
      nat_mod_eq_of_lt (nat_mod_lt _ hM)]
  have hBiasSum :
      Nat.mod (signedBias (bitWidthComp w) b1.toNat + signedBias (bitWidthComp w) b2.toNat)
        (modPow2 (bitWidthComp w)) =
      Nat.mod (b1.toNat + b2.toNat) (modPow2 (bitWidthComp w)) := by
    dsimp only [signedBias, wrapVal]
    rw [mod_add_mod_left (b1.toNat + H) _ _ hM,
        mod_add_mod_right (b1.toNat + H) (b2.toNat + H) _ hM]
    have hRe : (b1.toNat + H) + (b2.toNat + H) =
        modPow2 (bitWidthComp w) + (b1.toNat + b2.toNat) := by
      rw [← hHH, Nat.add_assoc b1.toNat H _, ← Nat.add_assoc H b2.toNat H,
          Nat.add_comm H b2.toNat, Nat.add_assoc b2.toNat H H,
          ← Nat.add_assoc b1.toNat b2.toNat _, Nat.add_comm (b1.toNat + b2.toNat) _]
    rw [hRe, nat_add_mod_self_left]
  rw [hBiasSum]
  have h128 : Nat.mod (b1.toNat + b2.toNat) (modPow2 (bitWidthComp w)) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (nat_mod_lt _ hM) (modPow2_bitWidth_le_128 w)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt h128]

/-- Signed wrapping `.sub` produces the exact same modular bit-pattern as
unsigned `.sub` (`wrapVal w (modPow2 w + b1 - b2)`). -/
theorem evalBinOp_sint_sub {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .sub (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true,
        BitVec.ofNat 128
          (wrapVal (bitWidthComp w)
            (modPow2 (bitWidthComp w) + b1.toNat - b2.toNat))⟩) := by
  have hw := bitWidthComp_valid w
  have hM : 0 < modPow2 (bitWidthComp w) := modPow2_pos (bitWidthComp w)
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.sub.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && _)) rfl,
      ite_bool_false (c := (true && false && _)) rfl,
      int_sub_sub_int_sub, truncateScalar_signed_eq]
  dsimp only
  rw [ite_bool_false (c := (_ && BinOp.sub.isUnchecked)) (Bool.and_false _),
      ite_bool_false (c := BinOp.sub.isOverflowing) rfl]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, true, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBits_bvOfInt_sub_toNat]
  let M := modPow2 (bitWidthComp w)
  have hU1Mod : wrapVal (bitWidthComp w) (signedBias (bitWidthComp w) b1.toNat) =
      signedBias (bitWidthComp w) b1.toNat := nat_mod_eq_of_lt (signedBias_lt b1.toNat)
  have hU2Mod : wrapVal (bitWidthComp w) (signedBias (bitWidthComp w) b2.toNat) =
      signedBias (bitWidthComp w) b2.toNat := nat_mod_eq_of_lt (signedBias_lt b2.toNat)
  rw [hU1Mod, hU2Mod]
  have hEqMod :
      wrapVal (bitWidthComp w)
        (M + signedBias (bitWidthComp w) b1.toNat - signedBias (bitWidthComp w) b2.toNat) =
      wrapVal (bitWidthComp w) (M + b1.toNat - b2.toNat) := by
    dsimp only [wrapVal]
    have hCancel : ∀ u v : Nat, u < M → v < M →
        Nat.mod (u + b2.toNat) M = Nat.mod (v + b2.toNat) M → u = v := by
      intro u v hu hv hE
      have hStep := congrArg (fun z => Nat.mod (z + (M - b2.toNat)) M) hE
      have hSimp : ∀ z : Nat, z < M →
          Nat.mod (Nat.mod (z + b2.toNat) M + (M - b2.toNat)) M = z := by
        intro z hz
        rw [mod_add_mod_left (z + b2.toNat) (M - b2.toNat) M hM,
            Nat.add_assoc z b2.toNat (M - b2.toNat),
            Nat.add_comm b2.toNat (M - b2.toNat),
            Nat.sub_add_cancel (Nat.le_of_lt h2),
            nat_add_mod_self_right, nat_mod_eq_of_lt hz]
      rw [hSimp u hu, hSimp v hv] at hStep
      exact hStep
    apply hCancel _ _ (nat_mod_lt _ hM) (nat_mod_lt _ hM)
    have hRhs : Nat.mod (Nat.mod (M + b1.toNat - b2.toNat) M + b2.toNat) M = b1.toNat := by
      rw [mod_add_mod_left (M + b1.toNat - b2.toNat) b2.toNat M hM,
          Nat.sub_add_cancel (Nat.le_trans (Nat.le_of_lt h2) (Nat.le_add_right M b1.toNat)),
          nat_add_mod_self_left, nat_mod_eq_of_lt h1]
    rw [hRhs]
    have hLhs :
        Nat.mod (Nat.mod (M + signedBias (bitWidthComp w) b1.toNat -
          signedBias (bitWidthComp w) b2.toNat) M + b2.toNat) M = b1.toNat := by
      have hSimpH :
          Nat.mod (Nat.mod (Nat.mod (M + signedBias (bitWidthComp w) b1.toNat -
            signedBias (bitWidthComp w) b2.toNat) M + b2.toNat) M +
            halfModPow2 (bitWidthComp w)) M =
          signedBias (bitWidthComp w) b1.toNat := by
        rw [mod_add_mod_left _ (halfModPow2 (bitWidthComp w)) M hM,
            Nat.add_assoc _ b2.toNat (halfModPow2 (bitWidthComp w)),
            ← mod_add_mod_right _ (b2.toNat + halfModPow2 (bitWidthComp w)) M hM]
        change Nat.mod (Nat.mod (M + signedBias (bitWidthComp w) b1.toNat -
          signedBias (bitWidthComp w) b2.toNat) M +
          signedBias (bitWidthComp w) b2.toNat) M = _
        rw [mod_add_mod_left _ (signedBias (bitWidthComp w) b2.toNat) M hM,
            Nat.sub_add_cancel
              (Nat.le_trans (Nat.le_of_lt (signedBias_lt b2.toNat)) (Nat.le_add_right M _)),
            nat_add_mod_self_left, nat_mod_eq_of_lt (signedBias_lt b1.toNat)]
      have hBack := congrArg (fun z => Nat.mod (halfModPow2 (bitWidthComp w) + z) M) hSimpH
      rw [signedBias_inv hw h1] at hBack
      have hL2 :
          Nat.mod (halfModPow2 (bitWidthComp w) +
            Nat.mod (Nat.mod (Nat.mod (M + signedBias (bitWidthComp w) b1.toNat -
              signedBias (bitWidthComp w) b2.toNat) M + b2.toNat) M +
              halfModPow2 (bitWidthComp w)) M) M =
          Nat.mod (Nat.mod (M + signedBias (bitWidthComp w) b1.toNat -
            signedBias (bitWidthComp w) b2.toNat) M + b2.toNat) M := by
        rw [mod_add_mod_right _ _ M hM,
            Nat.add_comm (Nat.mod _ M) (halfModPow2 (bitWidthComp w)),
            ← Nat.add_assoc (halfModPow2 (bitWidthComp w)) (halfModPow2 (bitWidthComp w)) _,
            ← modPow2_eq_half_add_half hw, nat_add_mod_self_left,
            nat_mod_eq_of_lt (nat_mod_lt _ hM)]
      rw [hL2] at hBack
      exact hBack
    exact hLhs
  rw [hEqMod]
  have h128 : wrapVal (bitWidthComp w) (M + b1.toNat - b2.toNat) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (nat_mod_lt _ hM) (modPow2_bitWidth_le_128 w)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt h128]

/-- Signed `.subUnchecked` soundness when
`signedBias b2 ≤ signedBias b1 + H ∧ signedBias b1 < signedBias b2 + H`. -/
theorem evalBinOp_sint_subUnchecked {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hLo : signedBias (bitWidthComp w) b2.toNat ≤
      signedBias (bitWidthComp w) b1.toNat + halfModPow2 (bitWidthComp w))
    (hHi : signedBias (bitWidthComp w) b1.toNat <
      signedBias (bitWidthComp w) b2.toNat + halfModPow2 (bitWidthComp w)) :
    evalBinOp .subUnchecked (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true,
        BitVec.ofNat 128
          (wrapVal (bitWidthComp w)
            (modPow2 (bitWidthComp w) + b1.toNat - b2.toNat))⟩) := by
  have hw := bitWidthComp_valid w
  let H := halfModPow2 (bitWidthComp w)
  let u1 := signedBias (bitWidthComp w) b1.toNat
  let u2 := signedBias (bitWidthComp w) b2.toNat
  let u := u1 + H - u2
  have huLt : u < modPow2 (bitWidthComp w) := by
    have h1' : u + u2 < modPow2 (bitWidthComp w) + u2 := by
      rw [Nat.sub_add_cancel hLo, modPow2_eq_half_add_half hw,
          Nat.add_comm (H + H) u2, ← Nat.add_assoc u2 H H]
      exact Nat.add_lt_add_right hHi H
    exact nat_lt_of_add_lt_add_right h1'
  have hValEq : Int.ofNat u1 - Int.ofNat u2 = Int.ofNat u - Int.ofNat H := by
    have hBase := int_sub_sub_int_sub (u1 + H) (u2 + H) H
    have hEq1 : Int.ofNat (u1 + H) - Int.ofNat H = Int.ofNat u1 := by
      rw [int_ofNat_sub_of_le (Nat.le_add_left H u1), Nat.add_sub_cancel]
    have hEq2 : Int.ofNat (u2 + H) - Int.ofNat H = Int.ofNat u2 := by
      rw [int_ofNat_sub_of_le (Nat.le_add_left H u2), Nat.add_sub_cancel]
    rw [hEq1, hEq2] at hBase
    rw [hBase]
    have hUAdd : u + u2 = u1 + H := Nat.sub_add_cancel hLo
    rw [← hUAdd]
    cases nat_le_or_gt H u with
    | inl hGe =>
      have hGe2 : u2 + H ≤ u + u2 := by
        rw [Nat.add_comm u u2]; exact Nat.add_le_add_left hGe u2
      rw [int_ofNat_sub_of_le hGe2, int_ofNat_sub_of_le hGe]
      apply congrArg Int.ofNat
      have hAdd : (u + u2) - (u2 + H) + (u2 + H) = (u - H) + (u2 + H) := by
        rw [Nat.sub_add_cancel hGe2, Nat.add_comm u2 H, ← Nat.add_assoc (u - H) H u2,
            Nat.sub_add_cancel hGe]
      exact Nat.add_right_cancel hAdd
    | inr hLt =>
      have hLt2 : u + u2 < u2 + H := by
        rw [Nat.add_comm u u2]; exact Nat.add_lt_add_left hLt u2
      rw [int_ofNat_sub_of_lt hLt2, int_ofNat_sub_of_lt hLt]
      apply congrArg (fun z => Int.negSucc (z - 1))
      have hAdd : ((u2 + H) - (u + u2)) + (u + u2) = (H - u) + (u + u2) := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt hLt2), ← Nat.add_assoc (H - u) u u2,
            Nat.sub_add_cancel (Nat.le_of_lt hLt), Nat.add_comm H u2]
      exact Nat.add_right_cancel hAdd
  have hNoOv := signed_in_range_no_overflow (w := w) huLt
  have hWrap := evalBinOp_sint_sub h1 h2
  dsimp only [evalBinOp] at hWrap
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.subUnchecked.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  rw [ite_bool_false (c := BinOp.sub.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2] at hWrap
  dsimp only [evalArithOp] at hWrap
  dsimp only [evalArithOp]
  rw [ite_bool_false (c := (false && _)) rfl,
      ite_bool_false (c := (true && false && _)) rfl,
      int_sub_sub_int_sub, hValEq, truncateScalar_signed_eq] at hWrap
  rw [ite_bool_false (c := (false && _)) rfl,
      ite_bool_false (c := (true && false && _)) rfl,
      int_sub_sub_int_sub, hValEq, truncateScalar_signed_eq]
  dsimp only at hWrap
  dsimp only
  rw [ite_bool_true (c := true) rfl]
  have hCondF :
      (((decide (Int.ofNat u - Int.ofNat H < Neg.neg (HPow.hPow (2 : Int) 127)) ||
         decide (Int.ofNat u - Int.ofNat H ≥ HPow.hPow (2 : Int) 127)) ||
        (signExtendBits w (truncateBits w (bvOfInt 128 (Int.ofNat u - Int.ofNat H))) !=
          bvToInt (bvOfInt 128 (Int.ofNat u - Int.ofNat H)))) &&
       BinOp.subUnchecked.isUnchecked) = false := by
    rw [hNoOv.1, hNoOv.2]; rfl
  rw [ite_bool_false hCondF,
      ite_bool_false (c := BinOp.subUnchecked.isOverflowing) rfl]
  rw [ite_bool_false (c := (_ && BinOp.sub.isUnchecked)) (Bool.and_false _),
      ite_bool_false (c := BinOp.sub.isOverflowing) rfl] at hWrap
  exact hWrap

/-- Wrapping `.mul` soundness on `evalBinOp` for both unsigned and signed
scalars across all six `IntWidth`s. -/
theorem evalBinOp_int_mul {w : IntWidth} {s : Bool} {b1 b2 : BitVec 128} :
    ∃ res : BitVec 128,
      evalBinOp .mul (.scalar ⟨w, s, b1⟩) (.scalar ⟨w, s, b2⟩) =
        .ok (.scalar ⟨w, s, res⟩) ∧
      res.toNat < modPow2 (bitWidthComp w) := by
  have hGuard : (!(IntWidth.beq w w && (s == s))) = false := by
    rw [intWidth_beq_refl w]; cases s <;> rfl
  have hDiv2 : (s && false && (decodeScalar ⟨w, s, b1⟩ == signedMinInt w &&
      decodeScalar ⟨w, s, b2⟩ == Neg.neg 1)) = false := by
    cases s <;> rfl
  cases truncateScalar_ok w s (decodeScalar ⟨w, s, b1⟩ * decodeScalar ⟨w, s, b2⟩) with
  | intro sv hSv =>
    cases hSv with | intro lossy hTr =>
    cases sv with | mk sw ss sb =>
    have hwEq : sw = w := hTr.2.1
    have hsEq : ss = s := hTr.2.2.1
    have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
    subst sw; subst ss
    have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
    have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
      rw [← hTrEq, truncateBits_toNat]
      exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
    refine ⟨sb, ?_, hLt⟩
    dsimp only [evalBinOp]
    rw [ite_bool_false (c := BinOp.mul.isShift) rfl,
        ite_bool_false hGuard]
    dsimp only [evalArithOp]
    rw [ite_bool_false (c := (false && _)) rfl,
        ite_bool_false hDiv2, hTr.1]
    dsimp only
    rw [ite_bool_false (c := (_ && BinOp.mul.isUnchecked)) (Bool.and_false _),
        ite_bool_false (c := BinOp.mul.isOverflowing) rfl]

/-- Signed `.bitAnd` soundness on `evalBinOp`. -/
theorem evalBinOp_sint_bitAnd {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .bitAnd (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true, BitVec.ofNat 128 (Nat.land b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.land b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_land, bitAt_zero_ge_of_lt_modPow2 h1 k hk]; rfl)
  dsimp only [evalBinOp, bvAnd]
  rw [ite_bool_false (c := BinOp.bitAnd.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      truncateBits_of_lt h1, truncateBits_of_lt h2,
      truncateBits_ofNat_lt hLt]

/-- Signed `.bitOr` soundness on `evalBinOp`. -/
theorem evalBinOp_sint_bitOr {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .bitOr (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true, BitVec.ofNat 128 (Nat.lor b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.lor b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_lor, bitAt_zero_ge_of_lt_modPow2 h1 k hk,
          bitAt_zero_ge_of_lt_modPow2 h2 k hk]; rfl)
  dsimp only [evalBinOp, bvOr]
  rw [ite_bool_false (c := BinOp.bitOr.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      truncateBits_of_lt h1, truncateBits_of_lt h2,
      truncateBits_ofNat_lt hLt]

/-- Signed `.bitXor` soundness on `evalBinOp`. -/
theorem evalBinOp_sint_bitXor {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .bitXor (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.scalar ⟨w, true, BitVec.ofNat 128 (Nat.xor b1.toNat b2.toNat)⟩) := by
  have hLt : Nat.xor b1.toNat b2.toNat < modPow2 (bitWidthComp w) :=
    lt_modPow2_of_bitAt_zero (fun k hk => by
      rw [bitAt_xor, bitAt_zero_ge_of_lt_modPow2 h1 k hk,
          bitAt_zero_ge_of_lt_modPow2 h2 k hk]; rfl)
  dsimp only [evalBinOp, bvXor]
  rw [ite_bool_false (c := BinOp.bitXor.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      truncateBits_of_lt h1, truncateBits_of_lt h2,
      truncateBits_ofNat_lt hLt]

private theorem signedMinInt_eq_neg_half (w : IntWidth) :
    signedMinInt w = Int.ofNat 0 - Int.ofNat (halfModPow2 (bitWidthComp w)) := by
  have hH : HPow.hPow (2 : Int) (w.bitWidth - 1) =
      Int.ofNat (halfModPow2 (bitWidthComp w)) := by
    cases w <;> decide
  dsimp only [signedMinInt]
  rw [hH]
  have hPos : 0 < halfModPow2 (bitWidthComp w) := halfModPow2_pos _
  rw [int_ofNat_sub_of_lt hPos, Nat.sub_zero]
  cases h : halfModPow2 (bitWidthComp w) with
  | zero => rw [h] at hPos; nomatch hPos
  | succ k => rfl

/-- Signed `.div` and `.rem` soundness when `signedBias b2 ≠ H` (nonzero) and
`¬(signedBias b1 = 0 ∧ signedBias b2 = H - 1)` (not `INT_MIN / -1`). -/
theorem evalBinOp_sint_div_rem {op : BinOp} {w : IntWidth} {b1 b2 : BitVec 128}
    (hOp : op = .div ∨ op = .rem)
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (hNe0 : signedBias (bitWidthComp w) b2.toNat ≠ halfModPow2 (bitWidthComp w))
    (hNotMin : ¬ (signedBias (bitWidthComp w) b1.toNat = 0 ∧
      signedBias (bitWidthComp w) b2.toNat = halfModPow2 (bitWidthComp w) - 1)) :
    ∃ res : BitVec 128,
      evalBinOp op (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
        .ok (.scalar ⟨w, true, res⟩) ∧
      res.toNat < modPow2 (bitWidthComp w) := by
  have hZeroF : (decodeScalar ⟨w, true, b2⟩ == 0) = false := by
    rw [decodeScalar_sint_eq_bias h2]
    dsimp only [BEq.beq]
    apply decide_eq_false
    intro hEq
    have hZeroEq : (0 : Int) = Int.ofNat (halfModPow2 (bitWidthComp w)) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) := by
      rw [int_ofNat_sub_of_le (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [hZeroEq] at hEq
    exact hNe0 (int_sub_eq_sub_iff.mp hEq)
  have hOvF : (decodeScalar ⟨w, true, b1⟩ == signedMinInt w &&
      decodeScalar ⟨w, true, b2⟩ == Neg.neg 1) = false := by
    rw [decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2,
        signedMinInt_eq_neg_half w]
    have hNeg1Eq : (Neg.neg (1 : Int)) =
        Int.ofNat (halfModPow2 (bitWidthComp w) - 1) -
          Int.ofNat (halfModPow2 (bitWidthComp w)) := by
      have hPos : 0 < halfModPow2 (bitWidthComp w) := halfModPow2_pos _
      rw [int_ofNat_sub_of_lt (Nat.sub_lt hPos (Nat.zero_lt_succ 0))]
      have hSub1 : halfModPow2 (bitWidthComp w) - (halfModPow2 (bitWidthComp w) - 1) = 1 := by
        have hA := Nat.sub_add_cancel hPos
        have hS := congrArg (fun z => z - (halfModPow2 (bitWidthComp w) - 1)) hA.symm
        rw [Nat.add_comm (halfModPow2 (bitWidthComp w) - 1) 1, Nat.add_sub_cancel] at hS
        exact hS
      rw [hSub1]; rfl
    rw [hNeg1Eq]
    cases hA : (Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) ==
        Int.ofNat 0 - Int.ofNat (halfModPow2 (bitWidthComp w))) with
    | false => rfl
    | true =>
      cases hB : (Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
          Int.ofNat (halfModPow2 (bitWidthComp w)) ==
          Int.ofNat (halfModPow2 (bitWidthComp w) - 1) -
            Int.ofNat (halfModPow2 (bitWidthComp w))) with
      | false => rfl
      | true =>
        exact False.elim (hNotMin ⟨int_sub_eq_sub_iff.mp (of_decide_eq_true hA),
          int_sub_eq_sub_iff.mp (of_decide_eq_true hB)⟩)
  cases hOp with
  | inl hDiv =>
    subst hDiv
    cases truncateScalar_ok w true
        (intTdiv (decodeScalar ⟨w, true, b1⟩) (decodeScalar ⟨w, true, b2⟩)) with
    | intro sv hSv =>
      cases hSv with | intro lossy hTr =>
      cases sv with | mk sw ss sb =>
      have hwEq : sw = w := hTr.2.1
      have hsEq : ss = true := hTr.2.2.1
      have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
      subst sw; subst hsEq
      have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
      have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
        rw [← hTrEq, truncateBits_toNat]
        exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
      refine ⟨sb, ?_, hLt⟩
      dsimp only [evalBinOp]
      rw [ite_bool_false (c := BinOp.div.isShift) rfl,
          ite_bool_false (same_sint_guard_false w)]
      dsimp only [evalArithOp]
      have hZ : (true && (decodeScalar ⟨w, true, b2⟩ == 0)) = false := by
        rw [hZeroF]; rfl
      have hO : (true && true &&
          (decodeScalar ⟨w, true, b1⟩ == signedMinInt w &&
            decodeScalar ⟨w, true, b2⟩ == Neg.neg 1)) = false := by
        rw [hOvF]; rfl
      rw [ite_bool_false hZ, ite_bool_false hO, hTr.1]
      dsimp only
      rw [ite_bool_false (c := (_ && BinOp.div.isUnchecked)) (Bool.and_false _),
          ite_bool_false (c := BinOp.div.isOverflowing) rfl]
  | inr hRem =>
    subst hRem
    cases truncateScalar_ok w true
        (intTmod (decodeScalar ⟨w, true, b1⟩) (decodeScalar ⟨w, true, b2⟩)) with
    | intro sv hSv =>
      cases hSv with | intro lossy hTr =>
      cases sv with | mk sw ss sb =>
      have hwEq : sw = w := hTr.2.1
      have hsEq : ss = true := hTr.2.2.1
      have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
      subst sw; subst hsEq
      have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
      have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
        rw [← hTrEq, truncateBits_toNat]
        exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
      refine ⟨sb, ?_, hLt⟩
      dsimp only [evalBinOp]
      rw [ite_bool_false (c := BinOp.rem.isShift) rfl,
          ite_bool_false (same_sint_guard_false w)]
      dsimp only [evalArithOp]
      have hZ : (true && (decodeScalar ⟨w, true, b2⟩ == 0)) = false := by
        rw [hZeroF]; rfl
      have hO : (true && true &&
          (decodeScalar ⟨w, true, b1⟩ == signedMinInt w &&
            decodeScalar ⟨w, true, b2⟩ == Neg.neg 1)) = false := by
        rw [hOvF]; rfl
      rw [ite_bool_false hZ, ite_bool_false hO, hTr.1]
      dsimp only
      rw [ite_bool_false (c := (_ && BinOp.rem.isUnchecked)) (Bool.and_false _),
          ite_bool_false (c := BinOp.rem.isOverflowing) rfl]

/-- Signed integer `.eq` characterization on `evalBinOp`. -/
theorem evalBinOp_sint_eq {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .eq (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.bool (Nat.beq b1.toNat b2.toNat)) := by
  have hw := bitWidthComp_valid w
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.eq.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  dsimp only [BEq.beq]
  cases hB : Nat.beq b1.toNat b2.toNat with
  | true =>
    have hE := Nat.eq_of_beq_eq_true hB
    rw [decide_eq_true (by rw [hE])]
  | false =>
    have hN : Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) ≠
        Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) := by
      intro hE
      have hNat := signedBias_inj hw h1 h2 (int_sub_eq_sub_iff.mp hE)
      rw [nat_beq_of_eq hNat] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Signed integer `.ne` characterization on `evalBinOp`. -/
theorem evalBinOp_sint_ne {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .ne (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.bool (!Nat.beq b1.toNat b2.toNat)) := by
  have hw := bitWidthComp_valid w
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.ne.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  dsimp only [bne, BEq.beq]
  cases hB : Nat.beq b1.toNat b2.toNat with
  | true =>
    have hE := Nat.eq_of_beq_eq_true hB
    rw [decide_eq_true (by rw [hE])]
  | false =>
    have hN : Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) ≠
        Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) := by
      intro hE
      have hNat := signedBias_inj hw h1 h2 (int_sub_eq_sub_iff.mp hE)
      rw [nat_beq_of_eq hNat] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Signed integer `.lt` characterization via `signedBias`. -/
theorem evalBinOp_sint_lt {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .lt (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.bool (Nat.blt (signedBias (bitWidthComp w) b1.toNat)
        (signedBias (bitWidthComp w) b2.toNat))) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.lt.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  cases hB : Nat.blt (signedBias (bitWidthComp w) b1.toNat)
      (signedBias (bitWidthComp w) b2.toNat) with
  | true =>
    rw [decide_eq_true (int_sub_lt_sub_iff.mpr (lt_of_blt_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) <
        Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w))) := by
      intro hLt
      rw [blt_true_of_lt (int_sub_lt_sub_iff.mp hLt)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Signed integer `.le` characterization via `signedBias`. -/
theorem evalBinOp_sint_le {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .le (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.bool (Nat.ble (signedBias (bitWidthComp w) b1.toNat)
        (signedBias (bitWidthComp w) b2.toNat))) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.le.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  cases hB : Nat.ble (signedBias (bitWidthComp w) b1.toNat)
      (signedBias (bitWidthComp w) b2.toNat) with
  | true =>
    rw [decide_eq_true (int_sub_le_sub_iff.mpr (Nat.le_of_ble_eq_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) ≤
        Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w))) := by
      intro hLe
      rw [Nat.ble_eq_true_of_le (int_sub_le_sub_iff.mp hLe)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Signed integer `.gt` characterization via `signedBias`. -/
theorem evalBinOp_sint_gt {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .gt (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.bool (Nat.blt (signedBias (bitWidthComp w) b2.toNat)
        (signedBias (bitWidthComp w) b1.toNat))) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.gt.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  cases hB : Nat.blt (signedBias (bitWidthComp w) b2.toNat)
      (signedBias (bitWidthComp w) b1.toNat) with
  | true =>
    rw [decide_eq_true (int_sub_lt_sub_iff.mpr (lt_of_blt_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) >
        Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w))) := by
      intro hGt
      rw [blt_true_of_lt (int_sub_lt_sub_iff.mp hGt)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- Signed integer `.ge` characterization via `signedBias`. -/
theorem evalBinOp_sint_ge {w : IntWidth} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w)) :
    evalBinOp .ge (.scalar ⟨w, true, b1⟩) (.scalar ⟨w, true, b2⟩) =
      .ok (.bool (Nat.ble (signedBias (bitWidthComp w) b2.toNat)
        (signedBias (bitWidthComp w) b1.toNat))) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (c := BinOp.ge.isShift) rfl,
      ite_bool_false (same_sint_guard_false w),
      decodeScalar_sint_eq_bias h1, decodeScalar_sint_eq_bias h2]
  cases hB : Nat.ble (signedBias (bitWidthComp w) b2.toNat)
      (signedBias (bitWidthComp w) b1.toNat) with
  | true =>
    rw [decide_eq_true (int_sub_le_sub_iff.mpr (Nat.le_of_ble_eq_true hB))]
  | false =>
    have hN : ¬ (Int.ofNat (signedBias (bitWidthComp w) b1.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w)) ≥
        Int.ofNat (signedBias (bitWidthComp w) b2.toNat) -
        Int.ofNat (halfModPow2 (bitWidthComp w))) := by
      intro hGe
      rw [Nat.ble_eq_true_of_le (int_sub_le_sub_iff.mp hGe)] at hB
      nomatch hB
    rw [decide_eq_false hN]

/-- General wrapping shift (`.shl`, `.shr`) soundness across arbitrary LHS/RHS
signedness and widths. -/
theorem evalBinOp_shift_wrapping {op : BinOp} {w rw_ : IntWidth} {sL sR : Bool}
    {b1 b2 : BitVec 128}
    (hOp : op = .shl ∨ op = .shr) :
    ∃ res : BitVec 128,
      evalBinOp op (.scalar ⟨w, sL, b1⟩) (.scalar ⟨rw_, sR, b2⟩) =
        .ok (.scalar ⟨w, sL, res⟩) ∧
      res.toNat < modPow2 (bitWidthComp w) := by
  cases hOp with
  | inl hShl =>
    subst hShl
    cases truncateScalar_ok w sL
        (intShiftLeft (decodeScalar ⟨w, sL, b1⟩)
          (intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth)).toNat) with
    | intro sv hSv =>
      cases hSv with | intro lossy hTr =>
      cases sv with | mk sw ss sb =>
      have hwEq : sw = w := hTr.2.1
      have hsEq : ss = sL := hTr.2.2.1
      have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
      subst sw; subst ss
      have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
      have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
        rw [← hTrEq, truncateBits_toNat]
        exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
      refine ⟨sb, ?_, hLt⟩
      dsimp only [evalBinOp, evalShiftOp]
      rw [ite_bool_true (c := BinOp.shl.isShift) rfl, hTr.1]
      dsimp only
      rw [ite_bool_false (c := (_ && BinOp.shl.isUnchecked)) (Bool.and_false _)]
  | inr hShr =>
    subst hShr
    cases truncateScalar_ok w sL
        (intShiftRight (decodeScalar ⟨w, sL, b1⟩)
          (intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth)).toNat) with
    | intro sv hSv =>
      cases hSv with | intro lossy hTr =>
      cases sv with | mk sw ss sb =>
      have hwEq : sw = w := hTr.2.1
      have hsEq : ss = sL := hTr.2.2.1
      have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
      subst sw; subst ss
      have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
      have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
        rw [← hTrEq, truncateBits_toNat]
        exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
      refine ⟨sb, ?_, hLt⟩
      dsimp only [evalBinOp, evalShiftOp]
      rw [ite_bool_true (c := BinOp.shr.isShift) rfl, hTr.1]
      dsimp only
      rw [ite_bool_false (c := (_ && BinOp.shr.isUnchecked)) (Bool.and_false _)]

/-- General unchecked shift (`.shlUnchecked`, `.shrUnchecked`) soundness across
arbitrary LHS/RHS signedness and widths whenever `b2.toNat < bitWidthComp w`
(which automatically rules out negative signed shift amounts since
`bitWidthComp w ≤ 128 ≤ halfModPow2 (bitWidthComp rw_)`). -/
theorem evalBinOp_shift_unchecked {op : BinOp} {w rw_ : IntWidth} {sL sR : Bool}
    {b1 b2 : BitVec 128}
    (hOp : op = .shlUnchecked ∨ op = .shrUnchecked)
    (hInB : b2.toNat < bitWidthComp w) :
    ∃ res : BitVec 128,
      evalBinOp op (.scalar ⟨w, sL, b1⟩) (.scalar ⟨rw_, sR, b2⟩) =
        .ok (.scalar ⟨w, sL, res⟩) ∧
      res.toNat < modPow2 (bitWidthComp w) := by
  have hHalfR : b2.toNat < halfModPow2 (bitWidthComp rw_) :=
    Nat.lt_of_lt_of_le hInB (bitWidthComp_le_halfModPow2 w rw_)
  have hModR : b2.toNat < modPow2 (bitWidthComp rw_) :=
    Nat.lt_trans hHalfR (halfModPow2_lt_modPow2 (bitWidthComp_valid rw_))
  have hDecR : decodeScalar ⟨rw_, sR, b2⟩ = Int.ofNat b2.toNat := by
    cases sR with
    | false => exact decodeScalar_uint_of_lt hModR
    | true =>
      exact decodeScalar_signed_of_lt_half
        (by rw [← halfModPow2_bitWidthComp_eq_half rw_]; exact hHalfR)
  have hEmod : intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth) =
      Int.ofNat b2.toNat := by
    rw [hDecR, ← bitWidthComp_eq w, intEmod_ofNat, nat_mod_eq_of_lt hInB]
  have hNoOv : (intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth) !=
      decodeScalar ⟨rw_, sR, b2⟩) = false := by
    rw [hEmod, hDecR]
    dsimp only [bne, BEq.beq]
    rw [decide_eq_true rfl]; rfl
  cases hOp with
  | inl hShl =>
    subst hShl
    cases truncateScalar_ok w sL
        (intShiftLeft (decodeScalar ⟨w, sL, b1⟩)
          (intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth)).toNat) with
    | intro sv hSv =>
      cases hSv with | intro lossy hTr =>
      cases sv with | mk sw ss sb =>
      have hwEq : sw = w := hTr.2.1
      have hsEq : ss = sL := hTr.2.2.1
      have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
      subst sw; subst ss
      have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
      have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
        rw [← hTrEq, truncateBits_toNat]
        exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
      refine ⟨sb, ?_, hLt⟩
      dsimp only [evalBinOp, evalShiftOp]
      rw [ite_bool_true (c := BinOp.shlUnchecked.isShift) rfl, hTr.1]
      dsimp only
      have hF : ((intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth) !=
          decodeScalar ⟨rw_, sR, b2⟩) && BinOp.shlUnchecked.isUnchecked) = false := by
        rw [hNoOv]; rfl
      rw [ite_bool_false hF]
  | inr hShr =>
    subst hShr
    cases truncateScalar_ok w sL
        (intShiftRight (decodeScalar ⟨w, sL, b1⟩)
          (intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth)).toNat) with
    | intro sv hSv =>
      cases hSv with | intro lossy hTr =>
      cases sv with | mk sw ss sb =>
      have hwEq : sw = w := hTr.2.1
      have hsEq : ss = sL := hTr.2.2.1
      have hWf : ScalarVal.wf ⟨sw, ss, sb⟩ = true := hTr.2.2.2
      subst sw; subst ss
      have hTrEq : truncateBits w sb = sb := eq_of_beq hWf
      have hLt : sb.toNat < modPow2 (bitWidthComp w) := by
        rw [← hTrEq, truncateBits_toNat]
        exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
      refine ⟨sb, ?_, hLt⟩
      dsimp only [evalBinOp, evalShiftOp]
      rw [ite_bool_true (c := BinOp.shrUnchecked.isShift) rfl, hTr.1]
      dsimp only
      have hF : ((intEmod (decodeScalar ⟨rw_, sR, b2⟩) (Int.ofNat w.bitWidth) !=
          decodeScalar ⟨rw_, sR, b2⟩) && BinOp.shrUnchecked.isUnchecked) = false := by
        rw [hNoOv]; rfl
      rw [ite_bool_false hF]

/-- `UnOp.not` soundness on any unsigned or signed integer scalar. -/
theorem evalUnOp_int_not {w : IntWidth} {s : Bool} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    evalUnOp .not (.scalar ⟨w, s, b⟩) =
      .ok (.scalar ⟨w, s,
        BitVec.ofNat 128 (Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1))⟩) := by
  have hModEq := modPow2_bitWidthComp_eq_modulus w
  have hHalfEq := halfModPow2_bitWidthComp_eq_half w
  have hM : 0 < modPow2 (bitWidthComp w) := modPow2_pos (bitWidthComp w)
  have hXorSub : Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1) =
      (modPow2 (bitWidthComp w) - 1) - b.toNat := by
    have hAdd : Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1) + b.toNat =
        modPow2 (bitWidthComp w) - 1 := by
      -- Since every bit k < w has `bitAt (M-1) k = true`, `xor x (M-1)` and `x`
      -- are disjoint and sum to `M - 1` (by `land = 0` and `lor = M-1`).
      have hDisj : Nat.land (Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1)) b.toNat = 0 := by
        apply nat_eq_of_bitAt; intro k
        rw [bitAt_land, bitAt_xor, bitAt_modPow2_sub_one, bitAt_zero_nat]
        cases hk : Nat.blt k (bitWidthComp w) with
        | true => cases bitAt b.toNat k <;> rfl
        | false =>
          have hkGe : bitWidthComp w ≤ k := Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hk; nomatch hk)
          rw [bitAt_zero_ge_of_lt_modPow2 hLt k hkGe]; rfl
      have hOr : Nat.lor (Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1)) b.toNat =
          modPow2 (bitWidthComp w) - 1 := by
        apply nat_eq_of_bitAt; intro k
        rw [bitAt_lor, bitAt_xor, bitAt_modPow2_sub_one]
        cases hk : Nat.blt k (bitWidthComp w) with
        | true => cases bitAt b.toNat k <;> rfl
        | false =>
          have hkGe : bitWidthComp w ≤ k := Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hk; nomatch hk)
          rw [bitAt_zero_ge_of_lt_modPow2 hLt k hkGe]; rfl
      have hSum := nat_add_eq_lor_of_disjoint
        (Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1)) b.toNat hDisj
      rw [hOr] at hSum
      exact hSum
    have hStep := congrArg (fun z => z - b.toNat) hAdd
    rw [Nat.add_sub_cancel] at hStep
    exact hStep
  have hSubEq : (modPow2 (bitWidthComp w) - 1) - b.toNat =
      modPow2 (bitWidthComp w) - (b.toNat + 1) := by
    rw [Nat.sub_sub, Nat.add_comm 1 b.toNat]
  have hXorLt : Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1) <
      modPow2 (bitWidthComp w) := by
    rw [hXorSub, hSubEq]; exact Nat.sub_lt hM (Nat.zero_lt_succ _)
  have hXor128 : Nat.xor b.toNat (modPow2 (bitWidthComp w) - 1) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hXorLt (modPow2_bitWidth_le_128 w)
  dsimp only [evalUnOp]
  cases s with
  | false =>
    rw [decodeScalar_uint_of_lt hLt]
    dsimp only [intNot]
    rw [truncateScalar_unsigned_eq]
    apply congrArg Except.ok
    apply congrArg (fun bv => Val.scalar ⟨w, false, bv⟩)
    apply bitVec_eq_of_toNat_eq
    rw [truncateBits_bvOfInt_negSucc_toNat, ← hModEq, nat_mod_eq_of_lt hLt,
        ← hSubEq, ← hXorSub]
    change _ = Nat.mod _ (Nat.pow 2 128)
    rw [nat_mod_eq_of_lt hXor128]
  | true =>
    rw [truncateScalar_signed_eq]
    apply congrArg Except.ok
    apply congrArg (fun bv => Val.scalar ⟨w, true, bv⟩)
    apply bitVec_eq_of_toNat_eq
    cases Nat.lt_or_ge b.toNat (halfModPow2 (bitWidthComp w)) with
    | inl hSmall =>
      rw [decodeScalar_signed_of_lt_half (by rw [← hHalfEq]; exact hSmall)]
      dsimp only [intNot]
      rw [truncateBits_bvOfInt_negSucc_toNat, ← hModEq, nat_mod_eq_of_lt hLt,
          ← hSubEq, ← hXorSub]
      change _ = Nat.mod _ (Nat.pow 2 128)
      rw [nat_mod_eq_of_lt hXor128]
    | inr hBig =>
      rw [decodeScalar_signed_of_ge_half
            (by rw [← hHalfEq]; exact hBig)
            (by rw [← hModEq]; exact hLt)]
      dsimp only [intNot]
      rw [truncateBits_bvOfInt_ofNat_toNat, ← hModEq]
      have hDiffEq : modPow2 (bitWidthComp w) - b.toNat - 1 =
          modPow2 (bitWidthComp w) - (b.toNat + 1) := by
        rw [Nat.sub_sub]
      rw [hDiffEq, nat_mod_eq_of_lt (Nat.sub_lt hM (Nat.zero_lt_succ _)),
          ← hSubEq, ← hXorSub]
      change _ = Nat.mod _ (Nat.pow 2 128)
      rw [nat_mod_eq_of_lt hXor128]

/-- `UnOp.neg` soundness on signed integer scalars (`-INT_MIN == INT_MIN`). -/
theorem evalUnOp_sint_neg {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < modPow2 (bitWidthComp w)) :
    evalUnOp .neg (.scalar ⟨w, true, b⟩) =
      .ok (.scalar ⟨w, true,
        BitVec.ofNat 128
          (wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) - b.toNat))⟩) := by
  have hModEq := modPow2_bitWidthComp_eq_modulus w
  have hHalfEq := halfModPow2_bitWidthComp_eq_half w
  have hM : 0 < modPow2 (bitWidthComp w) := modPow2_pos (bitWidthComp w)
  dsimp only [evalUnOp]
  rw [ite_bool_true rfl, truncateScalar_signed_eq]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, true, bv⟩)
  apply bitVec_eq_of_toNat_eq
  have h128 : wrapVal (bitWidthComp w) (modPow2 (bitWidthComp w) - b.toNat) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (nat_mod_lt _ hM) (modPow2_bitWidth_le_128 w)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt h128]
  cases Nat.lt_or_ge b.toNat (halfModPow2 (bitWidthComp w)) with
  | inl hSmall =>
    rw [decodeScalar_signed_of_lt_half (by rw [← hHalfEq]; exact hSmall)]
    cases hb : b.toNat with
    | zero =>
      change (truncateBits w (bvOfInt 128 (Int.ofNat 0))).toNat = _
      rw [truncateBits_bvOfInt_ofNat_toNat, ← hModEq, Nat.sub_zero]
      dsimp only [wrapVal]
      rw [nat_mod_self, nat_mod_eq_of_lt hM]
    | succ k =>
      change (truncateBits w (bvOfInt 128 (Int.negSucc k))).toNat = _
      rw [truncateBits_bvOfInt_negSucc_toNat, ← hModEq]
      have hkLt : k < modPow2 (bitWidthComp w) := by
        rw [hb] at hLt; exact Nat.lt_of_succ_lt hLt
      rw [nat_mod_eq_of_lt hkLt]
      dsimp only [wrapVal]
      rw [nat_mod_eq_of_lt (Nat.sub_lt hM (Nat.zero_lt_succ k))]
  | inr hBig =>
    rw [decodeScalar_signed_of_ge_half
          (by rw [← hHalfEq]; exact hBig)
          (by rw [← hModEq]; exact hLt)]
    have hNeg : Neg.neg (Int.negSucc (intWidthModulus w - b.toNat - 1)) =
        Int.ofNat (modPow2 (bitWidthComp w) - b.toNat) := by
      rw [← hModEq]
      change Int.ofNat ((modPow2 (bitWidthComp w) - b.toNat - 1) + 1) = _
      rw [Nat.sub_add_cancel (Nat.sub_pos_of_lt hLt)]
    rw [hNeg, truncateBits_bvOfInt_ofNat_toNat, ← hModEq]
    rfl

/-- Unsigned-to-any `CastKind.intToInt` soundness on `evalIntToIntCast`. -/
theorem evalIntToIntCast_uint_any {wSrc wDst : IntWidth} {sDst : Bool}
    {b : BitVec 128} (hLt : b.toNat < modPow2 (bitWidthComp wSrc)) :
    evalIntToIntCast (.scalar ⟨wSrc, false, b⟩) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst,
        BitVec.ofNat 128 (wrapVal (bitWidthComp wDst) b.toNat)⟩) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  rw [ite_bool_false rfl, truncateBits_of_lt hLt]
  dsimp only
  rw [bitVec128_ofNat_toNat b, truncateBits_eq_ofNat_wrapVal wDst b]

/-- Signed-to-any-signedness narrowing/same-width `CastKind.intToInt` soundness
(`bitWidthComp wDst ≤ bitWidthComp wSrc`): keeps low `wDst` bits verbatim. -/
theorem evalIntToIntCast_sint_trunc {wSrc wDst : IntWidth} {sDst : Bool}
    {b : BitVec 128}
    (hLe : bitWidthComp wDst ≤ bitWidthComp wSrc)
    (hLt : b.toNat < modPow2 (bitWidthComp wSrc)) :
    evalIntToIntCast (.scalar ⟨wSrc, true, b⟩) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst,
        BitVec.ofNat 128 (wrapVal (bitWidthComp wDst) b.toNat)⟩) := by
  have hModSrc := modPow2_bitWidthComp_eq_modulus wSrc
  have hModDst := modPow2_bitWidthComp_eq_modulus wDst
  have hHalfSrc := halfModPow2_bitWidthComp_eq_half wSrc
  have hMDst : 0 < modPow2 (bitWidthComp wDst) := modPow2_pos (bitWidthComp wDst)
  cases Nat.lt_or_ge b.toNat (halfModPow2 (bitWidthComp wSrc)) with
  | inl hSmall =>
    rw [evalIntToIntCast_signed_of_nonneg wSrc wDst sDst
          (by rw [← hHalfSrc]; exact hSmall),
        truncateBits_eq_ofNat_wrapVal wDst b]
  | inr hBig =>
    rw [evalIntToIntCast_signed_of_neg wSrc wDst sDst
          (by rw [← hHalfSrc]; exact hBig)
          (by rw [← hModSrc]; exact hLt),
        ← hModSrc, ← hModDst]
    apply congrArg Except.ok
    apply congrArg (fun bv => Val.scalar ⟨wDst, sDst, bv⟩)
    apply congrArg (BitVec.ofNat 128)
    let Ms := modPow2 (bitWidthComp wSrc)
    let Md := modPow2 (bitWidthComp wDst)
    have hDvd : Nat.mod Ms Md = 0 := by
      have hSplit : bitWidthComp wSrc = bitWidthComp wDst + (bitWidthComp wSrc - bitWidthComp wDst) :=
        (nat_add_sub_cancel_left hLe).symm
      dsimp only [Ms, Md]
      rw [hSplit, modPow2_add]
      exact Nat.mul_mod_right _ _
    have hDiffPos : 0 < Ms - b.toNat := Nat.sub_pos_of_lt hLt
    have hSubLt : Md - (Nat.mod (Ms - b.toNat - 1) Md + 1) < Md :=
      Nat.sub_lt hMDst (Nat.zero_lt_succ _)
    have hModAdd :
        Nat.mod ((Md - (Nat.mod (Ms - b.toNat - 1) Md + 1)) +
          (Nat.mod (Ms - b.toNat - 1) Md + 1)) Md =
        Nat.mod (Nat.mod b.toNat Md + (Nat.mod (Ms - b.toNat - 1) Md + 1)) Md := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (nat_mod_lt _ hMDst)), nat_mod_self]
      rw [mod_add_mod_left b.toNat (Nat.mod (Ms - b.toNat - 1) Md + 1) Md hMDst,
          ← mod_add_mod_right b.toNat (Nat.mod (Ms - b.toNat - 1) Md + 1) Md hMDst,
          mod_add_mod_left (Ms - b.toNat - 1) 1 Md hMDst,
          mod_add_mod_right b.toNat ((Ms - b.toNat - 1) + 1) Md hMDst,
          Nat.sub_add_cancel hDiffPos, Nat.add_comm b.toNat (Ms - b.toNat),
          Nat.sub_add_cancel (Nat.le_of_lt hLt), hDvd]
    have hCancel : ∀ u v k : Nat, u < Md → v < Md →
        Nat.mod (u + k) Md = Nat.mod (v + k) Md → u = v := by
      intro u v k hu hv hE
      have hStep := congrArg (fun z => Nat.mod (z + (Md - Nat.mod k Md)) Md) hE
      have hSimp : ∀ z : Nat, z < Md →
          Nat.mod (Nat.mod (z + k) Md + (Md - Nat.mod k Md)) Md = z := by
        intro z hz
        rw [mod_add_mod_left (z + k) (Md - Nat.mod k Md) Md hMDst,
            ← mod_add_mod_left (z + k) (Md - Nat.mod k Md) Md hMDst]
        have h1 : Nat.mod (z + k) Md = Nat.mod (z + Nat.mod k Md) Md :=
          (mod_add_mod_right z k Md hMDst).symm
        rw [h1, mod_add_mod_left (z + Nat.mod k Md) (Md - Nat.mod k Md) Md hMDst,
            Nat.add_assoc z (Nat.mod k Md) (Md - Nat.mod k Md),
            Nat.add_comm (Nat.mod k Md) (Md - Nat.mod k Md),
            Nat.sub_add_cancel (Nat.le_of_lt (nat_mod_lt k hMDst)),
            nat_add_mod_self_right, nat_mod_eq_of_lt hz]
      rw [hSimp u hu, hSimp v hv] at hStep
      exact hStep
    exact hCancel _ _ _ hSubLt (nat_mod_lt _ hMDst) hModAdd

/-- General signed-to-any-signedness `CastKind.intToInt` soundness (including
sign-extending widening casts). -/
theorem evalIntToIntCast_sint_any {wSrc wDst : IntWidth} {sDst : Bool}
    {b : BitVec 128} :
    ∃ res : BitVec 128,
      evalIntToIntCast (.scalar ⟨wSrc, true, b⟩) (.int wDst sDst) =
        .ok (.scalar ⟨wDst, sDst, res⟩) ∧
      res.toNat < modPow2 (bitWidthComp wDst) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  rw [ite_bool_true rfl]
  refine ⟨truncateBits wDst (BitVec.ofNat 128 (bvOfInt 128 (decodeScalar ⟨wSrc, true, b⟩)).toNat),
    rfl, ?_⟩
  rw [truncateBits_toNat]
  exact nat_mod_lt _ (modPow2_pos (bitWidthComp wDst))

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
  | sleConst (reg : LocalId) (w : IntWidth) (boundBits : Nat)
  | sgtConst (reg : LocalId) (w : IntWidth) (boundBits : Nat)
  | seqConst (reg : LocalId) (w : IntWidth) (val : Nat)
  | sneConst (reg : LocalId) (w : IntWidth) (val : Nat)

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
  | .sleConst r1 w1 b1, .sleConst r2 w2 b2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq b1 b2
  | .sgtConst r1 w1 b1, .sgtConst r2 w2 b2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq b1 b2
  | .seqConst r1 w1 v1, .seqConst r2 w2 v2 =>
    Nat.beq r1 r2 && intWidthBeqComp w1 w2 && Nat.beq v1 v2
  | .sneConst r1 w1 v1, .sneConst r2 w2 v2 =>
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
  | sleConst _ _ _ =>
    cases g2 with
    | sleConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h
  | sgtConst _ _ _ =>
    cases g2 with
    | sgtConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h
  | seqConst _ _ _ =>
    cases g2 with
    | seqConst _ _ _ =>
      dsimp only [RelGuard.beq] at h
      have h12 := bool_and_true_left h
      rw [Nat.eq_of_beq_eq_true (bool_and_true_left h12),
          intWidth_eq_of_beqComp (bool_and_true_right h12),
          Nat.eq_of_beq_eq_true (bool_and_true_right h)]
    | _ => nomatch h
  | sneConst _ _ _ =>
    cases g2 with
    | sneConst _ _ _ =>
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
  | .sleConst r w b => .sgtConst r w b
  | .sgtConst r w b => .sleConst r w b
  | .seqConst r w v => .sneConst r w v
  | .sneConst r w v => .seqConst r w v

/-- True iff `g` references local `id`. -/
@[expose] def RelGuard.mentions (id : LocalId) : RelGuard → Bool
  | .none => false
  | .uleConst r _ _ => Nat.beq r id
  | .ugtConst r _ _ => Nat.beq r id
  | .ultReg l r _ => Nat.beq l id || Nat.beq r id
  | .ugeReg l r _ => Nat.beq l id || Nat.beq r id
  | .ueqConst r _ _ => Nat.beq r id
  | .uneConst r _ _ => Nat.beq r id
  | .sleConst r _ _ => Nat.beq r id
  | .sgtConst r _ _ => Nat.beq r id
  | .seqConst r _ _ => Nat.beq r id
  | .sneConst r _ _ => Nat.beq r id

/-- Concrete extraction of an initialized unsigned scalar at local `r`. -/
@[expose] def localUintNat? (locals : List LocalSlot) (r : LocalId) (w :
    IntWidth) :
    Option Nat :=
  match compGetElem? locals r with
  | some (.immediate (some (.scalar sv))) =>
    if intWidthBeqComp sv.width w && !sv.signed then some sv.bits.toNat else none
  | _ => none

/-- Concrete extraction of an initialized signed scalar's raw bit-pattern at
local `r`. -/
@[expose] def localSintNat? (locals : List LocalSlot) (r : LocalId) (w :
    IntWidth) :
    Option Nat :=
  match compGetElem? locals r with
  | some (.immediate (some (.scalar sv))) =>
    if intWidthBeqComp sv.width w && sv.signed then some sv.bits.toNat else none
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
  | .sleConst r w boundBits =>
    ∀ x, localSintNat? locals r w = some x →
      (b = true ↔ signedBias (bitWidthComp w) x ≤ signedBias (bitWidthComp w) boundBits)
  | .sgtConst r w boundBits =>
    ∀ x, localSintNat? locals r w = some x →
      (b = true ↔ signedBias (bitWidthComp w) boundBits < signedBias (bitWidthComp w) x)
  | .seqConst r w val =>
    ∀ x, localSintNat? locals r w = some x → (b = true ↔ x = val)
  | .sneConst r w val =>
    ∀ x, localSintNat? locals r w = some x → (b = true ↔ x ≠ val)

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
  | sleConst r w boundBits =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hLe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hGt => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      have hNotLe : ¬ (signedBias (bitWidthComp w) x ≤ signedBias (bitWidthComp w) boundBits) :=
        fun hLe => nomatch (hIff.mpr hLe)
      exact ⟨(fun _ => Nat.lt_of_not_le hNotLe), (fun _ => rfl)⟩
  | sgtConst r w boundBits =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hGt := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hLe => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      have hNotGt : ¬ (signedBias (bitWidthComp w) boundBits < signedBias (bitWidthComp w) x) :=
        fun hGt => nomatch (hIff.mpr hGt)
      exact ⟨(fun _ => Nat.le_of_not_lt hNotGt), (fun _ => rfl)⟩
  | seqConst r w val =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hEq := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hNe => False.elim (hNe hEq))⟩
    | false =>
      have hNe : x ≠ val := fun hEq => nomatch (hIff.mpr hEq)
      exact ⟨(fun _ => hNe), (fun _ => rfl)⟩
  | sneConst r w val =>
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
          | ugeReg _ _ _ | ueqConst _ _ _ | uneConst _ _ _
          | sleConst _ _ _ | sgtConst _ _ _ | seqConst _ _ _ | sneConst _ _ _ =>
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
          | ugeReg _ _ _ | ueqConst _ _ _ | uneConst _ _ _
          | sleConst _ _ _ | sgtConst _ _ _ | seqConst _ _ _ | sneConst _ _ _ =>
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
          | ugeReg _ _ _ | ueqConst _ _ _ | uneConst _ _ _
          | sleConst _ _ _ | sgtConst _ _ _ | seqConst _ _ _ | sneConst _ _ _ =>
            rw [← relGuard_eq_of_beq hg]; exact ha.2
    | scalar _ | ptr _ | char _ | ordering _ | unit
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
    | vec _ _ _ | boxPtr _ _
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
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
    | vec _ _ _ | boxPtr _ _
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
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
    | vec _ _ _ | boxPtr _ _
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
  | sint (w : IntWidth) (a : AbsVal)
  | bool (b : BoolAbs)
  | unit

/-- Abstract MIR local frame (`MirAbsEnv`). -/
abbrev MirAbsEnv := List MirAbsSlot

/-- Initial uninitialized live abstract slot for a supported MIR local type. -/
@[expose] def liveUninitAbsSlot? : MirTy → Option MirAbsSlot
  | .int w false => some (.uint w (AbsVal.uninit (bitWidthComp w)))
  | .int w true => some (.sint w (AbsVal.uninit (bitWidthComp w)))
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
  | .sint w a =>
    ty = .int w true ∧
    match cslot with
    | .immediate none => a.denote (bitWidthComp w) none
    | .immediate (some (.scalar sv)) =>
      sv.width = w ∧ sv.signed = true ∧
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
  | sint _ _ => exact hDen
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
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
    | vec _ _ _ | boxPtr _ _
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
  | .sint w1 a1, .sint w2 a2 =>
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
      | dead | indirect _ | partialTuple _ => exact False.elim ha.2
      | immediate opt => exact boolAbs_le_sound hLe ha.2
    | dead | uint _ _ | sint _ _ | unit => nomatch hLe
  | uint w1 a1 =>
    cases b with
    | uint w2 a2 =>
      dsimp only [MirAbsSlot.le] at hLe
      have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hLe)
      have hAle := bool_and_true_right hLe
      subst hwEq
      refine ⟨ha.1, ?_⟩
      cases cs with
      | dead | indirect _ | partialTuple _ => exact False.elim ha.2
      | immediate opt =>
        cases opt with
        | none => exact absVal_le_sound hAle ha.2
        | some v =>
          cases v with
          | scalar sv =>
            exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.1,
              absVal_le_sound hAle ha.2.2.2.2⟩
          | ptr _ | bool _ | char _ | ordering _ | unit
          | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
          | vec _ _ _ | boxPtr _ _
          | enumVal _ _ | tuple _ | bytes _ => exact False.elim ha.2
    | dead | sint _ _ | bool _ | unit => nomatch hLe
  | sint w1 a1 =>
    cases b with
    | sint w2 a2 =>
      dsimp only [MirAbsSlot.le] at hLe
      have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hLe)
      have hAle := bool_and_true_right hLe
      subst hwEq
      refine ⟨ha.1, ?_⟩
      cases cs with
      | dead | indirect _ | partialTuple _ => exact False.elim ha.2
      | immediate opt =>
        cases opt with
        | none => exact absVal_le_sound hAle ha.2
        | some v =>
          cases v with
          | scalar sv =>
            exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.1,
              absVal_le_sound hAle ha.2.2.2.2⟩
          | ptr _ | bool _ | char _ | ordering _ | unit
          | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
          | enumVal _ _ | tuple _ | bytes _ | range _ _ | boxPtr _ _
          | vec _ _ _ => exact False.elim ha.2
          | optionVal optV => cases optV <;> (exact False.elim ha.2)
    | dead | uint _ _ | bool _ | unit => nomatch hLe

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
  | .sint w1 a1, .sint w2 a2 =>
    if intWidthBeqComp w1 w2 then
      some (.sint w1 (AbsVal.join (bitWidthComp w1) a1 a2))
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
    | uint _ _ | sint _ _ | bool _ | unit => nomatch hJ
  | unit =>
    cases b with
    | unit => injection hJ with hc; subst hc; exact ha
    | dead | uint _ _ | sint _ _ | bool _ => nomatch hJ
  | bool b1 =>
    cases b with
    | bool b2 =>
      injection hJ with hc; subst hc
      refine ⟨ha.1, ?_⟩
      cases cs with
      | dead | indirect _ | partialTuple _ => exact False.elim ha.2
      | immediate opt => exact boolAbs_join_sound_left ha.2
    | dead | uint _ _ | sint _ _ | unit => nomatch hJ
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
        | dead | indirect _ | partialTuple _ => exact False.elim ha.2
        | immediate opt =>
          cases opt with
          | none => exact absVal_join_sound_left (bitWidthComp_valid w1) a1 a2 ha.2
          | some v =>
            cases v with
            | scalar sv =>
              exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.1,
                absVal_join_sound_left (bitWidthComp_valid w1) a1 a2 ha.2.2.2.2⟩
            | ptr _ | bool _ | char _ | ordering _ | unit
            | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
            | vec _ _ _ | boxPtr _ _
            | enumVal _ _ | tuple _ | bytes _ => exact False.elim ha.2
    | dead | sint _ _ | bool _ | unit => nomatch hJ
  | sint w1 a1 =>
    cases b with
    | sint w2 a2 =>
      dsimp only [MirAbsSlot.join] at hJ
      cases hw : intWidthBeqComp w1 w2 with
      | false => rw [hw] at hJ; nomatch hJ
      | true =>
        rw [hw] at hJ
        injection hJ with hc; subst hc
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead | indirect _ | partialTuple _ => exact False.elim ha.2
        | immediate opt =>
          cases opt with
          | none => exact absVal_join_sound_left (bitWidthComp_valid w1) a1 a2 ha.2
          | some v =>
            cases v with
            | scalar sv =>
              exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.1,
                absVal_join_sound_left (bitWidthComp_valid w1) a1 a2 ha.2.2.2.2⟩
            | ptr _ | bool _ | char _ | ordering _ | unit
            | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
            | enumVal _ _ | tuple _ | bytes _ | range _ _ | boxPtr _ _
            | vec _ _ _ =>
              exact False.elim ha.2
            | optionVal optV => cases optV <;> (exact False.elim ha.2)
    | dead | uint _ _ | bool _ | unit => nomatch hJ

/-- Right join soundness on `MirAbsSlot`. -/
theorem mirAbsSlot_join_sound_right {ty : MirTy} {locals : List LocalSlot}
    {a b c : MirAbsSlot} {cs : LocalSlot}
    (hJ : MirAbsSlot.join a b = some c) (hb : b.denote ty locals cs) :
    c.denote ty locals cs := by
  cases a with
  | dead =>
    cases b with
    | dead => injection hJ with hc; subst hc; exact hb
    | uint _ _ | sint _ _ | bool _ | unit => nomatch hJ
  | unit =>
    cases b with
    | unit => injection hJ with hc; subst hc; exact hb
    | dead | uint _ _ | sint _ _ | bool _ => nomatch hJ
  | bool b1 =>
    cases b with
    | bool b2 =>
      injection hJ with hc; subst hc
      refine ⟨hb.1, ?_⟩
      cases cs with
      | dead | indirect _ | partialTuple _ => exact False.elim hb.2
      | immediate opt => exact boolAbs_join_sound_right hb.2
    | dead | uint _ _ | sint _ _ | unit => nomatch hJ
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
        | dead | indirect _ | partialTuple _ => exact False.elim hb.2
        | immediate opt =>
          cases opt with
          | none => exact absVal_join_sound_right (bitWidthComp_valid w1) a1 a2 hb.2
          | some v =>
            cases v with
            | scalar sv =>
              exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2.1,
                absVal_join_sound_right (bitWidthComp_valid w1) a1 a2 hb.2.2.2.2⟩
            | ptr _ | bool _ | char _ | ordering _ | unit
            | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
            | vec _ _ _ | boxPtr _ _
            | enumVal _ _ | tuple _ | bytes _ => exact False.elim hb.2
    | dead | sint _ _ | bool _ | unit => nomatch hJ
  | sint w1 a1 =>
    cases b with
    | sint w2 a2 =>
      dsimp only [MirAbsSlot.join] at hJ
      cases hw : intWidthBeqComp w1 w2 with
      | false => rw [hw] at hJ; nomatch hJ
      | true =>
        have hwEq := intWidth_eq_of_beqComp hw
        rw [hw] at hJ
        injection hJ with hc; subst hc; subst hwEq
        refine ⟨hb.1, ?_⟩
        cases cs with
        | dead | indirect _ | partialTuple _ => exact False.elim hb.2
        | immediate opt =>
          cases opt with
          | none => exact absVal_join_sound_right (bitWidthComp_valid w1) a1 a2 hb.2
          | some v =>
            cases v with
            | scalar sv =>
              exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2.1,
                absVal_join_sound_right (bitWidthComp_valid w1) a1 a2 hb.2.2.2.2⟩
            | ptr _ | bool _ | char _ | ordering _ | unit
            | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
            | enumVal _ _ | tuple _ | bytes _ | range _ _ | boxPtr _ _
            | vec _ _ _ =>
              exact False.elim hb.2
            | optionVal optV => cases optV <;> (exact False.elim hb.2)
    | dead | uint _ _ | bool _ | unit => nomatch hJ

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
  have hLocSintEq : ∀ r w, Nat.beq r id = false →
      localSintNat? locals' r w = localSintNat? locals r w := by
    intro r w hNeB
    have hNe : id ≠ r := fun hE => by
      rw [← hE, nat_beq_refl id] at hNeB; nomatch hNeB
    dsimp only [localSintNat?]
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
  | sleConst r w boundBits =>
    intro x hx
    rw [hLocSintEq r w hNoMent] at hx
    exact hDen x hx
  | sgtConst r w boundBits =>
    intro x hx
    rw [hLocSintEq r w hNoMent] at hx
    exact hDen x hx
  | seqConst r w val =>
    intro x hx
    rw [hLocSintEq r w hNoMent] at hx
    exact hDen x hx
  | sneConst r w val =>
    intro x hx
    rw [hLocSintEq r w hNoMent] at hx
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
        | sint w a => exact hOldDen
        | bool ba =>
          refine ⟨hOldDen.1, ?_⟩
          cases cs with
          | dead | indirect _ | partialTuple _ => exact False.elim hOldDen.2
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
              | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
              | vec _ _ _ | boxPtr _ _
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
  | .sleConst r w boundBits =>
    match compGetElem? env r with
    | some (.sint w' a) =>
      if intWidthBeqComp w w' && a.isInit &&
         Nat.blt boundBits (modPow2 (bitWidthComp w)) then
        let a' := AbsVal.refineSleConst (bitWidthComp w) a boundBits
        match compSetElem? env r (.sint w a') with
        | some env' => env'
        | none => env
      else env
    | _ => env
  | .sgtConst r w boundBits =>
    match compGetElem? env r with
    | some (.sint w' a) =>
      if intWidthBeqComp w w' && a.isInit &&
         Nat.blt boundBits (modPow2 (bitWidthComp w)) then
        let a' := AbsVal.refineSgtConst (bitWidthComp w) a boundBits
        match compSetElem? env r (.sint w a') with
        | some env' => env'
        | none => env
      else env
    | _ => env
  | .seqConst r w val =>
    match compGetElem? env r with
    | some (.sint w' a) =>
      if intWidthBeqComp w w' && a.isInit then
        let a' := AbsVal.refineEqConst (bitWidthComp w) a val
        match compSetElem? env r (.sint w a') with
        | some env' => env'
        | none => env
      else env
    | _ => env
  | .sneConst _ _ _ => env

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
  | none | uneConst _ _ _ | sneConst _ _ _ => exact hEnv
  | uleConst r w bound =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | sint _ _ | bool _ | unit => exact hEnv
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
            | dead | indirect _ | partialTuple _ => exact False.elim hDen.2
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
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                | vec _ _ _ | boxPtr _ _
                | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2
  | ugtConst r w bound =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | sint _ _ | bool _ | unit => exact hEnv
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
            | dead | indirect _ | partialTuple _ => exact False.elim hDen.2
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
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                | vec _ _ _ | boxPtr _ _
                | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2
  | ultReg l r w =>
    rw [hG] at hEff
    dsimp only
    cases hGetL : compGetElem? env l with
    | none => exact hEnv
    | some sl =>
      cases sl with
      | dead | sint _ _ | bool _ | unit => exact hEnv
      | uint wl al =>
        cases hGetR : compGetElem? env r with
        | none => exact hEnv
        | some sr =>
          cases sr with
          | dead | sint _ _ | bool _ | unit => exact hEnv
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
                | dead | indirect _ | partialTuple _ => exact False.elim hDenL.2
                | immediate optL =>
                  cases optL with
                  | none =>
                    cases absVal_init_of_isInit hInitL hDenL.2 with
                    | intro _ hx => nomatch hx.1
                  | some vL =>
                    cases vL with
                    | scalar svL =>
                      cases csR with
                      | dead | indirect _ | partialTuple _ => exact False.elim hDenR.2
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
                          | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                          | vec _ _ _ | boxPtr _ _
                          | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenR.2
                    | ptr _ | bool _ | char _ | ordering _ | unit
                    | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                    | vec _ _ _ | boxPtr _ _
                    | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenL.2
  | ugeReg l r w =>
    rw [hG] at hEff
    dsimp only
    cases hGetL : compGetElem? env l with
    | none => exact hEnv
    | some sl =>
      cases sl with
      | dead | sint _ _ | bool _ | unit => exact hEnv
      | uint wl al =>
        cases hGetR : compGetElem? env r with
        | none => exact hEnv
        | some sr =>
          cases sr with
          | dead | sint _ _ | bool _ | unit => exact hEnv
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
                | dead | indirect _ | partialTuple _ => exact False.elim hDenL.2
                | immediate optL =>
                  cases optL with
                  | none =>
                    cases absVal_init_of_isInit hInitL hDenL.2 with
                    | intro _ hx => nomatch hx.1
                  | some vL =>
                    cases vL with
                    | scalar svL =>
                      cases csR with
                      | dead | indirect _ | partialTuple _ => exact False.elim hDenR.2
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
                          | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                          | vec _ _ _ | boxPtr _ _
                          | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenR.2
                    | ptr _ | bool _ | char _ | ordering _ | unit
                    | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                    | vec _ _ _ | boxPtr _ _
                    | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDenL.2
  | ueqConst r w val =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | sint _ _ | bool _ | unit => exact hEnv
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
            | dead | indirect _ | partialTuple _ => exact False.elim hDen.2
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
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | range _ _ | optionVal _
                | vec _ _ _ | boxPtr _ _
                | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2
  | sleConst r w boundBits =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | uint _ _ | bool _ | unit => exact hEnv
      | sint w' a =>
        dsimp only
        cases hC : intWidthBeqComp w w' && a.isInit &&
            Nat.blt boundBits (modPow2 (bitWidthComp w)) with
        | false => exact hEnv
        | true =>
          have h12 := bool_and_true_left hC
          have hwEq := intWidth_eq_of_beqComp (bool_and_true_left h12)
          have hInit := bool_and_true_right h12
          have hBLt := lt_of_blt_true (bool_and_true_right hC)
          subst hwEq
          rw [ite_bool_true rfl]
          cases hSet : compSetElem? env r
              (.sint w (AbsVal.refineSleConst (bitWidthComp w) a boundBits)) with
          | none => exact hEnv
          | some env' =>
            apply refineSingleSlot_sound hEnv hSet
            intro ty cs hTy hCs
            have hDen := hEnv.2.2 r ty (.sint w a) cs hTy hGet hCs
            refine ⟨hDen.1, ?_⟩
            cases cs with
            | dead | indirect _ | partialTuple _ => exact False.elim hDen.2
            | immediate opt =>
              cases opt with
              | none =>
                cases absVal_init_of_isInit hInit hDen.2 with
                | intro _ hx => nomatch hx.1
              | some v =>
                cases v with
                | scalar sv =>
                  have hLoc : localSintNat? locals r w = some sv.bits.toNat := by
                    dsimp only [localSintNat?]
                    rw [hCs]; dsimp only
                    rw [hDen.2.1, hDen.2.2.1, intWidthBeqComp_refl w]; rfl
                  have hSle := (hEff sv.bits.toNat hLoc).mp rfl
                  exact ⟨hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                    absVal_refineSleConst_sound (bitWidthComp_valid w)
                      hDen.2.2.2.2 hInit hBLt hSle⟩
                | ptr _ | bool _ | char _ | ordering _ | unit
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
                | enumVal _ _ | tuple _ | bytes _ | range _ _ | boxPtr _ _
                | vec _ _ _ =>
                  exact False.elim hDen.2
                | optionVal optV => cases optV <;> (exact False.elim hDen.2)
  | sgtConst r w boundBits =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | uint _ _ | bool _ | unit => exact hEnv
      | sint w' a =>
        dsimp only
        cases hC : intWidthBeqComp w w' && a.isInit &&
            Nat.blt boundBits (modPow2 (bitWidthComp w)) with
        | false => exact hEnv
        | true =>
          have h12 := bool_and_true_left hC
          have hwEq := intWidth_eq_of_beqComp (bool_and_true_left h12)
          have hInit := bool_and_true_right h12
          have hBLt := lt_of_blt_true (bool_and_true_right hC)
          subst hwEq
          rw [ite_bool_true rfl]
          cases hSet : compSetElem? env r
              (.sint w (AbsVal.refineSgtConst (bitWidthComp w) a boundBits)) with
          | none => exact hEnv
          | some env' =>
            apply refineSingleSlot_sound hEnv hSet
            intro ty cs hTy hCs
            have hDen := hEnv.2.2 r ty (.sint w a) cs hTy hGet hCs
            refine ⟨hDen.1, ?_⟩
            cases cs with
            | dead | indirect _ | partialTuple _ => exact False.elim hDen.2
            | immediate opt =>
              cases opt with
              | none =>
                cases absVal_init_of_isInit hInit hDen.2 with
                | intro _ hx => nomatch hx.1
              | some v =>
                cases v with
                | scalar sv =>
                  have hLoc : localSintNat? locals r w = some sv.bits.toNat := by
                    dsimp only [localSintNat?]
                    rw [hCs]; dsimp only
                    rw [hDen.2.1, hDen.2.2.1, intWidthBeqComp_refl w]; rfl
                  have hSgt := (hEff sv.bits.toNat hLoc).mp rfl
                  exact ⟨hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                    absVal_refineSgtConst_sound (bitWidthComp_valid w)
                      hDen.2.2.2.2 hInit hBLt hSgt⟩
                | ptr _ | bool _ | char _ | ordering _ | unit
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
                | enumVal _ _ | tuple _ | bytes _ | range _ _ | boxPtr _ _
                | vec _ _ _ =>
                  exact False.elim hDen.2
                | optionVal optV => cases optV <;> (exact False.elim hDen.2)
  | seqConst r w val =>
    rw [hG] at hEff
    dsimp only
    cases hGet : compGetElem? env r with
    | none => exact hEnv
    | some s =>
      cases s with
      | dead | uint _ _ | bool _ | unit => exact hEnv
      | sint w' a =>
        dsimp only
        cases hC : intWidthBeqComp w w' && a.isInit with
        | false => exact hEnv
        | true =>
          have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
          have hInit := bool_and_true_right hC
          subst hwEq
          rw [ite_bool_true rfl]
          cases hSet : compSetElem? env r
              (.sint w (AbsVal.refineEqConst (bitWidthComp w) a val)) with
          | none => exact hEnv
          | some env' =>
            apply refineSingleSlot_sound hEnv hSet
            intro ty cs hTy hCs
            have hDen := hEnv.2.2 r ty (.sint w a) cs hTy hGet hCs
            refine ⟨hDen.1, ?_⟩
            cases cs with
            | dead | indirect _ | partialTuple _ => exact False.elim hDen.2
            | immediate opt =>
              cases opt with
              | none =>
                cases absVal_init_of_isInit hInit hDen.2 with
                | intro _ hx => nomatch hx.1
              | some v =>
                cases v with
                | scalar sv =>
                  have hLoc : localSintNat? locals r w = some sv.bits.toNat := by
                    dsimp only [localSintNat?]
                    rw [hCs]; dsimp only
                    rw [hDen.2.1, hDen.2.2.1, intWidthBeqComp_refl w]; rfl
                  have hEq := (hEff sv.bits.toNat hLoc).mp rfl
                  exact ⟨hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                    absVal_refineEqConst_sound (bitWidthComp_valid w)
                      hDen.2.2.2.2 hInit hEq⟩
                | ptr _ | bool _ | char _ | ordering _ | unit
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
                | enumVal _ _ | tuple _ | bytes _ | optionVal _ | range _ _
                | boxPtr _ _ | vec _ _ _ =>
                  exact False.elim hDen.2

end Anneal.AiPcc

end
