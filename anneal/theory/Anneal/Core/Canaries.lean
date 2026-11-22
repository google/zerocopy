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
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Trusted
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.MirTotal.Ops
import Anneal.MirTotal.StepCore
import Anneal.Core.BlockTree
import Anneal.Core.SepPCM
import Anneal.Core.StageCut

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.MirTotal

/-!
# Positive and Negative End-to-End Canaries (`Core.Canaries`)

Exercises `Core.BlockTree`, `Core.SepPCM`, and `Core.StageCut` (`0`
`noncomputable`, `0` `._unsafe_rec`) on concrete `Trusted.MirAst.Body` programs:

1. **8-Stage (`256`-Path, `26`-Block) Overflowing/Unchecked/Cast Diamond
   (`bodyOverflowCastJoin8`):** Verifies `SatisfiesPost` and `¬ Diverges` across
   all `65,536` `(seed : u8, fv : FlagVec8)` inputs (`37 ≤ acc ≤ 130561`) in `8`
   linear `@[irreducible]` stage cuts over `BlockTree.ofList`, paired with
   tight endpoint witnesses (`37` and `127327`) and a negative unchecked
   overflow fault canary (`FaultKind.undefined`).
2. **Two-Pass Conjunctive WP (`bodyTwoPassAdd`):** Proves safety/termination and
   functional `wlpProg` separately and combines them via
   `wpProg_of_wlp_and_safety`.
3. **Cleanup-Return Rejection & Shared `O(K)` `DropSpineCut`
   (`bodyCleanupFaultBlock`, `bodyCleanupChain4`):** Proves `cleanup = true`
   `return_` faults with `FaultKind.unsupported`, and verifies an `11`-block
   4-guard program sharing one `DropSpineCut` spine across all `16` guard paths.
4. **Early-Return (`?`) Loop Rule (`bodyLoopEarlyRetClean`,
   `bodyLoopEarlyRetUninitRet`):** Verifies a bounded loop with mid-loop early
   return via `wpOutcomeState_loop_early_return_sound` and refutes an early
   return that skips `_0` initialization (`FaultKind.undefined`).
5. **Spatial `ByteHeaplet` PCM & `MemDisjointFrame` Canaries:** Exercises
   disjoint heaplet framing, conflict refutation, and metadata preservation.
-/

/-! ## Computable Scalar / Tuple Helpers (`0` `noncomputable`) -/

/-- `u8` MIR type. -/
def coreU8Ty : MirTy := .int .i8 false

/-- `u32` MIR type. -/
def coreU32Ty : MirTy := .int .i32 false

/-- `(u32, bool)` overflowing-arithmetic return type. -/
def coreOvU32Ty : MirTy := .tuple [coreU32Ty, .bool]

/-- Canonical `u8` `Val` from `n : Nat`. -/
def coreU8Val (n : Nat) : Val :=
  .scalar ⟨.i8, false, truncateBitsComp .i8 (BitVec.ofNat 128 n)⟩

/-- Canonical `u32` `Val` from `n : Nat`. -/
def coreU32Val (n : Nat) : Val :=
  .scalar ⟨.i32, false, truncateBitsComp .i32 (BitVec.ofNat 128 n)⟩

/-- Constant `u8` `Operand`. -/
def coreU8Const (n : Nat) : Operand :=
  .constant ⟨coreU8Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Constant `u32` `Operand`. -/
def coreU32Const (n : Nat) : Operand :=
  .constant ⟨coreU32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Direct unprojected `Place` for `id`. -/
def coreLocalPlace (id : LocalId) : Place := ⟨id, []⟩

private theorem nat_lt_of_ble_true {a b : Nat}
    (h : Nat.ble (a + 1) b = true) : a < b :=
  Nat.le_of_ble_eq_true h

private theorem intWidthModulus_le_pow128 (w : IntWidth) :
    intWidthModulus w ≤ Nat.pow 2 128 := by
  cases w <;> decide

private theorem bitVec128_toNat_of_lt {n : Nat} (h : n < Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n :=
  Nat.mod_eq_of_lt h

private theorem bvOfIntComp_ofNat (n : Nat) :
    bvOfIntComp 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  apply bitVec_eq_of_toNat_eq
  exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))

private theorem truncateBitsComp_toNat_of_lt128 (w : IntWidth) {n : Nat}
    (h128 : n < Nat.pow 2 128) :
    (truncateBitsComp w (BitVec.ofNat 128 n)).toNat =
      Nat.mod n (intWidthModulus w) := by
  rw [truncateBitsComp_eq, toNat_truncateBits, bitVec128_toNat_of_lt h128]

private theorem truncateBitsComp_of_lt {w : IntWidth} {n : Nat}
    (h : n < intWidthModulus w) :
    truncateBitsComp w (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  have h128 : n < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le h (intWidthModulus_le_pow128 w)
  rw [truncateBitsComp_eq]
  apply truncateBits_of_toNat_lt
  rw [bitVec128_toNat_of_lt h128]
  exact h

private theorem truncateBitsComp_idem (w : IntWidth) (x : BitVec 128) :
    truncateBitsComp w (truncateBitsComp w x) = truncateBitsComp w x := by
  rw [truncateBitsComp_eq, truncateBitsComp_eq]
  exact truncateBits_idem w x

private theorem truncateScalarComp_unsigned_exact {w : IntWidth} {n : Nat}
    (h : n < intWidthModulus w) :
    truncateScalarComp w false (Int.ofNat n) =
      .ok (⟨w, false, truncateBitsComp w (BitVec.ofNat 128 n)⟩, false) := by
  change (Except.ok
      (⟨w, false, truncateBitsComp w (bvOfIntComp 128 (Int.ofNat n))⟩,
       !(bv128BeqComp (truncateBitsComp w (bvOfIntComp 128 (Int.ofNat n)))
         (bvOfIntComp 128 (Int.ofNat n)))) :
      Except FaultKind (ScalarVal × Bool)) = _
  rw [bvOfIntComp_ofNat, truncateBitsComp_of_lt h]
  have hRefl : bv128BeqComp (BitVec.ofNat 128 n) (BitVec.ofNat 128 n) = true :=
    Nat.beq_refl _
  rw [hRefl]
  rfl

private theorem decodeScalarComp_unsigned_of_lt {w : IntWidth} {n : Nat}
    (h : n < intWidthModulus w) :
    decodeScalarComp ⟨w, false, truncateBitsComp w (BitVec.ofNat 128 n)⟩ =
      Int.ofNat n := by
  have h128 : n < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le h (intWidthModulus_le_pow128 w)
  change Int.ofNat
    (truncateBitsComp w (truncateBitsComp w (BitVec.ofNat 128 n))).toNat =
    Int.ofNat n
  rw [truncateBitsComp_idem, truncateBitsComp_toNat_of_lt128 w h128]
  exact congrArg Int.ofNat (Nat.mod_eq_of_lt h)

private theorem intBleComp_pow128_ofNat_false {n : Nat}
    (h : n < Nat.pow 2 128) :
    intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat n) = false := by
  cases hb : intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat n) with
  | false => rfl
  | true =>
    have hLe := (intBleComp_iff (HPow.hPow (2 : Int) 128) (Int.ofNat n)).mp hb
    have hPow : HPow.hPow (2 : Int) 128 =
        Int.ofNat (Nat.succ (Nat.pow 2 128 - 1)) := by decide
    have hSucc : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
    rw [hPow] at hLe
    change Int.NonNeg (Int.subNatNat n (Nat.succ (Nat.pow 2 128 - 1))) at hLe
    rw [hSucc] at hLe
    unfold Int.subNatNat at hLe
    cases hSub : Nat.pow 2 128 - n with
    | zero => exact False.elim (Nat.not_le_of_gt h (Nat.le_of_sub_eq_zero hSub))
    | succ _ => rw [hSub] at hLe; nomatch hLe

private theorem checkValBy_mirTyBeq_u8 (n : Nat) :
    checkValBy MirTy.beq (coreU8Val n) coreU8Ty = true := by
  dsimp only [checkValBy, valTy?Comp, coreU8Val, coreU8Ty]
  rw [scalarWfComp_eq, truncateBitsComp_eq, scalarWf_truncateBits]
  rfl

private theorem checkValBy_mirTyBeq_u32 (n : Nat) :
    checkValBy MirTy.beq (coreU32Val n) coreU32Ty = true := by
  dsimp only [checkValBy, valTy?Comp, coreU32Val, coreU32Ty]
  rw [scalarWfComp_eq, truncateBitsComp_eq, scalarWf_truncateBits]
  rfl

private theorem checkValBy_mirTyBeq_ovU32 (n : Nat) (b : Bool) :
    checkValBy MirTy.beq (.tuple [coreU32Val n, .bool b]) coreOvU32Ty = true := by
  dsimp only [checkValBy, valTy?Comp, coreU32Val, coreOvU32Ty, coreU32Ty]
  rw [scalarWfComp_eq, truncateBitsComp_eq, scalarWf_truncateBits]
  rfl

private theorem coreU8Val_mod_of_lt128 {n : Nat} (h128 : n < Nat.pow 2 128) :
    coreU8Val (Nat.mod n 256) = coreU8Val n := by
  have hm128 : Nat.mod n 256 < Nat.pow 2 128 :=
    Nat.lt_trans (Nat.mod_lt n (by decide)) (by decide)
  unfold coreU8Val
  apply congrArg Val.scalar
  apply congrArg (ScalarVal.mk .i8 false)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBitsComp_toNat_of_lt128 .i8 hm128,
    truncateBitsComp_toNat_of_lt128 .i8 h128]
  exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))

private theorem evalConstLitComp_u8 (n : Nat) (hn : n < 256) :
    evalConstLitComp coreU8Ty (.scalar (BitVec.ofNat 128 n)) =
      .ok (coreU8Val n) := by
  have hn8 : n < intWidthModulus .i8 := hn
  change (if !(bv128BeqComp (truncateBitsComp .i8 (BitVec.ofNat 128 n))
        (BitVec.ofNat 128 n)) then
      Except.error FaultKind.unsupported
    else Except.ok (coreU8Val n)) = Except.ok (coreU8Val n)
  rw [truncateBitsComp_of_lt hn8]
  have hRefl : bv128BeqComp (BitVec.ofNat 128 n) (BitVec.ofNat 128 n) = true :=
    Nat.beq_refl _
  rw [hRefl]
  rfl

private theorem evalConstLitComp_u32 (n : Nat) (hn : n < 4294967296) :
    evalConstLitComp coreU32Ty (.scalar (BitVec.ofNat 128 n)) =
      .ok (coreU32Val n) := by
  have hn32 : n < intWidthModulus .i32 := hn
  change (if !(bv128BeqComp (truncateBitsComp .i32 (BitVec.ofNat 128 n))
        (BitVec.ofNat 128 n)) then
      Except.error FaultKind.unsupported
    else Except.ok (coreU32Val n)) = Except.ok (coreU32Val n)
  rw [truncateBitsComp_of_lt hn32]
  have hRefl : bv128BeqComp (BitVec.ofNat 128 n) (BitVec.ofNat 128 n) = true :=
    Nat.beq_refl _
  rw [hRefl]
  rfl

private theorem evalIntToIntCastComp_u8_to_u32 {a : Nat} (ha : a < 256) :
    evalIntToIntCastComp (coreU8Val a) coreU32Ty = .ok (coreU32Val a) := by
  have ha8 : a < intWidthModulus .i8 := ha
  have ha128 : a < Nat.pow 2 128 := Nat.lt_trans ha (by decide)
  have hBits :
      (truncateBitsComp .i8 (truncateBitsComp .i8 (BitVec.ofNat 128 a))).toNat =
        a := by
    rw [truncateBitsComp_idem, truncateBitsComp_toNat_of_lt128 .i8 ha128]
    exact Nat.mod_eq_of_lt ha8
  dsimp only [evalIntToIntCastComp, intLikeBitsComp, coreU8Val, coreU32Ty,
    coreU32Val]
  rw [hBits]
  rfl

private theorem evalIntToIntCastComp_u32_to_u8 {a : Nat} (ha : a < 4294967296) :
    evalIntToIntCastComp (coreU32Val a) coreU8Ty =
      .ok (coreU8Val (Nat.mod a 256)) := by
  have ha32 : a < intWidthModulus .i32 := ha
  have ha128 : a < Nat.pow 2 128 := Nat.lt_trans ha (by decide)
  have hBits :
      (truncateBitsComp .i32
        (truncateBitsComp .i32 (BitVec.ofNat 128 a))).toNat = a := by
    rw [truncateBitsComp_idem, truncateBitsComp_toNat_of_lt128 .i32 ha128]
    exact Nat.mod_eq_of_lt ha32
  dsimp only [evalIntToIntCastComp, intLikeBitsComp, coreU32Val, coreU8Ty]
  rw [hBits]
  change (Except.ok (coreU8Val a) : Except FaultKind Val) =
    Except.ok (coreU8Val (Nat.mod a 256))
  rw [coreU8Val_mod_of_lt128 ha128]

private theorem evalBinOpComp_addWithOverflow_u32 {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296) (hab : a + b < 4294967296) :
    evalBinOpComp .addWithOverflow (coreU32Val a) (coreU32Val b) =
      .ok (.tuple [coreU32Val (a + b), .bool false]) := by
  have ha32 : a < intWidthModulus .i32 := ha
  have hb32 : b < intWidthModulus .i32 := hb
  have hab32 : a + b < intWidthModulus .i32 := hab
  have hab128 : a + b < Nat.pow 2 128 := Nat.lt_trans hab (by decide)
  have hAdd : Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := rfl
  have hBlt0 : intBltComp (Int.ofNat (a + b)) 0 = false := rfl
  dsimp only [evalBinOpComp, binOpIsShiftComp, intWidthBeqComp, boolBeqComp,
    evalArithOpComp, binOpIsUncheckedComp, binOpIsOverflowingComp, coreU32Val]
  rw [decodeScalarComp_unsigned_of_lt ha32, decodeScalarComp_unsigned_of_lt hb32,
    hAdd, truncateScalarComp_unsigned_exact hab32]
  change (if ((intBltComp (Int.ofNat (a + b)) 0 ||
        intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat (a + b))) || false) &&
        false then
      Except.error FaultKind.undefined
    else
      Except.ok (Val.tuple [coreU32Val (a + b),
        Val.bool ((intBltComp (Int.ofNat (a + b)) 0 ||
          intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat (a + b))) || false)])) =
    Except.ok (Val.tuple [coreU32Val (a + b), Val.bool false])
  rw [hBlt0, intBleComp_pow128_ofNat_false hab128]
  rfl

private theorem evalBinOpComp_mulWithOverflow_u32 {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296) (hab : a * b < 4294967296) :
    evalBinOpComp .mulWithOverflow (coreU32Val a) (coreU32Val b) =
      .ok (.tuple [coreU32Val (a * b), .bool false]) := by
  have ha32 : a < intWidthModulus .i32 := ha
  have hb32 : b < intWidthModulus .i32 := hb
  have hab32 : a * b < intWidthModulus .i32 := hab
  have hab128 : a * b < Nat.pow 2 128 := Nat.lt_trans hab (by decide)
  have hMul : Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) := rfl
  have hBlt0 : intBltComp (Int.ofNat (a * b)) 0 = false := rfl
  dsimp only [evalBinOpComp, binOpIsShiftComp, intWidthBeqComp, boolBeqComp,
    evalArithOpComp, binOpIsUncheckedComp, binOpIsOverflowingComp, coreU32Val]
  rw [decodeScalarComp_unsigned_of_lt ha32, decodeScalarComp_unsigned_of_lt hb32,
    hMul, truncateScalarComp_unsigned_exact hab32]
  change (if ((intBltComp (Int.ofNat (a * b)) 0 ||
        intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat (a * b))) || false) &&
        false then
      Except.error FaultKind.undefined
    else
      Except.ok (Val.tuple [coreU32Val (a * b),
        Val.bool ((intBltComp (Int.ofNat (a * b)) 0 ||
          intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat (a * b))) || false)])) =
    Except.ok (Val.tuple [coreU32Val (a * b), Val.bool false])
  rw [hBlt0, intBleComp_pow128_ofNat_false hab128]
  rfl

private theorem evalBinOpComp_addUnchecked_u32 {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296) (hab : a + b < 4294967296) :
    evalBinOpComp .addUnchecked (coreU32Val a) (coreU32Val b) =
      .ok (coreU32Val (a + b)) := by
  have ha32 : a < intWidthModulus .i32 := ha
  have hb32 : b < intWidthModulus .i32 := hb
  have hab32 : a + b < intWidthModulus .i32 := hab
  have hab128 : a + b < Nat.pow 2 128 := Nat.lt_trans hab (by decide)
  have hAdd : Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := rfl
  have hBlt0 : intBltComp (Int.ofNat (a + b)) 0 = false := rfl
  dsimp only [evalBinOpComp, binOpIsShiftComp, intWidthBeqComp, boolBeqComp,
    evalArithOpComp, binOpIsUncheckedComp, binOpIsOverflowingComp, coreU32Val]
  rw [decodeScalarComp_unsigned_of_lt ha32, decodeScalarComp_unsigned_of_lt hb32,
    hAdd, truncateScalarComp_unsigned_exact hab32]
  change (if ((intBltComp (Int.ofNat (a + b)) 0 ||
        intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat (a + b))) || false) &&
        true then
      Except.error FaultKind.undefined
    else Except.ok (coreU32Val (a + b))) = Except.ok (coreU32Val (a + b))
  rw [hBlt0, intBleComp_pow128_ofNat_false hab128]
  rfl

private theorem evalBinOpComp_mulUnchecked_u32 {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296) (hab : a * b < 4294967296) :
    evalBinOpComp .mulUnchecked (coreU32Val a) (coreU32Val b) =
      .ok (coreU32Val (a * b)) := by
  have ha32 : a < intWidthModulus .i32 := ha
  have hb32 : b < intWidthModulus .i32 := hb
  have hab32 : a * b < intWidthModulus .i32 := hab
  have hab128 : a * b < Nat.pow 2 128 := Nat.lt_trans hab (by decide)
  have hMul : Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) := rfl
  have hBlt0 : intBltComp (Int.ofNat (a * b)) 0 = false := rfl
  dsimp only [evalBinOpComp, binOpIsShiftComp, intWidthBeqComp, boolBeqComp,
    evalArithOpComp, binOpIsUncheckedComp, binOpIsOverflowingComp, coreU32Val]
  rw [decodeScalarComp_unsigned_of_lt ha32, decodeScalarComp_unsigned_of_lt hb32,
    hMul, truncateScalarComp_unsigned_exact hab32]
  change (if ((intBltComp (Int.ofNat (a * b)) 0 ||
        intBleComp (HPow.hPow (2 : Int) 128) (Int.ofNat (a * b))) || false) &&
        true then
      Except.error FaultKind.undefined
    else Except.ok (coreU32Val (a * b))) = Except.ok (coreU32Val (a * b))
  rw [hBlt0, intBleComp_pow128_ofNat_false hab128]
  rfl

/-! ## Canary Suite 1: 256-Path Overflow/Cast Diamond -/

/-- Per-stage hull step `(min(2*lo, lo + k + 1), max(2*hi + 255, hi + k + 1))`.
-/
abbrev overflowHullStep (k : Nat) (lh : Nat × Nat) : Nat × Nat :=
  (compNatMin (2 * lh.1) (lh.1 + (k + 1)),
   compNatMax (2 * lh.2 + 255) (lh.2 + (k + 1)))

/-- Interval hull after `stages` diamond stages starting from `[1, 256]`. -/
abbrev overflowHullAt (stages : Nat) : Nat × Nat :=
  (@Nat.rec (fun _ => Nat × (Nat × Nat))
    (0, (1, 256))
    (fun _ st => (st.1 + 1, overflowHullStep st.1 st.2))
    stages).2

/-- Lower hull bound at stage `k`. -/
abbrev hullLo (k : Nat) : Nat := (overflowHullAt k).1

/-- Upper hull bound at stage `k`. -/
abbrev hullHi (k : Nat) : Nat := (overflowHullAt k).2

/-- Stage `k` boolean `SwitchInt` dispatch block (`3 * k + 1`). -/
def mkStageSwitchBlock (k : Nat) : BasicBlock :=
  { statements := []
    terminator := .switchInt (.copy (coreLocalPlace (k + 2)))
      { branches := [(0, 3 * k + 3)], otherwise := 3 * k + 2 }
    cleanup := false }

/-- Stage `k` `true`-arm block (`3 * k + 2`): `u32 -> u8 -> u32` roundtrip cast,
`mulWithOverflow` + `mulUnchecked` by `2`, and `addWithOverflow` +
`addUnchecked`. -/
def mkStageTrueBlock (k : Nat) : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 11)
        (.cast .intToInt (.copy (coreLocalPlace 10)) coreU8Ty),
      .assign (coreLocalPlace 12)
        (.cast .intToInt (.copy (coreLocalPlace 11)) coreU32Ty),
      .assign (coreLocalPlace 13)
        (.binaryOp .mulWithOverflow (.copy (coreLocalPlace 10)) (coreU32Const 2)),
      .assign (coreLocalPlace 10)
        (.binaryOp .mulUnchecked (.copy (coreLocalPlace 10)) (coreU32Const 2)),
      .assign (coreLocalPlace 13)
        (.binaryOp .addWithOverflow (.copy (coreLocalPlace 10))
          (.copy (coreLocalPlace 12))),
      .assign (coreLocalPlace 10)
        (.binaryOp .addUnchecked (.copy (coreLocalPlace 10))
          (.copy (coreLocalPlace 12)))
    ]
    terminator := .goto (3 * k + 4)
    cleanup := false }

/-- Stage `k` `false`-arm block (`3 * k + 3`): constant `(k + 1)u8 -> u32` cast
and `addWithOverflow` + `addUnchecked`. -/
def mkStageFalseBlock (k : Nat) : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 11) (.use (coreU8Const (k + 1))),
      .assign (coreLocalPlace 12)
        (.cast .intToInt (.copy (coreLocalPlace 11)) coreU32Ty),
      .assign (coreLocalPlace 13)
        (.binaryOp .addWithOverflow (.copy (coreLocalPlace 10))
          (.copy (coreLocalPlace 12))),
      .assign (coreLocalPlace 10)
        (.binaryOp .addUnchecked (.copy (coreLocalPlace 10))
          (.copy (coreLocalPlace 12)))
    ]
    terminator := .goto (3 * k + 4)
    cleanup := false }

/-- 3-block diamond slice for stage `k`. -/
def mkOverflowCastStageBlocks (k : Nat) : List BasicBlock :=
  [mkStageSwitchBlock k, mkStageTrueBlock k, mkStageFalseBlock k]

/-- Entry prologue block (`bb0`): widens `seed : u8` to `u32` and computes
`seed + 1` via `addWithOverflow` + `addUnchecked`. -/
def join8EntryBlock : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 11) (.use (.copy (coreLocalPlace 1))),
      .assign (coreLocalPlace 12)
        (.cast .intToInt (.copy (coreLocalPlace 11)) coreU32Ty),
      .assign (coreLocalPlace 13)
        (.binaryOp .addWithOverflow (.copy (coreLocalPlace 12)) (coreU32Const 1)),
      .assign (coreLocalPlace 10)
        (.binaryOp .addUnchecked (.copy (coreLocalPlace 12)) (coreU32Const 1))
    ]
    terminator := .goto 1
    cleanup := false }

/-- Exit block (`bb25`): returns `_13 : (u32, bool)`. -/
def join8ExitBlock : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 0) (.use (.copy (coreLocalPlace 13)))
    ]
    terminator := .return_
    cleanup := false }

/-- `26`-block, `256`-boolean-path MIR `Body` combining overflowing and
unchecked arithmetic with narrowing and widening integer casts. -/
def bodyOverflowCastJoin8 : Body :=
  { identity := "anneal_core::overflow_cast_join8"
    isUnsafe := false
    locals := [
      coreOvU32Ty, coreU8Ty,
      .bool, .bool, .bool, .bool, .bool, .bool, .bool, .bool,
      coreU32Ty, coreU8Ty, coreU32Ty, coreOvU32Ty
    ]
    argumentCount := 9
    basicBlocks :=
      [join8EntryBlock] ++
      mkOverflowCastStageBlocks 0 ++
      mkOverflowCastStageBlocks 1 ++
      mkOverflowCastStageBlocks 2 ++
      mkOverflowCastStageBlocks 3 ++
      mkOverflowCastStageBlocks 4 ++
      mkOverflowCastStageBlocks 5 ++
      mkOverflowCastStageBlocks 6 ++
      mkOverflowCastStageBlocks 7 ++
      [join8ExitBlock] }

/-- Balanced depth-`5` `BlockTree` built once outside the step loop. -/
def btOverflowCastJoin8 : BlockTree BasicBlock :=
  BlockTree.ofList bodyOverflowCastJoin8.basicBlocks

/-- Validity witness for `btOverflowCastJoin8`. -/
theorem valid_btOverflowCastJoin8 :
    ValidBlockTree bodyOverflowCastJoin8.basicBlocks btOverflowCastJoin8 :=
  valid_blockTree_ofList bodyOverflowCastJoin8.basicBlocks

/-- 8-bit branch-flag tuple for `bodyOverflowCastJoin8`. -/
structure FlagVec8 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool

/-- Projects flag `k` out of `fv : FlagVec8`. -/
def flagAt8 (fv : FlagVec8) (k : Nat) : Bool :=
  match k with
  | 0 => fv.b0
  | 1 => fv.b1
  | 2 => fv.b2
  | 3 => fv.b3
  | 4 => fv.b4
  | 5 => fv.b5
  | 6 => fv.b6
  | _ => fv.b7

/-- Entry argument list `[seedVal, b0, ..., b7]`. -/
def flagArgs8 (seedVal : Val) (fv : FlagVec8) : List Val :=
  [seedVal, .bool fv.b0, .bool fv.b1, .bool fv.b2, .bool fv.b3,
   .bool fv.b4, .bool fv.b5, .bool fv.b6, .bool fv.b7]

/-- Pure-data hull cutpoint descriptor `(blockIdx, lo, hi)`. -/
structure OverflowHullNode where
  blockIdx : Nat
  lo : Nat
  hi : Nat

/-- Canonical hull cutpoint node at stage `k` (`blockIdx = 3 * k + 1`). -/
def mkOverflowHullNode (k : Nat) : OverflowHullNode :=
  { blockIdx := 3 * k + 1, lo := hullLo k, hi := hullHi k }

private def mkJoin8Locals (s0 : LocalSlot) (seed : Nat) (fv : FlagVec8)
    (s10 s11 s12 s13 : LocalSlot) : List LocalSlot :=
  [s0, .immediate (some (coreU8Val seed)),
   .immediate (some (.bool fv.b0)), .immediate (some (.bool fv.b1)),
   .immediate (some (.bool fv.b2)), .immediate (some (.bool fv.b3)),
   .immediate (some (.bool fv.b4)), .immediate (some (.bool fv.b5)),
   .immediate (some (.bool fv.b6)), .immediate (some (.bool fv.b7)),
   s10, s11, s12, s13]

private def mkJoin8RawState (blockIdx stmtIdx : Nat)
    (locals : List LocalSlot) : State :=
  { frames := [{ defId := 0, blockIdx := blockIdx, stmtIdx := stmtIdx,
                 locals := locals }]
    callerMem := ⟨[]⟩
    mem := entryMemoryComp }

private def mkStageLocals (seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat) : List LocalSlot :=
  mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc)))
    (.immediate (some (coreU8Val v11)))
    (.immediate (some (coreU32Val v12)))
    (.immediate (some (.tuple [coreU32Val acc, .bool false])))

private def mkStageState (blockIdx stmtIdx seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat) : State :=
  mkJoin8RawState blockIdx stmtIdx (mkStageLocals seed fv acc v11 v12)

/-- Cutpoint state invariant at `node`. -/
def HoldsAtOverflowNode (node : OverflowHullNode) (seed : Nat)
    (fv : FlagVec8) (s : State) : Prop :=
  ∃ (acc v11 v12 : Nat),
    node.lo ≤ acc ∧ acc ≤ node.hi ∧
    s = mkStageState node.blockIdx 0 seed fv acc v11 v12

/-- Zero-`Prop`-argument stage-cut join predicate over `StepStageCut` /
`wpUntilCutStep` (sealed `@[irreducible]` below). -/
def OverflowCastStageCut (body : Body) (bt : BlockTree BasicBlock)
    (src dst : OverflowHullNode) (seed : Nat) (fv : FlagVec8)
    (fuel : Nat) : Prop :=
  ∀ s : State,
    HoldsAtOverflowNode src seed fv s →
    wpUntilCutStep (evalMirStepBlockTreeBy MirTy.beq bt body)
      (HoldsAtOverflowNode dst seed fv) fuel s

private theorem seal_overflowCastStage_hull {body : Body}
    {bt : BlockTree BasicBlock}
    {srcBlk dstBlk srcLo srcHi trueLo trueHi falseLo falseHi seed fuel : Nat}
    {fv : FlagVec8} (bStage : Bool)
    (hDiamond : ∀ (acc v11 v12 : Nat),
      srcLo ≤ acc → acc ≤ srcHi →
      if bStage then
        wpUntilCutStep (evalMirStepBlockTreeBy MirTy.beq bt body)
          (HoldsAtOverflowNode ⟨dstBlk, trueLo, trueHi⟩ seed fv)
          fuel (mkStageState srcBlk 0 seed fv acc v11 v12)
      else
        wpUntilCutStep (evalMirStepBlockTreeBy MirTy.beq bt body)
          (HoldsAtOverflowNode ⟨dstBlk, falseLo, falseHi⟩ seed fv)
          fuel (mkStageState srcBlk 0 seed fv acc v11 v12)) :
    OverflowCastStageCut body bt ⟨srcBlk, srcLo, srcHi⟩
      ⟨dstBlk, compNatMin trueLo falseLo, compNatMax trueHi falseHi⟩
      seed fv fuel := by
  intro s hSrc
  let ⟨acc, v11, v12, hLo, hHi, hs⟩ := hSrc
  subst hs
  have hD := hDiamond acc v11 v12 hLo hHi
  cases bStage with
  | true =>
    refine wpUntilCutStep_mono (fun sc hsc => ?_) hD
    let ⟨a', x11, x12, haLo, haHi, hscEq⟩ := hsc
    exact ⟨a', x11, x12,
      Nat.le_trans (compNatMin_le_left trueLo falseLo) haLo,
      Nat.le_trans haHi (le_compNatMax_left trueHi falseHi),
      hscEq⟩
  | false =>
    refine wpUntilCutStep_mono (fun sc hsc => ?_) hD
    let ⟨a', x11, x12, haLo, haHi, hscEq⟩ := hsc
    exact ⟨a', x11, x12,
      Nat.le_trans (compNatMin_le_right trueLo falseLo) haLo,
      Nat.le_trans haHi (le_compNatMax_right trueHi falseHi),
      hscEq⟩

/-- Sequential composition of `OverflowCastStageCut` stages. -/
theorem overflowCastStageCut_compose {body : Body} {bt : BlockTree BasicBlock}
    {n0 n1 n2 : OverflowHullNode} {seed f1 f2 : Nat} {fv : FlagVec8}
    (h01 : OverflowCastStageCut body bt n0 n1 seed fv f1)
    (h12 : OverflowCastStageCut body bt n1 n2 seed fv f2) :
    OverflowCastStageCut body bt n0 n2 seed fv (f1 + f2) :=
  fun s hs => wpUntilCutStep_trans (h01 s hs) (fun sc hsc => h12 sc hsc)

/-- Lifts a composed `OverflowCastStageCut` chain into `wpOutcomeState` via
`MirStageCut.ofBlockTree` (`wpOutcomeState_of_wpUntilCutBlockTree`). -/
theorem wpOutcomeState_of_overflowCastStageCut {body : Body}
    {bt : BlockTree BasicBlock}
    {src dst : OverflowHullNode} {seed fChain fExit : Nat} {fv : FlagVec8}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} {s : State}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hStart : HoldsAtOverflowNode src seed fv s)
    (hChain : OverflowCastStageCut body bt src dst seed fv fChain)
    (hExit : ∀ sc, HoldsAtOverflowNode dst seed fv sc →
      wpOutcomeState (bodyProg body) onDone onFault fExit sc) :
    wpOutcomeState (bodyProg body) onDone onFault (fChain + fExit) s :=
  wpOutcomeState_of_wpUntilCutBlockTree (fun _ _ => rfl) hValid
    (hChain s hStart) hExit

attribute [irreducible] OverflowCastStageCut

private theorem evalPrimitiveOperandComp_u32Const (locs : List LocalSlot)
    (n : Nat) (hn : n < 4294967296) :
    evalPrimitiveOperandComp bodyOverflowCastJoin8.locals locs entryMemoryComp
        (coreU32Const n) =
      .ok (coreU32Val n, locs, entryMemoryComp) := by
  dsimp only [evalPrimitiveOperandComp, evalOperandToSlotComp, coreU32Const]
  rw [evalConstLitComp_u32 n hn]
  rfl

private theorem evalRvalueBy_use_u8Const (locs : List LocalSlot)
    (n : Nat) (hn : n < 256) :
    evalRvalueBy MirTy.beq bodyOverflowCastJoin8.locals locs entryMemoryComp
        coreU8Ty (.use (coreU8Const n)) =
      .ok (coreU8Val n, locs, entryMemoryComp) := by
  dsimp only [evalRvalueBy, evalOperandToSlotComp, coreU8Const]
  rw [evalConstLitComp_u8 n hn]
  rfl

private theorem step_trueBlk_s0 (k seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hAcc : acc < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkStageState (3 * k + 2) 0 seed fv acc v11 v12) =
    .step (mkJoin8RawState (3 * k + 2) 1
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val (Nat.mod acc 256))))
        (.immediate (some (coreU32Val v12)))
        (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) := by
  dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
  rw [hTr]
  change (match evalIntToIntCastComp (coreU32Val acc) coreU8Ty with
    | .error k => StepResult.fault k
    | .ok val =>
      match writePlaceBy MirTy.beq (mkStageLocals seed fv acc v11 v12)
          entryMemoryComp 11 coreU8Ty val with
      | .error k => StepResult.fault k
      | .ok (lw, mw) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 3 * k + 2, stmtIdx := 1,
                       locals := lw }]
          callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalIntToIntCastComp_u32_to_u8 hAcc]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u8]
  rfl

private theorem step_trueBlk_s1 (k seed : Nat) (fv : FlagVec8)
    (acc m v12 : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hm : m < 256) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 2) 1
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc)))
          (.immediate (some (coreU8Val m)))
          (.immediate (some (coreU32Val v12)))
          (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) =
    .step (mkJoin8RawState (3 * k + 2) 2
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val m)))
        (.immediate (some (coreU32Val m)))
        (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) := by
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
  rw [hTr]
  change (match evalIntToIntCastComp (coreU8Val m) coreU32Ty with
    | .error k => StepResult.fault k
    | .ok val =>
      match writePlaceBy MirTy.beq _ entryMemoryComp 12 coreU32Ty val with
      | .error k => StepResult.fault k
      | .ok (lw, mw) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 3 * k + 2, stmtIdx := 2,
                       locals := lw }]
          callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalIntToIntCastComp_u8_to_u32 hm]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u32]
  rfl

private theorem step_trueBlk_s2 (k seed : Nat) (fv : FlagVec8) (acc m : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hAcc : acc < 4294967296) (hMul : acc * 2 < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 2) 2
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc)))
          (.immediate (some (coreU8Val m)))
          (.immediate (some (coreU32Val m)))
          (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) =
    .step (mkJoin8RawState (3 * k + 2) 3
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val m)))
        (.immediate (some (coreU32Val m)))
        (.immediate (some (.tuple [coreU32Val (2 * acc), .bool false]))))) := by
  have h2 : (2 : Nat) < 4294967296 := nat_lt_of_ble_true rfl
  have hComm : acc * 2 = 2 * acc := Nat.mul_comm acc 2
  let locs := mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc)))
    (.immediate (some (coreU8Val m)))
    (.immediate (some (coreU32Val m)))
    (.immediate (some (.tuple [coreU32Val acc, .bool false])))
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
  rw [hTr]
  change (match (match evalPrimitiveOperandComp bodyOverflowCastJoin8.locals locs
          entryMemoryComp (coreU32Const 2) with
        | .error k => Except.error k
        | .ok (rVal, l2, m2) =>
          match evalBinOpComp .mulWithOverflow (coreU32Val acc) rVal with
          | .error k => Except.error k
          | .ok res => Except.ok (res, l2, m2)) with
      | .error k => StepResult.fault k
      | .ok (val, lr, mr) =>
        match writePlaceBy MirTy.beq lr mr 13 coreOvU32Ty val with
        | .error k => StepResult.fault k
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 3 * k + 2, stmtIdx := 3,
                         locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalPrimitiveOperandComp_u32Const locs 2 h2]
  dsimp only
  rw [evalBinOpComp_mulWithOverflow_u32 hAcc h2 hMul, hComm]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_ovU32]
  rfl

private theorem step_trueBlk_s3 (k seed : Nat) (fv : FlagVec8) (acc m : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hAcc : acc < 4294967296) (hMul : acc * 2 < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 2) 3
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc)))
          (.immediate (some (coreU8Val m)))
          (.immediate (some (coreU32Val m)))
          (.immediate (some (.tuple [coreU32Val (2 * acc), .bool false]))))) =
    .step (mkJoin8RawState (3 * k + 2) 4
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val (2 * acc))))
        (.immediate (some (coreU8Val m)))
        (.immediate (some (coreU32Val m)))
        (.immediate (some (.tuple [coreU32Val (2 * acc), .bool false]))))) := by
  have h2 : (2 : Nat) < 4294967296 := nat_lt_of_ble_true rfl
  have hComm : acc * 2 = 2 * acc := Nat.mul_comm acc 2
  let locs := mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc)))
    (.immediate (some (coreU8Val m)))
    (.immediate (some (coreU32Val m)))
    (.immediate (some (.tuple [coreU32Val (2 * acc), .bool false])))
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
  rw [hTr]
  change (match (match evalPrimitiveOperandComp bodyOverflowCastJoin8.locals locs
          entryMemoryComp (coreU32Const 2) with
        | .error k => Except.error k
        | .ok (rVal, l2, m2) =>
          match evalBinOpComp .mulUnchecked (coreU32Val acc) rVal with
          | .error k => Except.error k
          | .ok res => Except.ok (res, l2, m2)) with
      | .error k => StepResult.fault k
      | .ok (val, lr, mr) =>
        match writePlaceBy MirTy.beq lr mr 10 coreU32Ty val with
        | .error k => StepResult.fault k
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 3 * k + 2, stmtIdx := 4,
                         locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalPrimitiveOperandComp_u32Const locs 2 h2]
  dsimp only
  rw [evalBinOpComp_mulUnchecked_u32 hAcc h2 hMul, hComm]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u32]
  rfl

private theorem step_trueBlk_s4 (k seed : Nat) (fv : FlagVec8) (acc2 m : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hAcc2 : acc2 < 4294967296) (hm32 : m < 4294967296)
    (hSum : acc2 + m < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 2) 4
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc2)))
          (.immediate (some (coreU8Val m)))
          (.immediate (some (coreU32Val m)))
          (.immediate (some (.tuple [coreU32Val acc2, .bool false]))))) =
    .step (mkJoin8RawState (3 * k + 2) 5
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc2)))
        (.immediate (some (coreU8Val m)))
        (.immediate (some (coreU32Val m)))
        (.immediate (some (.tuple [coreU32Val (acc2 + m), .bool false]))))) := by
  let locs := mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc2)))
    (.immediate (some (coreU8Val m)))
    (.immediate (some (coreU32Val m)))
    (.immediate (some (.tuple [coreU32Val acc2, .bool false])))
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
  rw [hTr]
  change (match (match evalBinOpComp .addWithOverflow (coreU32Val acc2)
          (coreU32Val m) with
        | .error k => Except.error k
        | .ok res => Except.ok (res, locs, entryMemoryComp)) with
      | .error k => StepResult.fault k
      | .ok (val, lr, mr) =>
        match writePlaceBy MirTy.beq lr mr 13 coreOvU32Ty val with
        | .error k => StepResult.fault k
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 3 * k + 2, stmtIdx := 5,
                         locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalBinOpComp_addWithOverflow_u32 hAcc2 hm32 hSum]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_ovU32]
  rfl

private theorem step_trueBlk_s5 (k seed : Nat) (fv : FlagVec8) (acc2 m : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hAcc2 : acc2 < 4294967296) (hm32 : m < 4294967296)
    (hSum : acc2 + m < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 2) 5
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc2)))
          (.immediate (some (coreU8Val m)))
          (.immediate (some (coreU32Val m)))
          (.immediate (some (.tuple [coreU32Val (acc2 + m), .bool false]))))) =
    .step (mkStageState (3 * k + 2) 6 seed fv (acc2 + m) m m) := by
  let locs := mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc2)))
    (.immediate (some (coreU8Val m)))
    (.immediate (some (coreU32Val m)))
    (.immediate (some (.tuple [coreU32Val (acc2 + m), .bool false])))
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState, mkStageState]
  rw [hTr]
  change (match (match evalBinOpComp .addUnchecked (coreU32Val acc2)
          (coreU32Val m) with
        | .error k => Except.error k
        | .ok res => Except.ok (res, locs, entryMemoryComp)) with
      | .error k => StepResult.fault k
      | .ok (val, lr, mr) =>
        match writePlaceBy MirTy.beq lr mr 10 coreU32Ty val with
        | .error k => StepResult.fault k
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 3 * k + 2, stmtIdx := 6,
                         locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalBinOpComp_addUnchecked_u32 hAcc2 hm32 hSum]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u32]
  rfl

private theorem step_trueBlk_goto (k seed : Nat) (fv : FlagVec8) (acc' m : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k)) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkStageState (3 * k + 2) 6 seed fv acc' m m) =
    .step (mkStageState (3 * k + 4) 0 seed fv acc' m m) := by
  dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
  rw [hTr]
  rfl

private theorem stage_true_arm_wpUntilCut (k seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat)
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hLo : hullLo k ≤ acc) (hHi : acc ≤ hullHi k)
    (hBound : 2 * hullHi k + 255 < 4294967296) :
    wpUntilCutStep
      (evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8)
      (HoldsAtOverflowNode ⟨3 * k + 4, 2 * hullLo k, 2 * hullHi k + 255⟩ seed fv)
      7 (mkStageState (3 * k + 2) 0 seed fv acc v11 v12) := by
  have hModLt256 : Nat.mod acc 256 < 256 := Nat.mod_lt acc (by decide)
  have hModLe255 : Nat.mod acc 256 ≤ 255 := Nat.le_of_lt_succ hModLt256
  have hModLt32 : Nat.mod acc 256 < 4294967296 :=
    Nat.lt_trans hModLt256 (by decide)
  have h2Hi : 2 * acc ≤ 2 * hullHi k := Nat.mul_le_mul_left 2 hHi
  have hSumHi : 2 * acc + Nat.mod acc 256 ≤ 2 * hullHi k + 255 :=
    Nat.add_le_add h2Hi hModLe255
  have hSumLt32 : 2 * acc + Nat.mod acc 256 < 4294967296 :=
    Nat.lt_of_le_of_lt hSumHi hBound
  have h2Lt32 : 2 * acc < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right (2 * acc) (Nat.mod acc 256)) hSumLt32
  have hAccLt32 : acc < 4294967296 := by
    have h1 : acc ≤ 2 * acc := by
      change acc ≤ (1 + 1) * acc
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.le_add_left acc acc
    exact Nat.lt_of_le_of_lt h1 h2Lt32
  have hMulLt32 : acc * 2 < 4294967296 := by
    rw [Nat.mul_comm acc 2]
    exact h2Lt32
  have hSumLo : 2 * hullLo k ≤ 2 * acc + Nat.mod acc 256 :=
    Nat.le_trans (Nat.mul_le_mul_left 2 hLo)
      (Nat.le_add_right (2 * acc) (Nat.mod acc 256))
  exact
    wpUntilCutStep_step (step_trueBlk_s0 k seed fv acc v11 v12 hTr hAccLt32)
    (wpUntilCutStep_step
      (step_trueBlk_s1 k seed fv acc (Nat.mod acc 256) v12 hTr hModLt256)
    (wpUntilCutStep_step
      (step_trueBlk_s2 k seed fv acc (Nat.mod acc 256) hTr hAccLt32 hMulLt32)
    (wpUntilCutStep_step
      (step_trueBlk_s3 k seed fv acc (Nat.mod acc 256) hTr hAccLt32 hMulLt32)
    (wpUntilCutStep_step
      (step_trueBlk_s4 k seed fv (2 * acc) (Nat.mod acc 256) hTr
        h2Lt32 hModLt32 hSumLt32)
    (wpUntilCutStep_step
      (step_trueBlk_s5 k seed fv (2 * acc) (Nat.mod acc 256) hTr
        h2Lt32 hModLt32 hSumLt32)
    (wpUntilCutStep_step
      (step_trueBlk_goto k seed fv (2 * acc + Nat.mod acc 256)
        (Nat.mod acc 256) hTr)
      (wpUntilCutStep_here 0
        ⟨2 * acc + Nat.mod acc 256, Nat.mod acc 256, Nat.mod acc 256,
         hSumLo, hSumHi, rfl⟩)))))))

private theorem step_falseBlk_s0 (k seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat)
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k))
    (hk256 : k + 1 < 256) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkStageState (3 * k + 3) 0 seed fv acc v11 v12) =
    .step (mkJoin8RawState (3 * k + 3) 1
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val (k + 1))))
        (.immediate (some (coreU32Val v12)))
        (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) := by
  let locs := mkStageLocals seed fv acc v11 v12
  dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
  rw [hFa]
  change (match evalRvalueBy MirTy.beq bodyOverflowCastJoin8.locals locs
        entryMemoryComp coreU8Ty (.use (coreU8Const (k + 1))) with
    | .error err => StepResult.fault err
    | .ok (val, lr, mr) =>
      match writePlaceBy MirTy.beq lr mr 11 coreU8Ty val with
      | .error err => StepResult.fault err
      | .ok (lw, mw) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 3 * k + 3, stmtIdx := 1,
                       locals := lw }]
          callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalRvalueBy_use_u8Const locs (k + 1) hk256]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u8]
  rfl

private theorem step_falseBlk_s1 (k seed : Nat) (fv : FlagVec8)
    (acc v12 : Nat)
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k))
    (hk256 : k + 1 < 256) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 3) 1
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc)))
          (.immediate (some (coreU8Val (k + 1))))
          (.immediate (some (coreU32Val v12)))
          (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) =
    .step (mkJoin8RawState (3 * k + 3) 2
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val (k + 1))))
        (.immediate (some (coreU32Val (k + 1))))
        (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) := by
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
  rw [hFa]
  change (match evalIntToIntCastComp (coreU8Val (k + 1)) coreU32Ty with
    | .error err => StepResult.fault err
    | .ok val =>
      match writePlaceBy MirTy.beq _ entryMemoryComp 12 coreU32Ty val with
      | .error err => StepResult.fault err
      | .ok (lw, mw) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 3 * k + 3, stmtIdx := 2,
                       locals := lw }]
          callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalIntToIntCastComp_u8_to_u32 hk256]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u32]
  rfl

private theorem step_falseBlk_s2 (k seed : Nat) (fv : FlagVec8) (acc : Nat)
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k))
    (hAcc : acc < 4294967296) (hk32 : k + 1 < 4294967296)
    (hSum : acc + (k + 1) < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 3) 2
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc)))
          (.immediate (some (coreU8Val (k + 1))))
          (.immediate (some (coreU32Val (k + 1))))
          (.immediate (some (.tuple [coreU32Val acc, .bool false]))))) =
    .step (mkJoin8RawState (3 * k + 3) 3
      (mkJoin8Locals (.immediate none) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val (k + 1))))
        (.immediate (some (coreU32Val (k + 1))))
        (.immediate (some (.tuple [coreU32Val (acc + (k + 1)), .bool false]))))) := by
  let locs := mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc)))
    (.immediate (some (coreU8Val (k + 1))))
    (.immediate (some (coreU32Val (k + 1))))
    (.immediate (some (.tuple [coreU32Val acc, .bool false])))
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
  rw [hFa]
  change (match (match evalBinOpComp .addWithOverflow (coreU32Val acc)
          (coreU32Val (k + 1)) with
        | .error err => Except.error err
        | .ok res => Except.ok (res, locs, entryMemoryComp)) with
      | .error err => StepResult.fault err
      | .ok (val, lr, mr) =>
        match writePlaceBy MirTy.beq lr mr 13 coreOvU32Ty val with
        | .error err => StepResult.fault err
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 3 * k + 3, stmtIdx := 3,
                         locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalBinOpComp_addWithOverflow_u32 hAcc hk32 hSum]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_ovU32]
  rfl

private theorem step_falseBlk_s3 (k seed : Nat) (fv : FlagVec8) (acc : Nat)
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k))
    (hAcc : acc < 4294967296) (hk32 : k + 1 < 4294967296)
    (hSum : acc + (k + 1) < 4294967296) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkJoin8RawState (3 * k + 3) 3
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate (some (coreU32Val acc)))
          (.immediate (some (coreU8Val (k + 1))))
          (.immediate (some (coreU32Val (k + 1))))
          (.immediate (some (.tuple [coreU32Val (acc + (k + 1)), .bool false]))))) =
    .step (mkStageState (3 * k + 3) 4 seed fv (acc + (k + 1)) (k + 1) (k + 1)) := by
  let locs := mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc)))
    (.immediate (some (coreU8Val (k + 1))))
    (.immediate (some (coreU32Val (k + 1))))
    (.immediate (some (.tuple [coreU32Val (acc + (k + 1)), .bool false])))
  dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState, mkStageState]
  rw [hFa]
  change (match (match evalBinOpComp .addUnchecked (coreU32Val acc)
          (coreU32Val (k + 1)) with
        | .error err => Except.error err
        | .ok res => Except.ok (res, locs, entryMemoryComp)) with
      | .error err => StepResult.fault err
      | .ok (val, lr, mr) =>
        match writePlaceBy MirTy.beq lr mr 10 coreU32Ty val with
        | .error err => StepResult.fault err
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 3 * k + 3, stmtIdx := 4,
                         locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
  rw [evalBinOpComp_addUnchecked_u32 hAcc hk32 hSum]
  dsimp only [writePlaceBy]
  rw [checkValBy_mirTyBeq_u32]
  rfl

private theorem step_falseBlk_goto (k seed : Nat) (fv : FlagVec8)
    (acc' m : Nat)
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k)) :
    evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
      (mkStageState (3 * k + 3) 4 seed fv acc' m m) =
    .step (mkStageState (3 * k + 4) 0 seed fv acc' m m) := by
  dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
  rw [hFa]
  rfl

private theorem stage_false_arm_wpUntilCut (k seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat)
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k))
    (hk256 : k + 1 < 256)
    (hLo : hullLo k ≤ acc) (hHi : acc ≤ hullHi k)
    (hBound : hullHi k + (k + 1) < 4294967296) :
    wpUntilCutStep
      (evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8)
      (HoldsAtOverflowNode ⟨3 * k + 4, hullLo k + (k + 1), hullHi k + (k + 1)⟩
        seed fv)
      7 (mkStageState (3 * k + 3) 0 seed fv acc v11 v12) := by
  have hSumHi : acc + (k + 1) ≤ hullHi k + (k + 1) :=
    Nat.add_le_add_right hHi (k + 1)
  have hSumLo : hullLo k + (k + 1) ≤ acc + (k + 1) :=
    Nat.add_le_add_right hLo (k + 1)
  have hSumLt32 : acc + (k + 1) < 4294967296 :=
    Nat.lt_of_le_of_lt hSumHi hBound
  have hAccLt32 : acc < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right acc (k + 1)) hSumLt32
  have hkLt32 : k + 1 < 4294967296 := Nat.lt_trans hk256 (by decide)
  exact
    wpUntilCutStep_step (step_falseBlk_s0 k seed fv acc v11 v12 hFa hk256)
    (wpUntilCutStep_step (step_falseBlk_s1 k seed fv acc v12 hFa hk256)
    (wpUntilCutStep_step
      (step_falseBlk_s2 k seed fv acc hFa hAccLt32 hkLt32 hSumLt32)
    (wpUntilCutStep_step
      (step_falseBlk_s3 k seed fv acc hFa hAccLt32 hkLt32 hSumLt32)
    (wpUntilCutStep_step
      (step_falseBlk_goto k seed fv (acc + (k + 1)) (k + 1) hFa)
      (wpUntilCutStep_here 2
        ⟨acc + (k + 1), k + 1, k + 1, hSumLo, hSumHi, rfl⟩)))))

private theorem prove_overflowCastStageCut (k seed : Nat) (fv : FlagVec8)
    (hNodeEq : mkOverflowHullNode (k + 1) =
      ⟨3 * k + 4, compNatMin (2 * hullLo k) (hullLo k + (k + 1)),
       compNatMax (2 * hullHi k + 255) (hullHi k + (k + 1))⟩)
    (hSw : ∀ acc v11 v12,
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkStageState (3 * k + 1) 0 seed fv acc v11 v12) =
      .step (mkStageState (if flagAt8 fv k then 3 * k + 2 else 3 * k + 3) 0
        seed fv acc v11 v12))
    (hTr : btOverflowCastJoin8.lookup (3 * k + 2) = some (mkStageTrueBlock k))
    (hFa : btOverflowCastJoin8.lookup (3 * k + 3) = some (mkStageFalseBlock k))
    (hk256 : k + 1 < 256)
    (hTrBound : 2 * hullHi k + 255 < 4294967296)
    (hFaBound : hullHi k + (k + 1) < 4294967296) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode k) (mkOverflowHullNode (k + 1)) seed fv 8 := by
  rw [hNodeEq]
  unfold mkOverflowHullNode
  refine seal_overflowCastStage_hull (flagAt8 fv k)
    (fun acc v11 v12 hLo hHi => ?_)
  have hStep0 := hSw acc v11 v12
  cases hb : flagAt8 fv k <;> rw [hb] at hStep0
  · exact wpUntilCutStep_step hStep0
      (stage_false_arm_wpUntilCut k seed fv acc v11 v12 hFa hk256
        hLo hHi hFaBound)
  · exact wpUntilCutStep_step hStep0
      (stage_true_arm_wpUntilCut k seed fv acc v11 v12 hTr
        hLo hHi hTrBound)

private theorem overflowCastStage0_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 0) (mkOverflowHullNode 1) seed fv 8 :=
  prove_overflowCastStageCut 0 seed fv rfl
    (fun _ _ _ => by
      have hSw0 : btOverflowCastJoin8.lookup 1 = some (mkStageSwitchBlock 0) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw0]
      cases fv with | mk b0 _ _ _ _ _ _ _ => cases b0 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage1_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 1) (mkOverflowHullNode 2) seed fv 8 :=
  prove_overflowCastStageCut 1 seed fv rfl
    (fun _ _ _ => by
      have hSw1 : btOverflowCastJoin8.lookup 4 = some (mkStageSwitchBlock 1) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw1]
      cases fv with | mk _ b1 _ _ _ _ _ _ => cases b1 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage2_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 2) (mkOverflowHullNode 3) seed fv 8 :=
  prove_overflowCastStageCut 2 seed fv rfl
    (fun _ _ _ => by
      have hSw2 : btOverflowCastJoin8.lookup 7 = some (mkStageSwitchBlock 2) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw2]
      cases fv with | mk _ _ b2 _ _ _ _ _ => cases b2 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage3_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 3) (mkOverflowHullNode 4) seed fv 8 :=
  prove_overflowCastStageCut 3 seed fv rfl
    (fun _ _ _ => by
      have hSw3 : btOverflowCastJoin8.lookup 10 = some (mkStageSwitchBlock 3) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw3]
      cases fv with | mk _ _ _ b3 _ _ _ _ => cases b3 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage4_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 4) (mkOverflowHullNode 5) seed fv 8 :=
  prove_overflowCastStageCut 4 seed fv rfl
    (fun _ _ _ => by
      have hSw4 : btOverflowCastJoin8.lookup 13 = some (mkStageSwitchBlock 4) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw4]
      cases fv with | mk _ _ _ _ b4 _ _ _ => cases b4 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage5_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 5) (mkOverflowHullNode 6) seed fv 8 :=
  prove_overflowCastStageCut 5 seed fv rfl
    (fun _ _ _ => by
      have hSw5 : btOverflowCastJoin8.lookup 16 = some (mkStageSwitchBlock 5) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw5]
      cases fv with | mk _ _ _ _ _ b5 _ _ => cases b5 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage6_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 6) (mkOverflowHullNode 7) seed fv 8 :=
  prove_overflowCastStageCut 6 seed fv rfl
    (fun _ _ _ => by
      have hSw6 : btOverflowCastJoin8.lookup 19 = some (mkStageSwitchBlock 6) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw6]
      cases fv with | mk _ _ _ _ _ _ b6 _ => cases b6 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

private theorem overflowCastStage7_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 7) (mkOverflowHullNode 8) seed fv 8 :=
  prove_overflowCastStageCut 7 seed fv rfl
    (fun _ _ _ => by
      have hSw7 : btOverflowCastJoin8.lookup 22 = some (mkStageSwitchBlock 7) :=
        rfl
      dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
      rw [hSw7]
      cases fv with | mk _ _ _ _ _ _ _ b7 => cases b7 <;> rfl)
    rfl rfl (nat_lt_of_ble_true rfl)
    (nat_lt_of_ble_true rfl) (nat_lt_of_ble_true rfl)

/-- Linear 8-stage composition across all `256` boolean paths (`fuel = 64`). -/
theorem overflowCastAll8Stages_cut (seed : Nat) (fv : FlagVec8) :
    OverflowCastStageCut bodyOverflowCastJoin8 btOverflowCastJoin8
      (mkOverflowHullNode 0) (mkOverflowHullNode 8) seed fv 64 :=
  overflowCastStageCut_compose (overflowCastStage0_cut seed fv)
  (overflowCastStageCut_compose (overflowCastStage1_cut seed fv)
  (overflowCastStageCut_compose (overflowCastStage2_cut seed fv)
  (overflowCastStageCut_compose (overflowCastStage3_cut seed fv)
  (overflowCastStageCut_compose (overflowCastStage4_cut seed fv)
  (overflowCastStageCut_compose (overflowCastStage5_cut seed fv)
  (overflowCastStageCut_compose (overflowCastStage6_cut seed fv)
    (overflowCastStage7_cut seed fv)))))))

private theorem join8_entry_wpUntilCut (seed : Nat) (fv : FlagVec8)
    (hSeed : seed < 256) :
    wpUntilCutStep
      (evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8)
      (HoldsAtOverflowNode (mkOverflowHullNode 0) seed fv)
      5 { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                       locals := initLocalsLoopComp bodyOverflowCastJoin8
                         (flagArgs8 (coreU8Val seed) fv) 0
                         bodyOverflowCastJoin8.locals }]
          callerMem := ⟨[]⟩, mem := entryMemoryComp } := by
  have hSeed32 : seed < 4294967296 :=
    Nat.lt_trans hSeed (nat_lt_of_ble_true rfl)
  have h1Lt32 : (1 : Nat) < 4294967296 := nat_lt_of_ble_true rfl
  have hSeed1Le : seed + 1 ≤ 256 := Nat.succ_le_of_lt hSeed
  have hSeed1Lt32 : seed + 1 < 4294967296 :=
    Nat.lt_of_le_of_lt hSeed1Le (nat_lt_of_ble_true rfl)
  have hSeed1Lo : 1 ≤ seed + 1 := Nat.le_add_left 1 seed
  have hEntry0 : btOverflowCastJoin8.lookup 0 = some join8EntryBlock := rfl
  have hEntrySt :
      ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                      locals := initLocalsLoopComp bodyOverflowCastJoin8
                        (flagArgs8 (coreU8Val seed) fv) 0
                        bodyOverflowCastJoin8.locals }]
         callerMem := ⟨[]⟩, mem := entryMemoryComp } : State) =
      mkJoin8RawState 0 0
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate none) (.immediate none)
          (.immediate none) (.immediate none)) := rfl
  rw [hEntrySt]
  have hS0 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkJoin8RawState 0 0
          (mkJoin8Locals (.immediate none) seed fv
            (.immediate none) (.immediate none)
            (.immediate none) (.immediate none))) =
      .step (mkJoin8RawState 0 1
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate none) (.immediate (some (coreU8Val seed)))
          (.immediate none) (.immediate none))) := by
    dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
    rw [hEntry0]
    change (match writePlaceBy MirTy.beq _ entryMemoryComp 11 coreU8Ty
          (coreU8Val seed) with
      | .error err => StepResult.fault err
      | .ok (lw, mw) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := lw }]
          callerMem := ⟨[]⟩, mem := mw } : State)) = _
    dsimp only [writePlaceBy]
    rw [checkValBy_mirTyBeq_u8]
    rfl
  have hS1 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkJoin8RawState 0 1
          (mkJoin8Locals (.immediate none) seed fv
            (.immediate none) (.immediate (some (coreU8Val seed)))
            (.immediate none) (.immediate none))) =
      .step (mkJoin8RawState 0 2
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate none) (.immediate (some (coreU8Val seed)))
          (.immediate (some (coreU32Val seed))) (.immediate none))) := by
    dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
    rw [hEntry0]
    change (match evalIntToIntCastComp (coreU8Val seed) coreU32Ty with
      | .error err => StepResult.fault err
      | .ok val =>
        match writePlaceBy MirTy.beq _ entryMemoryComp 12 coreU32Ty val with
        | .error err => StepResult.fault err
        | .ok (lw, mw) =>
          StepResult.step ({
            frames := [{ defId := 0, blockIdx := 0, stmtIdx := 2, locals := lw }]
            callerMem := ⟨[]⟩, mem := mw } : State)) = _
    rw [evalIntToIntCastComp_u8_to_u32 hSeed]
    dsimp only [writePlaceBy]
    rw [checkValBy_mirTyBeq_u32]
    rfl
  have hS2 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkJoin8RawState 0 2
          (mkJoin8Locals (.immediate none) seed fv
            (.immediate none) (.immediate (some (coreU8Val seed)))
            (.immediate (some (coreU32Val seed))) (.immediate none))) =
      .step (mkJoin8RawState 0 3
        (mkJoin8Locals (.immediate none) seed fv
          (.immediate none) (.immediate (some (coreU8Val seed)))
          (.immediate (some (coreU32Val seed)))
          (.immediate (some (.tuple [coreU32Val (seed + 1), .bool false]))))) := by
    let locs2 := mkJoin8Locals (.immediate none) seed fv
      (.immediate none) (.immediate (some (coreU8Val seed)))
      (.immediate (some (coreU32Val seed))) (.immediate none)
    dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState]
    rw [hEntry0]
    change (match (match evalPrimitiveOperandComp bodyOverflowCastJoin8.locals
            locs2 entryMemoryComp (coreU32Const 1) with
          | .error err => Except.error err
          | .ok (rVal, l2, m2) =>
            match evalBinOpComp .addWithOverflow (coreU32Val seed) rVal with
            | .error err => Except.error err
            | .ok res => Except.ok (res, l2, m2)) with
        | .error err => StepResult.fault err
        | .ok (val, lr, mr) =>
          match writePlaceBy MirTy.beq lr mr 13 coreOvU32Ty val with
          | .error err => StepResult.fault err
          | .ok (lw, mw) =>
            StepResult.step ({
              frames := [{ defId := 0, blockIdx := 0, stmtIdx := 3,
                           locals := lw }]
              callerMem := ⟨[]⟩, mem := mw } : State)) = _
    rw [evalPrimitiveOperandComp_u32Const locs2 1 h1Lt32]
    dsimp only
    rw [evalBinOpComp_addWithOverflow_u32 hSeed32 h1Lt32 hSeed1Lt32]
    dsimp only [writePlaceBy]
    rw [checkValBy_mirTyBeq_ovU32]
    rfl
  have hS3 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkJoin8RawState 0 3
          (mkJoin8Locals (.immediate none) seed fv
            (.immediate none) (.immediate (some (coreU8Val seed)))
            (.immediate (some (coreU32Val seed)))
            (.immediate (some (.tuple [coreU32Val (seed + 1), .bool false]))))) =
      .step (mkStageState 0 4 seed fv (seed + 1) seed seed) := by
    let locs3 := mkJoin8Locals (.immediate none) seed fv
      (.immediate none) (.immediate (some (coreU8Val seed)))
      (.immediate (some (coreU32Val seed)))
      (.immediate (some (.tuple [coreU32Val (seed + 1), .bool false])))
    dsimp only [evalMirStepBlockTreeBy, mkJoin8RawState, mkStageState]
    rw [hEntry0]
    change (match (match evalPrimitiveOperandComp bodyOverflowCastJoin8.locals
            locs3 entryMemoryComp (coreU32Const 1) with
          | .error err => Except.error err
          | .ok (rVal, l2, m2) =>
            match evalBinOpComp .addUnchecked (coreU32Val seed) rVal with
            | .error err => Except.error err
            | .ok res => Except.ok (res, l2, m2)) with
        | .error err => StepResult.fault err
        | .ok (val, lr, mr) =>
          match writePlaceBy MirTy.beq lr mr 10 coreU32Ty val with
          | .error err => StepResult.fault err
          | .ok (lw, mw) =>
            StepResult.step ({
              frames := [{ defId := 0, blockIdx := 0, stmtIdx := 4,
                           locals := lw }]
              callerMem := ⟨[]⟩, mem := mw } : State)) = _
    rw [evalPrimitiveOperandComp_u32Const locs3 1 h1Lt32]
    dsimp only
    rw [evalBinOpComp_addUnchecked_u32 hSeed32 h1Lt32 hSeed1Lt32]
    dsimp only [writePlaceBy]
    rw [checkValBy_mirTyBeq_u32]
    rfl
  have hS4 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkStageState 0 4 seed fv (seed + 1) seed seed) =
      .step (mkStageState 1 0 seed fv (seed + 1) seed seed) := by
    dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
    rw [hEntry0]
    rfl
  exact
    wpUntilCutStep_step hS0
    (wpUntilCutStep_step hS1
    (wpUntilCutStep_step hS2
    (wpUntilCutStep_step hS3
    (wpUntilCutStep_step hS4
      (wpUntilCutStep_here 0 ⟨seed + 1, seed, seed, hSeed1Lo, hSeed1Le, rfl⟩)))))

/-- Postcondition `37 ≤ acc ≤ 130561` with `overflow = false` for
`bodyOverflowCastJoin8`. -/
def OverflowCastJoin8Post (out : TerminalOut) : Prop :=
  ∃ acc : Nat,
    37 ≤ acc ∧ acc ≤ 130561 ∧
    out = .returned ⟨.tuple [coreU32Val acc, .bool false], ⟨[]⟩⟩

private theorem join8_exit_wpOutcomeState (seed : Nat) (fv : FlagVec8) :
    ∀ sc : State,
      HoldsAtOverflowNode (mkOverflowHullNode 8) seed fv sc →
      wpOutcomeState (bodyProg bodyOverflowCastJoin8)
        OverflowCastJoin8Post (fun _ => False) 2 sc := by
  intro sc hNode8
  have hNode8Eq : mkOverflowHullNode 8 = ⟨25, 37, 130561⟩ := rfl
  rw [hNode8Eq] at hNode8
  let ⟨acc, v11, v12, hLo37, hHi130561, hsc⟩ := hNode8
  subst hsc
  have hExit25 : btOverflowCastJoin8.lookup 25 = some join8ExitBlock := rfl
  let st1 : State :=
    mkJoin8RawState 25 1
      (mkJoin8Locals
        (.immediate (some (.tuple [coreU32Val acc, .bool false]))) seed fv
        (.immediate (some (coreU32Val acc)))
        (.immediate (some (coreU8Val v11)))
        (.immediate (some (coreU32Val v12)))
        (.immediate (some (.tuple [coreU32Val acc, .bool false]))))
  have hBtStep1 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        (mkStageState 25 0 seed fv acc v11 v12) = .step st1 := by
    dsimp only [evalMirStepBlockTreeBy, mkStageState, mkJoin8RawState]
    rw [hExit25]
    change (match writePlaceBy MirTy.beq _ entryMemoryComp 0 coreOvU32Ty
          (.tuple [coreU32Val acc, .bool false]) with
      | .error err => StepResult.fault err
      | .ok (lw, mw) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 25, stmtIdx := 1, locals := lw }]
          callerMem := ⟨[]⟩, mem := mw } : State)) = _
    dsimp only [writePlaceBy]
    rw [checkValBy_mirTyBeq_ovU32]
    rfl
  have hBtStep2 :
      evalMirStepBlockTreeBy MirTy.beq btOverflowCastJoin8 bodyOverflowCastJoin8
        st1 = .done (.returned ⟨.tuple [coreU32Val acc, .bool false], ⟨[]⟩⟩) := by
    dsimp only [evalMirStepBlockTreeBy, st1, mkJoin8RawState]
    rw [hExit25]
    rfl
  have hMirStep1 :
      evalStep (bodyProg bodyOverflowCastJoin8) 0
        (mkStageState 25 0 seed fv acc v11 v12) = .step st1 := by
    rw [← evalMirStepBlockTreeBy_eq_evalStep MirTy.beq (fun _ _ => rfl)
      valid_btOverflowCastJoin8]
    exact hBtStep1
  have hMirStep2 :
      evalStep (bodyProg bodyOverflowCastJoin8) 0 st1 =
        .done (.returned ⟨.tuple [coreU32Val acc, .bool false], ⟨[]⟩⟩) := by
    rw [← evalMirStepBlockTreeBy_eq_evalStep MirTy.beq (fun _ _ => rfl)
      valid_btOverflowCastJoin8]
    exact hBtStep2
  apply wpOutcomeState_of_execOutcomeState
  change (match evalStep (bodyProg bodyOverflowCastJoin8) 0
        (mkStageState 25 0 seed fv acc v11 v12) with
      | .step s1 =>
        match evalStep (bodyProg bodyOverflowCastJoin8) 0 s1 with
        | .step _ => False
        | .done out => OverflowCastJoin8Post out
        | .fault _ => False
      | .done out => OverflowCastJoin8Post out
      | .fault _ => False)
  rw [hMirStep1]
  dsimp only
  rw [hMirStep2]
  exact ⟨acc, hLo37, hHi130561, rfl⟩

/-- End-to-end `wpProg` proof across all `256` boolean paths and all `256`
`seed : u8` inputs (`65,536` runs) in `8` linear cutpoint stages (`fuel = 71`).
-/
theorem bodyOverflowCastJoin8_wpProg (seed : Nat) (fv : FlagVec8)
    (hSeed : seed < 256) :
    wpProg (bodyProg bodyOverflowCastJoin8) 71
      { args := flagArgs8 (coreU8Val seed) fv } OverflowCastJoin8Post := by
  have hInit :
      initState (bodyProg bodyOverflowCastJoin8)
        { args := flagArgs8 (coreU8Val seed) fv } =
      .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                         locals := initLocalsLoopComp bodyOverflowCastJoin8
                           (flagArgs8 (coreU8Val seed) fv) 0
                           bodyOverflowCastJoin8.locals }]
            callerMem := ⟨[]⟩, mem := entryMemoryComp } := by
    rw [← initStateBy_eq MirTy.beq (fun _ _ => rfl)]
    dsimp only [initStateBy, bodyProg, compGetElem?, List.foldr,
      storageAnnotationsInBoundsComp, discriminantTypesValidBy,
      castTypesValidBy, isSupportedScalarOrUnitTyComp, isOverflowPairTyComp,
      intWidthBeqComp, boolBeqComp, MirTy.beq]
    change (if !(checkValBy MirTy.beq (coreU8Val seed) coreU8Ty && true) then
        Except.error FaultKind.unsupported
      else Except.ok _) = Except.ok _
    rw [checkValBy_mirTyBeq_u8]
    rfl
  unfold wpProg
  rw [hInit]
  exact wpOutcomeState_of_wpUntilCutBlockTree (f₁ := 5) (f₂ := 66)
    (fun _ _ => rfl) valid_btOverflowCastJoin8
    (join8_entry_wpUntilCut seed fv hSeed)
    (fun sc hsc =>
      wpOutcomeState_of_overflowCastStageCut (fChain := 64) (fExit := 2)
        valid_btOverflowCastJoin8 hsc
        (overflowCastAll8Stages_cut seed fv)
        (join8_exit_wpOutcomeState seed fv))

/-- End-to-end `SatisfiesPost`, `¬ Diverges`, and bounded `Behavior` witness for
`bodyOverflowCastJoin8` across all `65,536` `(seed, fv)` inputs. -/
theorem bodyOverflowCastJoin8_satisfiesPost (seed : Nat) (fv : FlagVec8)
    (hSeed : seed < 256) :
    SatisfiesPost (bodyProg bodyOverflowCastJoin8)
      { args := flagArgs8 (coreU8Val seed) fv } OverflowCastJoin8Post ∧
    ¬ Diverges (bodyProg bodyOverflowCastJoin8)
      { args := flagArgs8 (coreU8Val seed) fv } ∧
    ∃ out : TerminalOut,
      Behavior (bodyProg bodyOverflowCastJoin8)
        { args := flagArgs8 (coreU8Val seed) fv } out ∧
      OverflowCastJoin8Post out :=
  wellFormed_and_spec_of_wp_base (bodyProg bodyOverflowCastJoin8)
    { args := flagArgs8 (coreU8Val seed) fv } 71 OverflowCastJoin8Post
    (bodyOverflowCastJoin8_wpProg seed fv hSeed)

/-- Tight lower-endpoint witness: `seed = 0` with all `8` flags `false`
evaluates to `(37, false)`. -/
theorem bodyOverflowCastJoin8_endpoint_min_37 :
    PositiveCanaryClaim (bodyProg bodyOverflowCastJoin8)
      { args := flagArgs8 (coreU8Val 0)
          ⟨false, false, false, false, false, false, false, false⟩ }
      (.tuple [coreU32Val 37, .bool false]) :=
  positiveCanary_of_exec (fuel := 71) rfl

/-- Tight upper-endpoint witness: `seed = 254` with all `8` flags `true`
evaluates to `(127327, false)`. -/
theorem bodyOverflowCastJoin8_endpoint_max_127327 :
    PositiveCanaryClaim (bodyProg bodyOverflowCastJoin8)
      { args := flagArgs8 (coreU8Val 254)
          ⟨true, true, true, true, true, true, true, true⟩ }
      (.tuple [coreU32Val 127327, .bool false]) :=
  positiveCanary_of_exec (fuel := 71) rfl

/-- Negative unchecked-overflow canary: `addUnchecked(u32::MAX, 1)` faults with
`FaultKind.undefined` and refutes `WellFormed`. -/
def bodyUncheckedOverflowFault : Body :=
  { identity := "anneal_core::unchecked_overflow_fault"
    isUnsafe := false
    locals := [coreU32Ty]
    argumentCount := 0
    basicBlocks := [{
      statements := [
        .assign (coreLocalPlace 0)
          (.binaryOp .addUnchecked (coreU32Const 4294967295) (coreU32Const 1))
      ]
      terminator := .return_
      cleanup := false
    }] }

/-- Negative canary for `bodyUncheckedOverflowFault` (`FaultKind.undefined` vs
`FaultKind.unsupported`). -/
theorem bodyUncheckedOverflowFault_negative_canary :
    NegativeCanaryClaim (bodyProg bodyUncheckedOverflowFault)
      { args := [] } .undefined .unsupported :=
  negativeCanary_of_execFault (fuel := 1) (by intro h; cases h) rfl

/-! ## Canary Suite 2: Two-Pass Conjunctive WP (`bodyTwoPassAdd`) -/

/-- Single-block `u32` addition body exercising `wpProg_of_wlp_and_safety`. -/
def bodyTwoPassAdd : Body :=
  { identity := "anneal_core::two_pass_add"
    isUnsafe := false
    locals := [coreU32Ty, coreU32Ty, coreU32Ty]
    argumentCount := 2
    basicBlocks := [{
      statements := [
        .assign (coreLocalPlace 0)
          (.binaryOp .add (.copy (coreLocalPlace 1)) (.copy (coreLocalPlace 2)))
      ]
      terminator := .return_
      cleanup := false
    }] }

/-- Concrete two-pass verification of `bodyTwoPassAdd (19, 23) = 42` combining
independent Pass-1 `wpProg` safety and Pass-2 `wlpProg` functional specs via
`wpProg_of_wlp_and_safety`. -/
theorem bodyTwoPassAdd_19_23_canary :
    PositiveCanaryClaim (bodyProg bodyTwoPassAdd)
      { args := [coreU32Val 19, coreU32Val 23] } (coreU32Val 42) := by
  have hSafe : wpProg (bodyProg bodyTwoPassAdd) 2
      { args := [coreU32Val 19, coreU32Val 23] } (fun _ => True) :=
    wpProg_of_execProg True.intro
  have hWlp : wlpProg (bodyProg bodyTwoPassAdd) 2
      { args := [coreU32Val 19, coreU32Val 23] }
      (fun out => out = .returned ⟨coreU32Val 42, ⟨[]⟩⟩) := by
    change wlpOutcomeState (bodyProg bodyTwoPassAdd)
      (fun out => out = .returned ⟨coreU32Val 42, ⟨[]⟩⟩) (fun _ => True) 2 _
    intro c₁ hc₁
    subst hc₁
    intro c₂ hc₂
    subst hc₂
    rfl
  exact positiveCanary_of_wp (wpProg_of_wlp_and_safety hSafe hWlp)

/-! ## Canary Suite 3: Cleanup-Return Guard & Shared `O(K)` `DropSpineCut` -/

/-- `cleanup = true` block ending in `return_` (forbidden by MIR cleanup rules).
-/
def bodyCleanupFaultBlock : Body :=
  { identity := "anneal_core::cleanup_return_fault"
    isUnsafe := false
    locals := [coreU32Ty]
    argumentCount := 0
    basicBlocks := [{
      statements := []
      terminator := .return_
      cleanup := true
    }] }

/-- Negative canary: `bodyCleanupFaultBlock` faults with `FaultKind.unsupported`
and never terminates normally. -/
theorem bodyCleanupFaultBlock_rejects_done :
    wpFaultProg (bodyProg bodyCleanupFaultBlock) 1 { args := [] } .unsupported ∧
    ReachesResult (bodyProg bodyCleanupFaultBlock) { args := [] }
      (.fault .unsupported) ∧
    ∀ out : TerminalOut,
      ¬ ReachesResult (bodyProg bodyCleanupFaultBlock) { args := [] }
        (.done out) :=
  cleanup_block_return_faults_unsupported bodyCleanupFaultBlock []
    { statements := [], terminator := .return_, cleanup := true }
    rfl rfl rfl rfl rfl rfl

private def mkGuardScopeBlock (scopeLocal guardLocal retCode : Nat)
    (earlyBlk contBlk : BasicBlockId) : BasicBlock :=
  { statements := [
      .storageLive scopeLocal,
      .assign (coreLocalPlace 0) (.use (coreU32Const retCode))
    ]
    terminator := .switchInt (.copy (coreLocalPlace guardLocal))
      { branches := [(1, earlyBlk)], otherwise := contBlk }
    cleanup := false }

private def mkConstRetJoinBlock (retCode : Nat)
    (cleanBlk : BasicBlockId) : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 0) (.use (coreU32Const retCode))
    ]
    terminator := .goto cleanBlk
    cleanup := false }

private def mkStorageDeadGotoBlock (dropIdx nextBlk : Nat) : BasicBlock :=
  { statements := [.storageDead dropIdx]
    terminator := .goto nextBlk
    cleanup := false }

/-- `11`-block nested-guard MIR `Body` sharing a 5-block LIFO `StorageDead`
cleanup spine (`bb6 -> bb7 -> bb8 -> bb9 -> bb10`). -/
def bodyCleanupChain4 : Body :=
  { identity := "anneal_core::cleanup_chain_4"
    isUnsafe := false
    argumentCount := 4
    locals := [coreU32Ty, .bool, .bool, .bool, .bool,
               coreU32Ty, coreU32Ty, coreU32Ty, coreU32Ty]
    basicBlocks := [
      mkConstRetJoinBlock 0 1,
      mkGuardScopeBlock 5 1 101 9 2,
      mkGuardScopeBlock 6 2 102 8 3,
      mkGuardScopeBlock 7 3 103 7 4,
      mkGuardScopeBlock 8 4 104 6 5,
      mkConstRetJoinBlock 200 6,
      mkStorageDeadGotoBlock 8 7,
      mkStorageDeadGotoBlock 7 8,
      mkStorageDeadGotoBlock 6 9,
      mkStorageDeadGotoBlock 5 10,
      { statements := [], terminator := .return_, cleanup := false }
    ] }

/-- Balanced `BlockTree` for `bodyCleanupChain4`. -/
def btCleanupChain4 : BlockTree BasicBlock :=
  BlockTree.ofList bodyCleanupChain4.basicBlocks

/-- Functional specification of `bodyCleanupChain4`. -/
def cleanupChain4Spec (g0 g1 g2 g3 : Bool) : Nat :=
  if g0 then 101
  else if g1 then 102
  else if g2 then 103
  else if g3 then 104
  else 200

/-- Verifies all `16` boolean paths of `bodyCleanupChain4` by proving the shared
`bb6..bb10` cleanup spine once via `@[irreducible] DropSpineCut`. -/
theorem bodyCleanupChain4_single_cutpoint_wpProg (g0 g1 g2 g3 : Bool) :
    wpProg (bodyProg bodyCleanupChain4) 30
      { args := [.bool g0, .bool g1, .bool g2, .bool g3] }
      (twoTrackPost
        (fun out => out.ret = coreU32Val (cleanupChain4Spec g0 g1 g2 g3))
        (fun _ => False)) := by
  let rVal := coreU32Val (cleanupChain4Spec g0 g1 g2 g3)
  have hValid := valid_blockTree_ofList bodyCleanupChain4.basicBlocks
  have cut10 : DropSpineCut bodyCleanupChain4 btCleanupChain4 10 5 9 rVal 1 :=
    dropSpineCut_base_ret btCleanupChain4 rfl
  have cut9 : DropSpineCut bodyCleanupChain4 btCleanupChain4 9 6 9 rVal 3 :=
    dropSpineCut_prepend_storageDead btCleanupChain4 (by decide) (by decide)
      rfl cut10
  have cut8 : DropSpineCut bodyCleanupChain4 btCleanupChain4 8 7 9 rVal 5 :=
    dropSpineCut_prepend_storageDead btCleanupChain4 (by decide) (by decide)
      rfl cut9
  have cut7 : DropSpineCut bodyCleanupChain4 btCleanupChain4 7 8 9 rVal 7 :=
    dropSpineCut_prepend_storageDead btCleanupChain4 (by decide) (by decide)
      rfl cut8
  have cut6 : DropSpineCut bodyCleanupChain4 btCleanupChain4 6 9 9 rVal 9 :=
    dropSpineCut_prepend_storageDead btCleanupChain4 (by decide) (by decide)
      rfl cut7
  have hInit := initState_eq_ok (p := bodyProg bodyCleanupChain4)
    (args := [.bool g0, .bool g1, .bool g2, .bool g3]) rfl rfl rfl
  unfold wpProg
  rw [hInit]
  cases g0 with
  | true =>
    have hPre : MirStageCut (bodyProg bodyCleanupChain4) 5
        (mkState 0 0 (initLocalsLoop bodyCleanupChain4
          [.bool true, .bool g1, .bool g2, .bool g3] 0
          bodyCleanupChain4.locals))
        { frames := [{ defId := 0, blockIdx := 9, stmtIdx := 0,
                       locals := [.immediate (some (coreU32Val 101)),
                         .immediate (some (.bool true)),
                         .immediate (some (.bool g1)),
                         .immediate (some (.bool g2)),
                         .immediate (some (.bool g3)),
                         .immediate none, .dead, .dead, .dead] }]
          callerMem := ⟨[]⟩, mem := entryMemory } :=
      StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
        (StepStageCut.step rfl (StepStageCut.step rfl
          (StepStageCut.refl _ 0 _)))))
    exact wpOutcomeState_fuel_mono (show 5 + 3 ≤ 30 from by decide)
      (wpOutcomeState_of_mirStageCut hPre
        (wpTwoTrack_of_dropSpineCut hValid cut9
          ⟨_, ⟨[]⟩, entryMemory, rfl, by decide, Nat.le_refl 9, rfl, rfl,
           ⟨rfl, rfl, rfl, True.intro⟩⟩))
  | false =>
    cases g1 with
    | true =>
      have hPre : MirStageCut (bodyProg bodyCleanupChain4) 8
          (mkState 0 0 (initLocalsLoop bodyCleanupChain4
            [.bool false, .bool true, .bool g2, .bool g3] 0
            bodyCleanupChain4.locals))
          { frames := [{ defId := 0, blockIdx := 8, stmtIdx := 0,
                         locals := [.immediate (some (coreU32Val 102)),
                           .immediate (some (.bool false)),
                           .immediate (some (.bool true)),
                           .immediate (some (.bool g2)),
                           .immediate (some (.bool g3)),
                           .immediate none, .immediate none, .dead, .dead] }]
            callerMem := ⟨[]⟩, mem := entryMemory } :=
        StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
          (StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
            (StepStageCut.step rfl (StepStageCut.step rfl
              (StepStageCut.refl _ 0 _))))))))
      exact wpOutcomeState_fuel_mono (show 8 + 5 ≤ 30 from by decide)
        (wpOutcomeState_of_mirStageCut hPre
          (wpTwoTrack_of_dropSpineCut hValid cut8
            ⟨_, ⟨[]⟩, entryMemory, rfl, by decide, Nat.le_refl 9, rfl, rfl,
             ⟨rfl, rfl, True.intro⟩⟩))
    | false =>
      cases g2 with
      | true =>
        have hPre : MirStageCut (bodyProg bodyCleanupChain4) 11
            (mkState 0 0 (initLocalsLoop bodyCleanupChain4
              [.bool false, .bool false, .bool true, .bool g3] 0
              bodyCleanupChain4.locals))
            { frames := [{ defId := 0, blockIdx := 7, stmtIdx := 0,
                           locals := [.immediate (some (coreU32Val 103)),
                             .immediate (some (.bool false)),
                             .immediate (some (.bool false)),
                             .immediate (some (.bool true)),
                             .immediate (some (.bool g3)),
                             .immediate none, .immediate none,
                             .immediate none, .dead] }]
              callerMem := ⟨[]⟩, mem := entryMemory } :=
          StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
            (StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
              (StepStageCut.step rfl (StepStageCut.step rfl
                (StepStageCut.step rfl (StepStageCut.step rfl
                  (StepStageCut.step rfl (StepStageCut.refl _ 0 _)))))))))))
        exact wpOutcomeState_fuel_mono (show 11 + 7 ≤ 30 from by decide)
          (wpOutcomeState_of_mirStageCut hPre
            (wpTwoTrack_of_dropSpineCut hValid cut7
              ⟨_, ⟨[]⟩, entryMemory, rfl, by decide, Nat.le_refl 9, rfl, rfl,
               ⟨rfl, True.intro⟩⟩))
      | false =>
        cases g3 with
        | true =>
          have hPre : MirStageCut (bodyProg bodyCleanupChain4) 14
              (mkState 0 0 (initLocalsLoop bodyCleanupChain4
                [.bool false, .bool false, .bool false, .bool true] 0
                bodyCleanupChain4.locals))
              { frames := [{ defId := 0, blockIdx := 6, stmtIdx := 0,
                             locals := [.immediate (some (coreU32Val 104)),
                               .immediate (some (.bool false)),
                               .immediate (some (.bool false)),
                               .immediate (some (.bool false)),
                               .immediate (some (.bool true)),
                               .immediate none, .immediate none,
                               .immediate none, .immediate none] }]
                callerMem := ⟨[]⟩, mem := entryMemory } :=
            StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
              (StepStageCut.step rfl (StepStageCut.step rfl
                (StepStageCut.step rfl (StepStageCut.step rfl
                  (StepStageCut.step rfl (StepStageCut.step rfl
                    (StepStageCut.step rfl (StepStageCut.step rfl
                      (StepStageCut.step rfl (StepStageCut.step rfl
                        (StepStageCut.step rfl
                          (StepStageCut.refl _ 0 _))))))))))))))
          exact wpOutcomeState_fuel_mono (show 14 + 9 ≤ 30 from by decide)
            (wpOutcomeState_of_mirStageCut hPre
              (wpTwoTrack_of_dropSpineCut hValid cut6
                ⟨_, ⟨[]⟩, entryMemory, rfl, Nat.le_refl 9, Nat.le_refl 9,
                 rfl, rfl, True.intro⟩))
        | false =>
          have hPre : MirStageCut (bodyProg bodyCleanupChain4) 16
              (mkState 0 0 (initLocalsLoop bodyCleanupChain4
                [.bool false, .bool false, .bool false, .bool false] 0
                bodyCleanupChain4.locals))
              { frames := [{ defId := 0, blockIdx := 6, stmtIdx := 0,
                             locals := [.immediate (some (coreU32Val 200)),
                               .immediate (some (.bool false)),
                               .immediate (some (.bool false)),
                               .immediate (some (.bool false)),
                               .immediate (some (.bool false)),
                               .immediate none, .immediate none,
                               .immediate none, .immediate none] }]
                callerMem := ⟨[]⟩, mem := entryMemory } :=
            StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
              (StepStageCut.step rfl (StepStageCut.step rfl
                (StepStageCut.step rfl (StepStageCut.step rfl
                  (StepStageCut.step rfl (StepStageCut.step rfl
                    (StepStageCut.step rfl (StepStageCut.step rfl
                      (StepStageCut.step rfl (StepStageCut.step rfl
                        (StepStageCut.step rfl (StepStageCut.step rfl
                          (StepStageCut.step rfl
                            (StepStageCut.refl _ 0 _))))))))))))))))
          exact wpOutcomeState_fuel_mono (show 16 + 9 ≤ 30 from by decide)
            (wpOutcomeState_of_mirStageCut hPre
              (wpTwoTrack_of_dropSpineCut hValid cut6
                ⟨_, ⟨[]⟩, entryMemory, rfl, Nat.le_refl 9, Nat.le_refl 9,
                 rfl, rfl, True.intro⟩))

/-! ## Canary Suite 4: Bounded Early-Return (`?`) Loop Rule -/

/-- 6-block MIR loop with a mid-loop `?`-style early-return guard (`bb1 -> bb2`)
and a normal exit (`bb3 -> bb5`). -/
def bodyLoopEarlyRetClean : Body :=
  { identity := "anneal_core::loop_early_ret_clean"
    isUnsafe := false
    argumentCount := 2
    locals := [coreU32Ty, coreU32Ty, .bool, coreU32Ty, coreU32Ty, .bool]
    basicBlocks := [
      { statements := [
          .storageLive 4,
          .assign (coreLocalPlace 4) (.use (coreU32Const 0)),
          .storageLive 3,
          .assign (coreLocalPlace 3) (.use (coreU32Const 7))
        ]
        terminator := .goto 1
        cleanup := false },
      { statements := []
        terminator := .switchInt (.copy (coreLocalPlace 2))
          { branches := [(1, 2)], otherwise := 3 }
        cleanup := false },
      { statements := [
          .assign (coreLocalPlace 0) (.use (.copy (coreLocalPlace 1))),
          .storageDead 3,
          .storageDead 4
        ]
        terminator := .return_
        cleanup := false },
      { statements := [
          .storageLive 5,
          .assign (coreLocalPlace 5)
            (.binaryOp .lt (.copy (coreLocalPlace 4)) (coreU32Const 1))
        ]
        terminator := .switchInt (.copy (coreLocalPlace 5))
          { branches := [(1, 4)], otherwise := 5 }
        cleanup := false },
      { statements := [
          .storageDead 5,
          .assign (coreLocalPlace 4)
            (.binaryOp .add (.copy (coreLocalPlace 4)) (coreU32Const 1))
        ]
        terminator := .goto 1
        cleanup := false },
      { statements := [
          .storageDead 5,
          .assign (coreLocalPlace 0)
            (.binaryOp .add (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 3))),
          .storageDead 3,
          .storageDead 4
        ]
        terminator := .return_
        cleanup := false }
    ] }

/-- Buggy early-return loop variant omitting `_0` initialization on the early
exit (`bb2`), which must fault with `FaultKind.undefined`. -/
def bodyLoopEarlyRetUninitRet : Body :=
  { identity := "anneal_core::loop_early_ret_uninit_ret"
    isUnsafe := false
    argumentCount := 2
    locals := [coreU32Ty, coreU32Ty, .bool, coreU32Ty, coreU32Ty, .bool]
    basicBlocks := [
      { statements := [
          .storageLive 4,
          .assign (coreLocalPlace 4) (.use (coreU32Const 0)),
          .storageLive 3,
          .assign (coreLocalPlace 3) (.use (coreU32Const 7))
        ]
        terminator := .goto 1
        cleanup := false },
      { statements := []
        terminator := .switchInt (.copy (coreLocalPlace 2))
          { branches := [(1, 2)], otherwise := 3 }
        cleanup := false },
      { statements := [
          .storageDead 3,
          .storageDead 4
        ]
        terminator := .return_
        cleanup := false },
      { statements := [
          .storageLive 5,
          .assign (coreLocalPlace 5)
            (.binaryOp .lt (.copy (coreLocalPlace 4)) (coreU32Const 1))
        ]
        terminator := .switchInt (.copy (coreLocalPlace 5))
          { branches := [(1, 4)], otherwise := 5 }
        cleanup := false },
      { statements := [
          .storageDead 5,
          .assign (coreLocalPlace 4)
            (.binaryOp .add (.copy (coreLocalPlace 4)) (coreU32Const 1))
        ]
        terminator := .goto 1
        cleanup := false },
      { statements := [
          .storageDead 5,
          .assign (coreLocalPlace 0)
            (.binaryOp .add (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 3))),
          .storageDead 3,
          .storageDead 4
        ]
        terminator := .return_
        cleanup := false }
    ] }

/-- Verifies `bodyLoopEarlyRetClean` across both `earlyFlag = true` (`ret = 10`)
and `earlyFlag = false` (`ret = 17`) via `wpIterWithRetGuard_of_step` and
`wpOutcomeState_loop_early_return_sound`. -/
theorem bodyLoopEarlyRetClean_canary (earlyFlag : Bool) :
    let exp := if earlyFlag then 10 else 17
    wpProg (bodyProg bodyLoopEarlyRetClean) 24
      { args := [coreU32Val 10, .bool earlyFlag] }
      (twoTrackPost (fun out => out = ⟨coreU32Val exp, ⟨[]⟩⟩)
        (fun _ => False)) := by
  have hInit := initState_eq_ok (p := bodyProg bodyLoopEarlyRetClean)
    (args := [coreU32Val 10, .bool earlyFlag]) rfl rfl rfl
  unfold wpProg
  rw [hInit]
  let lsLoop (c : Nat) : List LocalSlot :=
    [.immediate none, .immediate (some (coreU32Val 10)),
     .immediate (some (.bool earlyFlag)), .immediate (some (coreU32Val 7)),
     .immediate (some (coreU32Val c)), .dead]
  have hHead : MirStageCut (bodyProg bodyLoopEarlyRetClean) 5
      (mkState 0 0 (initLocalsLoop bodyLoopEarlyRetClean
        [coreU32Val 10, .bool earlyFlag] 0 bodyLoopEarlyRetClean.locals))
      (mkState 1 0 (lsLoop 0)) :=
    StepStageCut.step rfl (StepStageCut.step rfl (StepStageCut.step rfl
      (StepStageCut.step rfl (StepStageCut.step rfl
        (StepStageCut.refl _ 0 _)))))
  cases earlyFlag with
  | true =>
    let loopInv : Nat → State → Prop := fun m st =>
      m = 2 ∧ st = mkState 1 0 (lsLoop 0)
    have hLoop : wpIterWithRetGuard (bodyProg bodyLoopEarlyRetClean)
        (fun st => ∃ m : Nat, loopInv m st)
        (fun st => st = mkState 2 0 (lsLoop 0))
        (fun _ => False) 7 2 (mkState 1 0 (lsLoop 0)) :=
      wpIterWithRetGuard_of_step
        (fun _ h0 => False.elim (by cases h0.1))
        (fun k st hk => by
          cases k with
          | zero => exact False.elim (by cases hk.1)
          | succ k2 =>
            cases k2 with
            | succ _ => exact False.elim (by cases hk.1)
            | zero =>
              have hEq : st = mkState 1 0 (lsLoop 0) := hk.2
              subst hEq
              exact .inr (.inr
                (wpUntilCutStep_step rfl
                  (wpUntilCutStep_here 6 (.inr (.inr rfl))))))
        ⟨rfl, rfl⟩
    have hBody :
        wpOutcomeState (bodyProg bodyLoopEarlyRetClean)
          (twoTrackPost (fun out => out = ⟨coreU32Val 10, ⟨[]⟩⟩)
            (fun _ => False))
          (fun _ => False)
          (2 * 7 + compNatMax 5 4)
          (mkState 1 0 (lsLoop 0)) :=
      wpOutcomeState_loop_early_return_sound
        (fuelNormal := 5) (fuelEarly := 4) hLoop
        (fun _ hf => False.elim hf)
        (fun st hst => by
          subst hst
          exact wpOutcomeState_of_execOutcomeState rfl)
    exact wpOutcomeState_fuel_mono
      (show 5 + (2 * 7 + compNatMax 5 4) ≤ 24 from by decide)
      (wpOutcomeState_of_mirStageCut hHead hBody)
  | false =>
    let lsCond1False : List LocalSlot :=
      [.immediate none, .immediate (some (coreU32Val 10)),
       .immediate (some (.bool false)), .immediate (some (coreU32Val 7)),
       .immediate (some (coreU32Val 1)), .immediate (some (.bool false))]
    let loopInv : Nat → State → Prop := fun m st =>
      match m with
      | 2 => st = mkState 1 0 (lsLoop 0)
      | 1 => st = mkState 1 0 (lsLoop 1)
      | _ => False
    have hLoop : wpIterWithRetGuard (bodyProg bodyLoopEarlyRetClean)
        (fun st => ∃ m : Nat, loopInv m st) (fun _ => False)
        (fun st => st = mkState 5 0 lsCond1False)
        7 2 (mkState 1 0 (lsLoop 0)) :=
      wpIterWithRetGuard_of_step (inv := loopInv)
        (fun _ h0 => False.elim h0)
        (fun k st hk => by
          cases k with
          | zero =>
            subst hk
            exact .inr (.inr
              (wpUntilCutStep_step rfl (wpUntilCutStep_step rfl
              (wpUntilCutStep_step rfl (wpUntilCutStep_step rfl
                (wpUntilCutStep_here 3 (.inr (.inl rfl))))))))
          | succ k2 =>
            cases k2 with
            | succ _ => exact False.elim hk
            | zero =>
              subst hk
              exact .inr (.inr
                (wpUntilCutStep_step rfl (wpUntilCutStep_step rfl
                (wpUntilCutStep_step rfl (wpUntilCutStep_step rfl
                (wpUntilCutStep_step rfl (wpUntilCutStep_step rfl
                (wpUntilCutStep_step rfl
                  (wpUntilCutStep_here 0 (.inl rfl)))))))))))
        rfl
    have hBody :
        wpOutcomeState (bodyProg bodyLoopEarlyRetClean)
          (twoTrackPost (fun out => out = ⟨coreU32Val 17, ⟨[]⟩⟩)
            (fun _ => False))
          (fun _ => False)
          (2 * 7 + compNatMax 5 4)
          (mkState 1 0 (lsLoop 0)) :=
      wpOutcomeState_loop_early_return_sound
        (fuelNormal := 5) (fuelEarly := 4) hLoop
        (fun st hst => by
          subst hst
          exact wpOutcomeState_of_execOutcomeState rfl)
        (fun _ hf => False.elim hf)
    exact wpOutcomeState_fuel_mono
      (show 5 + (2 * 7 + compNatMax 5 4) ≤ 24 from by decide)
      (wpOutcomeState_of_mirStageCut hHead hBody)

/-- Negative canary: omitting `_0` initialization on the early-return exit in
`bodyLoopEarlyRetUninitRet` faults with `FaultKind.undefined`. -/
theorem bodyLoopEarlyRetUninitRet_negative_canary :
    NegativeCanaryClaim (bodyProg bodyLoopEarlyRetUninitRet)
      { args := [coreU32Val 10, .bool true] } .undefined .unsupported :=
  negativeCanary_of_execFault (fuel := 9) (by intro h; cases h) rfl

/-! ## Canary Suite 5: `ByteHeaplet` Separation Algebra & `MemDisjointFrame` -/

/-- Positive and negative `ByteHeaplet` separation-logic canary: distinct byte
addresses compose and commute under `sepConj`, while identical addresses
conflict. -/
theorem byteHeaplet_disjoint_and_conflict_canary :
    (∃ h : ByteHeaplet,
      sepConj byteHeapletPCM
        (bytePointsTo ⟨2, 4⟩ (.init 0xaa none))
        (bytePointsTo ⟨2, 0⟩ (.init 0x55 none)) h) ∧
    (∀ h : ByteHeaplet,
      ¬ sepConj byteHeapletPCM
        (bytePointsTo ⟨2, 0⟩ (.init 0x55 none))
        (bytePointsTo ⟨2, 0⟩ (.uninit)) h) := by
  have hNe : (⟨2, 0⟩ : ByteAddr) ≠ ⟨2, 4⟩ := fun he => by cases he
  let ⟨h₀, hConj₀⟩ :=
    bytePointsTo_disjoint_of_ne (v₁ := .init 0x55 none) (v₂ := .init 0xaa none)
      hNe
  exact ⟨⟨h₀, (sepConj_comm byteHeapletPCM _ _ h₀).mp hConj₀⟩,
         bytePointsTo_conflict ⟨2, 0⟩ (.init 0x55 none) .uninit⟩

/-- Concrete two-allocation `MemoryState` before writing byte `⟨0, 0⟩`. -/
def frameCanaryMemBefore : MemoryState :=
  { allocations := [
      { allocId := 0, alignLog2 := 0, mutability := .mut,
        bytes := [.init 0x11 none, .init 0x22 none], live := true },
      { allocId := 1, alignLog2 := 0, mutability := .shared,
        bytes := [.init 0x33 none], live := true }
    ]
    nextAllocId := 2 }

/-- Concrete two-allocation `MemoryState` after `storeIndirect` writes `0x7a` at
`⟨0, 0⟩`. -/
def frameCanaryMemAfter : MemoryState :=
  { allocations := [
      { allocId := 0, alignLog2 := 0, mutability := .mut,
        bytes := [.init 0x7a none, .init 0x22 none], live := true },
      { allocId := 1, alignLog2 := 0, mutability := .shared,
        bytes := [.init 0x33 none], live := true }
    ]
    nextAllocId := 2 }

/-- Positive and negative `MemDisjointFrame` + `FramePreserving` canary over
`Trusted.MirSemantics.storeIndirect` and `byteHeapletPCM`: writing `u8` at
`⟨0, 0⟩` produces `frameCanaryMemAfter`, preserves allocation metadata and all
bytes outside `[⟨0, 0, 1⟩]`, refutes the empty-footprint frame
`MemDisjointFrame []`, unconditionally establishes the framed `bytePointsTo`
update across `⟨1, 0⟩ ↦ 0x33` via `bytePointsTo_framePreserving_update` and
`FramePreserving.frame`, and refutes an aliasing `FramePreserving` claim that
moves `⟨0, 0⟩` onto the framed address `⟨1, 0⟩`. -/
theorem memDisjointFrame_storeIndirect_and_framePreserving_canary :
    storeIndirect frameCanaryMemBefore coreU8Ty ⟨0, 0⟩ (coreU8Val 0x7a) =
      .ok frameCanaryMemAfter ∧
    MemDisjointFrame [⟨0, 0, 1⟩] frameCanaryMemBefore frameCanaryMemAfter ∧
    ¬ MemDisjointFrame [] frameCanaryMemBefore frameCanaryMemAfter ∧
    FramePreserving byteHeapletPCM
      (sepConj byteHeapletPCM
        (bytePointsTo ⟨0, 0⟩ (.init 0x11 none))
        (bytePointsTo ⟨1, 0⟩ (.init 0x33 none)))
      (sepConj byteHeapletPCM
        (bytePointsTo ⟨0, 0⟩ (.init 0x7a none))
        (bytePointsTo ⟨1, 0⟩ (.init 0x33 none))) ∧
    ¬ FramePreserving byteHeapletPCM
        (sepConj byteHeapletPCM
          (bytePointsTo ⟨0, 0⟩ (.init 0x11 none))
          (bytePointsTo ⟨1, 0⟩ (.init 0x33 none)))
        (sepConj byteHeapletPCM
          (bytePointsTo ⟨1, 0⟩ (.init 0x7a none))
          (bytePointsTo ⟨1, 0⟩ (.init 0x33 none))) := by
  refine ⟨rfl, ?_, ?_,
    FramePreserving.frame (bytePointsTo ⟨1, 0⟩ (.init 0x33 none))
      (bytePointsTo_framePreserving_update ⟨0, 0⟩
        (.init 0x11 none) (.init 0x7a none)),
    ?_⟩
  · refine ⟨Nat.le_refl 2, fun aid hAid => ?_⟩
    cases aid with
    | zero =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun off hOut => ?_⟩
      cases off with
      | zero => cases hOut
      | succ k =>
        cases k with
        | zero => rfl
        | succ _ => rfl
    | succ a1 =>
      cases a1 with
      | zero =>
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun off _ => ?_⟩
        cases off with
        | zero => rfl
        | succ _ => rfl
      | succ a2 =>
        exact False.elim
          (Nat.not_lt_zero a2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hAid)))
  · intro hEmpty
    have h0 := hEmpty.2 0 (Nat.succ_pos 1)
    have hByte0 := h0.2.2.2.2.2 0 rfl
    cases hByte0
  · intro hBad
    have hNe01 : (⟨0, 0⟩ : ByteAddr) ≠ ⟨1, 0⟩ := fun he => by cases he
    let ⟨h₀, hConj₀⟩ :=
      bytePointsTo_disjoint_of_ne
        (v₁ := .init 0x11 none) (v₂ := .init 0x33 none) hNe01
    have hUnit : byteHeapletPCM.op h₀ byteHeapletPCM.unit = some h₀ :=
      ExplPCM.unit_right byteHeapletPCM h₀
    let ⟨h₂, _, _, hConj₂⟩ := hBad h₀ byteHeapletPCM.unit h₀ hConj₀ hUnit
    exact bytePointsTo_conflict ⟨1, 0⟩ (.init 0x7a none) (.init 0x33 none)
      h₂ hConj₂

private def mkNatRangeFrom : Nat → Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat)
    (fun _ => [])
    (fun _ ih start => start :: ih (start + 1))

/-- 128-element `BlockTree.ofList` scaling canary under default elaborator
reduction options (`compLog2Depth 128 = 7`, `compLog2Depth 1024 = 10`, and
in-bounds/out-of-bounds `BlockTree.ofList` lookups at indices `0`, `63`, `127`,
and `128` discharged directly by `rfl`). -/
theorem blockTree128_ofList_scaling_canary :
    compLog2Depth 64 = 6 ∧
    compLog2Depth 128 = 7 ∧
    compLog2Depth 1024 = 10 ∧
    (BlockTree.ofList (mkNatRangeFrom 128 0)).lookup 0 = some 0 ∧
    (BlockTree.ofList (mkNatRangeFrom 128 0)).lookup 63 = some 63 ∧
    (BlockTree.ofList (mkNatRangeFrom 128 0)).lookup 127 = some 127 ∧
    (BlockTree.ofList (mkNatRangeFrom 128 0)).lookup 128 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Core
