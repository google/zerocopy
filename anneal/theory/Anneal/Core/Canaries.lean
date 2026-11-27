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
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Framework.StepWp
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.Core.BlockTree
public import Anneal.Core.SepPCM
public import Anneal.Core.StageCut
public import Anneal.Core.SpecRealizability
public import Anneal.Core.AlignMath
public import Anneal.Core.BitValidity
public import Anneal.Core.FixedByteCodec
public import Anneal.ByteSubLens.Lens
public import Anneal.Core.PtrTypestate
public import Anneal.Core.BitVecMirBridge
public import Anneal.Core.BitVecMirBridgeExt
public import Anneal.Core.BitIntrinsicBridge

public section

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
6. **`zerocopy` Alignment MIR Canaries:** Exercises hand-modeled Profile v1
   64-bit `usize` scalar equivalents of `padding_needed_for`
   (`bodyZerocopyPaddingNeededFor`) and
   `round_down_to_next_multiple_of_alignment` (`bodyZerocopyRoundDown`) over
   `MirWp`, concrete non-vacuity runs, and negative `align = 6`
   counterexamples (verbatim `zerocopy/src/util/mod.rs` capture remains gated
   on `NonZeroUsize` struct parameters, `TerminatorKind::Call`, and
   `debug_assert!`).
7. **Zerocopy Bit-Validity & Transmutation Canaries:** Exercises
   `Core.BitValidity` across Profile v1 primitives, overflow pairs
   (no modeled trait, with and without `.uninit` local-slot padding),
   `AsInitialized` acceptance of padded and invalid-`bool` pairs and rejection
   of all-`.uninit` pairs, exact `TryFromBytes` validators and the unsound
   accept-all `bool` validator, ZST/2-variant/`256`-variant fieldless enums,
   trait hierarchy separations, and equal-size `transmute_sound` corollaries.
8. **Zerocopy `FixedByteCodec` & Padding Canaries:** Exercises
   `Core.FixedByteCodec` exact-width enforcement (including `n = 0`), endian
   serialization (`LeBytes` and `MirSemantics.Bytes`), `[u16; 4]` array
   chunking and element slicing, `MirBytesCodec` (`FromZeros`, `FromBytes`,
   `IntoBytes`), and equal-size `8`-byte transmutation contrast between
   unpadded `(u32, u16, u16)` and padded `(u32, u8, 3-byte pad)`.
9. **Spec Realizability, Dichotomy, and Vacuity (`Core.SpecRealizability`):**
   Exercises vacuity taxonomy, realizability, and contract dichotomy.
10. **BitVec, BitVecArith, and LeBytes MIR Bridge (`Core.BitVecMirBridge`):**
   Positive/negative `evalBinOp`/`evalUnOp`/`evalIntToIntCast` bridges, `tnum`
   lifts, byte-codec round-trips, chunking, and symbolic `Body` execution.
11. **Extended `BitVecMirBridge` Canaries (`Core.BitVecMirBridgeExt`):**
   Signed/unsigned shifts, signed arithmetic + overflow, `.cmp`/`.bool`/
   `.char` ops, unary/cast rejections, and signed `.div` `Body` faults.
-/

/-! ## Computable Scalar / Tuple Helpers (`0` `noncomputable`) -/

/-- `u8` MIR type. -/
@[expose] def coreU8Ty : MirTy := .int .i8 false

/-- `u32` MIR type. -/
@[expose] def coreU32Ty : MirTy := .int .i32 false

/-- `(u32, bool)` overflowing-arithmetic return type. -/
@[expose] def coreOvU32Ty : MirTy := .tuple [coreU32Ty, .bool]

/-- Canonical `u8` `Val` from `n : Nat`. -/
@[expose] def coreU8Val (n : Nat) : Val :=
  .scalar ⟨.i8, false, truncateBitsComp .i8 (BitVec.ofNat 128 n)⟩

/-- Canonical `u32` `Val` from `n : Nat`. -/
@[expose] def coreU32Val (n : Nat) : Val :=
  .scalar ⟨.i32, false, truncateBitsComp .i32 (BitVec.ofNat 128 n)⟩

/-- Constant `u8` `Operand`. -/
@[expose] def coreU8Const (n : Nat) : Operand :=
  .constant ⟨coreU8Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Constant `u32` `Operand`. -/
@[expose] def coreU32Const (n : Nat) : Operand :=
  .constant ⟨coreU32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Direct unprojected `Place` for `id`. -/
@[expose] def coreLocalPlace (id : LocalId) : Place := ⟨id, []⟩

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
@[expose] def mkStageSwitchBlock (k : Nat) : BasicBlock :=
  { statements := []
    terminator := .switchInt (.copy (coreLocalPlace (k + 2)))
      { branches := [(0, 3 * k + 3)], otherwise := 3 * k + 2 }
    cleanup := false }

/-- Stage `k` `true`-arm block (`3 * k + 2`): `u32 -> u8 -> u32` roundtrip cast,
`mulWithOverflow` + `mulUnchecked` by `2`, and `addWithOverflow` +
`addUnchecked`. -/
@[expose] def mkStageTrueBlock (k : Nat) : BasicBlock :=
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
@[expose] def mkStageFalseBlock (k : Nat) : BasicBlock :=
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
@[expose] def mkOverflowCastStageBlocks (k : Nat) : List BasicBlock :=
  [mkStageSwitchBlock k, mkStageTrueBlock k, mkStageFalseBlock k]

/-- Entry prologue block (`bb0`): widens `seed : u8` to `u32` and computes
`seed + 1` via `addWithOverflow` + `addUnchecked`. -/
@[expose] def join8EntryBlock : BasicBlock :=
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
@[expose] def join8ExitBlock : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 0) (.use (.copy (coreLocalPlace 13)))
    ]
    terminator := .return_
    cleanup := false }

/-- `26`-block, `256`-boolean-path MIR `Body` combining overflowing and
unchecked arithmetic with narrowing and widening integer casts. -/
@[expose] def bodyOverflowCastJoin8 : Body :=
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
@[expose] def btOverflowCastJoin8 : BlockTree BasicBlock :=
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
@[expose] def flagAt8 (fv : FlagVec8) (k : Nat) : Bool :=
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
@[expose] def flagArgs8 (seedVal : Val) (fv : FlagVec8) : List Val :=
  [seedVal, .bool fv.b0, .bool fv.b1, .bool fv.b2, .bool fv.b3,
   .bool fv.b4, .bool fv.b5, .bool fv.b6, .bool fv.b7]

/-- Pure-data hull cutpoint descriptor `(blockIdx, lo, hi)`. -/
structure OverflowHullNode where
  blockIdx : Nat
  lo : Nat
  hi : Nat

/-- Canonical hull cutpoint node at stage `k` (`blockIdx = 3 * k + 1`). -/
@[expose] def mkOverflowHullNode (k : Nat) : OverflowHullNode :=
  { blockIdx := 3 * k + 1, lo := hullLo k, hi := hullHi k }

@[expose] def mkJoin8Locals (s0 : LocalSlot) (seed : Nat) (fv : FlagVec8)
    (s10 s11 s12 s13 : LocalSlot) : List LocalSlot :=
  [s0, .immediate (some (coreU8Val seed)),
   .immediate (some (.bool fv.b0)), .immediate (some (.bool fv.b1)),
   .immediate (some (.bool fv.b2)), .immediate (some (.bool fv.b3)),
   .immediate (some (.bool fv.b4)), .immediate (some (.bool fv.b5)),
   .immediate (some (.bool fv.b6)), .immediate (some (.bool fv.b7)),
   s10, s11, s12, s13]

@[expose] def mkJoin8RawState (blockIdx stmtIdx : Nat)
    (locals : List LocalSlot) : State :=
  { frames := [{ defId := 0, blockIdx := blockIdx, stmtIdx := stmtIdx,
                 locals := locals }]
    callerMem := ⟨[]⟩
    mem := entryMemoryComp }

@[expose] def mkStageLocals (seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat) : List LocalSlot :=
  mkJoin8Locals (.immediate none) seed fv
    (.immediate (some (coreU32Val acc)))
    (.immediate (some (coreU8Val v11)))
    (.immediate (some (coreU32Val v12)))
    (.immediate (some (.tuple [coreU32Val acc, .bool false])))

@[expose] def mkStageState (blockIdx stmtIdx seed : Nat) (fv : FlagVec8)
    (acc v11 v12 : Nat) : State :=
  mkJoin8RawState blockIdx stmtIdx (mkStageLocals seed fv acc v11 v12)

/-- Cutpoint state invariant at `node`. -/
@[expose] def HoldsAtOverflowNode (node : OverflowHullNode) (seed : Nat)
    (fv : FlagVec8) (s : State) : Prop :=
  ∃ (acc v11 v12 : Nat),
    node.lo ≤ acc ∧ acc ≤ node.hi ∧
    s = mkStageState node.blockIdx 0 seed fv acc v11 v12

/-- Zero-`Prop`-argument stage-cut join predicate over `StepStageCut` /
`wpUntilCutStep` (sealed `@[irreducible]` below). -/
@[expose] def OverflowCastStageCut (body : Body) (bt : BlockTree BasicBlock)
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
@[expose] def OverflowCastJoin8Post (out : TerminalOut) : Prop :=
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
  dsimp only [execOutcomeState, Anneal.Framework.StepWp.execStepOutcome]
  rw [Anneal.Framework.StepWp.execStepPred_succ_iff, hMirStep1]
  dsimp only
  rw [Anneal.Framework.StepWp.execStepPred_succ_iff, hMirStep2]
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
@[expose] def bodyUncheckedOverflowFault : Body :=
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
@[expose] def bodyTwoPassAdd : Body :=
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
@[expose] def bodyCleanupFaultBlock : Body :=
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

@[expose] def mkGuardScopeBlock (scopeLocal guardLocal retCode : Nat)
    (earlyBlk contBlk : BasicBlockId) : BasicBlock :=
  { statements := [
      .storageLive scopeLocal,
      .assign (coreLocalPlace 0) (.use (coreU32Const retCode))
    ]
    terminator := .switchInt (.copy (coreLocalPlace guardLocal))
      { branches := [(1, earlyBlk)], otherwise := contBlk }
    cleanup := false }

@[expose] def mkConstRetJoinBlock (retCode : Nat)
    (cleanBlk : BasicBlockId) : BasicBlock :=
  { statements := [
      .assign (coreLocalPlace 0) (.use (coreU32Const retCode))
    ]
    terminator := .goto cleanBlk
    cleanup := false }

@[expose] def mkStorageDeadGotoBlock (dropIdx nextBlk : Nat) : BasicBlock :=
  { statements := [.storageDead dropIdx]
    terminator := .goto nextBlk
    cleanup := false }

/-- `11`-block nested-guard MIR `Body` sharing a 5-block LIFO `StorageDead`
cleanup spine (`bb6 -> bb7 -> bb8 -> bb9 -> bb10`). -/
@[expose] def bodyCleanupChain4 : Body :=
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
@[expose] def btCleanupChain4 : BlockTree BasicBlock :=
  BlockTree.ofList bodyCleanupChain4.basicBlocks

/-- Functional specification of `bodyCleanupChain4`. -/
@[expose] def cleanupChain4Spec (g0 g1 g2 g3 : Bool) : Nat :=
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
@[expose] def bodyLoopEarlyRetClean : Body :=
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
@[expose] def bodyLoopEarlyRetUninitRet : Body :=
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
@[expose] def frameCanaryMemBefore : MemoryState :=
  { allocations := [
      { allocId := 0, alignLog2 := 0, mutability := .mut,
        bytes := [.init 0x11 none, .init 0x22 none], live := true },
      { allocId := 1, alignLog2 := 0, mutability := .shared,
        bytes := [.init 0x33 none], live := true }
    ]
    nextAllocId := 2 }

/-- Concrete two-allocation `MemoryState` after `storeIndirect` writes `0x7a` at
`⟨0, 0⟩`. -/
@[expose] def frameCanaryMemAfter : MemoryState :=
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

@[expose] def mkNatRangeFrom : Nat → Nat → List Nat :=
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

/-! ## Canary Suite 6: Spec Realizability, Dichotomy, and Vacuity -/

private theorem coreU32Val_inj {a b : Nat}
    (ha : a < intWidthModulus .i32) (hb : b < intWidthModulus .i32)
    (h : coreU32Val a = coreU32Val b) : a = b := by
  unfold coreU32Val at h
  rw [truncateBitsComp_of_lt ha, truncateBitsComp_of_lt hb] at h
  injection h with hScalar
  injection hScalar with _ _ hBv
  have hNat :
      (BitVec.ofNat 128 a).toNat = (BitVec.ofNat 128 b).toNat :=
    congrArg BitVec.toNat hBv
  rw [bitVec128_toNat_of_lt
        (Nat.lt_of_lt_of_le ha (intWidthModulus_le_pow128 .i32)),
      bitVec128_toNat_of_lt
        (Nat.lt_of_lt_of_le hb (intWidthModulus_le_pow128 .i32))] at hNat
  exact hNat

@[expose] def canaryNonEmptyCallerMem : CallerMemory :=
  ⟨[{ allocId := 1, alignLog2 := 0, mutability := .mut, bytes := [],
      live := true }]⟩

private theorem canaryCallerMem_empty_ne_nonEmpty :
    (⟨[]⟩ : CallerMemory) ≠ canaryNonEmptyCallerMem := by
  intro hEq
  have hAllocs : ([] : List Allocation) = canaryNonEmptyCallerMem.allocations :=
    congrArg CallerMemory.allocations hEq
  cases hAllocs

/-- `VacuityClass` wire-name taxonomy canary: verifies exhaustive enumeration,
injectivity, and round-trip lookup across all 5 classes plus unknown wire
names. -/
theorem vacuityClass_wire_taxonomy_canary :
    VacuityClass.all.length = 5 ∧
    VacuityClass.ofCanonicalName? "DeadPrecondition" =
      some .deadPrecondition ∧
    VacuityClass.ofCanonicalName? "SpecViolation" = some .specViolation ∧
    VacuityClass.ofCanonicalName? "TrivialPostcondition" =
      some .trivialPostcondition ∧
    VacuityClass.ofCanonicalName? "UnboundReturnOutput" =
      some .unboundReturnOutput ∧
    VacuityClass.ofCanonicalName? "SurvivedAllMutants" =
      some .survivedAllMutants ∧
    VacuityClass.ofCanonicalName? "NotAClass" = none ∧
    (∀ c : VacuityClass, c ∈ VacuityClass.all) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, VacuityClass.mem_all⟩

@[expose] def twoPassAddQuery19_23 : Query :=
  { args := [coreU32Val 19, coreU32Val 23] }

@[expose] def twoPassAddSpecPre (q : Query) : Prop :=
  q = twoPassAddQuery19_23

@[expose] def twoPassAddSpecPost (_q : Query) (out : TerminalOut) : Prop :=
  out = .returned ⟨coreU32Val 42, ⟨[]⟩⟩

/-- Positive `SatisfiesPost` bridge canary on `bodyTwoPassAdd (19, 23) = 42`:
derives `ContractRealizable`, `TerminalReturnDichotomy`,
`PostconditionDichotomy`, a concrete `MutantKilledBySpec` witness, and
`ContractDeterministic` directly from `Trusted.MirSemantics.SatisfiesPost`. -/
theorem bodyTwoPassAdd_realizability_and_dichotomy_canary :
    ContractRealizable twoPassAddSpecPre twoPassAddSpecPost ∧
    TerminalReturnDichotomy twoPassAddSpecPre twoPassAddSpecPost ∧
    PostconditionDichotomy twoPassAddSpecPre twoPassAddSpecPost ∧
    MutantKilledBySpec twoPassAddSpecPre twoPassAddSpecPost
      twoPassAddQuery19_23
      (.returned ⟨coreU32Val 42, ⟨[]⟩⟩)
      (.returned ⟨coreU32Val 0, ⟨[]⟩⟩) ∧
    ContractDeterministic twoPassAddSpecPre twoPassAddSpecPost := by
  have hCan := bodyTwoPassAdd_19_23_canary
  have hSafe : wpProg (bodyProg bodyTwoPassAdd) 2
      twoPassAddQuery19_23 (fun _ => True) :=
    wpProg_of_execProg True.intro
  have hWlp : wlpProg (bodyProg bodyTwoPassAdd) 2
      twoPassAddQuery19_23 (twoPassAddSpecPost twoPassAddQuery19_23) := by
    change wlpOutcomeState (bodyProg bodyTwoPassAdd)
      (fun out => out = TerminalOut.returned ⟨coreU32Val 42, ⟨[]⟩⟩)
      (fun _ => True) 2 _
    intro c₁ hc₁
    subst hc₁
    intro c₂ hc₂
    subst hc₂
    rfl
  have hWp : wpProg (bodyProg bodyTwoPassAdd) 2
      twoPassAddQuery19_23 (twoPassAddSpecPost twoPassAddQuery19_23) :=
    wpProg_of_wlp_and_safety hSafe hWlp
  have hSat : SatisfiesPost (bodyProg bodyTwoPassAdd) twoPassAddQuery19_23
      (twoPassAddSpecPost twoPassAddQuery19_23) :=
    (wellFormed_and_spec_of_wp_base (bodyProg bodyTwoPassAdd)
      twoPassAddQuery19_23 2 (twoPassAddSpecPost twoPassAddQuery19_23) hWp).1
  have hBad :
      ¬ twoPassAddSpecPost twoPassAddQuery19_23
          (.returned ⟨coreU32Val 0, ⟨[]⟩⟩) := by
    intro hEq
    injection hEq with hOut
    injection hOut with hRet _
    have hNat : (0 : Nat) = 42 :=
      coreU32Val_inj (by decide) (by decide) hRet
    cases hNat
  have hReal : ContractRealizable twoPassAddSpecPre twoPassAddSpecPost :=
    satisfiesPost_contractRealizable rfl hCan.2 hSat
  have hTermDich :
      TerminalReturnDichotomy twoPassAddSpecPre twoPassAddSpecPost :=
    satisfiesPost_terminalReturnDichotomy rfl hCan.2 hSat hBad
  have hDich : PostconditionDichotomy twoPassAddSpecPre twoPassAddSpecPost :=
    hTermDich.toDichotomy
  have hNe :
      (TerminalOut.returned ⟨coreU32Val 0, ⟨[]⟩⟩) ≠
        (TerminalOut.returned ⟨coreU32Val 42, ⟨[]⟩⟩) := by
    intro hEq
    injection hEq with hOut
    injection hOut with hRet _
    have hNat : (0 : Nat) = 42 :=
      coreU32Val_inj (by decide) (by decide) hRet
    cases hNat
  have hMut :
      MutantKilledBySpec twoPassAddSpecPre twoPassAddSpecPost
        twoPassAddQuery19_23
        (.returned ⟨coreU32Val 42, ⟨[]⟩⟩)
        (.returned ⟨coreU32Val 0, ⟨[]⟩⟩) :=
    ⟨rfl, hNe, hSat.2 _ hCan.2, hBad⟩
  have hDet : ContractDeterministic twoPassAddSpecPre twoPassAddSpecPost := by
    unfold twoPassAddSpecPost
    exact contractDeterministic_of_function twoPassAddSpecPre
      (fun _ => TerminalOut.returned ⟨coreU32Val 42, ⟨[]⟩⟩)
  exact ⟨hReal, hTermDich, hDich, hMut, hDet⟩

@[expose] def statefulAllocBumpPre (_args : List Val) (mem : CallerMemory) :
    Prop :=
  mem = ⟨[]⟩

@[expose] def statefulAllocBumpPost (_args : List Val) (mem : CallerMemory)
    (ret : Val) (mem' : CallerMemory) : Prop :=
  ret = coreU32Val mem.allocations.length ∧ mem' = canaryNonEmptyCallerMem

/-- Positive stateful contract canary over `(List Val, CallerMemory)`: verifies
`NonVacuousStatefulPre`, `StatefulRealizable`, `StatefulReturnDichotomy`,
`StatefulDichotomy`, and `StatefulDeterministic`. -/
theorem statefulAllocBump_realizability_canary :
    NonVacuousStatefulPre statefulAllocBumpPre ∧
    StatefulRealizable statefulAllocBumpPre statefulAllocBumpPost ∧
    StatefulReturnDichotomy statefulAllocBumpPre statefulAllocBumpPost ∧
    StatefulDichotomy statefulAllocBumpPre statefulAllocBumpPost ∧
    StatefulDeterministic statefulAllocBumpPre statefulAllocBumpPost := by
  have hPre : NonVacuousStatefulPre statefulAllocBumpPre := ⟨[], ⟨[]⟩, rfl⟩
  have hReal : StatefulRealizable statefulAllocBumpPre statefulAllocBumpPost :=
    ⟨([], ⟨[]⟩), rfl, (coreU32Val 0, canaryNonEmptyCallerMem), ⟨rfl, rfl⟩⟩
  have hRetDich :
      StatefulReturnDichotomy statefulAllocBumpPre statefulAllocBumpPost := by
    refine ⟨[], ⟨[]⟩, canaryNonEmptyCallerMem, coreU32Val 0, coreU32Val 1,
      rfl, ⟨rfl, rfl⟩, ?_⟩
    intro hBad
    have hNat : (1 : Nat) = 0 :=
      coreU32Val_inj (by decide) (by decide) hBad.1
    cases hNat
  have hDich : StatefulDichotomy statefulAllocBumpPre statefulAllocBumpPost :=
    hRetDich.toDichotomy
  have hDet :
      StatefulDeterministic statefulAllocBumpPre statefulAllocBumpPost := by
    intro p q₁ q₂ hPreP h1 h2
    let ⟨_, mem⟩ := p
    let ⟨v₁, m₁⟩ := q₁
    let ⟨v₂, m₂⟩ := q₂
    have hv : v₁ = v₂ := h1.1.trans h2.1.symm
    have hm : m₁ = m₂ := h1.2.trans h2.2.symm
    cases hv
    cases hm
    rfl
  exact ⟨hPre, hReal, hRetDich, hDich, hDet⟩

@[expose] def deadNatPre (n : Nat) : Prop := 100 < n ∧ n < 50
@[expose] def deadNatPost (n ret : Nat) : Prop := ret = n

@[expose] def bodyUnsafeOverflowVacuous : Body :=
  { identity := "anneal_core::unsafe_overflow_vacuous"
    isUnsafe := true
    locals := [coreU32Ty]
    argumentCount := 0
    basicBlocks := bodyUncheckedOverflowFault.basicBlocks }

@[expose] def deadSafetyPre (args : List Val) : Prop := args.length = 99

@[expose] def specViolPre (n : Nat) : Prop := n < 10
@[expose] def specViolPost (n ret : Nat) : Prop := 10 ≤ n ∧ ret = 5
@[expose] def contraNatPost (_n ret : Nat) : Prop := ret = 1 ∧ ret = 2

@[expose] def trivReflNatPost (_n ret : Nat) : Prop := ret = ret
@[expose] def trivDisjNatPost (_n ret : Nat) : Prop := ret = ret ∨ ret = 0

@[expose] def inputOnlyNatPost (n _ret : Nat) : Prop := n < 100

@[expose] def memOnlyStatefulPre (_args : List Val) (_mem : CallerMemory) :
    Prop :=
  True

@[expose] def memOnlyStatefulPost (_args : List Val) (mem : CallerMemory)
    (_ret : Val) (mem' : CallerMemory) : Prop :=
  mem' = mem

@[expose] def unwoundOnlyTrapPre (_q : Query) : Prop := True

@[expose] def unwoundOnlyTrapPost (_q : Query) : TerminalOut → Prop
  | .returned _ => True
  | .unwound _ | .aborted _ => False

@[expose] def survivedNatPre (n : Nat) : Prop := n < 10
@[expose] def survivedDisjNatPost (n ret : Nat) : Prop := n < 10 ∨ ret = 42
@[expose] def survivedImpNatPost (n ret : Nat) : Prop := 10 ≤ n → ret = 42

/-- Negative vacuity canary suite exercising all five `VacuityClass` failure
modes (`DeadPrecondition`, `SpecViolation`, `TrivialPostcondition`,
`UnboundReturnOutput`, `SurvivedAllMutants`), plus disjunctive-branch
splitting. -/
theorem specRealizability_negative_vacuity_and_composition_canary :
    (¬ PreconditionSatisfiable deadNatPre) ∧
    (¬ ContractRealizable deadNatPre deadNatPost) ∧
    BodyVerified (bodyProg bodyUnsafeOverflowVacuous) 0
      bodyUnsafeOverflowVacuous deadSafetyPre ∧
    (¬ ContractRealizable specViolPre specViolPost) ∧
    (¬ ContractRealizable (fun _ : Nat => True) contraNatPost) ∧
    (¬ PostconditionDichotomy (fun _ : Nat => True) trivReflNatPost) ∧
    (¬ PostconditionDichotomy (fun _ : Nat => True) trivDisjNatPost) ∧
    (¬ PostconditionDichotomy (fun _ : Nat => True) inputOnlyNatPost) ∧
    (¬ PostconditionDichotomy (fun _ : Nat => True)
        (fun (_ : Nat) (r : Option Empty) => r = none)) ∧
    (StatefulDichotomy memOnlyStatefulPre memOnlyStatefulPost ∧
      ¬ StatefulReturnDichotomy memOnlyStatefulPre memOnlyStatefulPost) ∧
    (PostconditionDichotomy unwoundOnlyTrapPre unwoundOnlyTrapPost ∧
      ¬ TerminalReturnDichotomy unwoundOnlyTrapPre unwoundOnlyTrapPost) ∧
    (PreconditionSatisfiable survivedNatPre ∧
      ¬ PostconditionDichotomy survivedNatPre survivedDisjNatPost ∧
      ¬ PostconditionDichotomy survivedNatPre survivedImpNatPost) ∧
    PostconditionDichotomy (fun n => deadNatPre n ∨ n = 7) deadNatPost ∧
    ¬ PostconditionDichotomy (fun n => deadNatPre n ∨ n = 7)
        trivReflNatPost := by
  have hDeadUnsat : ¬ PreconditionSatisfiable deadNatPre := by
    intro h
    let ⟨n, hGt, hLt⟩ := h
    exact Nat.lt_asymm (Nat.lt_trans (by decide : 50 < 100) hGt) hLt
  have hDeadReal : ¬ ContractRealizable deadNatPre deadNatPost :=
    not_contractRealizable_of_unsat_pre hDeadUnsat
  have hDeadSafetyUnsat :
      ¬ NonVacuousBodySafetyPre bodyUnsafeOverflowVacuous deadSafetyPre := by
    intro h
    let ⟨args, hValid, hLen⟩ := h
    dsimp only [ValidEntryArgs, bodyUnsafeOverflowVacuous] at hValid
    cases args with
    | nil => cases hLen
    | cons _ _ => exact False.elim (Bool.noConfusion hValid)
  have hBodyVacuous :
      BodyVerified (bodyProg bodyUnsafeOverflowVacuous) 0
        bodyUnsafeOverflowVacuous deadSafetyPre :=
    bodyVerified_vacuous_safety_of_unsat rfl rfl rfl hDeadSafetyUnsat
  have hSpecViol : ¬ ContractRealizable specViolPre specViolPost := by
    intro h
    let ⟨n, hLt, _, hGe, _⟩ := h
    exact Nat.not_lt_of_le hGe hLt
  have hContra : ¬ ContractRealizable (fun _ : Nat => True) contraNatPost := by
    intro h
    let ⟨_, _, _, h1, h2⟩ := h
    rw [h1] at h2
    cases h2
  have hTrivRefl :
      ¬ PostconditionDichotomy (fun _ : Nat => True) trivReflNatPost :=
    not_postconditionDichotomy_of_trivial (fun _ _ _ => rfl)
  have hTrivDisj :
      ¬ PostconditionDichotomy (fun _ : Nat => True) trivDisjNatPost :=
    not_postconditionDichotomy_of_trivial (fun _ _ _ => Or.inl rfl)
  have hInputOnly :
      ¬ PostconditionDichotomy (fun _ : Nat => True) inputOnlyNatPost :=
    not_postconditionDichotomy_of_outputInsensitive (fun _ _ _ _ => Iff.rfl)
  have hSubsing :
      ¬ PostconditionDichotomy (fun _ : Nat => True)
          (fun (_ : Nat) (r : Option Empty) => r = none) := by
    have hSub : Subsingleton (Option Empty) :=
      ⟨fun a b => by
        cases a with
        | none =>
          cases b with
          | none => rfl
          | some e => exact nomatch e
        | some e => exact nomatch e⟩
    exact @not_postconditionDichotomy_of_subsingleton _ _ hSub _ _
  have hMemOnlyDich :
      StatefulDichotomy memOnlyStatefulPre memOnlyStatefulPost := by
    refine ⟨([], ⟨[]⟩), True.intro,
      ⟨(.unit, ⟨[]⟩), rfl⟩,
      ⟨(.unit, canaryNonEmptyCallerMem), ?_⟩⟩
    intro hEq
    exact canaryCallerMem_empty_ne_nonEmpty hEq.symm
  have hMemOnlyNotRet :
      ¬ StatefulReturnDichotomy memOnlyStatefulPre memOnlyStatefulPost :=
    not_statefulReturnDichotomy_of_returnInsensitive
      (fun _ _ _ _ _ _ hOk => hOk)
  have hUnwoundDich :
      PostconditionDichotomy unwoundOnlyTrapPre unwoundOnlyTrapPost :=
    ⟨{ args := [] }, True.intro,
      ⟨.returned ⟨.unit, ⟨[]⟩⟩, True.intro⟩,
      ⟨.unwound ⟨[]⟩, fun hF => hF⟩⟩
  have hUnwoundNotRet :
      ¬ TerminalReturnDichotomy unwoundOnlyTrapPre unwoundOnlyTrapPost :=
    not_terminalReturnDichotomy_of_returnInsensitive
      (fun _ _ _ _ _ _ => True.intro)
  have hSurvPre : PreconditionSatisfiable survivedNatPre :=
    ⟨0, Nat.zero_lt_succ 9⟩
  have hSurvDisj :
      ¬ PostconditionDichotomy survivedNatPre survivedDisjNatPost :=
    not_postconditionDichotomy_of_trivial (fun _ _ hPre => Or.inl hPre)
  have hSurvImp :
      ¬ PostconditionDichotomy survivedNatPre survivedImpNatPost :=
    not_postconditionDichotomy_of_trivial (fun _ _ hPre hGe =>
      False.elim (Nat.not_lt_of_le hGe hPre))
  have hBranchPos :
      PostconditionDichotomy (fun n => deadNatPre n ∨ n = 7) deadNatPost := by
    refine (postconditionDichotomy_or_pre_iff (pre₁ := deadNatPre)
      (pre₂ := fun n => n = 7) (post := deadNatPost)).mpr (Or.inr ?_)
    refine ⟨7, rfl, ⟨7, rfl⟩, ⟨8, ?_⟩⟩
    intro hEq
    cases hEq
  have hBranchNeg :
      ¬ PostconditionDichotomy (fun n => deadNatPre n ∨ n = 7)
          trivReflNatPost := by
    refine (not_postconditionDichotomy_or_pre_iff (pre₁ := deadNatPre)
      (pre₂ := fun n => n = 7) (post := trivReflNatPost)).mpr ⟨?_, ?_⟩
    · exact not_postconditionDichotomy_of_unsat_pre hDeadUnsat
    · exact not_postconditionDichotomy_of_trivial (fun _ _ _ => rfl)
  exact ⟨hDeadUnsat, hDeadReal, hBodyVacuous, hSpecViol, hContra, hTrivRefl,
    hTrivDisj, hInputOnly, hSubsing, ⟨hMemOnlyDich, hMemOnlyNotRet⟩,
    ⟨hUnwoundDich, hUnwoundNotRet⟩, ⟨hSurvPre, hSurvDisj, hSurvImp⟩,
    hBranchPos, hBranchNeg⟩

/-! ## `zerocopy` Alignment MIR Canaries -/

/-- Hand-modeled Profile v1 64-bit `usize` (`MirTy.int .isize false`) MIR
scalar equivalent (with overflow checks off) of
`zerocopy::util::padding_needed_for` (`!(len.wrapping_sub(1)) & (align - 1)`
in `zerocopy/src/util/mod.rs`). Direct capture of the verbatim item is
blocked by Profile v1's fail-closed rejection of the `NonZeroUsize` struct
parameter and `TerminatorKind::Call` (`NonZero::get` and
`usize::wrapping_sub`). -/
@[expose] def bodyZerocopyPaddingNeededFor : Body :=
  { identity := "canary::zerocopy_align_math::padding_needed_for_model"
    isUnsafe := false
    locals :=
      [alignUsizeTy, alignUsizeTy, alignUsizeTy, alignUsizeTy, alignUsizeTy]
    argumentCount := 2
    basicBlocks := [
      { statements := [
          .storageLive 3,
          .assign (coreLocalPlace 3)
            (.binaryOp .sub (.copy (coreLocalPlace 1)) (alignUsizeConst 1)),
          .assign (coreLocalPlace 3)
            (.unaryOp .not (.copy (coreLocalPlace 3))),
          .storageLive 4,
          .assign (coreLocalPlace 4)
            (.binaryOp .sub (.copy (coreLocalPlace 2)) (alignUsizeConst 1)),
          .assign (coreLocalPlace 0)
            (.binaryOp .bitAnd (.copy (coreLocalPlace 3))
              (.copy (coreLocalPlace 4))),
          .storageDead 4,
          .storageDead 3
        ]
        terminator := .return_
        cleanup := false }
    ] }

/-- Hand-modeled Profile v1 64-bit `usize` (`MirTy.int .isize false`) MIR
scalar equivalent (with overflow checks off) of
`zerocopy::util::round_down_to_next_multiple_of_alignment` (`n & !(align - 1)`
in `zerocopy/src/util/mod.rs`). Direct capture of the verbatim item is
blocked by Profile v1's fail-closed rejection of the `NonZeroUsize` struct
parameter, `TerminatorKind::Call` (`NonZero::get`), and `debug_assert!`
lowering. -/
@[expose] def bodyZerocopyRoundDown : Body :=
  { identity := "canary::zerocopy_align_math::round_down_model"
    isUnsafe := false
    locals := [alignUsizeTy, alignUsizeTy, alignUsizeTy, alignUsizeTy]
    argumentCount := 2
    basicBlocks := [
      { statements := [
          .storageLive 3,
          .assign (coreLocalPlace 3)
            (.binaryOp .sub (.copy (coreLocalPlace 2)) (alignUsizeConst 1)),
          .assign (coreLocalPlace 3)
            (.unaryOp .not (.copy (coreLocalPlace 3))),
          .assign (coreLocalPlace 0)
            (.binaryOp .bitAnd (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 3))),
          .storageDead 3
        ]
        terminator := .return_
        cleanup := false }
    ] }

private theorem wpProg_of_executes {body : Body} {args : List Val}
    {s₀ : State} {vRet : Val}
    (hInit : initState (bodyProg body) { args := args } = .ok s₀)
    (hExec : Executes body s₀ vRet) :
    ∃ fuel, wpProg (bodyProg body) fuel { args := args }
      (fun out => out = .returned ⟨vRet, ⟨[]⟩⟩) := by
  let ⟨fuel, hRuns⟩ := executes_iff_wpState.mp hExec
  refine ⟨fuel, ?_⟩
  unfold wpProg
  rw [hInit]
  exact wpOutcomeState_of_execOutcomeState hRuns

private theorem bvZeroExtend_128_u64_one :
    bvZeroExtend 128 (BitVec.ofNat 64 1) = BitVec.ofNat 128 1 := by
  unfold bvZeroExtend
  rw [Anneal.BitVec.toNat_ofNat,
    (by decide : Nat.mod 1 (Nat.pow 2 64) = 1)]

private theorem evalPrimitiveOperand_alignUsizeConst_one
    (tys : List MirTy) (locs : List LocalSlot) (m : MemoryState) :
    evalPrimitiveOperand tys locs m (alignUsizeConst 1) =
      .ok (alignUsizeVal (BitVec.ofNat 64 1), locs, m) := by
  unfold alignUsizeVal
  rw [bvZeroExtend_128_u64_one]
  rfl

private theorem evalRvalue_binaryOp_usize {tys : List MirTy}
    {ls ls₁ ls₂ : List LocalSlot} {m m₁ m₂ : MemoryState} {dstTy : MirTy}
    {op : BinOp} {lhs rhs : Operand} {lVal rVal res : Val}
    (hL : evalPrimitiveOperand tys ls m lhs = .ok (lVal, ls₁, m₁))
    (hR : evalPrimitiveOperand tys ls₁ m₁ rhs = .ok (rVal, ls₂, m₂))
    (hOp : evalBinOp op lVal rVal = .ok res) :
    evalRvalue tys ls m dstTy (.binaryOp op lhs rhs) =
      .ok (res, ls₂, m₂) := by
  unfold evalRvalue
  dsimp only
  rw [hL]
  dsimp only
  rw [hR]
  dsimp only
  rw [hOp]

private theorem evalRvalue_unaryOp_usize {tys : List MirTy}
    {ls ls₁ : List LocalSlot} {m m₁ : MemoryState} {dstTy : MirTy}
    {op : UnOp} {opnd : Operand} {v res : Val}
    (hOpnd : evalPrimitiveOperand tys ls m opnd = .ok (v, ls₁, m₁))
    (hOp : evalUnOp op v = .ok res) :
    evalRvalue tys ls m dstTy (.unaryOp op opnd) = .ok (res, ls₁, m₁) := by
  unfold evalRvalue
  dsimp only
  rw [hOpnd]
  dsimp only
  rw [hOp]

private theorem evalStatement_assign_any {body : Body}
    {frame : FrameState} {m m₁ m₂ : MemoryState} {cm : CallerMemory}
    {dst : Place} {rvalue : Rvalue} {dstTy : MirTy} {val : Val}
    {ls ls' : List LocalSlot}
    (hProj : dst.projection.isEmpty = true)
    (hLoc : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some dstTy)
    (hRv : evalRvalue body.locals frame.locals m dstTy rvalue =
      .ok (val, ls, m₁))
    (hW : writePlace ls m₁ dst.localId dstTy val = .ok (ls', m₂)) :
    evalStatement body frame m cm (.assign dst rvalue) =
      .step {
        frames := [{
          frame with
          stmtIdx := frame.stmtIdx + 1
          locals := ls'
        }]
        callerMem := cm
        mem := m₂
      } := by
  have hNotProj : (!dst.projection.isEmpty) = false := by
    rw [hProj]
    rfl
  unfold evalStatement
  dsimp only
  rw [ite_bool_false hNotProj, hLoc]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hW]

private theorem writePlace_usize {ls ls' : List LocalSlot}
    {m : MemoryState} {dstId : LocalId} {x : BitVec 64}
    {old : Option Val}
    (hGet : Trusted.MirSemantics.getElem? ls dstId =
      some (.immediate old))
    (hSet : Trusted.MirSemantics.setElem? ls dstId
      (.immediate (some (alignUsizeVal x))) = some ls') :
    writePlace ls m dstId alignUsizeTy (alignUsizeVal x) =
      .ok (ls', m) := by
  have hNotChk : (!checkVal (alignUsizeVal x) alignUsizeTy) = false := by
    rw [checkVal_alignUsizeVal x]
    rfl
  unfold writePlace
  rw [ite_bool_false hNotChk, hGet, hSet]

private theorem evalStep_stmt_step {body : Body} {bb : BasicBlock}
    {k : Nat} {stmt : StatementKind} {ls : List LocalSlot} {next : State}
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks 0 = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements k = some stmt)
    (hEval :
      evalStatement body
        { defId := 0, blockIdx := 0, stmtIdx := k, locals := ls }
        entryMemory ⟨[]⟩ stmt = .step next) :
    evalStep (bodyProg body) 0 (mkState 0 k ls) = .step next := by
  have hBody : Trusted.MirSemantics.getElem? [body] 0 = some body := rfl
  unfold bodyProg evalStep mkState
  dsimp only [activeFrameBody, attachCallers]
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [hStmt]
  exact hEval

private theorem evalStep_assign_usize {body : Body} {bb : BasicBlock}
    (k : Nat) (dst : Place) (rvalue : Rvalue) (val : Val)
    (ls ls' : List LocalSlot)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks 0 = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements k =
      some (.assign dst rvalue))
    (hProj : dst.projection.isEmpty = true)
    (hLoc : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some alignUsizeTy)
    (hRv : evalRvalue body.locals ls entryMemory alignUsizeTy rvalue =
      .ok (val, ls, entryMemory))
    (hW : writePlace ls entryMemory dst.localId alignUsizeTy val =
      .ok (ls', entryMemory)) :
    evalStep (bodyProg body) 0 (mkState 0 k ls) =
      .step (mkState 0 (k + 1) ls') :=
  evalStep_stmt_step hBb hStmt
    (evalStatement_assign_any
      (frame := { defId := 0, blockIdx := 0, stmtIdx := k, locals := ls })
      hProj hLoc hRv hW)

private theorem alignUsizeVal_inj {x y : BitVec 64}
    (h : alignUsizeVal x = alignUsizeVal y) : x = y := by
  unfold alignUsizeVal at h
  injection h with hSv
  injection hSv with _ _ hBv
  have hNat := congrArg BitVec.toNat hBv
  rw [bvZeroExtend_128_toNat, bvZeroExtend_128_toNat] at hNat
  exact Anneal.BitVec.eq_of_toNat_eq hNat

private theorem validEntryArgs_pad_usize (len align : BitVec 64) :
    ValidEntryArgs bodyZerocopyPaddingNeededFor
      [alignUsizeVal len, alignUsizeVal align] :=
  (checkArgsMatch_cons_iff (args := [alignUsizeVal len, alignUsizeVal align])
    (ty := alignUsizeTy) (tys := [alignUsizeTy])).mpr
    ⟨alignUsizeVal len, [alignUsizeVal align], rfl, checkVal_alignUsizeVal len,
      (checkArgsMatch_cons_iff (args := [alignUsizeVal align])
        (ty := alignUsizeTy) (tys := [])).mpr
        ⟨alignUsizeVal align, [], rfl, checkVal_alignUsizeVal align,
          checkArgsMatch_nil_iff.mpr rfl⟩⟩

/-- Symbolic 9-step weakest-precondition certificate for
`bodyZerocopyPaddingNeededFor` across arbitrary 64-bit `usize` inputs
`len, align : BitVec 64`. -/
theorem bodyZerocopyPaddingNeededFor_wpProg (len align : BitVec 64) :
    ∃ fuel, wpProg (bodyProg bodyZerocopyPaddingNeededFor) fuel
      { args := [alignUsizeVal len, alignUsizeVal align] }
      (fun out =>
        out = .returned ⟨alignUsizeVal (paddingFast len align), ⟨[]⟩⟩) := by
  have hInit :
      initState (bodyProg bodyZerocopyPaddingNeededFor)
        { args := [alignUsizeVal len, alignUsizeVal align] } =
        .ok (mkState 0 0
          [.immediate none, .immediate (some (alignUsizeVal len)),
           .immediate (some (alignUsizeVal align)), .dead, .dead]) :=
    initState_eq_ok (body := bodyZerocopyPaddingNeededFor) rfl rfl
      (validEntryArgs_pad_usize len align)
  let vLen := alignUsizeVal len
  let vAlign := alignUsizeVal align
  let t1 := len - BitVec.ofNat 64 1
  let vt1 := alignUsizeVal t1
  let t2 := Anneal.BitVec.not t1
  let vt2 := alignUsizeVal t2
  let t3 := align - BitVec.ofNat 64 1
  let vt3 := alignUsizeVal t3
  let vRet := alignUsizeVal (paddingFast len align)
  let ls0 : List LocalSlot :=
    [.immediate none, .immediate (some vLen), .immediate (some vAlign),
     .dead, .dead]
  let ls1 : List LocalSlot :=
    [.immediate none, .immediate (some vLen), .immediate (some vAlign),
     .immediate none, .dead]
  let ls2 : List LocalSlot :=
    [.immediate none, .immediate (some vLen), .immediate (some vAlign),
     .immediate (some vt1), .dead]
  let ls3 : List LocalSlot :=
    [.immediate none, .immediate (some vLen), .immediate (some vAlign),
     .immediate (some vt2), .dead]
  let ls4 : List LocalSlot :=
    [.immediate none, .immediate (some vLen), .immediate (some vAlign),
     .immediate (some vt2), .immediate none]
  let ls5 : List LocalSlot :=
    [.immediate none, .immediate (some vLen), .immediate (some vAlign),
     .immediate (some vt2), .immediate (some vt3)]
  let ls6 : List LocalSlot :=
    [.immediate (some vRet), .immediate (some vLen), .immediate (some vAlign),
     .immediate (some vt2), .immediate (some vt3)]
  let ls7 : List LocalSlot :=
    [.immediate (some vRet), .immediate (some vLen), .immediate (some vAlign),
     .immediate (some vt2), .dead]
  let ls8 : List LocalSlot :=
    [.immediate (some vRet), .immediate (some vLen), .immediate (some vAlign),
     .dead, .dead]
  have hStep0 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 0 ls0) =
        .step (mkState 0 1 ls1) := rfl
  have hStep1 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 1 ls1) =
        .step (mkState 0 2 ls2) := by
    have hRv := evalRvalue_binaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyPaddingNeededFor.locals) (ls := ls1)
      (m := entryMemory) (lhs := .copy (coreLocalPlace 1))
      (rhs := alignUsizeConst 1) (lVal := vLen)
      (rVal := alignUsizeVal (BitVec.ofNat 64 1)) (res := vt1)
      rfl (evalPrimitiveOperand_alignUsizeConst_one _ _ _)
      (evalBinOp_sub_usize len (BitVec.ofNat 64 1))
    have hW := writePlace_usize (ls := ls1) (ls' := ls2) (m := entryMemory)
      (dstId := 3) (x := t1) (old := none) rfl rfl
    exact evalStep_assign_usize 1 (coreLocalPlace 3)
      (.binaryOp .sub (.copy (coreLocalPlace 1)) (alignUsizeConst 1))
      vt1 ls1 ls2 rfl rfl rfl rfl hRv hW
  have hStep2 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 2 ls2) =
        .step (mkState 0 3 ls3) := by
    have hRv := evalRvalue_unaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyPaddingNeededFor.locals) (ls := ls2)
      (m := entryMemory) (op := .not) (opnd := .copy (coreLocalPlace 3))
      (v := vt1) (res := vt2) rfl (evalUnOp_not_usize t1)
    have hW := writePlace_usize (ls := ls2) (ls' := ls3) (m := entryMemory)
      (dstId := 3) (x := t2) (old := some vt1) rfl rfl
    exact evalStep_assign_usize 2 (coreLocalPlace 3)
      (.unaryOp .not (.copy (coreLocalPlace 3)))
      vt2 ls2 ls3 rfl rfl rfl rfl hRv hW
  have hStep3 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 3 ls3) =
        .step (mkState 0 4 ls4) := rfl
  have hStep4 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 4 ls4) =
        .step (mkState 0 5 ls5) := by
    have hRv := evalRvalue_binaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyPaddingNeededFor.locals) (ls := ls4)
      (m := entryMemory) (lhs := .copy (coreLocalPlace 2))
      (rhs := alignUsizeConst 1) (lVal := vAlign)
      (rVal := alignUsizeVal (BitVec.ofNat 64 1)) (res := vt3)
      rfl (evalPrimitiveOperand_alignUsizeConst_one _ _ _)
      (evalBinOp_sub_usize align (BitVec.ofNat 64 1))
    have hW := writePlace_usize (ls := ls4) (ls' := ls5) (m := entryMemory)
      (dstId := 4) (x := t3) (old := none) rfl rfl
    exact evalStep_assign_usize 4 (coreLocalPlace 4)
      (.binaryOp .sub (.copy (coreLocalPlace 2)) (alignUsizeConst 1))
      vt3 ls4 ls5 rfl rfl rfl rfl hRv hW
  have hStep5 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 5 ls5) =
        .step (mkState 0 6 ls6) := by
    have hRv := evalRvalue_binaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyPaddingNeededFor.locals) (ls := ls5)
      (m := entryMemory) (op := .bitAnd) (lhs := .copy (coreLocalPlace 3))
      (rhs := .copy (coreLocalPlace 4)) (lVal := vt2) (rVal := vt3)
      (res := vRet) rfl rfl (evalBinOp_bitAnd_usize t2 t3)
    have hW := writePlace_usize (ls := ls5) (ls' := ls6) (m := entryMemory)
      (dstId := 0) (x := paddingFast len align) (old := none) rfl rfl
    exact evalStep_assign_usize 5 (coreLocalPlace 0)
      (.binaryOp .bitAnd (.copy (coreLocalPlace 3)) (.copy (coreLocalPlace 4)))
      vRet ls5 ls6 rfl rfl rfl rfl hRv hW
  have hStep6 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 6 ls6) =
        .step (mkState 0 7 ls7) := rfl
  have hStep7 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 7 ls7) =
        .step (mkState 0 8 ls8) := rfl
  have hStep8 :
      evalStep (bodyProg bodyZerocopyPaddingNeededFor) 0 (mkState 0 8 ls8) =
        .done (.returned ⟨vRet, ⟨[]⟩⟩) := rfl
  change initState (bodyProg bodyZerocopyPaddingNeededFor)
    { args := [alignUsizeVal len, alignUsizeVal align] } =
      .ok (mkState 0 0 ls0) at hInit
  exact wpProg_of_executes hInit
    (.next hStep0 (.next hStep1 (.next hStep2 (.next hStep3
      (.next hStep4 (.next hStep5 (.next hStep6 (.next hStep7
        (.ret hStep8)))))))))

/-- End-to-end MIR WP + mathematical alignment specification for the
hand-modeled 64-bit `usize` `bodyZerocopyPaddingNeededFor` across all
`len, align : BitVec 64` satisfying `isPow2BV align`. -/
theorem zerocopy_padding_needed_for_mir_spec (len align : BitVec 64)
    (hAlign : isPow2BV align) :
    let q : Query := { args := [alignUsizeVal len, alignUsizeVal align] }
    let p : BitVec 64 := paddingFast len align
    WellFormed (bodyProg bodyZerocopyPaddingNeededFor) q ∧
    ¬ Diverges (bodyProg bodyZerocopyPaddingNeededFor) q ∧
    SatisfiesPost (bodyProg bodyZerocopyPaddingNeededFor) q
      (fun out => out = .returned ⟨alignUsizeVal p, ⟨[]⟩⟩) ∧
    p = paddingNaive len align ∧
    p.toNat < align.toNat ∧
    Nat.mod (len.toNat + p.toNat) align.toNat = 0 ∧
    Nat.mod (len + p).toNat align.toNat = 0 ∧
    (∀ r : BitVec 64, Nat.mod (len + r).toNat align.toNat = 0 → p ≤ r) := by
  let q : Query := { args := [alignUsizeVal len, alignUsizeVal align] }
  let ⟨fuel, hWp⟩ := bodyZerocopyPaddingNeededFor_wpProg len align
  let ⟨hSat, hNdiv, _, _, _⟩ :=
    wellFormed_and_spec_of_wp (bodyProg bodyZerocopyPaddingNeededFor) q fuel
      (fun out =>
        out = .returned ⟨alignUsizeVal (paddingFast len align), ⟨[]⟩⟩)
      hWp
  let ⟨hEq, hLt, hMath, hWrap, hMin⟩ := paddingFast_spec_u64 hAlign len
  exact ⟨hSat.1, hNdiv, hSat, hEq, hLt, hMath, hWrap, hMin⟩

private theorem validEntryArgs_round_usize (n align : BitVec 64) :
    ValidEntryArgs bodyZerocopyRoundDown
      [alignUsizeVal n, alignUsizeVal align] :=
  (checkArgsMatch_cons_iff (args := [alignUsizeVal n, alignUsizeVal align])
    (ty := alignUsizeTy) (tys := [alignUsizeTy])).mpr
    ⟨alignUsizeVal n, [alignUsizeVal align], rfl, checkVal_alignUsizeVal n,
      (checkArgsMatch_cons_iff (args := [alignUsizeVal align])
        (ty := alignUsizeTy) (tys := [])).mpr
        ⟨alignUsizeVal align, [], rfl, checkVal_alignUsizeVal align,
          checkArgsMatch_nil_iff.mpr rfl⟩⟩

/-- Symbolic 6-step weakest-precondition certificate for
`bodyZerocopyRoundDown` across arbitrary 64-bit `usize` inputs
`n, align : BitVec 64`. -/
theorem bodyZerocopyRoundDown_wpProg (n align : BitVec 64) :
    ∃ fuel, wpProg (bodyProg bodyZerocopyRoundDown) fuel
      { args := [alignUsizeVal n, alignUsizeVal align] }
      (fun out =>
        out = .returned ⟨alignUsizeVal (roundDownFast n align), ⟨[]⟩⟩) := by
  have hInit :
      initState (bodyProg bodyZerocopyRoundDown)
        { args := [alignUsizeVal n, alignUsizeVal align] } =
        .ok (mkState 0 0
          [.immediate none, .immediate (some (alignUsizeVal n)),
           .immediate (some (alignUsizeVal align)), .dead]) :=
    initState_eq_ok (body := bodyZerocopyRoundDown) rfl rfl
      (validEntryArgs_round_usize n align)
  let vN := alignUsizeVal n
  let vAlign := alignUsizeVal align
  let t1 := align - BitVec.ofNat 64 1
  let vt1 := alignUsizeVal t1
  let t2 := Anneal.BitVec.not t1
  let vt2 := alignUsizeVal t2
  let vRet := alignUsizeVal (roundDownFast n align)
  let ls0 : List LocalSlot :=
    [.immediate none, .immediate (some vN), .immediate (some vAlign), .dead]
  let ls1 : List LocalSlot :=
    [.immediate none, .immediate (some vN), .immediate (some vAlign),
     .immediate none]
  let ls2 : List LocalSlot :=
    [.immediate none, .immediate (some vN), .immediate (some vAlign),
     .immediate (some vt1)]
  let ls3 : List LocalSlot :=
    [.immediate none, .immediate (some vN), .immediate (some vAlign),
     .immediate (some vt2)]
  let ls4 : List LocalSlot :=
    [.immediate (some vRet), .immediate (some vN), .immediate (some vAlign),
     .immediate (some vt2)]
  let ls5 : List LocalSlot :=
    [.immediate (some vRet), .immediate (some vN), .immediate (some vAlign),
     .dead]
  have hStep0 :
      evalStep (bodyProg bodyZerocopyRoundDown) 0 (mkState 0 0 ls0) =
        .step (mkState 0 1 ls1) := rfl
  have hStep1 :
      evalStep (bodyProg bodyZerocopyRoundDown) 0 (mkState 0 1 ls1) =
        .step (mkState 0 2 ls2) := by
    have hRv := evalRvalue_binaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyRoundDown.locals) (ls := ls1) (m := entryMemory)
      (lhs := .copy (coreLocalPlace 2)) (rhs := alignUsizeConst 1)
      (lVal := vAlign) (rVal := alignUsizeVal (BitVec.ofNat 64 1)) (res := vt1)
      rfl (evalPrimitiveOperand_alignUsizeConst_one _ _ _)
      (evalBinOp_sub_usize align (BitVec.ofNat 64 1))
    have hW := writePlace_usize (ls := ls1) (ls' := ls2) (m := entryMemory)
      (dstId := 3) (x := t1) (old := none) rfl rfl
    exact evalStep_assign_usize 1 (coreLocalPlace 3)
      (.binaryOp .sub (.copy (coreLocalPlace 2)) (alignUsizeConst 1))
      vt1 ls1 ls2 rfl rfl rfl rfl hRv hW
  have hStep2 :
      evalStep (bodyProg bodyZerocopyRoundDown) 0 (mkState 0 2 ls2) =
        .step (mkState 0 3 ls3) := by
    have hRv := evalRvalue_unaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyRoundDown.locals) (ls := ls2) (m := entryMemory)
      (op := .not) (opnd := .copy (coreLocalPlace 3))
      (v := vt1) (res := vt2) rfl (evalUnOp_not_usize t1)
    have hW := writePlace_usize (ls := ls2) (ls' := ls3) (m := entryMemory)
      (dstId := 3) (x := t2) (old := some vt1) rfl rfl
    exact evalStep_assign_usize 2 (coreLocalPlace 3)
      (.unaryOp .not (.copy (coreLocalPlace 3)))
      vt2 ls2 ls3 rfl rfl rfl rfl hRv hW
  have hStep3 :
      evalStep (bodyProg bodyZerocopyRoundDown) 0 (mkState 0 3 ls3) =
        .step (mkState 0 4 ls4) := by
    have hRv := evalRvalue_binaryOp_usize (dstTy := alignUsizeTy)
      (tys := bodyZerocopyRoundDown.locals) (ls := ls3) (m := entryMemory)
      (op := .bitAnd) (lhs := .copy (coreLocalPlace 1))
      (rhs := .copy (coreLocalPlace 3)) (lVal := vN) (rVal := vt2)
      (res := vRet) rfl rfl (evalBinOp_bitAnd_usize n t2)
    have hW := writePlace_usize (ls := ls3) (ls' := ls4) (m := entryMemory)
      (dstId := 0) (x := roundDownFast n align) (old := none) rfl rfl
    exact evalStep_assign_usize 3 (coreLocalPlace 0)
      (.binaryOp .bitAnd (.copy (coreLocalPlace 1)) (.copy (coreLocalPlace 3)))
      vRet ls3 ls4 rfl rfl rfl rfl hRv hW
  have hStep4 :
      evalStep (bodyProg bodyZerocopyRoundDown) 0 (mkState 0 4 ls4) =
        .step (mkState 0 5 ls5) := rfl
  have hStep5 :
      evalStep (bodyProg bodyZerocopyRoundDown) 0 (mkState 0 5 ls5) =
        .done (.returned ⟨vRet, ⟨[]⟩⟩) := rfl
  change initState (bodyProg bodyZerocopyRoundDown)
    { args := [alignUsizeVal n, alignUsizeVal align] } =
      .ok (mkState 0 0 ls0) at hInit
  exact wpProg_of_executes hInit
    (.next hStep0 (.next hStep1 (.next hStep2 (.next hStep3
      (.next hStep4 (.ret hStep5))))))

/-- End-to-end MIR WP + mathematical alignment specification for the
hand-modeled 64-bit `usize` `bodyZerocopyRoundDown` across all
`n, align : BitVec 64` satisfying `isPow2BV align`. -/
theorem zerocopy_round_down_mir_spec (n align : BitVec 64)
    (hAlign : isPow2BV align) :
    let q : Query := { args := [alignUsizeVal n, alignUsizeVal align] }
    let r : BitVec 64 := roundDownFast n align
    WellFormed (bodyProg bodyZerocopyRoundDown) q ∧
    ¬ Diverges (bodyProg bodyZerocopyRoundDown) q ∧
    SatisfiesPost (bodyProg bodyZerocopyRoundDown) q
      (fun out => out = .returned ⟨alignUsizeVal r, ⟨[]⟩⟩) ∧
    r ≤ n ∧
    Nat.mod r.toNat align.toNat = 0 ∧
    n.toNat < r.toNat + align.toNat ∧
    (∀ m : BitVec 64, m ≤ n → Nat.mod m.toNat align.toNat = 0 → m ≤ r) := by
  let q : Query := { args := [alignUsizeVal n, alignUsizeVal align] }
  let ⟨fuel, hWp⟩ := bodyZerocopyRoundDown_wpProg n align
  let ⟨hSat, hNdiv, _, _, _⟩ :=
    wellFormed_and_spec_of_wp (bodyProg bodyZerocopyRoundDown) q fuel
      (fun out =>
        out = .returned ⟨alignUsizeVal (roundDownFast n align), ⟨[]⟩⟩)
      hWp
  let ⟨hLe, hMod, hLt, hMax⟩ := roundDownFast_spec_u64 hAlign n
  exact ⟨hSat.1, hNdiv, hSat, hLe, hMod, hLt, hMax⟩

private theorem bitVec64_toNat_of_lt {n : Nat} (hn : n < Nat.pow 2 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [Anneal.BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hn

/-- Explicit non-vacuity and concrete positive MIR execution witnesses on the
hand-modeled 64-bit `usize` bodies `bodyZerocopyPaddingNeededFor` (`(300, 32)
-> 20`, `(320, 32) -> 0`, and 64-bit `usize::MAX - 5` wraparound at `align =
16 -> 6`) and `bodyZerocopyRoundDown` (`(300, 32) -> 288`), plus
`PreconditionSatisfiable`. -/
theorem zerocopy_align_nonvacuity_canaries :
    PreconditionSatisfiable (fun args : BitVec 64 × BitVec 64 =>
      isPow2BV args.2) ∧
    PositiveCanaryClaim (bodyProg bodyZerocopyPaddingNeededFor)
      { args := [alignUsizeVal (BitVec.ofNat 64 300),
                 alignUsizeVal (BitVec.ofNat 64 32)] }
      (alignUsizeVal (BitVec.ofNat 64 20)) ∧
    PositiveCanaryClaim (bodyProg bodyZerocopyPaddingNeededFor)
      { args := [alignUsizeVal (BitVec.ofNat 64 320),
                 alignUsizeVal (BitVec.ofNat 64 32)] }
      (alignUsizeVal (BitVec.ofNat 64 0)) ∧
    PositiveCanaryClaim (bodyProg bodyZerocopyPaddingNeededFor)
      { args := [alignUsizeVal (BitVec.ofNat 64 18446744073709551610),
                 alignUsizeVal (BitVec.ofNat 64 16)] }
      (alignUsizeVal (BitVec.ofNat 64 6)) ∧
    PositiveCanaryClaim (bodyProg bodyZerocopyRoundDown)
      { args := [alignUsizeVal (BitVec.ofNat 64 300),
                 alignUsizeVal (BitVec.ofNat 64 32)] }
      (alignUsizeVal (BitVec.ofNat 64 288)) := by
  have hPow32 : isPow2BV (BitVec.ofNat 64 32) :=
    isPow2BV_ofNat_pow (w := 64) (k := 5) (by decide)
  have hPow16 : isPow2BV (BitVec.ofNat 64 16) :=
    isPow2BV_ofNat_pow (w := 64) (k := 4) (by decide)
  have hPreSat : PreconditionSatisfiable (fun args : BitVec 64 × BitVec 64 =>
      isPow2BV args.2) :=
    ⟨(BitVec.ofNat 64 300, BitVec.ofNat 64 32), hPow32⟩
  have hPad300 :
      paddingFast (BitVec.ofNat 64 300) (BitVec.ofNat 64 32) =
        BitVec.ofNat 64 20 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_paddingFast hPow32,
      bitVec64_toNat_of_lt (by decide : 300 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 32 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 20 < Nat.pow 2 64)]
    decide
  have hPad320 :
      paddingFast (BitVec.ofNat 64 320) (BitVec.ofNat 64 32) =
        BitVec.ofNat 64 0 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_paddingFast hPow32,
      bitVec64_toNat_of_lt (by decide : 320 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 32 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 0 < Nat.pow 2 64)]
    decide
  have hPadWrap :
      paddingFast (BitVec.ofNat 64 18446744073709551610) (BitVec.ofNat 64 16) =
        BitVec.ofNat 64 6 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_paddingFast hPow16,
      bitVec64_toNat_of_lt
        (by decide : 18446744073709551610 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 16 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 6 < Nat.pow 2 64)]
    decide
  have hRound300 :
      roundDownFast (BitVec.ofNat 64 300) (BitVec.ofNat 64 32) =
        BitVec.ofNat 64 288 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_roundDownFast_eq_div_mul hPow32,
      bitVec64_toNat_of_lt (by decide : 300 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 32 < Nat.pow 2 64),
      bitVec64_toNat_of_lt (by decide : 288 < Nat.pow 2 64)]
  let ⟨_, hWp1⟩ := bodyZerocopyPaddingNeededFor_wpProg
    (BitVec.ofNat 64 300) (BitVec.ofNat 64 32)
  rw [hPad300] at hWp1
  let ⟨_, hWp2⟩ := bodyZerocopyPaddingNeededFor_wpProg
    (BitVec.ofNat 64 320) (BitVec.ofNat 64 32)
  rw [hPad320] at hWp2
  let ⟨_, hWp3⟩ := bodyZerocopyPaddingNeededFor_wpProg
    (BitVec.ofNat 64 18446744073709551610) (BitVec.ofNat 64 16)
  rw [hPadWrap] at hWp3
  let ⟨_, hWp4⟩ := bodyZerocopyRoundDown_wpProg
    (BitVec.ofNat 64 300) (BitVec.ofNat 64 32)
  rw [hRound300] at hWp4
  exact ⟨hPreSat, positiveCanary_of_wp hWp1, positiveCanary_of_wp hWp2,
    positiveCanary_of_wp hWp3, positiveCanary_of_wp hWp4⟩

/-- Negative counterexamples showing why `isPow2BV align` is essential:
1. `align = 6` fails `isPow2BV`.
2. Executing `bodyZerocopyPaddingNeededFor` at `(len = 4, align = 6)` returns
   `4` (`(4 + 4) mod 6 = 2 ≠ 0`), refuting alignment congruence.
3. Executing `bodyZerocopyRoundDown` at `(n = 6, align = 6)` returns `2`
   (`2 mod 6 = 2 ≠ 0`), refuting alignment congruence. -/
theorem zerocopy_align_negative_counterexamples :
    ¬ isPow2BV (BitVec.ofNat 64 6) ∧
    ¬ SatisfiesPost (bodyProg bodyZerocopyPaddingNeededFor)
        { args := [alignUsizeVal (BitVec.ofNat 64 4),
                   alignUsizeVal (BitVec.ofNat 64 6)] }
        (fun out => ∃ r : BitVec 64,
          out = .returned ⟨alignUsizeVal r, ⟨[]⟩⟩ ∧
          Nat.mod (4 + r.toNat) 6 = 0) ∧
    ¬ SatisfiesPost (bodyProg bodyZerocopyRoundDown)
        { args := [alignUsizeVal (BitVec.ofNat 64 6),
                   alignUsizeVal (BitVec.ofNat 64 6)] }
        (fun out => ∃ r : BitVec 64,
          out = .returned ⟨alignUsizeVal r, ⟨[]⟩⟩ ∧
          Nat.mod r.toNat 6 = 0) := by
  have h6 : (BitVec.ofNat 64 6).toNat = 6 :=
    bitVec64_toNat_of_lt (by decide : 6 < Nat.pow 2 64)
  have h1 : (BitVec.ofNat 64 1).toNat = 1 :=
    bitVec64_toNat_of_lt (by decide : 1 < Nat.pow 2 64)
  have h5 : (BitVec.ofNat 64 6 - BitVec.ofNat 64 1).toNat = 5 := by
    have hLe : BitVec.ofNat 64 1 ≤ BitVec.ofNat 64 6 := by
      change (BitVec.ofNat 64 1).toNat ≤ (BitVec.ofNat 64 6).toNat
      rw [h1, h6]
      decide
    rw [Anneal.BitVec.toNat_sub_of_le hLe, h6, h1]
  have hNotPow6 : ¬ isPow2BV (BitVec.ofNat 64 6) := by
    intro hBad
    have hNat := congrArg BitVec.toNat hBad.2
    rw [Anneal.BitVec.toNat_and, h6, h5, Anneal.BitVec.toNat_zero] at hNat
    cases (by decide : Nat.land 6 5 = 4).symm.trans hNat
  have hPad46 :
      paddingFast (BitVec.ofNat 64 4) (BitVec.ofNat 64 6) =
        BitVec.ofNat 64 4 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    unfold paddingFast
    have h4 : (BitVec.ofNat 64 4).toNat = 4 :=
      bitVec64_toNat_of_lt (by decide : 4 < Nat.pow 2 64)
    have h3 : (BitVec.ofNat 64 4 - BitVec.ofNat 64 1).toNat = 3 := by
      have hLe : BitVec.ofNat 64 1 ≤ BitVec.ofNat 64 4 := by
        change (BitVec.ofNat 64 1).toNat ≤ (BitVec.ofNat 64 4).toNat
        rw [h1, h4]
        decide
      rw [Anneal.BitVec.toNat_sub_of_le hLe, h4, h1]
    have hNot3 :
        (Anneal.BitVec.not (BitVec.ofNat 64 4 - BitVec.ofNat 64 1)).toNat =
          Nat.pow 2 64 - 4 := by
      rw [Anneal.BitVecArith.toNat_not_eq_sub, h3, Nat.sub_sub,
        Nat.add_comm 1 3]
    rw [Anneal.BitVec.toNat_and, hNot3, h5, h4]
    decide
  have hRound66 :
      roundDownFast (BitVec.ofNat 64 6) (BitVec.ofNat 64 6) =
        BitVec.ofNat 64 2 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    unfold roundDownFast
    have h2 : (BitVec.ofNat 64 2).toNat = 2 :=
      bitVec64_toNat_of_lt (by decide : 2 < Nat.pow 2 64)
    have hNot5 :
        (Anneal.BitVec.not (BitVec.ofNat 64 6 - BitVec.ofNat 64 1)).toNat =
          Nat.pow 2 64 - 6 := by
      rw [Anneal.BitVecArith.toNat_not_eq_sub, h5, Nat.sub_sub,
        Nat.add_comm 1 5]
    rw [Anneal.BitVec.toNat_and, h6, hNot5, h2]
    decide
  have hNegPad :
      ¬ SatisfiesPost (bodyProg bodyZerocopyPaddingNeededFor)
          { args := [alignUsizeVal (BitVec.ofNat 64 4),
                     alignUsizeVal (BitVec.ofNat 64 6)] }
          (fun out => ∃ r : BitVec 64,
            out = .returned ⟨alignUsizeVal r, ⟨[]⟩⟩ ∧
            Nat.mod (4 + r.toNat) 6 = 0) := by
    intro hSat
    let ⟨_, hWp⟩ := bodyZerocopyPaddingNeededFor_wpProg
      (BitVec.ofNat 64 4) (BitVec.ofNat 64 6)
    let ⟨_, hBeh, _, _⟩ := spec_and_behavior_of_wp_eq hWp
    let ⟨r, hrEq, hrMod⟩ := hSat.2 _ hBeh
    rw [hPad46] at hrEq
    injection hrEq with hRes
    injection hRes with hVal _
    have hr := alignUsizeVal_inj hVal
    subst hr
    rw [bitVec64_toNat_of_lt (by decide : 4 < Nat.pow 2 64)] at hrMod
    exact False.elim ((by decide : Nat.mod (4 + 4) 6 ≠ 0) hrMod)
  have hNegRound :
      ¬ SatisfiesPost (bodyProg bodyZerocopyRoundDown)
          { args := [alignUsizeVal (BitVec.ofNat 64 6),
                     alignUsizeVal (BitVec.ofNat 64 6)] }
          (fun out => ∃ r : BitVec 64,
            out = .returned ⟨alignUsizeVal r, ⟨[]⟩⟩ ∧
            Nat.mod r.toNat 6 = 0) := by
    intro hSat
    let ⟨_, hWp⟩ := bodyZerocopyRoundDown_wpProg
      (BitVec.ofNat 64 6) (BitVec.ofNat 64 6)
    let ⟨_, hBeh, _, _⟩ := spec_and_behavior_of_wp_eq hWp
    let ⟨r, hrEq, hrMod⟩ := hSat.2 _ hBeh
    rw [hRound66] at hrEq
    injection hrEq with hRes
    injection hRes with hVal _
    have hr := alignUsizeVal_inj hVal
    subst hr
    rw [bitVec64_toNat_of_lt (by decide : 2 < Nat.pow 2 64)] at hrMod
    exact False.elim ((by decide : Nat.mod 2 6 ≠ 0) hrMod)
  exact ⟨hNotPow6, hNegPad, hNegRound⟩

/-! ## Zerocopy Bit-Validity & Trait Canaries (`Core.BitValidity`) -/

/-- Two-variant `#[repr(u8)]` enum `{ A = 0, B = 1 }`: `FromZeros`,
`IntoBytes`, `Unaligned`, `TryFromBytes`, and `¬ FromBytes`. -/
@[expose] def canaryTwoVarU8Enum : EnumTy where
  id := 9001
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [0, 1]

/-- Non-zero-discriminant `#[repr(u8)]` enum `{ A = 1, B = 2 }`:
`IntoBytes`, `Unaligned`, `TryFromBytes`, `¬ FromZeros`, and `¬ FromBytes`. -/
@[expose] def canaryNonZeroU8Enum : EnumTy where
  id := 9002
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [1, 2]

/-- Exhaustive `256`-variant `#[repr(u8)]` enum (`0..255`): satisfies all five
traits (`FromBytes`, `FromZeros`, `IntoBytes`, `TryFromBytes`, `Unaligned`). -/
@[expose] def canaryExhaustiveU8Enum : EnumTy where
  id := 9003
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := natRangeFrom 0 256

/-- Single-variant zero-sized enum `enum SingleZst { Only }`: satisfies all
five traits. -/
@[expose] def canarySingleZstEnum : EnumTy where
  id := 9004
  discrWidth := .isize
  discrSigned := true
  tagRepr := .zeroSized
  discriminants := [0]

/-- Primitive trait classification canaries: `bool`, `char`, `Ordering`,
integers, `()`, and `!` across both byte orders. -/
theorem canary_bitValidity_primitives (endian : TargetEndian) :
    (IsIntoBytes endian .bool ∧ IsFromZeros endian .bool ∧ IsUnaligned .bool ∧
      IsExactTryFromBytes endian .bool (scalarCheck endian boolValid) ∧
      ¬ IsFromBytes endian .bool) ∧
    (IsIntoBytes endian .char ∧ IsFromZeros endian .char ∧ ¬ IsUnaligned .char ∧
      IsExactTryFromBytes endian .char (scalarCheck endian isUnicodeScalar) ∧
      ¬ IsFromBytes endian .char) ∧
    (IsIntoBytes endian .ordering ∧ IsFromZeros endian .ordering ∧
      IsUnaligned .ordering ∧
      IsExactTryFromBytes endian .ordering (scalarCheck endian orderingValid) ∧
      ¬ IsFromBytes endian .ordering) ∧
    (IsFromBytes endian (.int .i32 false) ∧
      IsFromZeros endian (.int .i32 false) ∧
      IsIntoBytes endian (.int .i32 false) ∧
      ¬ IsUnaligned (.int .i32 false)) ∧
    (IsFromBytes endian .unit ∧ IsIntoBytes endian .unit ∧ IsUnaligned .unit) ∧
    (IsIntoBytes endian .never ∧
      IsExactTryFromBytes endian .never (fun _ => false) ∧
      IsUnaligned .never ∧ ¬ IsFromZeros endian .never ∧
      ¬ IsFromBytes endian .never) :=
  ⟨⟨bool_isIntoBytes endian, bool_isFromZeros endian, bool_isUnaligned,
    bool_isExactTryFromBytes endian, bool_not_isFromBytes endian⟩,
   ⟨char_isIntoBytes endian, char_isFromZeros endian, char_not_isUnaligned,
    char_isExactTryFromBytes endian, char_not_isFromBytes endian⟩,
   ⟨ordering_isIntoBytes endian, ordering_isFromZeros endian,
    ordering_isUnaligned, ordering_isExactTryFromBytes endian,
    ordering_not_isFromBytes endian⟩,
   ⟨int_isFromBytes endian .i32 false, int_isFromZeros endian .i32 false,
    int_isIntoBytes endian .i32 false,
    int_not_isUnaligned_of_ne_i8 (fun h => by nomatch h) false⟩,
   ⟨unit_isFromBytes endian, unit_isIntoBytes endian, unit_isUnaligned⟩,
   ⟨never_isIntoBytes endian, never_isExactTryFromBytes endian, never_isUnaligned,
    never_not_isFromZeros endian, never_not_isFromBytes endian⟩⟩

/-- Overflow-pair canaries. Overflow pairs have no addressable layout, so even
padding-free `(u8, bool)` satisfies none of the modeled `zerocopy` traits
(blocking, for example, a `(u8, bool)` to `u16` transmutation). Profile v1's
local-slot representation still has the analogous internal facts: all-zero bytes
decode, not every initialized byte sequence decodes, `overflowPairCheck`
recognizes exactly the bit-valid initialized bytes, the `(u8, bool)` encoding
is fully initialized, and the `(u32, bool)` encoding embeds `3` `.uninit`
padding bytes, so it is `.bitValid` without being `.initialized`. -/
theorem canary_bitValidity_overflowPairs (endian : TargetEndian) :
    (∀ tr : ZerocopyTrait,
      ¬ ValidForTrait tr endian (.tuple [.int .i8 false, .bool]) ∧
        ¬ ValidForTrait tr endian (.tuple [.int .i32 false, .bool])) ∧
    (∃ v, decodeVal endian (.tuple [.int .i32 false, .bool])
      (zeroInitBytes (overflowPairLayout .i32).size) = .ok (some v)) ∧
    (¬ ∀ bs,
        bs.length = (overflowPairLayout .i8).size →
        AllBytesInit bs →
        ∃ v, decodeVal endian (.tuple [.int .i8 false, .bool]) bs =
          .ok (some v)) ∧
    (∀ bs,
      ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .initialized bs →
      (overflowPairCheck endian .i32 bs = true ↔
        ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .bitValid bs)) ∧
    ((∀ v bs,
        encodeVal endian (.tuple [.int .i8 false, .bool]) v = .ok bs →
        AllBytesInit bs) ∧
      ¬ ∀ v bs,
        encodeVal endian (.tuple [.int .i32 false, .bool]) v = .ok bs →
        AllBytesInit bs) ∧
    (∃ bs : List AllocByte,
      encodeVal endian (.tuple [.int .i32 false, .bool])
          (.tuple [.scalar ⟨.i32, false, 0⟩, .bool false]) = .ok bs ∧
        ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .bitValid bs ∧
        ¬ ByteSeqValid endian (.tuple [.int .i32 false, .bool])
            .initialized bs) :=
  ⟨fun tr => ⟨overflowPair_not_validForTrait tr endian .i8 false,
    overflowPair_not_validForTrait tr endian .i32 false⟩,
   overflowPair_localSlot_zero_decodes endian .i32 false,
   overflowPair_localSlot_not_allInitDecode endian .i8 false,
   overflowPair_localSlotCheck_exact endian .i32 false,
   ⟨(overflowPair_encodeVal_allBytesInit_iff endian .i8 false).2 rfl,
    fun h => nomatch (overflowPair_encodeVal_allBytesInit_iff endian .i32 false).1 h⟩,
   byteSeqValid_bitValid_not_implies_initialized_overflowPair endian⟩

/-- `AsInitialized` canaries (`ByteSeqValid … .asInitialized`): the encoded
`(0 : u32, false)` pair with `3` `.uninit` padding bytes is accepted; `8`
`.uninit` bytes at `(u32, bool)` are rejected because every valid pair
initializes its `u32` bytes; a pair with invalid `bool` byte `0x02` and
`.uninit` padding is accepted without being `.bitValid`; and initialized `bool`
byte `0x02` is accepted without being `.bitValid`. -/
theorem canary_bitValidity_asInitialized (endian : TargetEndian) :
    ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .asInitialized
        [.init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .uninit, .uninit, .uninit] ∧
      ¬ ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .asInitialized
        (List.replicate 8 AllocByte.uninit) ∧
      ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .asInitialized
        [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init (UInt8.ofNat 2) none, .uninit, .uninit, .uninit] ∧
      ¬ ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .bitValid
        [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init (UInt8.ofNat 2) none, .uninit, .uninit, .uninit] ∧
      ByteSeqValid endian .bool .asInitialized [.init (UInt8.ofNat 2) none] ∧
      ¬ ByteSeqValid endian .bool .bitValid [.init (UInt8.ofNat 2) none] :=
  ⟨byteSeqValid_asInitialized_overflowPair_padded endian,
   byteSeqValid_asInitialized_overflowPair_uninit_false endian,
   (byteSeqValid_asInitialized_overflowPair_invalidBool endian).1,
   (byteSeqValid_asInitialized_overflowPair_invalidBool endian).2,
   (byteSeqValid_asInitialized_not_implies_bitValid_bool endian).1,
   (byteSeqValid_asInitialized_not_implies_bitValid_bool endian).2⟩

/-- `TryFromBytes` validator canaries: accepting every candidate is unsound for
`bool` and rejecting every candidate is sound but inexact; the exact `bool`
validator accepts byte `0x01`, rejects byte `0x02`, and its acceptance yields
bit-validity (`try_from_bytes_sound`). -/
theorem canary_bitValidity_tryFromBytes (endian : TargetEndian) :
    ¬ IsTryFromBytes endian .bool (fun _ => true) ∧
      IsTryFromBytes endian .bool (fun _ => false) ∧
      ¬ IsExactTryFromBytes endian .bool (fun _ => false) ∧
      scalarCheck endian boolValid [.init 1 none] = true ∧
      scalarCheck endian boolValid [.init (UInt8.ofNat 2) none] = false ∧
      ByteSeqValid endian .bool .bitValid [.init 1 none] := by
  have hT : scalarCheck endian boolValid [.init 1 none] = true := by
    cases endian <;> rfl
  refine ⟨bool_not_isTryFromBytes_true endian,
    isTryFromBytes_false endian (layout := ⟨1, 0⟩) rfl,
    bool_not_isExactTryFromBytes_false endian, hT,
    by cases endian <;> rfl, ?_⟩
  exact try_from_bytes_sound
    (isExactTryFromBytes_implies_isTryFromBytes (bool_isExactTryFromBytes endian))
    ⟨⟨1, 0⟩, rfl, rfl, rfl⟩ hT

/-- Enum bit-validity canaries: `2`-variant `u8` (`FromZeros`, `¬ FromBytes`),
non-zero `2`-variant `u8` (`¬ FromZeros`), `256`-variant exhaustive `u8`
(`FromBytes`), and `1`-variant ZST enum (all 5 traits). -/
theorem canary_bitValidity_enums (endian : TargetEndian) :
    (IsFromZeros endian (.enum canaryTwoVarU8Enum) ∧
      IsIntoBytes endian (.enum canaryTwoVarU8Enum) ∧
      IsUnaligned (.enum canaryTwoVarU8Enum) ∧
      IsExactTryFromBytes endian (.enum canaryTwoVarU8Enum)
        (scalarCheck endian (enumTagValid canaryTwoVarU8Enum .i8 false)) ∧
      ¬ IsFromBytes endian (.enum canaryTwoVarU8Enum)) ∧
    (¬ IsFromZeros endian (.enum canaryNonZeroU8Enum) ∧
      IsIntoBytes endian (.enum canaryNonZeroU8Enum) ∧
      ¬ IsFromBytes endian (.enum canaryNonZeroU8Enum)) ∧
    (IsFromBytes endian (.enum canaryExhaustiveU8Enum) ∧
      IsFromZeros endian (.enum canaryExhaustiveU8Enum) ∧
      IsIntoBytes endian (.enum canaryExhaustiveU8Enum) ∧
      IsUnaligned (.enum canaryExhaustiveU8Enum) ∧
      IsExactTryFromBytes endian (.enum canaryExhaustiveU8Enum)
        (fun _ => true)) ∧
    (IsFromBytes endian (.enum canarySingleZstEnum) ∧
      IsFromZeros endian (.enum canarySingleZstEnum) ∧
      IsIntoBytes endian (.enum canarySingleZstEnum) ∧
      IsUnaligned (.enum canarySingleZstEnum) ∧
      IsExactTryFromBytes endian (.enum canarySingleZstEnum)
        (fun _ => true)) := by
  have h2Adm : enumAdmitted canaryTwoVarU8Enum = true := by rfl
  have h2FzBool : isFromZerosEnum canaryTwoVarU8Enum = true := by rfl
  have h2Fz : IsFromZeros endian (.enum canaryTwoVarU8Enum) :=
    (enum_isFromZeros_iff endian canaryTwoVarU8Enum).mpr h2FzBool
  have h2NotFb : ¬ IsFromBytes endian (.enum canaryTwoVarU8Enum) :=
    scalarEnum_not_isFromBytes_of_invalid_tag endian canaryTwoVarU8Enum
      .i8 false h2Adm rfl 2 (by decide) (by rfl)
  have hNzAdm : enumAdmitted canaryNonZeroU8Enum = true := by rfl
  have hNzFzBool : isFromZerosEnum canaryNonZeroU8Enum = false := by rfl
  have hNzNotFz : ¬ IsFromZeros endian (.enum canaryNonZeroU8Enum) := by
    intro hFz
    have hEq := (enum_isFromZeros_iff endian canaryNonZeroU8Enum).mp hFz
    rw [hNzFzBool] at hEq
    nomatch hEq
  have hNzNotFb : ¬ IsFromBytes endian (.enum canaryNonZeroU8Enum) :=
    scalarEnum_not_isFromBytes_of_invalid_tag endian canaryNonZeroU8Enum
      .i8 false hNzAdm rfl 0 (by decide) (by rfl)
  have h256Adm : enumAdmitted canaryExhaustiveU8Enum = true :=
    u8ExhaustiveEnum_enumAdmitted canaryExhaustiveU8Enum rfl rfl
  have h256Bool : isFromBytesEnum canaryExhaustiveU8Enum = true :=
    u8ExhaustiveEnum_isFromBytesEnum canaryExhaustiveU8Enum rfl rfl
  have h256Fb : IsFromBytes endian (.enum canaryExhaustiveU8Enum) :=
    isFromBytesEnum_sound endian canaryExhaustiveU8Enum h256Bool
  have hZstAdm : enumAdmitted canarySingleZstEnum = true := by rfl
  exact ⟨⟨h2Fz,
          scalarEnum_isIntoBytes endian canaryTwoVarU8Enum .i8 false h2Adm rfl,
          (scalarEnum_isUnaligned_iff canaryTwoVarU8Enum .i8 false
            h2Adm rfl).mpr rfl,
          scalarEnum_isExactTryFromBytes endian canaryTwoVarU8Enum .i8 false
            h2Adm rfl,
          h2NotFb⟩,
         ⟨hNzNotFz,
          scalarEnum_isIntoBytes endian canaryNonZeroU8Enum .i8 false
            hNzAdm rfl,
          hNzNotFb⟩,
         ⟨h256Fb, isFromBytes_implies_isFromZeros endian _ h256Fb,
          scalarEnum_isIntoBytes endian canaryExhaustiveU8Enum .i8 false
            h256Adm rfl,
          (scalarEnum_isUnaligned_iff canaryExhaustiveU8Enum .i8 false
            h256Adm rfl).mpr rfl,
          isFromBytes_implies_isExactTryFromBytes endian _ h256Fb⟩,
         ⟨zstEnum_isFromBytes endian canarySingleZstEnum hZstAdm rfl,
          zstEnum_isFromZeros endian canarySingleZstEnum hZstAdm rfl,
          zstEnum_isIntoBytes endian canarySingleZstEnum hZstAdm rfl,
          zstEnum_isUnaligned canarySingleZstEnum hZstAdm rfl,
          zstEnum_isExactTryFromBytes endian canarySingleZstEnum hZstAdm rfl⟩⟩

/-- Equal-size transmutation canaries: `bool -> u8`, `Ordering -> i8`,
`TwoVarU8 -> u8`, `char -> u32`, `u32 -> i32`, and `SingleZst <-> ()`. -/
theorem canary_bitValidity_transmutes (endian : TargetEndian) :
    (∀ b bs, encodeVal endian .bool (.bool b) = .ok bs →
      NoProvBytes bs ∧
        ∃ v', decodeVal endian (.int .i8 false) bs = .ok (some v')) ∧
    (∀ ord bs, encodeVal endian .ordering (.ordering ord) = .ok bs →
      NoProvBytes bs ∧
        ∃ v', decodeVal endian (.int .i8 true) bs = .ok (some v')) ∧
    (∀ idx bs, encodeVal endian (.enum canaryTwoVarU8Enum)
        (.enumVal canaryTwoVarU8Enum idx) = .ok bs →
      NoProvBytes bs ∧
        ∃ v', decodeVal endian (.int .i8 false) bs = .ok (some v')) ∧
    (∀ c bs, encodeVal endian .char (.char c) = .ok bs →
      NoProvBytes bs ∧
        ∃ v', decodeVal endian (.int .i32 false) bs = .ok (some v')) ∧
    (∀ sv bs, encodeVal endian (.int .i32 false) (.scalar sv) = .ok bs →
      NoProvBytes bs ∧
        ∃ v', decodeVal endian (.int .i32 true) bs = .ok (some v')) ∧
    (∀ bs, encodeVal endian (.enum canarySingleZstEnum)
        (.enumVal canarySingleZstEnum 0) = .ok bs →
      NoProvBytes bs ∧ ∃ v', decodeVal endian .unit bs = .ok (some v')) ∧
    (∀ bs, encodeVal endian .unit .unit = .ok bs →
      NoProvBytes bs ∧
        ∃ v',
          decodeVal endian (.enum canarySingleZstEnum) bs = .ok (some v')) :=
  ⟨fun b bs h => transmute_bool_to_i8_sound endian false (.bool b) bs h,
   fun ord bs h =>
     transmute_ordering_to_i8_sound endian true (.ordering ord) bs h,
   fun idx bs h =>
     transmute_scalarEnum_i8_to_i8_sound endian canaryTwoVarU8Enum false false
       (by rfl) rfl (.enumVal canaryTwoVarU8Enum idx) bs h,
   fun c bs h => transmute_char_to_i32_sound endian false (.char c) bs h,
   fun sv bs h =>
     transmute_int_to_int_sound endian .i32 .i32 false true rfl
       (.scalar sv) bs h,
   fun bs h =>
     transmute_zstEnum_to_unit_sound endian canarySingleZstEnum (by rfl) rfl
       (.enumVal canarySingleZstEnum 0) bs h,
   fun bs h =>
     transmute_unit_to_zstEnum_sound endian canarySingleZstEnum (by rfl) rfl
       .unit bs h⟩

/-! ## Zerocopy `FixedByteCodec` & Padding Canaries (`Core.FixedByteCodec`) -/

/-- Unpadded 8-byte struct model `(u32, u16, u16)` under `endian`: satisfies
`IsInitCodec`, `NoProvCodec`, `IsSurjectiveInitDecoder`, and `HasZeroValid`.
-/
@[expose] def unpaddedTripleCodec (endian : TargetEndian) :
    FixedByteCodec (BitVec 32 × (BitVec 16 × BitVec 16)) 8 :=
  FixedByteCodec.prod (u32Codec endian)
    (FixedByteCodec.prod (u16Codec endian) (u16Codec endian))

/-- Padded 8-byte struct model `(u32, u8, 3-byte .uninit pad)` under `endian`:
satisfies `HasZeroValid` and `IsSurjectiveInitDecoder`, yet refutes
`IsInitCodec`. -/
@[expose] def paddedPairCodec (endian : TargetEndian) :
    FixedByteCodec (BitVec 32 × BitVec 8) 8 :=
  FixedByteCodec.padRight
    (FixedByteCodec.prod (u32Codec endian) (u8Codec endian)) 3

/-- Exact-width (`n = 0` and `n > 0`), endian `LeBytes` / `MirSemantics.Bytes`
agreement, and prefix-free `sliceBytes` framing canaries. -/
theorem canary_fixedByteCodec_width_and_endian (endian : TargetEndian) :
    ((∀ bs : List AllocByte, bs ≠ [] → FixedByteCodec.zst.decode bs = none) ∧
      FixedByteCodec.zst.decode [] = some () ∧
      FixedByteCodec.zst.decode [.init 0 none] = none ∧
      FixedByteCodec.zst.decode [.uninit] = none) ∧
    ((∀ (bs : List AllocByte) (x : BitVec 32),
        (u32Codec endian).decode bs = some x → bs.length = 4) ∧
      (u32Codec endian).decode [.init 1 none, .init 2 none, .init 3 none] =
        none ∧
      (u32Codec endian).decode
          [.init 1 none, .init 2 none, .init 3 none, .init 4 none,
           .init 5 none] = none ∧
      (u32Codec endian).decode
          [.init 1 none, .init 2 none, .init 3 none, .uninit] = none) ∧
    ((u32Codec .little).encode (BitVec.ofNat 32 0x12345678) =
        [.init 0x78 none, .init 0x56 none, .init 0x34 none, .init 0x12 none] ∧
      (u32Codec .big).encode (BitVec.ofNat 32 0x12345678) =
        [.init 0x12 none, .init 0x34 none, .init 0x56 none, .init 0x78 none]) ∧
    (∀ pre post x,
      (sliceBytes (pre ++ (u32Codec endian).encode x ++ post)
        pre.length 4).bind (u32Codec endian).decode = some x) := by
  have hZst :
      (∀ bs : List AllocByte, bs ≠ [] → FixedByteCodec.zst.decode bs = none) ∧
        FixedByteCodec.zst.decode [] = some () ∧
        FixedByteCodec.zst.decode [.init 0 none] = none ∧
        FixedByteCodec.zst.decode [.uninit] = none :=
    ⟨fun _ h => FixedByteCodec.zst.rejects_nonempty_of_zero h, rfl, rfl, rfl⟩
  have hU32Exact :
      ∀ (bs : List AllocByte) (x : BitVec 32),
        (u32Codec endian).decode bs = some x → bs.length = 4 :=
    fun _ _ h => (u32Codec endian).decode_length h
  have hU32Bad :
      (u32Codec endian).decode [.init 1 none, .init 2 none, .init 3 none] =
          none ∧
        (u32Codec endian).decode
            [.init 1 none, .init 2 none, .init 3 none, .init 4 none,
             .init 5 none] = none ∧
        (u32Codec endian).decode
            [.init 1 none, .init 2 none, .init 3 none, .uninit] = none := by
    refine ⟨(u32Codec endian).rejects_short (by decide),
      (u32Codec endian).rejects_long (by decide), ?_⟩
    cases endian <;> rfl
  have hEnd :
      (u32Codec .little).encode (BitVec.ofNat 32 0x12345678) =
          [.init 0x78 none, .init 0x56 none, .init 0x34 none, .init 0x12 none] ∧
        (u32Codec .big).encode (BitVec.ofNat 32 0x12345678) =
          [.init 0x12 none, .init 0x34 none, .init 0x56 none,
           .init 0x78 none] := by
    constructor <;> rfl
  refine ⟨hZst, ⟨hU32Exact, hU32Bad⟩, hEnd, fun pre post x => ?_⟩
  exact (u32Codec endian).decode_sliceBytes_append pre post x

/-- Homogeneous `[u16; 4]` (`8`-byte) array codec canaries: exact width, total
init encoding/decoding, `ListChunks.chunksOf 2` indexing, per-element slice
recovery, and `.uninit` element rejection. -/
theorem canary_fixedByteCodec_array_u16_4 (endian : TargetEndian) :
    (∀ bs : List AllocByte, bs.length ≠ 8 →
      (FixedByteCodec.array 4 (u16Codec endian)).decode bs = none) ∧
    (FixedByteCodec.array 4 (u16Codec endian)).IsInitCodec ∧
    (FixedByteCodec.array 4 (u16Codec endian)).NoProvCodec ∧
    (FixedByteCodec.array 4 (u16Codec endian)).IsSurjectiveInitDecoder ∧
    (FixedByteCodec.array 4 (u16Codec endian)).HasZeroValid ∧
    (∀ (xs : Subtype (fun xs : List (BitVec 16) => xs.length = 4)) (i : Nat)
        (x : BitVec 16),
      xs.val[i]? = some x →
      (((FixedByteCodec.array 4 (u16Codec endian)).encode xs).drop (i * 2)).take
          2 = (u16Codec endian).encode x ∧
        (Anneal.ListChunks.chunksOf 2
          ((FixedByteCodec.array 4 (u16Codec endian)).encode xs))[i]? =
          some ((u16Codec endian).encode x)) ∧
    ((FixedByteCodec.array 4 (u16Codec endian)).decode
        [.init 0 none, .init 1 none, .init 2 none, .init 3 none,
         .init 4 none, .uninit, .init 6 none, .init 7 none] = none) := by
  have hExact :
      ∀ bs : List AllocByte, bs.length ≠ 8 →
        (FixedByteCodec.array 4 (u16Codec endian)).decode bs = none :=
    fun _ h => (FixedByteCodec.array 4 (u16Codec endian)).rejects_ne h
  have hInit : (FixedByteCodec.array 4 (u16Codec endian)).IsInitCodec :=
    FixedByteCodec.array_isInitCodec 4
      (uintBvCodec_isInitCodec endian 2 (by decide))
  have hNoProv : (FixedByteCodec.array 4 (u16Codec endian)).NoProvCodec :=
    FixedByteCodec.array_noProvCodec 4
      (uintBvCodec_noProvCodec endian 2 (by decide))
  have hSurj :
      (FixedByteCodec.array 4 (u16Codec endian)).IsSurjectiveInitDecoder :=
    FixedByteCodec.array_isSurjectiveInitDecoder
      (uintBvCodec_isSurjectiveInitDecoder endian 2 (by decide)) 4
  have hZero : (FixedByteCodec.array 4 (u16Codec endian)).HasZeroValid :=
    hSurj.hasZeroValid
  refine ⟨hExact, hInit, hNoProv, hSurj, hZero, ?_, ?_⟩
  · intro xs i x hGet
    refine ⟨FixedByteCodec.encodeElems_drop_take_of_getElem?
        (u16Codec endian) hGet, ?_⟩
    rw [FixedByteCodec.chunksOf_array_encode_getElem? (by decide : 0 < 2)
        4 (u16Codec endian) xs i, hGet]
    rfl
  · cases endian <;> rfl

/-- Equal-size `8`-byte struct transmutation and padding canaries:
- `MirBytesCodec` instances realize `unit`, `bool` (`¬ FromBytes`), and `u64`
  traits across both byte orders.
- Unpadded `(u32, u16, u16)` satisfies `IsInitCodec` and
  `IsSurjectiveInitDecoder`, transmuting soundly both ways with `u64`
  (`MirTy.int .i64 false`) and into `[u16; 4]` and `(u32, u8, 3-byte pad)`.
- Padded `(u32, u8, 3-byte pad)` preserves `HasZeroValid` (`FromZeros`) and
  `IsSurjectiveInitDecoder` (`FromBytes`), accepts `.uninit` in its 3 padding
  bytes on `decode`, yet refutes `IsInitCodec` (`IntoBytes`) and fails
  transmutation to `unpaddedTripleCodec`, `[u16; 4]`, and `u64`
  (`decodeVal = .ok none`). This mirrors the padding contrast between the
  Profile v1 local-slot encodings of `(u8, bool)` and `(u32, bool)`, although
  overflow pairs have no addressable layout and are never `IntoBytes` or
  transmutable. -/
theorem canary_fixedByteCodec_padding_and_transmute (endian : TargetEndian) :
    (IsIntoBytes endian .unit ∧ IsFromBytes endian .unit) ∧
    (IsIntoBytes endian .bool ∧ IsFromZeros endian .bool ∧
      ¬ IsFromBytes endian .bool) ∧
    (IsIntoBytes endian (.int .i64 false) ∧
      IsFromBytes endian (.int .i64 false)) ∧
    ((unpaddedTripleCodec endian).IsInitCodec ∧
      (unpaddedTripleCodec endian).IsSurjectiveInitDecoder ∧
      CodecTransmuteSound (unpaddedTripleCodec endian)
        (FixedByteCodec.array 4 (u16Codec endian)) ∧
      CodecTransmuteSound (unpaddedTripleCodec endian)
        (paddedPairCodec endian) ∧
      (∀ x, NoProvBytes ((unpaddedTripleCodec endian).encode x) ∧
        ∃ v', decodeVal endian (.int .i64 false)
          ((unpaddedTripleCodec endian).encode x) = .ok (some v')) ∧
      (∀ v bs, encodeVal endian (.int .i64 false) v = .ok bs →
        NoProvBytes bs ∧
          ∃ p, (unpaddedTripleCodec endian).decode bs = some p)) ∧
    ((∀ bs : List AllocByte, bs.length < 8 →
        (paddedPairCodec endian).decode bs = none) ∧
      (paddedPairCodec endian).HasZeroValid ∧
      (paddedPairCodec endian).IsSurjectiveInitDecoder ∧
      (paddedPairCodec endian).decode
        ((u32Codec endian).encode (BitVec.ofNat 32 7) ++
          (u8Codec endian).encode (BitVec.ofNat 8 9) ++
          [.uninit, .uninit, .uninit]) =
        some (BitVec.ofNat 32 7, BitVec.ofNat 8 9) ∧
      (∀ v bs, encodeVal endian (.int .i64 false) v = .ok bs →
        NoProvBytes bs ∧
          ∃ p, (paddedPairCodec endian).decode bs = some p) ∧
      ¬ (paddedPairCodec endian).IsInitCodec ∧
      (unpaddedTripleCodec endian).decode
        ((paddedPairCodec endian).encode
          (BitVec.ofNat 32 0x11223344, BitVec.ofNat 8 0x55)) = none ∧
      (FixedByteCodec.array 4 (u16Codec endian)).decode
        ((paddedPairCodec endian).encode
          (BitVec.ofNat 32 0x11223344, BitVec.ofNat 8 0x55)) = none ∧
      (∀ a b s,
        decodeVal endian (.int .i64 s)
          ((paddedPairCodec endian).encode (a, b)) = .ok none)) ∧
    ((overflowPairCodec endian .i8).IsInitCodec ∧
      ¬ (overflowPairCodec endian .i32).IsInitCodec) := by
  have hUnitInto := (MirBytesCodec.unit endian).isIntoBytes
    FixedByteCodec.zst_isInitCodec
  have hUnitFrom := (MirBytesCodec.unit endian).isFromBytes
    FixedByteCodec.zst_isSurjectiveInitDecoder
  have hBoolInto := (MirBytesCodec.bool endian).isIntoBytes boolCodec_isInitCodec
  have hBoolFz := (MirBytesCodec.bool endian).isFromZeros boolCodec_hasZeroValid
  have hBoolNotFrom := (MirBytesCodec.bool endian).not_isFromBytes_of_rejected_init
    (bs := [.init 2 none]) rfl rfl (by rfl)
  let hU64M := MirBytesCodec.int endian .i64 false
  have hU64Into := hU64M.isIntoBytes
    (uintBvCodec_isInitCodec endian (fbcByteSize .i64) (fbcByteSize_pos .i64))
  have hU64From := hU64M.isFromBytes
    (uintBvCodec_isSurjectiveInitDecoder endian (fbcByteSize .i64)
      (fbcByteSize_pos .i64))
  have hUnpInit : (unpaddedTripleCodec endian).IsInitCodec :=
    FixedByteCodec.prod_isInitCodec
      (uintBvCodec_isInitCodec endian 4 (by decide))
      (FixedByteCodec.prod_isInitCodec
        (uintBvCodec_isInitCodec endian 2 (by decide))
        (uintBvCodec_isInitCodec endian 2 (by decide)))
  have hUnpNoProv : (unpaddedTripleCodec endian).NoProvCodec :=
    FixedByteCodec.prod_noProvCodec
      (uintBvCodec_noProvCodec endian 4 (by decide))
      (FixedByteCodec.prod_noProvCodec
        (uintBvCodec_noProvCodec endian 2 (by decide))
        (uintBvCodec_noProvCodec endian 2 (by decide)))
  have hUnpSurj : (unpaddedTripleCodec endian).IsSurjectiveInitDecoder :=
    FixedByteCodec.prod_isSurjectiveInitDecoder
      (uintBvCodec_isSurjectiveInitDecoder endian 4 (by decide))
      (FixedByteCodec.prod_isSurjectiveInitDecoder
        (uintBvCodec_isSurjectiveInitDecoder endian 2 (by decide))
        (uintBvCodec_isSurjectiveInitDecoder endian 2 (by decide)))
  have hArrSurj := FixedByteCodec.array_isSurjectiveInitDecoder
    (uintBvCodec_isSurjectiveInitDecoder endian 2 (by decide)) 4
  have hPadCoreSurj :
      (FixedByteCodec.prod (u32Codec endian) (u8Codec endian)).IsSurjectiveInitDecoder :=
    FixedByteCodec.prod_isSurjectiveInitDecoder
      (uintBvCodec_isSurjectiveInitDecoder endian 4 (by decide))
      (uintBvCodec_isSurjectiveInitDecoder endian 1 (by decide))
  have hPadCoreNoProv :
      (FixedByteCodec.prod (u32Codec endian) (u8Codec endian)).NoProvCodec :=
    FixedByteCodec.prod_noProvCodec
      (uintBvCodec_noProvCodec endian 4 (by decide))
      (uintBvCodec_noProvCodec endian 1 (by decide))
  have hPadDich :=
    padRight_preserves_fromBytes_not_intoBytes
      (FixedByteCodec.prod (u32Codec endian) (u8Codec endian))
      (by decide : 0 < 3) hPadCoreNoProv hPadCoreSurj
      (BitVec.ofNat 32 0, BitVec.ofNat 8 0)
  have hPadExact :
      ∀ bs : List AllocByte, bs.length < 8 →
        (paddedPairCodec endian).decode bs = none :=
    fun _ h => (paddedPairCodec endian).rejects_short h
  have hPadZero := hPadDich.2.1
  have hPadSurj := hPadDich.2.2.1
  have hPadNotInit := hPadDich.2.2.2
  refine ⟨⟨hUnitInto, hUnitFrom⟩, ⟨hBoolInto, hBoolFz, hBoolNotFrom⟩,
    ⟨hU64Into, hU64From⟩, ?_, ?_, ?_⟩
  · refine ⟨hUnpInit, hUnpSurj,
      codecTransmute_sound _ _ hUnpInit hUnpNoProv hArrSurj,
      codecTransmute_sound _ _ hUnpInit hUnpNoProv hPadSurj, ?_, ?_⟩
    · intro x
      exact transmute_codec_to_mirTy_sound endian (unpaddedTripleCodec endian)
        (.int .i64 false) (intLayout .i64) hUnpInit hUnpNoProv hU64From rfl rfl x
    · intro v bs hEnc
      exact transmute_mirTy_to_codec_sound endian (.int .i64 false)
        (intLayout .i64) (unpaddedTripleCodec endian) hU64Into hUnpSurj rfl rfl
        v bs hEnc
  · refine ⟨hPadExact, hPadZero, hPadSurj, ?_, ?_, hPadNotInit, ?_, ?_, ?_⟩
    · exact (paddedPairCodec endian).decode_encode
        (BitVec.ofNat 32 7, BitVec.ofNat 8 9)
    · intro v bs hEnc
      exact transmute_mirTy_to_codec_sound endian (.int .i64 false)
        (intLayout .i64) (paddedPairCodec endian) hU64Into hPadSurj rfl rfl
        v bs hEnc
    · cases endian <;> rfl
    · cases endian <;> rfl
    · intro a b s
      exact decodeVal_int_padRight_eq_none endian .i64 s
        (FixedByteCodec.prod (u32Codec endian) (u8Codec endian))
        (by decide : 0 < 3) rfl (a, b)
  · constructor
    · exact FixedByteCodec.padRight_zero_isInitCodec
        (FixedByteCodec.prod_isInitCodec
          (uintBvCodec_isInitCodec endian 1 (by decide))
          boolCodec_isInitCodec)
    · exact FixedByteCodec.padRight_not_isInitCodec
        (FixedByteCodec.prod (intBvCodec endian .i32) boolCodec)
        (by decide : 0 < 3) (BitVec.ofNat 32 0, false)

/-! ## Zerocopy `PtrTypestate` & Framing Canaries (`Core.PtrTypestate`) -/

section
open Anneal.ByteSubLens

/-- Partial-order and strict-separation canaries across `AliasingLe`,
`AlignLe`, `ValidityLe`, and `PtrInvLe`. -/
theorem canary_ptrInv_partial_order_and_separation :
    AliasingLe .exclusive .shared ∧
    ¬ AliasingLe .shared .exclusive ∧
    AlignLe .aligned .unaligned ∧
    ¬ AlignLe .unaligned .aligned ∧
    ValidityLe .safe .asInitialized ∧
    ValidityLe .initialized .asInitialized ∧
    ValidityLe .asInitialized .uninit ∧
    ¬ ValidityLe .safe .initialized ∧
    ¬ ValidityLe .initialized .safe ∧
    ¬ ValidityLe .asInitialized .initialized ∧
    ¬ ValidityLe .asInitialized .safe ∧
    ¬ ValidityLe .uninit .asInitialized ∧
    PtrInvLe ⟨.exclusive, .aligned, .safe⟩
      ⟨.shared, .unaligned, .asInitialized⟩ :=
  ⟨rfl, aliasingLe_shared_exclusive_false,
   rfl, alignLe_unaligned_aligned_false,
   rfl, rfl, rfl,
   validityLe_safe_initialized_false,
   validityLe_initialized_safe_false,
   validityLe_asInitialized_initialized_false,
   validityLe_asInitialized_safe_false,
   validityLe_uninit_asInitialized_false,
   ⟨rfl, rfl, rfl⟩⟩

abbrev ptCanaryAllocMutUninit : Allocation :=
  { allocId := 0, alignLog2 := 2, mutability := .mut,
    bytes := [.uninit, .uninit, .uninit, .uninit,
              .init 0x10 none, .init 0x20 none, .init 0x30 none,
              .init 0x40 none],
    live := true }

abbrev ptCanaryAllocSharedRo : Allocation :=
  { allocId := 1, alignLog2 := 2, mutability := .shared,
    bytes := [.init 0x78 none, .init 0x56 none, .init 0x34 none,
              .init 0x12 none],
    live := true }

abbrev ptCanaryMem0 : MemoryState :=
  { nextAllocId := 2
    allocations := [ptCanaryAllocMutUninit, ptCanaryAllocSharedRo] }

abbrev ptCanarySub0 : ByteSubLens := ⟨0, 0, 4, 2⟩
abbrev ptCanarySub0B : ByteSubLens := ⟨0, 4, 4, 2⟩
abbrev ptCanarySubRo : ByteSubLens := ⟨1, 0, 4, 2⟩

/-- End-to-end `PtrHolds` lifecycle canary on concrete `MemoryState`:
`.uninit` read refusal -> `ptrWrite` upgrade to `.safe` -> `as_mut` via
`byteSubLensGet`/`byteSubLensPut` -> `forget_aligned` & `try_into_aligned` ->
`into_shared` / `reborrow_shared` -> `as_ref` read -> `.shared` allocation
read via `ptrRead` (`readBytes`) -> `.shared` write rejection. -/
theorem canary_ptr_lifecycle_and_shared_vs_mut :
    (ptrRead ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
      false true ptCanaryMem0 = none) ∧
    (∃ mem1 mem2 : MemoryState,
      ptrWrite ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
        (BitVec.ofNat 32 0x12345678) ptCanaryMem0 = some mem1 ∧
      PtrHolds ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
        false mem1 ∧
      ptrRead ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
        false true mem1 = some (BitVec.ofNat 32 0x12345678) ∧
      byteSubLensPut ptCanarySub0 mem1
        ((u32Codec .little).encode (BitVec.ofNat 32 0xdeadbeef)) = some mem2 ∧
      (byteSubLensGet ptCanarySub0 mem2).bind (u32Codec .little).decode =
        some (BitVec.ofNat 32 0xdeadbeef) ∧
      PtrHolds ptCanarySub0 (u32Codec .little)
        ⟨.exclusive, .unaligned, .safe⟩ false mem2 ∧
      ptrCheckAligned ptCanarySub0 mem2 = true ∧
      PtrHolds ptCanarySub0 (u32Codec .little) ⟨.shared, .aligned, .safe⟩
        false mem2 ∧
      ptrAsRefRead ptCanarySub0 (u32Codec .little) ⟨.shared, .aligned, .safe⟩
        false mem2 = some (BitVec.ofNat 32 0xdeadbeef)) ∧
    (PtrHolds ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
      false ptCanaryMem0 ∧
     ptrRead ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       false true ptCanaryMem0 = some (BitVec.ofNat 32 0x12345678) ∧
     ptrWrite ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       (BitVec.ofNat 32 0) ptCanaryMem0 = none ∧
     byteSubLensGet ptCanarySubRo ptCanaryMem0 = none) := by
  have hUninitNone :
      ptrRead ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
        false true ptCanaryMem0 = none :=
    ptrRead_rejected_of_uninit ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .aligned, .uninit⟩ false true ptCanaryMem0 rfl
  have hHoldsUninit :
      PtrHolds ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
        false ptCanaryMem0 :=
    ⟨by decide, rfl, ptCanaryAllocMutUninit, rfl, rfl, ⟨rfl, by decide⟩,
     (fun _ => rfl), (fun _ => rfl), ⟨rfl, trivial⟩⟩
  let ⟨mem1, hWr1, _, hHolds1, hRd1⟩ :=
    ptrWrite_sound ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .aligned, .uninit⟩ false (BitVec.ofNat 32 0x12345678)
      ptCanaryMem0 rfl (validityIncl_of_validityLe _ rfl) hHoldsUninit
  let ⟨_, _, mem2, _, _, hPut2, hHolds2, hRdMut2⟩ :=
    ptrAsMut_access_sound ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .aligned, .safe⟩ false mem1 rfl hHolds1
      (BitVec.ofNat 32 0xdeadbeef)
  have hUnalign2 :=
    ptrHolds_forgetAligned ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .aligned, .safe⟩ false mem2 hHolds2
  have hChk2 : ptrCheckAligned ptCanarySub0 mem2 = true :=
    (ptrTryIntoAligned_iff ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .unaligned, .safe⟩ false mem2 hUnalign2).mpr hHolds2
  have hShared2 :=
    ptrHolds_intoShared ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .aligned, .safe⟩ false mem2 hHolds2
  let ⟨_xRef, _hxRef, hRefShared⟩ :=
    ptrAsRefRead_sound ptCanarySub0 (u32Codec .little)
      ⟨.shared, .aligned, .safe⟩ false mem2 rfl hShared2
  have hRdDirect :
      ptrAsRefRead ptCanarySub0 (u32Codec .little) ⟨.shared, .aligned, .safe⟩
        false mem2 = some (BitVec.ofNat 32 0xdeadbeef) := by
    have hEq :=
      ptrRead_agrees_with_byteSubLensGet ptCanarySub0 (u32Codec .little)
        ⟨.exclusive, .aligned, .safe⟩ false mem2 rfl rfl rfl hHolds2
    rw [hRdMut2] at hEq
    -- Compare via direct readBytesComp on shared vs exclusive mem2.
    have hAsRefEq :
        ptrAsRefRead ptCanarySub0 (u32Codec .little) ⟨.shared, .aligned, .safe⟩
          false mem2 =
        ptrRead ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
          false true mem2 := rfl
    rw [hAsRefEq, hEq]
  have hRoHolds :
      PtrHolds ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
        false ptCanaryMem0 :=
    ⟨by decide, rfl, ptCanaryAllocSharedRo, rfl, rfl, ⟨rfl, by decide⟩,
     (fun hEx => by nomatch hEx), (fun _ => rfl),
     ⟨rfl, ⟨BitVec.ofNat 32 0x12345678, rfl⟩⟩⟩
  refine ⟨hUninitNone, ⟨mem1, mem2, hWr1, hHolds1, hRd1, hPut2, hRdMut2,
    hUnalign2, hChk2, hRefShared, hRdDirect⟩,
    ⟨hRoHolds, rfl, rfl, rfl⟩⟩

@[expose] def ptPairU16Codec : FixedByteCodec (BitVec 16 × BitVec 16) 4 :=
  FixedByteCodec.prod (u16Codec .little) (u16Codec .little)

/-- `bool -> u8` shared-transmute inclusion: `bool` is unpadded `IntoBytes`
and `u8` is `FromBytes`. -/
theorem ptCanary_boolU8_validityIncl :
    ValidityIncl boolCodec .safe (u8Codec .little) .safe :=
  validityIncl_intoBytes_fromBytes boolCodec_allDecodableInit
    (uintBvCodec_isSurjectiveInitDecoder .little 1 (by decide))

/-- Transmutation and fallible `try_cast_into` canaries: `(u16, u16) -> u32`
under either aliasing (both are `IntoBytes + FromBytes`, so the exclusive
reverse inclusion holds), which forgets alignment like `zerocopy`'s
`transmute`; a shared `(u16, u16) -> u32` whose alignment is regained by
`try_into_aligned`; shared `bool -> u8`; valid `u8 -> bool` `ptrTryCastInto`
(`0x01`); and invalid `u8 -> bool` rejection (`0x02`). -/
theorem canary_ptr_transmute_and_tryCastInto_matrix :
    (∀ (mem : MemoryState) (inv : PtrInv),
      inv.validity = .safe →
      PtrHolds ptCanarySub0 ptPairU16Codec inv false mem →
      PtrHolds { ptCanarySub0 with alignLog2 := 2 } (u32Codec .little)
        { inv with align := .unaligned, validity := .safe } false mem) ∧
    (∀ (mem : MemoryState),
      PtrHolds ptCanarySub0 ptPairU16Codec ⟨.shared, .aligned, .safe⟩
        false mem →
      PtrHolds { ptCanarySub0 with alignLog2 := 1 } (u32Codec .little)
        ⟨.shared, .aligned, .safe⟩ false mem) ∧
    (∀ (mem : MemoryState),
      PtrHolds ⟨0, 0, 1, 0⟩ boolCodec ⟨.shared, .aligned, .safe⟩ false mem →
      PtrHolds ⟨0, 0, 1, 0⟩ (u8Codec .little) ⟨.shared, .unaligned, .safe⟩
        false mem) ∧
    (let memTrue : MemoryState :=
       { nextAllocId := 1
         allocations := [{ allocId := 0, alignLog2 := 0, mutability := .shared,
                           bytes := [.init 1 none], live := true }] }
     let memTwo : MemoryState :=
       { nextAllocId := 1
         allocations := [{ allocId := 0, alignLog2 := 0, mutability := .shared,
                           bytes := [.init 2 none], live := true }] }
     ptrTryCastInto ⟨0, 0, 1, 0⟩ 0 boolCodec ⟨.shared, .aligned, .safe⟩
       false false memTrue = some true ∧
     PtrHolds ⟨0, 0, 1, 0⟩ boolCodec ⟨.shared, .aligned, .safe⟩ false memTrue ∧
     ptrTryCastInto ⟨0, 0, 1, 0⟩ 0 boolCodec ⟨.shared, .aligned, .safe⟩
       false false memTwo = none) := by
  have hPairInit : AllDecodableInit ptPairU16Codec :=
    prod_allDecodableInit
      (uintBvCodec_allDecodableInit .little 2 (by decide))
      (uintBvCodec_allDecodableInit .little 2 (by decide))
  have hPairSurj : ptPairU16Codec.IsSurjectiveInitDecoder :=
    FixedByteCodec.prod_isSurjectiveInitDecoder
      (uintBvCodec_isSurjectiveInitDecoder .little 2 (by decide))
      (uintBvCodec_isSurjectiveInitDecoder .little 2 (by decide))
  have hU32Init : AllDecodableInit (u32Codec .little) :=
    uintBvCodec_allDecodableInit .little 4 (by decide)
  have hU32Surj := uintBvCodec_isSurjectiveInitDecoder .little 4 (by decide)
  have hFwd : ValidityIncl ptPairU16Codec .safe (u32Codec .little) .safe :=
    validityIncl_intoBytes_fromBytes hPairInit hU32Surj
  have hRev : ValidityIncl (u32Codec .little) .safe ptPairU16Codec .safe :=
    validityIncl_intoBytes_fromBytes hU32Init hPairSurj
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mem inv hSafe hHolds
    have hC : TransmuteCompat inv.aliasing false false ptPairU16Codec
        inv.validity (u32Codec .little) .safe := by
      rw [hSafe]
      cases inv.aliasing with
      | exclusive => exact transmuteCompat_exclusive false false hFwd hRev
      | shared => exact transmuteCompat_shared hFwd
    exact (ptrTransmute_sound ptCanarySub0 2 ptPairU16Codec (u32Codec .little)
      inv .safe false false mem hC hHolds).1
  · intro mem hHolds
    have hSrc1 :=
      ptrHolds_shrinkAlign ptCanarySub0 1 ptPairU16Codec
        ⟨.shared, .aligned, .safe⟩ false mem (fun _ => Nat.ble_eq.mp rfl) hHolds
    have hChk : ptrCheckAligned { ptCanarySub0 with alignLog2 := 1 } mem =
        true :=
      (ptrTryIntoAligned_iff { ptCanarySub0 with alignLog2 := 1 }
        ptPairU16Codec ⟨.shared, .aligned, .safe⟩ false mem hSrc1).mpr hSrc1
    have hDst := (ptrTransmute_sound ptCanarySub0 1 ptPairU16Codec
      (u32Codec .little) ⟨.shared, .aligned, .safe⟩ .safe false false mem
      (transmuteCompat_shared hFwd) hHolds).1
    exact ptrTryIntoAligned_sound { ptCanarySub0 with alignLog2 := 1 }
      (u32Codec .little) ⟨.shared, .unaligned, .safe⟩ false mem hDst hChk
  · intro mem hHolds
    exact (ptrTransmute_sound ⟨0, 0, 1, 0⟩ 0 boolCodec (u8Codec .little)
      ⟨.shared, .aligned, .safe⟩ .safe false false mem
      (transmuteCompat_shared ptCanary_boolU8_validityIncl) hHolds).1
  · dsimp only
    let memTrue : MemoryState :=
      { nextAllocId := 1
        allocations := [{ allocId := 0, alignLog2 := 0, mutability := .shared,
                          bytes := [.init 1 none], live := true }] }
    have hSrcTrue :
        PtrHolds ⟨0, 0, 1, 0⟩ (u8Codec .little) ⟨.shared, .aligned, .safe⟩
          false memTrue :=
      ⟨by decide, rfl,
       { allocId := 0, alignLog2 := 0, mutability := .shared,
         bytes := [.init 1 none], live := true },
       rfl, rfl, ⟨rfl, by decide⟩, (fun hEx => by nomatch hEx), (fun _ => rfl),
       ⟨rfl, ⟨BitVec.ofNat 8 1, rfl⟩⟩⟩
    exact ⟨rfl,
      (ptrTryCastInto_sound ⟨0, 0, 1, 0⟩ 0 (u8Codec .little) boolCodec
        ⟨.shared, .aligned, .safe⟩ false false memTrue true
        (fun hPM => nomatch hPM) hSrcTrue rfl).1,
      rfl⟩

/-- Cast-compatibility boundary canaries.

(a) Exclusive `bool -> u8` is rejected (`TransmuteCompat` fails): writing `2`
through the `u8` view of a `.mut` `bool` leaves a valid `u8` and an invalid
`bool`. Shared `bool -> u8` and exclusive equivalent representations
(`u32 <-> [u8; 4]`, `u8 <-> u8`) are accepted, and a shared `UnsafeCell`
destination is rejected (`castReadCompat`).
(b) A `2^63`-byte span passes `isInBounds` against a `2^63`-byte allocation, but
no such allocation fits in `isize` (`PtrSpanInBounds`), so no `PtrHolds` covers
a `2^63`-byte codec.
(c) Shared `ptrTryCastInto` into an `UnsafeCell` destination fails closed,
whereas the same cast into an `UnsafeCell`-free destination, or under
`.exclusive`, succeeds. -/
theorem canary_ptr_cast_compat_boundaries :
    (¬ TransmuteCompat .exclusive false false boolCodec .safe
        (u8Codec .little) .safe ∧
     (let sub : ByteSubLens := ⟨0, 0, 1, 0⟩
      let memTrue : MemoryState :=
        { nextAllocId := 1
          allocations := [{ allocId := 0, alignLog2 := 0, mutability := .mut,
                            bytes := [.init 1 none], live := true }] }
      let memTwo : MemoryState :=
        { nextAllocId := 1
          allocations := [{ allocId := 0, alignLog2 := 0, mutability := .mut,
                            bytes := [.init 2 none], live := true }] }
      PtrHolds sub boolCodec ⟨.exclusive, .aligned, .safe⟩ false memTrue ∧
      ptrWrite sub (u8Codec .little) ⟨.exclusive, .aligned, .safe⟩
        (BitVec.ofNat 8 2) memTrue = some memTwo ∧
      PtrHolds sub (u8Codec .little) ⟨.exclusive, .aligned, .safe⟩ false
        memTwo ∧
      ¬ PtrHolds sub boolCodec ⟨.exclusive, .aligned, .safe⟩ false memTwo) ∧
     TransmuteCompat .shared false false boolCodec .safe
       (u8Codec .little) .safe ∧
     ¬ TransmuteCompat .shared false true boolCodec .safe
       (u8Codec .little) .safe ∧
     TransmuteCompat .exclusive false false (u32Codec .little) .safe
       (FixedByteCodec.array 4 (u8Codec .little)) .safe ∧
     TransmuteCompat .exclusive false false (u8Codec .little) .safe
       (u8Codec .little) .safe) ∧
    (∀ a : Allocation, a.bytes.length = isizeMaxBytes →
      isInBounds a 0 isizeMaxBytes = true ∧
        ¬ PtrSpanInBounds a 0 isizeMaxBytes) ∧
    (∀ {α : Type} (sub : ByteSubLens) (c : FixedByteCodec α isizeMaxBytes)
        (inv : PtrInv) (uc : Bool) (mem : MemoryState),
      ¬ PtrHolds sub c inv uc mem) ∧
    (let memTrue : MemoryState :=
       { nextAllocId := 1
         allocations := [{ allocId := 0, alignLog2 := 0, mutability := .shared,
                           bytes := [.init 1 none], live := true }] }
     ptrTryCastInto ⟨0, 0, 1, 0⟩ 0 boolCodec ⟨.shared, .aligned, .safe⟩
       false true memTrue = none ∧
     ptrTryCastInto ⟨0, 0, 1, 0⟩ 0 boolCodec ⟨.shared, .aligned, .safe⟩
       false false memTrue = some true ∧
     ptrTryCastInto ⟨0, 0, 1, 0⟩ 0 boolCodec ⟨.exclusive, .aligned, .safe⟩
       false true memTrue = some true) := by
  have hNotExcl : ¬ TransmuteCompat .exclusive false false boolCodec .safe
      (u8Codec .little) .safe := by
    intro ⟨_, _, hMutC⟩
    have hU8 : ValidityHolds (u8Codec .little) .safe [.init 2 none] :=
      ⟨rfl, ⟨BitVec.ofNat 8 2, rfl⟩⟩
    let ⟨_, hDec⟩ := (hMutC rfl _ hU8).2
    nomatch hDec
  let allocTrue : Allocation :=
    { allocId := 0, alignLog2 := 0, mutability := .mut,
      bytes := [.init 1 none], live := true }
  let allocTwo : Allocation :=
    { allocId := 0, alignLog2 := 0, mutability := .mut,
      bytes := [.init 2 none], live := true }
  have hBoolTrue :
      PtrHolds ⟨0, 0, 1, 0⟩ boolCodec ⟨.exclusive, .aligned, .safe⟩ false
        { nextAllocId := 1, allocations := [allocTrue] } :=
    ⟨by decide, rfl, allocTrue, rfl, rfl, ⟨rfl, by decide⟩, (fun _ => rfl),
     (fun _ => rfl), ⟨rfl, ⟨true, rfl⟩⟩⟩
  have hU8Two :
      PtrHolds ⟨0, 0, 1, 0⟩ (u8Codec .little) ⟨.exclusive, .aligned, .safe⟩
        false { nextAllocId := 1, allocations := [allocTwo] } :=
    ⟨by decide, rfl, allocTwo, rfl, rfl, ⟨rfl, by decide⟩, (fun _ => rfl),
     (fun _ => rfl), ⟨rfl, ⟨BitVec.ofNat 8 2, rfl⟩⟩⟩
  have hBoolTwo :
      ¬ PtrHolds ⟨0, 0, 1, 0⟩ boolCodec ⟨.exclusive, .aligned, .safe⟩ false
        { nextAllocId := 1, allocations := [allocTwo] } := by
    intro ⟨_, _, a, hFind, _, _, _, _, hVal⟩
    injection hFind with hEq
    subst hEq
    let ⟨_, hDec⟩ := hVal.2
    nomatch hDec
  have hNotSharedUc : ¬ TransmuteCompat .shared false true boolCodec .safe
      (u8Codec .little) .safe := by
    intro ⟨hRd, _, _⟩
    nomatch hRd
  have hU32Arr : TransmuteCompat .exclusive false false (u32Codec .little)
      .safe (FixedByteCodec.array 4 (u8Codec .little)) .safe :=
    transmuteCompat_exclusive false false
      (validityIncl_intoBytes_fromBytes
        (uintBvCodec_allDecodableInit .little 4 (by decide))
        (FixedByteCodec.array_isSurjectiveInitDecoder
          (uintBvCodec_isSurjectiveInitDecoder .little 1 (by decide)) 4))
      (validityIncl_intoBytes_fromBytes
        (array_allDecodableInit
          (uintBvCodec_allDecodableInit .little 1 (by decide)) 4)
        (uintBvCodec_isSurjectiveInitDecoder .little 4 (by decide)))
  have hSpan : ∀ a : Allocation, a.bytes.length = isizeMaxBytes →
      isInBounds a 0 isizeMaxBytes = true ∧
        ¬ PtrSpanInBounds a 0 isizeMaxBytes := by
    intro a hLen
    refine ⟨?_, fun h => ?_⟩
    · unfold isInBounds
      rw [hLen, Nat.zero_add]
      exact Nat.ble_eq.mpr (Nat.le_refl _)
    · have hLt := h.2
      rw [hLen] at hLt
      exact Nat.lt_irrefl _ hLt
  have hNoHolds : ∀ {α : Type} (sub : ByteSubLens)
      (c : FixedByteCodec α isizeMaxBytes) (inv : PtrInv) (uc : Bool)
      (mem : MemoryState), ¬ PtrHolds sub c inv uc mem := by
    intro _ sub _ _ _ _ ⟨_, _, _, _, _, hB, _, _, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt
      (Nat.le_add_left isizeMaxBytes sub.offset)
      (ptrSpanInBounds_end_lt_isize hB))
  exact ⟨⟨hNotExcl, ⟨hBoolTrue, rfl, hU8Two, hBoolTwo⟩,
      transmuteCompat_shared ptCanary_boolU8_validityIncl, hNotSharedUc,
      hU32Arr,
      transmuteCompat_exclusive false false (validityIncl_refl _ _)
        (validityIncl_refl _ _)⟩,
    hSpan, hNoHolds, ⟨rfl, rfl, rfl⟩⟩

abbrev ptPadU16Codec := FixedByteCodec.padRight (u16Codec .little) 2

abbrev ptArrU8x4Codec := FixedByteCodec.array 4 (u8Codec .little)

abbrev ptCanaryAllocMis1 : Allocation :=
  { allocId := 0, alignLog2 := 2, mutability := .mut,
    bytes := [.init 0 none, .init 1 none, .init 2 none, .init 3 none,
              .init 4 none],
    live := true }

abbrev ptCanaryMemMis1 : MemoryState :=
  { nextAllocId := 1, allocations := [ptCanaryAllocMis1] }

/-- Offset `1` in `ptCanaryAllocMis1`, aligned only for `alignLog2 = 0`. -/
abbrev ptCanarySubMis1 : ByteSubLens := ⟨0, 1, 4, 0⟩

/-- Validity-change, alignment, and `Copy` boundary canaries.

(a) An exclusive `.initialized -> .safe` recall on padded `ptPadU16Codec` is
rejected (`¬ MutationCompat`): its zero encoding is `.safe` but leaves the
padding uninitialized, so a `.safe` write would break `.initialized`. The same
fact refutes `ptrWrite_sound`'s precondition on an `.initialized` padded
pointer. The shared recall and the exclusive unpadded `u32Codec` recall
succeed.
(b) Transmuting an aligned `[u8; 4]` at offset `1` (`alignLog2 = 0`) to `u32`
(`dstAlignLog2 = 2`) yields an `.unaligned` pointer with `alignLog2 = 2`, and
`try_into_aligned` rejects it.
(c) `ptrRead` fails closed for a non-`Copy` referent (`isCopy = false`) and
succeeds for a `Copy` one. -/
theorem canary_ptr_validity_change_boundaries :
    (¬ MutationCompat .exclusive false ptPadU16Codec .initialized
        ptPadU16Codec .safe ∧
     ¬ ValidityIncl ptPadU16Codec .safe ptPadU16Codec .initialized ∧
     (∀ (sub : ByteSubLens) (mem : MemoryState),
       PtrHolds sub ptPadU16Codec ⟨.shared, .aligned, .initialized⟩ false mem →
       PtrHolds sub ptPadU16Codec ⟨.shared, .aligned, .safe⟩ false mem) ∧
     (∀ (sub : ByteSubLens) (mem : MemoryState),
       PtrHolds sub (u32Codec .little) ⟨.exclusive, .aligned, .initialized⟩
         false mem →
       PtrHolds sub (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩ false
         mem)) ∧
    (PtrHolds ptCanarySubMis1 ptArrU8x4Codec ⟨.exclusive, .aligned, .safe⟩
       false ptCanaryMemMis1 ∧
     PtrHolds { ptCanarySubMis1 with alignLog2 := 2 } (u32Codec .little)
       ⟨.exclusive, .unaligned, .safe⟩ false ptCanaryMemMis1 ∧
     ptrCheckAligned { ptCanarySubMis1 with alignLog2 := 2 }
       ptCanaryMemMis1 = false ∧
     ¬ PtrHolds { ptCanarySubMis1 with alignLog2 := 2 } (u32Codec .little)
       ⟨.exclusive, .aligned, .safe⟩ false ptCanaryMemMis1) ∧
    (ptrRead ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       false false ptCanaryMem0 = none ∧
     ptrRead ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       false true ptCanaryMem0 = some (BitVec.ofNat 32 0x12345678)) := by
  have hU32Init : AllDecodableInit (u32Codec .little) :=
    uintBvCodec_allDecodableInit .little 4 (by decide)
  have hU32Surj := uintBvCodec_isSurjectiveInitDecoder .little 4 (by decide)
  have hU8Surj := uintBvCodec_isSurjectiveInitDecoder .little 1 (by decide)
  have hArrSurj : ptArrU8x4Codec.IsSurjectiveInitDecoder :=
    FixedByteCodec.array_isSurjectiveInitDecoder hU8Surj 4
  have hArrInit : AllDecodableInit ptArrU8x4Codec :=
    array_allDecodableInit (uintBvCodec_allDecodableInit .little 1 (by decide))
      4
  have hNotIncl :
      ¬ ValidityIncl ptPadU16Codec .safe ptPadU16Codec .initialized := by
    intro hInc
    have hS : ValidityHolds ptPadU16Codec .safe
        (ptPadU16Codec.encode (BitVec.ofNat 16 0)) :=
      ⟨ptPadU16Codec.encode_length _,
       ⟨BitVec.ofNat 16 0, ptPadU16Codec.decode_encode _⟩⟩
    have hI : AllBytesInit (ptPadU16Codec.encode (BitVec.ofNat 16 0)) :=
      (hInc _ hS).2
    have hF :
        allBytesInit (ptPadU16Codec.encode (BitVec.ofNat 16 0)) = false :=
      FixedByteCodec.allBytesInit_padRight_encode_eq_false (u16Codec .little)
        (by decide) (BitVec.ofNat 16 0)
    rw [hI] at hF
    nomatch hF
  have hPadRecall : ∀ (sub : ByteSubLens) (mem : MemoryState),
      PtrHolds sub ptPadU16Codec ⟨.shared, .aligned, .initialized⟩ false mem →
      PtrHolds sub ptPadU16Codec ⟨.shared, .aligned, .safe⟩ false mem :=
    fun sub mem hHolds =>
      (ptrRecallValidity_sound sub ptPadU16Codec
        ⟨.shared, .aligned, .initialized⟩ .safe false mem
        (validityIncl_initialized_fromBytes ptPadU16Codec
          (FixedByteCodec.padRight_isSurjectiveInitDecoder 2
            (uintBvCodec_isSurjectiveInitDecoder .little 2 (by decide))))
        (fun hPM => nomatch hPM) hHolds).1
  have hU32Recall : ∀ (sub : ByteSubLens) (mem : MemoryState),
      PtrHolds sub (u32Codec .little) ⟨.exclusive, .aligned, .initialized⟩
        false mem →
      PtrHolds sub (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩ false
        mem :=
    fun sub mem hHolds =>
      (ptrRecallValidity_sound sub (u32Codec .little)
        ⟨.exclusive, .aligned, .initialized⟩ .safe false mem
        (validityIncl_initialized_fromBytes (u32Codec .little) hU32Surj)
        (fun _ => validityIncl_safe_initialized_of_allDecodableInit hU32Init)
        hHolds).1
  have hSrc :
      PtrHolds ptCanarySubMis1 ptArrU8x4Codec ⟨.exclusive, .aligned, .safe⟩
        false ptCanaryMemMis1 :=
    ⟨by decide, rfl, ptCanaryAllocMis1, rfl, rfl, ⟨rfl, by decide⟩,
     (fun _ => rfl),
     (fun _ => rfl),
     ⟨rfl, hArrSurj [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
       rfl rfl⟩⟩
  have hC : TransmuteCompat .exclusive false false ptArrU8x4Codec .safe
      (u32Codec .little) .safe :=
    transmuteCompat_exclusive false false
      (validityIncl_intoBytes_fromBytes hArrInit hU32Surj)
      (validityIncl_intoBytes_fromBytes hU32Init hArrSurj)
  have hDst :
      PtrHolds { ptCanarySubMis1 with alignLog2 := 2 } (u32Codec .little)
        ⟨.exclusive, .unaligned, .safe⟩ false ptCanaryMemMis1 :=
    (ptrTransmute_sound ptCanarySubMis1 2 ptArrU8x4Codec (u32Codec .little)
      ⟨.exclusive, .aligned, .safe⟩ .safe false false ptCanaryMemMis1 hC
      hSrc).1
  have hChk : ptrCheckAligned { ptCanarySubMis1 with alignLog2 := 2 }
      ptCanaryMemMis1 = false := rfl
  exact ⟨⟨fun hMut => hNotIncl (hMut rfl), hNotIncl, hPadRecall, hU32Recall⟩,
    ⟨hSrc, hDst, hChk,
     ptrTryIntoAligned_rejected { ptCanarySubMis1 with alignLog2 := 2 }
       (u32Codec .little) ⟨.exclusive, .unaligned, .safe⟩ false
       ptCanaryMemMis1 hDst hChk⟩,
    ⟨rfl, rfl⟩⟩

/-- Explicit negative boundary canaries: reject `as_ref` with
`containsUnsafeCell = true`, reject `as_mut` on `.shared`, reject `transmute`
from padded `padRight (u16Codec .little) 2` into unpadded `u32Codec .little`,
reject `ptrRead` on `.uninit`, and reject `try_into_aligned` on misaligned
offset `1` (`alignLog2 = 2`). -/
theorem canary_ptr_negative_boundaries :
    (canAsRef ⟨.shared, .aligned, .safe⟩ true = false ∧
     ptrAsRefRead ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       true ptCanaryMem0 = none) ∧
    (canAsMut ⟨.shared, .aligned, .safe⟩ = false ∧
     ptrWrite ptCanarySub0 (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       (BitVec.ofNat 32 0) ptCanaryMem0 = none) ∧
    (¬ (FixedByteCodec.padRight (u16Codec .little) 2).IsInitCodec ∧
     ¬ AllDecodableInit (FixedByteCodec.padRight (u16Codec .little) 2) ∧
     ∃ (sub : ByteSubLens) (mem : MemoryState),
       PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
         ⟨.exclusive, .aligned, .safe⟩ false mem ∧
       PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
         ⟨.exclusive, .aligned, .asInitialized⟩ false mem ∧
       ¬ PtrHolds sub (FixedByteCodec.padRight (u16Codec .little) 2)
         ⟨.exclusive, .aligned, .initialized⟩ false mem ∧
       ¬ PtrHolds sub (u32Codec .little)
         ⟨.exclusive, .aligned, .safe⟩ false mem) ∧
    (ptrRead ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
       false true ptCanaryMem0 = none) ∧
    (let memMisaligned : MemoryState :=
       { nextAllocId := 1
         allocations := [{ allocId := 0, alignLog2 := 2, mutability := .mut,
                           bytes := [.init 0 none, .init 1 none, .init 2 none,
                                     .init 3 none, .init 4 none],
                           live := true }] }
     let subMis : ByteSubLens := ⟨0, 1, 4, 2⟩
     PtrHolds subMis (u32Codec .little) ⟨.exclusive, .unaligned, .safe⟩
       false memMisaligned ∧
     ptrCheckAligned subMis memMisaligned = false ∧
     ¬ PtrHolds subMis (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
       false memMisaligned) := by
  have hRef := ptrAsRefRead_rejected_of_unsafeCell ptCanarySubRo
    (u32Codec .little) ⟨.shared, .aligned, .safe⟩ ptCanaryMem0
  have hMut : canAsMut ⟨.shared, .aligned, .safe⟩ = false ∧
      ptrWrite ptCanarySub0 (u32Codec .little) ⟨.shared, .aligned, .safe⟩
        (BitVec.ofNat 32 0) ptCanaryMem0 = none :=
    ⟨canAsMut_rejected_of_shared ⟨.shared, .aligned, .safe⟩ rfl,
     ptrWrite_rejected_of_shared ptCanarySub0 (u32Codec .little)
       ⟨.shared, .aligned, .safe⟩ (BitVec.ofNat 32 0) ptCanaryMem0 rfl⟩
  have hPad := padding_refutes_intoBytes_and_unpadded_transmute
  have hUninit := ptrRead_rejected_of_uninit ptCanarySub0 (u32Codec .little)
    ⟨.exclusive, .aligned, .uninit⟩ false true ptCanaryMem0 rfl
  let memMisaligned : MemoryState :=
    { nextAllocId := 1
      allocations := [{ allocId := 0, alignLog2 := 2, mutability := .mut,
                        bytes := [.init 0 none, .init 1 none, .init 2 none,
                                  .init 3 none, .init 4 none],
                        live := true }] }
  let subMis : ByteSubLens := ⟨0, 1, 4, 2⟩
  have hUnalHolds :
      PtrHolds subMis (u32Codec .little) ⟨.exclusive, .unaligned, .safe⟩
        false memMisaligned :=
    ⟨by decide, rfl,
     { allocId := 0, alignLog2 := 2, mutability := .mut,
       bytes := [.init 0 none, .init 1 none, .init 2 none, .init 3 none,
                 .init 4 none],
       live := true },
     rfl, rfl, ⟨rfl, by decide⟩, (fun _ => rfl), (fun hAl => by nomatch hAl),
     ⟨rfl, ⟨BitVec.ofNat 32 0x04030201, rfl⟩⟩⟩
  have hFailChk : ptrCheckAligned subMis memMisaligned = false := rfl
  have hNotAligned :=
    ptrTryIntoAligned_rejected subMis (u32Codec .little)
      ⟨.exclusive, .unaligned, .safe⟩ false memMisaligned hUnalHolds hFailChk
  exact ⟨hRef, hMut, hPad, hUninit,
    ⟨hUnalHolds, hFailChk, hNotAligned⟩⟩

abbrev ptCanaryAllocMutAfter : Allocation :=
  { allocId := 0, alignLog2 := 2, mutability := .mut,
    bytes := [.init 0x04 none, .init 0x03 none, .init 0x02 none,
              .init 0x01 none, .init 0x10 none, .init 0x20 none,
              .init 0x30 none, .init 0x40 none],
    live := true }

abbrev ptCanaryMemAfter : MemoryState :=
  { nextAllocId := 2
    allocations := [ptCanaryAllocMutAfter, ptCanaryAllocSharedRo] }

/-- Disjoint write framing and `ptrHeapletPred` `FramePreserving` canary:
writing `ptCanarySub0` preserves disjoint `ptCanarySub0B` (same allocation,
adjacent `[4, 8)`) and `ptCanarySubRo` (different `.shared` allocation) via
both `ptrWrite_preserves_disjoint_ptrHolds` and `ptrHolds_of_memDisjointFrame`,
yields a concrete `MemDisjointFrame [⟨0, 0, 4⟩]`, and lifts cleanly across
`ptrHeapletPred` frames over `byteHeapletPCM`. -/
theorem canary_ptr_framing_and_heaplet :
    (ptrWrite ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
      (BitVec.ofNat 32 0x01020304) ptCanaryMem0 = some ptCanaryMemAfter ∧
     PtrHolds ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
       false ptCanaryMemAfter ∧
     PtrHolds ptCanarySub0B (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
       false ptCanaryMemAfter ∧
     PtrHolds ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
       false ptCanaryMemAfter ∧
     MemDisjointFrame [⟨0, 0, 4⟩] ptCanaryMem0 ptCanaryMemAfter) ∧
    FramePreserving byteHeapletPCM
      (sepConj byteHeapletPCM
        (ptrHeapletPred ptCanarySub0 (u32Codec .little)
          ⟨.exclusive, .aligned, .uninit⟩)
        (ptrHeapletPred ptCanarySubRo (u32Codec .little)
          ⟨.shared, .aligned, .safe⟩))
      (sepConj byteHeapletPCM
        (ptrHeapletPred ptCanarySub0 (u32Codec .little)
          ⟨.exclusive, .aligned, .safe⟩)
        (ptrHeapletPred ptCanarySubRo (u32Codec .little)
          ⟨.shared, .aligned, .safe⟩)) := by
  have hHolds0 :
      PtrHolds ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
        false ptCanaryMem0 :=
    ⟨by decide, rfl, ptCanaryAllocMutUninit, rfl, rfl, ⟨rfl, by decide⟩,
     (fun _ => rfl), (fun _ => rfl), ⟨rfl, trivial⟩⟩
  have hHolds0B :
      PtrHolds ptCanarySub0B (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
        false ptCanaryMem0 :=
    ⟨by decide, rfl, ptCanaryAllocMutUninit, rfl, rfl, ⟨rfl, by decide⟩,
     (fun _ => rfl), (fun _ => rfl),
     ⟨rfl, ⟨BitVec.ofNat 32 0x40302010, rfl⟩⟩⟩
  have hHoldsRo :
      PtrHolds ptCanarySubRo (u32Codec .little) ⟨.shared, .aligned, .safe⟩
        false ptCanaryMem0 :=
    ⟨by decide, rfl, ptCanaryAllocSharedRo, rfl, rfl, ⟨rfl, by decide⟩,
     (fun hEx => by nomatch hEx), (fun _ => rfl),
     ⟨rfl, ⟨BitVec.ofNat 32 0x12345678, rfl⟩⟩⟩
  have hWr :
      ptrWrite ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .uninit⟩
        (BitVec.ofNat 32 0x01020304) ptCanaryMem0 = some ptCanaryMemAfter := rfl
  have hAfter0 :
      PtrHolds ptCanarySub0 (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩
        false ptCanaryMemAfter :=
    ⟨by decide, rfl, ptCanaryAllocMutAfter, rfl, rfl, ⟨rfl, by decide⟩,
     (fun _ => rfl), (fun _ => rfl),
     ⟨rfl, ⟨BitVec.ofNat 32 0x01020304, rfl⟩⟩⟩
  have hFrame :
      MemDisjointFrame [⟨0, 0, 4⟩] ptCanaryMem0 ptCanaryMemAfter := by
    refine ⟨Nat.le_refl 2, fun aid hAid => ?_⟩
    cases aid with
    | zero =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun off hOut => ?_⟩
      cases off with
      | zero => cases hOut
      | succ o1 =>
        cases o1 with
        | zero => cases hOut
        | succ o2 =>
          cases o2 with
          | zero => cases hOut
          | succ o3 =>
            cases o3 with
            | zero => cases hOut
            | succ o4 =>
              cases o4 with
              | zero => rfl
              | succ o5 =>
                cases o5 with
                | zero => rfl
                | succ o6 =>
                  cases o6 with
                  | zero => rfl
                  | succ o7 =>
                    cases o7 with
                    | zero => rfl
                    | succ _ => rfl
    | succ a1 =>
      cases a1 with
      | zero =>
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun off _ => ?_⟩
        cases off with
        | zero => rfl
        | succ o1 =>
          cases o1 with
          | zero => rfl
          | succ o2 =>
            cases o2 with
            | zero => rfl
            | succ o3 =>
              cases o3 with
              | zero => rfl
              | succ _ => rfl
      | succ a2 =>
        exact False.elim
          (Nat.not_lt_zero a2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hAid)))
  have hDisj0B : DisjointPtrWrites ptCanarySub0 ptCanarySub0B := rfl
  have _hAfter0BWrite :=
    ptrWrite_preserves_disjoint_ptrHolds ptCanarySub0 (u32Codec .little)
      ⟨.exclusive, .aligned, .uninit⟩ (BitVec.ofNat 32 0x01020304)
      ptCanarySub0B (u32Codec .little) ⟨.exclusive, .aligned, .safe⟩ false
      ptCanaryMem0 ptCanaryMemAfter hDisj0B hWr hHolds0B
  have hAfter0B :=
    ptrHolds_of_memDisjointFrame [⟨0, 0, 4⟩] ptCanarySub0B (u32Codec .little)
      ⟨.exclusive, .aligned, .safe⟩ false ptCanaryMem0 ptCanaryMemAfter
      (by decide) hFrame (fun i hi => by
        cases i with
        | zero => rfl
        | succ i1 =>
          cases i1 with
          | zero => rfl
          | succ i2 =>
            cases i2 with
            | zero => rfl
            | succ i3 =>
              cases i3 with
              | zero => rfl
              | succ i4 =>
                exact False.elim (Nat.not_lt_zero i4
                  (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))))))
      hHolds0B
  have hAfterRo :=
    ptrHolds_of_memDisjointFrame [⟨0, 0, 4⟩] ptCanarySubRo (u32Codec .little)
      ⟨.shared, .aligned, .safe⟩ false ptCanaryMem0 ptCanaryMemAfter
      (by decide) hFrame (fun _ _ => rfl) hHoldsRo
  refine ⟨⟨hWr, hAfter0, hAfter0B, hAfterRo, hFrame⟩, ?_⟩
  exact ptrHeapletPred_write_framed ptCanarySub0 (u32Codec .little)
    ⟨.exclusive, .aligned, .uninit⟩ (BitVec.ofNat 32 0x01020304)
    (ptrHeapletPred ptCanarySubRo (u32Codec .little)
      ⟨.shared, .aligned, .safe⟩)

/-- `Option<u8>`-like `2`-byte codec whose initialization requirement depends
on its tag byte: `none ↦ [0x00, uninit]` and `some b ↦ [0x01, b]`. -/
@[expose] def ptOptU8Codec : FixedByteCodec (Option UInt8) 2 :=
  FixedByteCodec.ofRoundTrip
    (fun o =>
      match o with
      | none => [AllocByte.init 0 none, AllocByte.uninit]
      | some b => [AllocByte.init 1 none, AllocByte.init b none])
    (fun bs =>
      match bs with
      | [.init t _, b1] =>
        if Nat.beq t.toNat 0 then some none
        else if Nat.beq t.toNat 1 then
          match b1 with
          | .init b _ => some (some b)
          | .uninit => none
        else none
      | _ => none)
    (fun o => by cases o <;> rfl)
    (fun o => by cases o <;> rfl)
    (by
      intro bs _ h
      cases bs with
      | nil => nomatch h
      | cons b0 rest =>
        cases b0 with
        | uninit => nomatch h
        | init _ _ =>
          cases rest with
          | nil => nomatch h
          | cons _ rest2 =>
            cases rest2 with
            | nil => rfl
            | cons _ _ => nomatch h)

private theorem ptOptU8_tag1_requires_payload :
    ∀ (bs : List AllocByte) (x : Option UInt8),
      bs.length = 2 →
      bs.take 1 = [AllocByte.init 1 none] →
      ptOptU8Codec.decode bs = some x →
      ByteInitAt bs 1
  | [_, .init _ _], _, _, _, _ => trivial
  | [_, .uninit], _, _, hPre, hDec => by
    cases hPre
    nomatch hDec

private theorem ptOptU8_asInitFor_none_at :
    ∀ i : Nat, i < 2 →
      CodecRequiresInitAt ptOptU8Codec
        ([AllocByte.init 0 none, AllocByte.uninit].take i) i →
      ByteInitAt [AllocByte.init 0 none, AllocByte.uninit] i
  | 0, _, _ => trivial
  | 1, _, .inl hAll => hAll [.init 0 none, .uninit] none rfl rfl
  | 1, _, .inr ⟨_, hS⟩ => hS [.init 0 none, .uninit] none rfl rfl rfl
  | n + 2, hi, _ => absurd hi (Nat.not_lt_of_le (Nat.le_add_left 2 n))

/-- Prefix-conditional `AsInitialized` canary (`AsInitFor`): for
`ptOptU8Codec`, the first clause does not require payload byte `1` (the `none`
encoding leaves it `.uninit`), but the second clause requires it after tag
`0x01`, so `[0x01, uninit]` is not `.asInitialized` while `[0x00, uninit]` is.
-/
theorem canary_ptr_asInitFor_prefix_conditional :
    ¬ (∀ (bs : List AllocByte) (x : Option UInt8),
        bs.length = 2 → ptOptU8Codec.decode bs = some x → ByteInitAt bs 1) ∧
      ¬ AsInitFor ptOptU8Codec [AllocByte.init 1 none, AllocByte.uninit] ∧
      AsInitFor ptOptU8Codec [AllocByte.init 0 none, AllocByte.uninit] :=
  ⟨fun hAll => hAll [.init 0 none, .uninit] none rfl rfl,
   fun ⟨_, h⟩ => h 1 (by decide)
     (.inr ⟨⟨[.init 1 none, .init 0 none], some 0, rfl, rfl, rfl⟩,
       ptOptU8_tag1_requires_payload⟩),
   ⟨rfl, ptOptU8_asInitFor_none_at⟩⟩

end

/-! ## Canary Suite 7: `BitVec`, `BitVecArith`, and `LeBytes` MIR Bridge -/

/-- Positive `BitVecMirBridge` canary exercising scalar embeddings, bitwise +
`tnum` soundness lifts, wrapping/div/rem/overflowing/unchecked arithmetic
(including `u128`), comparisons (`slt`/`sle`), shifts, unary ops, and
unsigned/signed casts (`setWidth` and widening/narrowing `signExtend`). -/
theorem bitVecMirBridge_positive_ops_canary
    (x8 y8 : BitVec (8 * IntWidth.i8.byteSize))
    (x32 y32 : BitVec (8 * IntWidth.i32.byteSize))
    (hy32 : y32.toNat ≠ 0)
    (x128 y128 : BitVec (8 * IntWidth.i128.byteSize))
    (m1 m2 v1 v2 : BitVec (8 * IntWidth.i32.byteSize))
    (hm1 : Anneal.BitVec.MaskEq m1 x32 v1)
    (hm2 : Anneal.BitVec.MaskEq m2 y32 v2) :
    scalarToBv (bvToScalar .i32 false x32) = x32 ∧
    checkVal (.scalar (bvToScalar .i32 false x32)) (.int .i32 false) = true ∧
    evalBinOp .bitAnd (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.and x32 y32))) ∧
    evalBinOp .bitOr (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.or x32 y32))) ∧
    evalBinOp .bitXor (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.xor x32 y32))) ∧
    (∃ r : BitVec (8 * IntWidth.i32.byteSize),
      evalBinOp .bitAnd (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i32 false y32)) =
        .ok (.scalar (bvToScalar .i32 false r)) ∧
      Anneal.BitVec.MaskEq
        (Anneal.BitVec.or
          (Anneal.BitVec.or (Anneal.BitVec.and m1 m2) (Anneal.BitVec.and m1 v2))
          (Anneal.BitVec.and v1 m2))
        r (Anneal.BitVec.and v1 v2)) ∧
    (∃ r : BitVec (8 * IntWidth.i32.byteSize),
      evalBinOp .add (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i32 false y32)) =
        .ok (.scalar (bvToScalar .i32 false r)) ∧
      let v1' := Anneal.BitVec.and v1 (Anneal.BitVec.not m1)
      let v2' := Anneal.BitVec.and v2 (Anneal.BitVec.not m2)
      let sm := m1 + m2
      let sv := v1' + v2'
      let sigma := sm + sv
      let chi := Anneal.BitVec.xor sigma sv
      let mu := Anneal.BitVec.or chi (Anneal.BitVec.or m1 m2)
      Anneal.BitVec.MaskEq mu r (Anneal.BitVec.and sv (Anneal.BitVec.not mu))) ∧
    evalBinOp .add (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (x32 + y32))) ∧
    evalBinOp .add (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true y32)) =
      .ok (.scalar (bvToScalar .i32 true (x32 + y32))) ∧
    evalBinOp .sub (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (x32 - y32))) ∧
    evalBinOp .mul (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.mul x32 y32))) ∧
    evalBinOp .div (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.udiv x32 y32))) ∧
    evalBinOp .rem (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.scalar (bvToScalar .i32 false
        (Anneal.BitVecArith.urem x32 y32))) ∧
    evalBinOp .addWithOverflow (.scalar (bvToScalar .i128 false x128))
        (.scalar (bvToScalar .i128 false y128)) =
      .ok (.tuple [
        .scalar (bvToScalar .i128 false (x128 + y128)),
        .bool (decide (Nat.pow 2 128 ≤ x128.toNat + y128.toNat))
      ]) ∧
    evalBinOp .addWithOverflow
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 10)))
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 20))) =
      .ok (.tuple [
        .scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 30)),
        .bool false
      ]) ∧
    evalBinOp .addWithOverflow
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) (Nat.pow 2 128 - 1))))
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1))) =
      .ok (.tuple [
        .scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 0)),
        .bool true
      ]) ∧
    evalBinOp .addUnchecked
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 10)))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20))) =
      .ok (.scalar (bvToScalar .i32 false
        (BitVec.ofNat (8 * IntWidth.i32.byteSize) 30))) ∧
    evalBinOp .subWithOverflow
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20)))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) =
      .ok (.tuple [
        .scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 15)),
        .bool false
      ]) ∧
    evalBinOp .subUnchecked
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20)))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) =
      .ok (.scalar (bvToScalar .i32 false
        (BitVec.ofNat (8 * IntWidth.i32.byteSize) 15))) ∧
    evalBinOp .lt (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.bool (decide (x32.toNat < y32.toNat))) ∧
    evalBinOp .le (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.bool (decide (x32.toNat ≤ y32.toNat))) ∧
    evalBinOp .eq (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true y32)) =
      .ok (.bool (decide (x32 = y32))) ∧
    (∃ b : Bool,
      evalBinOp .lt (.scalar (bvToScalar .i32 true x32))
          (.scalar (bvToScalar .i32 true y32)) = .ok (.bool b) ∧
      (b = true ↔ Anneal.BitVecArith.slt x32 y32)) ∧
    (∃ b : Bool,
      evalBinOp .le (.scalar (bvToScalar .i32 true x32))
          (.scalar (bvToScalar .i32 true y32)) = .ok (.bool b) ∧
      (b = true ↔ Anneal.BitVecArith.sle x32 y32)) ∧
    evalBinOp .shl (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false y8)) =
      .ok (.scalar (bvToScalar .i32 false
        (Anneal.BitVec.shl x32 (Nat.mod y8.toNat 32)))) ∧
    evalBinOp .shr (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false y8)) =
      .ok (.scalar (bvToScalar .i32 false
        (Anneal.BitVec.ushr x32 (Nat.mod y8.toNat 32)))) ∧
    evalBinOp .shr (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i8 false y8)) =
      .ok (.scalar (bvToScalar .i32 true
        (Anneal.BitVecArith.ashr x32 (Nat.mod y8.toNat 32)))) ∧
    evalBinOp .shlUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 3))) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.shl x32 3))) ∧
    evalUnOp .not (.scalar (bvToScalar .i32 false x32)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.not x32))) ∧
    evalUnOp .neg (.scalar (bvToScalar .i32 true x32)) =
      .ok (.scalar (bvToScalar .i32 true (Anneal.BitVecArith.neg x32))) ∧
    evalIntToIntCast (.scalar (bvToScalar .i8 false x8)) (.int .i32 false) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.setWidth 32 x8))) ∧
    evalIntToIntCast (.scalar (bvToScalar .i8 true x8)) (.int .i32 true) =
      .ok (.scalar (bvToScalar .i32 true
        (Anneal.BitVecArith.signExtend 32 x8))) ∧
    evalIntToIntCast (.scalar (bvToScalar .i32 true x32)) (.int .i8 true) =
      .ok (.scalar (bvToScalar .i8 true
        (Anneal.BitVecArith.signExtend 8 x32))) := by
  have h1020Lt :
      (BitVec.ofNat (8 * IntWidth.i128.byteSize) 10).toNat +
        (BitVec.ofNat (8 * IntWidth.i128.byteSize) 20).toNat <
      Nat.pow 2 (8 * IntWidth.i128.byteSize) := by
    have hPow : Nat.pow 2 128 = Nat.pow 2 (8 * IntWidth.i128.byteSize) := rfl
    have h30 :
        (BitVec.ofNat (8 * IntWidth.i128.byteSize) 10).toNat +
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 20).toNat = 30 := rfl
    rw [h30, ← hPow]
    exact Nat.lt_trans (by decide : 30 < 64)
      (Nat.lt_of_lt_of_le (by decide : 64 < Nat.pow 2 7)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 7 ≤ 128)))
  have hAddNoOvf128 :
      evalBinOp .addWithOverflow
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 10)))
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 20))) =
        .ok (.tuple [
          .scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 30)),
          .bool false
        ]) := by
    rw [evalBinOp_addWithOverflow_unsigned_eq]
    have hNot : ¬ (Nat.pow 2 (8 * IntWidth.i128.byteSize) ≤
        (BitVec.ofNat (8 * IntWidth.i128.byteSize) 10).toNat +
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 20).toNat) :=
      Nat.not_le_of_gt h1020Lt
    rw [decide_eq_false hNot]
    rfl
  have hAddOvf128 :
      evalBinOp .addWithOverflow
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) (Nat.pow 2 128 - 1))))
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1))) =
        .ok (.tuple [
          .scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 0)),
          .bool true
        ]) := by
    rw [evalBinOp_addWithOverflow_unsigned_eq]
    have hPos128 : 1 ≤ Nat.pow 2 128 := Nat.pow_pos (by decide : 0 < 2)
    have hLt128 : Nat.pow 2 128 - 1 < Nat.pow 2 128 :=
      Nat.sub_lt hPos128 Nat.one_pos
    have hLhs : (BitVec.ofNat (8 * IntWidth.i128.byteSize)
        (Nat.pow 2 128 - 1)).toNat = Nat.pow 2 128 - 1 := by
      change Nat.mod (Nat.pow 2 128 - 1) (Nat.pow 2 128) = Nat.pow 2 128 - 1
      exact Nat.mod_eq_of_lt hLt128
    have hRhs : (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat = 1 := rfl
    have hGe : Nat.pow 2 (8 * IntWidth.i128.byteSize) ≤
        (BitVec.ofNat (8 * IntWidth.i128.byteSize)
          (Nat.pow 2 128 - 1)).toNat +
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat := by
      change Nat.pow 2 128 ≤
          (BitVec.ofNat (8 * IntWidth.i128.byteSize)
            (Nat.pow 2 128 - 1)).toNat +
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat
      rw [hLhs, hRhs, Nat.sub_add_cancel hPos128]
      exact Nat.le_refl _
    have hZero :
        (BitVec.ofNat (8 * IntWidth.i128.byteSize) (Nat.pow 2 128 - 1)) +
          BitVec.ofNat (8 * IntWidth.i128.byteSize) 1 =
        BitVec.ofNat (8 * IntWidth.i128.byteSize) 0 := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_add]
      change Nat.mod ((BitVec.ofNat (8 * IntWidth.i128.byteSize)
          (Nat.pow 2 128 - 1)).toNat +
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat)
          (Nat.pow 2 128) = 0
      rw [hLhs, hRhs, Nat.sub_add_cancel hPos128]
    rw [decide_eq_true hGe, hZero]
  have hAddUnchk32 :
      evalBinOp .addUnchecked
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 10)))
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20))) =
        .ok (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 30))) := by
    rw [evalBinOp_addUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_true_of (by decide :
      (BitVec.ofNat (8 * IntWidth.i32.byteSize) 10).toNat +
        (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20).toNat <
      Nat.pow 2 (8 * IntWidth.i32.byteSize))]
    rfl
  have hSubOvf32 :
      evalBinOp .subWithOverflow
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20)))
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) =
        .ok (.tuple [
          .scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 15)),
          .bool false
        ]) := by
    rw [evalBinOp_subWithOverflow_unsigned_eq]
    rfl
  have hSubUnchk32 :
      evalBinOp .subUnchecked
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20)))
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) =
        .ok (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 15))) := by
    rw [evalBinOp_subUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_true_of (by decide :
      (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5).toNat ≤
        (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20).toNat)]
    rfl
  have hShlUnchk32 :
      evalBinOp .shlUnchecked (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 3))) =
        .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.shl x32 3))) := by
    rw [evalBinOp_shlUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_true_of (by decide :
      (BitVec.ofNat (8 * IntWidth.i8.byteSize) 3).toNat <
        8 * IntWidth.i32.byteSize)]
    rfl
  exact ⟨scalarToBv_bvToScalar .i32 false x32,
    checkVal_bvToScalar .i32 false x32,
    evalBinOp_bitAnd_eq_and .i32 false x32 y32,
    evalBinOp_bitOr_eq_or .i32 false x32 y32,
    evalBinOp_bitXor_eq_xor .i32 false x32 y32,
    evalBinOp_bitAnd_tnum_sound false hm1 hm2,
    evalBinOp_add_tnum_sound false hm1 hm2,
    evalBinOp_add_eq_add .i32 false x32 y32,
    evalBinOp_add_eq_add .i32 true x32 y32,
    evalBinOp_sub_eq_sub .i32 false x32 y32,
    evalBinOp_mul_eq_mul .i32 false x32 y32,
    evalBinOp_div_unsigned_eq_udiv x32 hy32,
    evalBinOp_rem_unsigned_eq_urem x32 hy32,
    evalBinOp_addWithOverflow_unsigned_eq .i128 x128 y128,
    hAddNoOvf128, hAddOvf128, hAddUnchk32, hSubOvf32, hSubUnchk32,
    evalBinOp_lt_unsigned_eq .i32 x32 y32,
    evalBinOp_le_unsigned_eq .i32 x32 y32,
    evalBinOp_eq_eq .i32 true x32 y32,
    evalBinOp_lt_signed_eq_slt .i32 x32 y32,
    evalBinOp_le_signed_eq_sle .i32 x32 y32,
    evalBinOp_shl_unsigned_eq_shl .i32 .i8 x32 y8,
    evalBinOp_shr_unsigned_eq_ushr .i32 .i8 x32 y8,
    evalBinOp_shr_signed_eq_ashr .i32 .i8 x32 y8,
    hShlUnchk32,
    evalUnOp_not_eq_not .i32 false x32,
    evalUnOp_neg_signed_eq_neg .i32 x32,
    evalIntToIntCast_unsigned_eq_setWidth .i8 .i32 false x8,
    evalIntToIntCast_signed_eq_signExtend .i8 .i32 true x8,
    evalIntToIntCast_signed_eq_signExtend .i32 .i8 true x32⟩

/-- Negative `BitVecMirBridge` canary verifying UB/error faults (`div`/`rem` by
`0`, `addUnchecked` `u128` overflow, `subUnchecked` underflow, `shlUnchecked`
overshift, unsigned `.neg` unsupported) and `.uninit` byte rejections. -/
theorem bitVecMirBridge_negative_canaries
    (x32 : BitVec (8 * IntWidth.i32.byteSize)) :
    evalBinOp .div (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0))) =
      .error .undefined ∧
    evalBinOp .rem (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0))) =
      .error .undefined ∧
    evalBinOp .addUnchecked
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) (Nat.pow 2 128 - 1))))
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1))) =
      .error .undefined ∧
    evalBinOp .subUnchecked
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 3)))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) =
      .error .undefined ∧
    evalBinOp .shlUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 32))) =
      .error .undefined ∧
    evalUnOp .neg (.scalar (bvToScalar .i32 false x32)) =
      .error .unsupported ∧
    allBytesInit [.init (UInt8.ofBitVec (BitVec.ofNat 8 7)) none, .uninit] =
      false ∧
    initBytes? [.init (UInt8.ofBitVec (BitVec.ofNat 8 7)) none, .uninit] =
      none ∧
    decodeVal .little (.int .i16 false)
        [.init (UInt8.ofBitVec (BitVec.ofNat 8 7)) none, .uninit] =
      .ok none ∧
    (extractInitBvBytes [AllocByte.uninit]).length ≠
      ([AllocByte.uninit] : List AllocByte).length := by
  have hDiv0 := evalBinOp_div_unsigned_zero_fault x32
    (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0) rfl
  have hRem0 := evalBinOp_rem_unsigned_zero_fault x32
    (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0) rfl
  have hAddUnchkOvf :
      evalBinOp .addUnchecked
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) (Nat.pow 2 128 - 1))))
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1))) =
        .error .undefined := by
    rw [evalBinOp_addUnchecked_unsigned_eq]
    have hPos128 : 1 ≤ Nat.pow 2 128 := Nat.pow_pos (by decide : 0 < 2)
    have hLt128 : Nat.pow 2 128 - 1 < Nat.pow 2 128 :=
      Nat.sub_lt hPos128 Nat.one_pos
    have hLhs : (BitVec.ofNat (8 * IntWidth.i128.byteSize)
        (Nat.pow 2 128 - 1)).toNat = Nat.pow 2 128 - 1 := by
      change Nat.mod (Nat.pow 2 128 - 1) (Nat.pow 2 128) = Nat.pow 2 128 - 1
      exact Nat.mod_eq_of_lt hLt128
    have hNot : ¬ ((BitVec.ofNat (8 * IntWidth.i128.byteSize)
          (Nat.pow 2 128 - 1)).toNat +
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat <
          Nat.pow 2 (8 * IntWidth.i128.byteSize)) := by
      have hRhs : (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat = 1 := rfl
      change ¬ ((BitVec.ofNat (8 * IntWidth.i128.byteSize)
          (Nat.pow 2 128 - 1)).toNat +
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1).toNat <
          Nat.pow 2 128)
      rw [hLhs, hRhs, Nat.sub_add_cancel hPos128]
      exact Nat.lt_irrefl _
    rw [Anneal.InitLemmas.ite_false_of hNot]
  have hSubUnchkUnder :
      evalBinOp .subUnchecked
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 3)))
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) =
        .error .undefined := by
    rw [evalBinOp_subUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_false_of (by decide :
      ¬ ((BitVec.ofNat (8 * IntWidth.i32.byteSize) 5).toNat ≤
        (BitVec.ofNat (8 * IntWidth.i32.byteSize) 3).toNat))]
  have hShlUnchkOver :
      evalBinOp .shlUnchecked (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 32))) =
        .error .undefined := by
    rw [evalBinOp_shlUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_false_of (by decide :
      ¬ ((BitVec.ofNat (8 * IntWidth.i8.byteSize) 32).toNat <
        8 * IntWidth.i32.byteSize))]
  have hLenNe : (extractInitBvBytes [AllocByte.uninit]).length ≠
      ([AllocByte.uninit] : List AllocByte).length := by
    intro hEq
    have hBad := (length_extractInitBvBytes_eq_iff [AllocByte.uninit]).mp hEq
    cases hBad
  exact ⟨hDiv0, hRem0, hAddUnchkOvf, hSubUnchkUnder, hShlUnchkOver,
    evalUnOp_neg_unsigned_unsupported .i32 x32,
    rfl, rfl, rfl, hLenNe⟩

/-- Unchecked right-shift canary: `evalBinOp_shrUnchecked_unsigned_eq` gives
`ushr` for an in-range `u32` shift amount and `.error .undefined` for an amount
equal to the bit width. -/
theorem bitVecMirBridge_shrUnchecked_canary
    (x32 : BitVec (8 * IntWidth.i32.byteSize)) :
    evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 3))) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.ushr x32 3))) ∧
    evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 32))) =
      .error .undefined := by
  have hIn :
      evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 3))) =
        .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.ushr x32 3))) := by
    rw [evalBinOp_shrUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_true_of (by decide :
      (BitVec.ofNat (8 * IntWidth.i8.byteSize) 3).toNat <
        8 * IntWidth.i32.byteSize)]
    rfl
  have hOver :
      evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 32))) =
        .error .undefined := by
    rw [evalBinOp_shrUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_false_of (by decide :
      ¬ ((BitVec.ofNat (8 * IntWidth.i8.byteSize) 32).toNat <
        8 * IntWidth.i32.byteSize))]
  exact ⟨hIn, hOver⟩

/-- Byte-codec and chunking adequacy canary: verifies `encodeVal`/`decodeVal`
round-trips on `.little`, `.big`, and `profileTargetEndian`, chunking commutes
with `extractInitBvBytes`, and `leBytesOfNat_append_eq` splits a `u64` into two
`u32` little-endian chunks. -/
theorem bitVecMirBridge_bytes_and_chunks_canary (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) (prov : Option AllocId)
    (k : Nat) (bs : List (BitVec 8))
    {lo : Nat} (hLo : lo < Nat.pow 2 (4 * 8)) (hi : Nat) :
    (∃ bytesL : List AllocByte,
      encodeVal .little (.int w s) (.scalar (bvToScalar w s x)) = .ok bytesL ∧
      decodeVal .little (.int w s) bytesL =
        .ok (some (.scalar (bvToScalar w s x)))) ∧
    (∃ bytesB : List AllocByte,
      encodeVal .big (.int w s) (.scalar (bvToScalar w s x)) = .ok bytesB ∧
      decodeVal .big (.int w s) bytesB =
        .ok (some (.scalar (bvToScalar w s x)))) ∧
    (∃ bytesP : List AllocByte,
      encodeVal profileTargetEndian (.int w s) (.scalar (bvToScalar w s x)) =
        .ok bytesP ∧
      decodeVal profileTargetEndian (.int w s) bytesP =
        .ok (some (.scalar (bvToScalar w s x)))) ∧
    (Anneal.ListChunks.chunksOf k (bs.map (allocByteOfBv prov))).map
        extractInitBvBytes =
      Anneal.ListChunks.chunksOf k bs ∧
    leBytesOfNat 4 lo ++ leBytesOfNat 4 hi =
      leBytesOfNat 8 (lo + Nat.pow 2 (4 * 8) * hi) := by
  have hChunks :
      (Anneal.ListChunks.chunksOf k (bs.map (allocByteOfBv prov))).map
          extractInitBvBytes =
        Anneal.ListChunks.chunksOf k bs := by
    rw [chunksOf_extractInitBvBytes k (bs.map (allocByteOfBv prov))
        (allBytesInit_map_allocByteOfBv prov bs),
      extractInitBvBytes_map_allocByteOfBv prov bs]
  exact ⟨decodeVal_encodeVal_bvToScalar .little w s x,
    decodeVal_encodeVal_bvToScalar .big w s x,
    decodeVal_encodeVal_bvToScalar profileTargetEndian w s x,
    hChunks,
    leBytesOfNat_append_eq hLo hi⟩

private theorem evalRvalue_add_twoPass {v1 v2 res : Val}
    (hBin : evalBinOp .add v1 v2 = .ok res) :
    evalRvalue bodyTwoPassAdd.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory coreU32Ty
      (.binaryOp .add (.copy (coreLocalPlace 1)) (.copy (coreLocalPlace 2))) =
      .ok (res, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := by
  unfold evalRvalue
  dsimp only
  have hP1 : evalPrimitiveOperand bodyTwoPassAdd.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory (.copy (coreLocalPlace 1)) =
      .ok (v1, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := rfl
  have hP2 : evalPrimitiveOperand bodyTwoPassAdd.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory (.copy (coreLocalPlace 2)) =
      .ok (v2, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := rfl
  rw [hP1]
  dsimp only
  rw [hP2]
  dsimp only
  rw [hBin]

private theorem writePlace_ret_twoPass {v1 v2 res : Val}
    (hChk : checkVal res coreU32Ty = true) :
    writePlace [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory 0 coreU32Ty res =
      .ok ([.immediate (some res), .immediate (some v1),
            .immediate (some v2)], entryMemory) := by
  unfold writePlace
  rw [hChk]
  rfl

/-- End-to-end symbolic MIR `Body` canary connecting `bodyTwoPassAdd` to
`BitVecMirBridge.bvToScalar` and `evalBinOp_add_eq_add` for every pair
`(x, y : BitVec (8 * IntWidth.i32.byteSize))`. -/
theorem bodyTwoPassAdd_bvToScalar_canary
    (x y : BitVec (8 * IntWidth.i32.byteSize)) :
    PositiveCanaryClaim (bodyProg bodyTwoPassAdd)
      { args := [.scalar (bvToScalar .i32 false x),
                 .scalar (bvToScalar .i32 false y)] }
      (.scalar (bvToScalar .i32 false (x + y))) := by
  have hChkX :
      checkVal (.scalar (bvToScalar .i32 false x)) coreU32Ty = true :=
    checkVal_bvToScalar .i32 false x
  have hChkY :
      checkVal (.scalar (bvToScalar .i32 false y)) coreU32Ty = true :=
    checkVal_bvToScalar .i32 false y
  have hChkSum :
      checkVal (.scalar (bvToScalar .i32 false (x + y))) coreU32Ty = true :=
    checkVal_bvToScalar .i32 false (x + y)
  have hArgs :
      ValidEntryArgs bodyTwoPassAdd
        [.scalar (bvToScalar .i32 false x),
         .scalar (bvToScalar .i32 false y)] := by
    unfold ValidEntryArgs
    change checkArgsMatch
        [.scalar (bvToScalar .i32 false x),
         .scalar (bvToScalar .i32 false y)]
        [coreU32Ty, coreU32Ty] = true
    unfold checkArgsMatch
    rw [hChkX]
    unfold checkArgsMatch
    rw [hChkY]
    rfl
  have hInit :
      initState (bodyProg bodyTwoPassAdd)
        { args := [.scalar (bvToScalar .i32 false x),
                   .scalar (bvToScalar .i32 false y)] } =
        .ok {
          frames := [{
            defId := 0
            blockIdx := 0
            stmtIdx := 0
            locals := [
              .immediate none,
              .immediate (some (.scalar (bvToScalar .i32 false x))),
              .immediate (some (.scalar (bvToScalar .i32 false y)))
            ]
          }]
          callerMem := ⟨[]⟩
          mem := entryMemory
        } :=
    initState_eq_ok (body := bodyTwoPassAdd) rfl rfl hArgs
  have hStep1 :
      evalStep (bodyProg bodyTwoPassAdd) 0 {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [
            .immediate none,
            .immediate (some (.scalar (bvToScalar .i32 false x))),
            .immediate (some (.scalar (bvToScalar .i32 false y)))
          ]
        }]
        callerMem := ⟨[]⟩
        mem := entryMemory
      } =
      .step {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 1
          locals := [
            .immediate (some (.scalar (bvToScalar .i32 false (x + y)))),
            .immediate (some (.scalar (bvToScalar .i32 false x))),
            .immediate (some (.scalar (bvToScalar .i32 false y)))
          ]
        }]
        callerMem := ⟨[]⟩
        mem := entryMemory
      } := by
    unfold evalStep evalStatement bodyProg
    dsimp only [activeFrameBody, attachCallers]
    have hBody : Trusted.MirSemantics.getElem? [bodyTwoPassAdd] 0 =
        some bodyTwoPassAdd := rfl
    have hBb : Trusted.MirSemantics.getElem? bodyTwoPassAdd.basicBlocks 0 =
        some {
          statements := [
            .assign (coreLocalPlace 0)
              (.binaryOp .add (.copy (coreLocalPlace 1))
                (.copy (coreLocalPlace 2)))
          ]
          terminator := .return_
          cleanup := false
        } := rfl
    have hStmt :
        Trusted.MirSemantics.getElem?
          [StatementKind.assign (coreLocalPlace 0)
            (.binaryOp .add (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 2)))]
          0 =
          some (.assign (coreLocalPlace 0)
            (.binaryOp .add (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 2)))) := rfl
    have hLoc0 : Trusted.MirSemantics.getElem? bodyTwoPassAdd.locals 0 =
        some coreU32Ty := rfl
    have hProj : (!(coreLocalPlace 0).projection.isEmpty) = false := rfl
    have hId0 : (coreLocalPlace 0).localId = 0 := rfl
    have hIfFalse : ∀ {α : Type} (a b : α),
        (if (false = true) then a else b) = b := fun _ _ => rfl
    rw [hBody]
    dsimp only
    rw [hBb]
    dsimp only
    rw [hStmt]
    dsimp only
    rw [hProj, hId0, hIfFalse, hLoc0]
    dsimp only
    rw [evalRvalue_add_twoPass (evalBinOp_add_eq_add .i32 false x y)]
    dsimp only
    rw [writePlace_ret_twoPass hChkSum]
  have hExec : execProg (bodyProg bodyTwoPassAdd) 2
      { args := [.scalar (bvToScalar .i32 false x),
                 .scalar (bvToScalar .i32 false y)] }
      (fun out => out = .returned
        ⟨.scalar (bvToScalar .i32 false (x + y)), ⟨[]⟩⟩) := by
    unfold execProg execState
    rw [hInit]
    dsimp only [execOutcomeState, Anneal.Framework.StepWp.execStepOutcome]
    rw [Anneal.Framework.StepWp.execStepPred_succ_iff, hStep1]
    rfl
  exact positiveCanary_of_exec hExec

/-! ## Canary Suite 8: Extended `BitVecMirBridgeExt` & Signed `Body` Faults -/

/-- `i32` MIR type. -/
@[expose] def coreI32Ty : MirTy := .int .i32 true

/-- Single-block signed `i32` division body (`_0 := _1 / _2`). -/
@[expose] def bodyI32Div : Body :=
  { identity := "anneal_core::i32_div"
    isUnsafe := false
    locals := [coreI32Ty, coreI32Ty, coreI32Ty]
    argumentCount := 2
    basicBlocks := [{
      statements := [
        .assign (coreLocalPlace 0)
          (.binaryOp .div (.copy (coreLocalPlace 1)) (.copy (coreLocalPlace 2)))
      ]
      terminator := .return_
      cleanup := false
    }] }

/-- Extended shift canaries covering unsigned/signed `.shrUnchecked`, signed
`.shl`/`.shr` with signed shift amounts, and negative shift faults. -/
theorem bitVecMirBridgeExt_shift_canaries
    (y8 : BitVec (8 * IntWidth.i8.byteSize))
    (x32 : BitVec (8 * IntWidth.i32.byteSize)) :
    evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 5))) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.ushr x32 5))) ∧
    evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 32))) =
      .error .undefined ∧
    evalBinOp .shl (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i8 true y8)) =
      .ok (.scalar (bvToScalar .i32 true
        (Anneal.BitVec.shl x32 (Nat.mod y8.toNat (8 * IntWidth.i32.byteSize))))) ∧
    evalBinOp .shr (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i8 true y8)) =
      .ok (.scalar (bvToScalar .i32 true
        (Anneal.BitVecArith.ashr x32
          (Nat.mod y8.toNat (8 * IntWidth.i32.byteSize))))) ∧
    evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i8 false
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 4))) =
      .ok (.scalar (bvToScalar .i32 true
        (Anneal.BitVecArith.ashr x32 4))) ∧
    evalBinOp .shlUnchecked (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i8 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i8.byteSize)))) =
      .error .undefined ∧
    evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i8 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i8.byteSize)))) =
      .error .undefined := by
  have hUshrOk :
      evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 5))) =
        .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.ushr x32 5))) := by
    have h5 : (BitVec.ofNat (8 * IntWidth.i8.byteSize) 5).toNat = 5 := by
      decide
    rw [evalBinOp_shrUnchecked_unsigned_eq,
      Anneal.InitLemmas.ite_true_of (by decide :
        (BitVec.ofNat (8 * IntWidth.i8.byteSize) 5).toNat <
          8 * IntWidth.i32.byteSize),
      h5]
  have hUshrOver :
      evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 32))) =
        .error .undefined := by
    rw [evalBinOp_shrUnchecked_unsigned_eq]
    rw [Anneal.InitLemmas.ite_false_of (by decide :
      ¬ ((BitVec.ofNat (8 * IntWidth.i8.byteSize) 32).toNat <
        8 * IntWidth.i32.byteSize))]
  have hSignedShrOk :
      evalBinOp .shrUnchecked (.scalar (bvToScalar .i32 true x32))
          (.scalar (bvToScalar .i8 false
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 4))) =
        .ok (.scalar (bvToScalar .i32 true
          (Anneal.BitVecArith.ashr x32 4))) := by
    rw [evalBinOp_shrUnchecked_eq]
    rw [Anneal.InitLemmas.ite_true_of (by decide :
      ((!false || !Anneal.BitVecArith.msb
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 4)) &&
        decide ((BitVec.ofNat (8 * IntWidth.i8.byteSize) 4).toNat <
          8 * IntWidth.i32.byteSize)) = true)]
    rfl
  have hMsbAll1 :
      Anneal.BitVecArith.msb
          (Anneal.BitVec.allOnes (8 * IntWidth.i8.byteSize)) = true := by
    rw [Anneal.BitVecArith.msb_eq_true_iff (by decide :
        0 < 8 * IntWidth.i8.byteSize),
      Anneal.BitVec.toNat_allOnes]
    decide
  exact ⟨hUshrOk, hUshrOver,
    evalBinOp_shl_eq_shl .i32 .i8 true true x32 y8,
    evalBinOp_shr_eq .i32 .i8 true true x32 y8,
    hSignedShrOk,
    evalBinOp_shiftUnchecked_neg_rhs_fault .shlUnchecked (Or.inl rfl)
      .i32 .i8 true x32 hMsbAll1,
    evalBinOp_shiftUnchecked_neg_rhs_fault .shrUnchecked (Or.inr rfl)
      .i32 .i8 false x32 hMsbAll1⟩

/-- Extended signed arithmetic, 128-bit overflow, unchecked overflow fault, and
signed division/remainder canaries (including `INT_MIN / -1` and `INT_MIN % -1`
`.undefined` faults). -/
theorem bitVecMirBridgeExt_signed_arith_and_overflow_canaries
    (x32 y32 : BitVec (8 * IntWidth.i32.byteSize))
    (hy32 : y32.toNat ≠ 0)
    (hNoOvf32 : ¬ (x32 = Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize) ∧
      y32 = Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))
    (x128 y128 : BitVec (8 * IntWidth.i128.byteSize)) :
    evalBinOp .mulWithOverflow (.scalar (bvToScalar .i128 false x128))
        (.scalar (bvToScalar .i128 false y128)) =
      .ok (.tuple [
        .scalar (bvToScalar .i128 false (Anneal.BitVec.mul x128 y128)),
        .bool (decide (Nat.pow 2 (8 * IntWidth.i128.byteSize) ≤
          x128.toNat * y128.toNat))
      ]) ∧
    evalBinOp .mulUnchecked
        (.scalar (bvToScalar .i128 false
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
        (.scalar (bvToScalar .i128 false
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 2))) =
      .error .undefined ∧
    evalBinOp .addWithOverflow
        (.scalar (bvToScalar .i8 true
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)))
        (.scalar (bvToScalar .i8 true
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 20))) =
      .ok (.tuple [
        .scalar (bvToScalar .i8 true
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 120)),
        .bool false
      ]) ∧
    evalBinOp .addUnchecked
        (.scalar (bvToScalar .i8 true
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)))
        (.scalar (bvToScalar .i8 true
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 50))) =
      .error .undefined ∧
    evalBinOp .subUnchecked
        (.scalar (bvToScalar .i128 true
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
        (.scalar (bvToScalar .i128 true
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1))) =
      .error .undefined ∧
    evalBinOp .mulUnchecked
        (.scalar (bvToScalar .i128 true
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
        (.scalar (bvToScalar .i128 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i128.byteSize)))) =
      .error .undefined ∧
    evalBinOp .div (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true y32)) =
      .ok (.scalar (bvToScalar .i32 true (bvSdiv x32 y32))) ∧
    evalBinOp .rem (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true y32)) =
      .ok (.scalar (bvToScalar .i32 true (bvSrem x32 y32))) ∧
    evalBinOp .div (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0))) =
      .error .undefined ∧
    evalBinOp .div
        (.scalar (bvToScalar .i32 true
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize))))
        (.scalar (bvToScalar .i32 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))) =
      .error .undefined ∧
    evalBinOp .rem
        (.scalar (bvToScalar .i128 true
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
        (.scalar (bvToScalar .i128 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i128.byteSize)))) =
      .error .undefined := by
  have hUMul128Ovf :
      evalBinOp .mulUnchecked
          (.scalar (bvToScalar .i128 false
            (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
          (.scalar (bvToScalar .i128 false
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 2))) =
        .error .undefined := by
    rw [evalBinOp_mulUnchecked_unsigned_eq]
    have hGe : Nat.pow 2 (8 * IntWidth.i128.byteSize) ≤
        (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize)).toNat *
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 2).toNat := by
      have hSb :
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize)).toNat =
            Nat.pow 2 127 := by
        rw [Anneal.BitVecArith.toNat_signBit_of_pos (by decide :
          0 < 8 * IntWidth.i128.byteSize)]
        rfl
      have h2 : (BitVec.ofNat (8 * IntWidth.i128.byteSize) 2).toNat = 2 := rfl
      change Nat.pow 2 128 ≤ _
      rw [hSb, h2]
      decide
    rw [Anneal.InitLemmas.ite_false_of (Nat.not_lt_of_ge hGe)]
  have hSAdd8No :
      evalBinOp .addWithOverflow
          (.scalar (bvToScalar .i8 true
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)))
          (.scalar (bvToScalar .i8 true
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 20))) =
        .ok (.tuple [
          .scalar (bvToScalar .i8 true
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 120)),
          .bool false
        ]) := by
    rw [evalBinOp_addWithOverflow_signed_eq]
    have hF : signedOverflowAddBv
        (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)
        (BitVec.ofNat (8 * IntWidth.i8.byteSize) 20) = false := by
      rw [signedOverflowAddBv_eq_false_iff (by decide :
        0 < 8 * IntWidth.i8.byteSize)]
      decide
    rw [hF]
    rfl
  have hSAdd8Unchk :
      evalBinOp .addUnchecked
          (.scalar (bvToScalar .i8 true
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)))
          (.scalar (bvToScalar .i8 true
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 50))) =
        .error .undefined := by
    rw [evalBinOp_addUnchecked_signed_eq]
    have hT : signedOverflowAddBv
        (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)
        (BitVec.ofNat (8 * IntWidth.i8.byteSize) 50) = true := by
      cases hOv : signedOverflowAddBv
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100)
          (BitVec.ofNat (8 * IntWidth.i8.byteSize) 50) with
      | true => rfl
      | false =>
        rw [signedOverflowAddBv_eq_false_iff (by decide :
          0 < 8 * IntWidth.i8.byteSize)] at hOv
        exact False.elim ((by decide : ¬ (Nat.pow 2 (8 * IntWidth.i8.byteSize - 1) ≤
          Anneal.BitVecArith.signedKey
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100) +
          Anneal.BitVecArith.signedKey
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 50) ∧
          Anneal.BitVecArith.signedKey
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 100) +
          Anneal.BitVecArith.signedKey
            (BitVec.ofNat (8 * IntWidth.i8.byteSize) 50) <
          Nat.pow 2 (8 * IntWidth.i8.byteSize - 1) +
            Nat.pow 2 (8 * IntWidth.i8.byteSize))) hOv)
    rw [hT]
    rfl
  have hSSub128Unchk :
      evalBinOp .subUnchecked
          (.scalar (bvToScalar .i128 true
            (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
          (.scalar (bvToScalar .i128 true
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1))) =
        .error .undefined := by
    rw [evalBinOp_subUnchecked_signed_eq]
    have hT : signedOverflowSubBv
        (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))
        (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1) = true := by
      cases hOv : signedOverflowSubBv
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))
          (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1) with
      | true => rfl
      | false =>
        rw [signedOverflowSubBv_eq_false_iff (by decide :
          0 < 8 * IntWidth.i128.byteSize)] at hOv
        have hSb : Anneal.BitVecArith.signedKey
            (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize)) = 0 := by
          rw [Anneal.BitVecArith.signedKey_eq_of_msb_true (by decide :
              0 < 8 * IntWidth.i128.byteSize)
              (by rw [Anneal.BitVecArith.msb_eq_true_iff (by decide :
                    0 < 8 * IntWidth.i128.byteSize),
                    Anneal.BitVecArith.toNat_signBit_of_pos (by decide :
                    0 < 8 * IntWidth.i128.byteSize)]
                  exact Nat.le_refl _),
            Anneal.BitVecArith.toNat_signBit_of_pos (by decide :
              0 < 8 * IntWidth.i128.byteSize), Nat.sub_self]
        have h1 : Anneal.BitVecArith.signedKey
            (BitVec.ofNat (8 * IntWidth.i128.byteSize) 1) =
            Nat.pow 2 127 + 1 := by
          rw [Anneal.BitVecArith.signedKey_eq_of_msb_false (by decide :
              0 < 8 * IntWidth.i128.byteSize)
              (by rw [Anneal.BitVecArith.msb_eq_false_iff (by decide :
                    0 < 8 * IntWidth.i128.byteSize)]
                  decide)]
          rfl
        have hBad := hOv.1
        rw [hSb] at hBad
        rw [h1, Nat.zero_add] at hBad
        exact False.elim (Nat.not_le_of_gt (Nat.lt_succ_self (Nat.pow 2 127)) hBad)
    rw [hT]
    rfl
  have hSMul128Unchk :
      evalBinOp .mulUnchecked
          (.scalar (bvToScalar .i128 true
            (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))))
          (.scalar (bvToScalar .i128 true
            (Anneal.BitVec.allOnes (8 * IntWidth.i128.byteSize)))) =
        .error .undefined := by
    rw [evalBinOp_mulUnchecked_signed_eq]
    have hT : signedOverflowMulBv
        (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))
        (Anneal.BitVec.allOnes (8 * IntWidth.i128.byteSize)) = true := by
      cases hOv : signedOverflowMulBv
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize))
          (Anneal.BitVec.allOnes (8 * IntWidth.i128.byteSize)) with
      | true => rfl
      | false =>
        rw [signedOverflowMulBv_eq_false_iff (by decide :
          0 < 8 * IntWidth.i128.byteSize)] at hOv
        have hW128 : 0 < 8 * IntWidth.i128.byteSize := by decide
        have hProd : bvToInt
            (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i128.byteSize)) *
            bvToInt (Anneal.BitVec.allOnes (8 * IntWidth.i128.byteSize)) =
            Int.ofNat (Nat.pow 2 127) := by
          rw [bvToInt_signBit, bvToInt_allOnes hW128]
          have hMin : signedMinInt .i128 =
              Int.negSucc (Nat.pow 2 127 - 1) := by
            have hPos : 0 < Nat.pow 2 127 := Anneal.InitLemmas.nat_two_pow_pos 127
            have hPow : HPow.hPow (2 : Int) 127 =
                Int.ofNat (Nat.succ (Nat.pow 2 127 - 1)) := by
              change Int.ofNat (Nat.pow 2 127) =
                Int.ofNat ((Nat.pow 2 127 - 1) + 1)
              rw [Nat.sub_add_cancel hPos]
            unfold signedMinInt
            change Neg.neg (HPow.hPow (2 : Int) 127) = _
            rw [hPow]
            rfl
          have hNeg1 : Neg.neg (1 : Int) = Int.negSucc 0 := rfl
          rw [hMin, hNeg1]
          change Int.ofNat (Nat.succ (Nat.pow 2 127 - 1) * 1) =
            Int.ofNat (Nat.pow 2 127)
          rw [Nat.mul_one]
        have hBad := hOv.2
        rw [hProd] at hBad
        change Int.NonNeg (Int.ofNat (Nat.pow 2 127) -
          (Int.ofNat (Nat.pow 2 127) + 1)) at hBad
        have hSub : Int.ofNat (Nat.pow 2 127) -
            (Int.ofNat (Nat.pow 2 127) + 1) = Int.negSucc 0 := by
          change Int.subNatNat (Nat.pow 2 127) (Nat.pow 2 127 + 1) =
            Int.negSucc 0
          unfold Int.subNatNat
          have hD : (Nat.pow 2 127 + 1) - Nat.pow 2 127 = 1 := by
            rw [Nat.add_comm, Nat.add_sub_cancel]
          rw [hD]
        rw [hSub] at hBad
        nomatch hBad
    rw [hT]
    rfl
  exact ⟨evalBinOp_mulWithOverflow_unsigned_eq .i128 x128 y128,
    hUMul128Ovf, hSAdd8No, hSAdd8Unchk, hSSub128Unchk, hSMul128Unchk,
    evalBinOp_div_signed_eq .i32 hy32 hNoOvf32,
    evalBinOp_rem_signed_eq .i32 hy32 hNoOvf32,
    evalBinOp_div_signed_zero_fault .i32 x32 rfl,
    evalBinOp_div_signed_min_neg_one_fault .i32,
    evalBinOp_rem_signed_min_neg_one_fault .i128⟩

/-- Extended comparison, `.bool`/`.char`, `evalUnOp` (`srange`/tnum neg), and
`evalIntToIntCast` canaries (including code points `> 255` `.char` and
negative-integer cast rejections). -/
theorem bitVecMirBridgeExt_cmp_bool_char_unop_cast_canaries
    (x32 y32 m v : BitVec (8 * IntWidth.i32.byteSize))
    (hm : Anneal.BitVec.MaskEq m x32 v)
    (b1 b2 : Bool) (c1 c2 : Char) :
    evalBinOp .ne (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true y32)) =
      .ok (.bool (decide (x32 ≠ y32))) ∧
    evalBinOp .gt (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.bool (decide (y32.toNat < x32.toNat))) ∧
    evalBinOp .ge (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.bool (decide (y32.toNat ≤ x32.toNat))) ∧
    evalBinOp .cmp (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) =
      .ok (.ordering (cmpOrderingOfNat x32.toNat y32.toNat)) ∧
    evalBinOp .cmp (.scalar (bvToScalar .i32 true x32))
        (.scalar (bvToScalar .i32 true y32)) =
      .ok (.ordering (bvScmp x32 y32)) ∧
    evalBinOp .add (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 true y32)) = .error .unsupported ∧
    evalBinOp .offset (.scalar (bvToScalar .i32 false x32))
        (.scalar (bvToScalar .i32 false y32)) = .error .unsupported ∧
    evalBinOp .bitXor (.bool b1) (.bool b2) = .ok (.bool (bne b1 b2)) ∧
    evalBinOp .cmp (.bool b1) (.bool b2) = .error .unsupported ∧
    evalBinOp .cmp (.char c1) (.char c2) =
      .ok (.ordering (cmpOrderingOfNat c1.toNat c2.toNat)) ∧
    evalBinOp .add (.char c1) (.char c2) = .error .unsupported ∧
    evalUnOp .not (.bool b1) = .ok (.bool (!b1)) ∧
    evalUnOp .neg (.char c1) = .error .unsupported ∧
    evalUnOp .ptrMetadata (.scalar (bvToScalar .i32 false x32)) =
      .error .unsupported ∧
    (∃ r : BitVec (8 * IntWidth.i32.byteSize),
      evalUnOp .neg (.scalar (bvToScalar .i32 true x32)) =
        .ok (.scalar (bvToScalar .i32 true r)) ∧
      Anneal.BitVec.MaskEq (tnumNegMask m v) r (tnumNegVal m v)) ∧
    (Anneal.BitVecArith.sle (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5) x32 →
      Anneal.BitVecArith.sle x32 (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20) →
      Anneal.BitVecArith.sle
        (Anneal.BitVecArith.neg (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20))
        (Anneal.BitVecArith.neg x32) ∧
      Anneal.BitVecArith.sle
        (Anneal.BitVecArith.neg x32)
        (Anneal.BitVecArith.neg (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5))) ∧
    evalIntToIntCast (.bool true) (.int .i32 false) =
      .ok (.scalar (bvToScalar .i32 false
        (BitVec.ofNat (8 * IntWidth.i32.byteSize) 1))) ∧
    evalIntToIntCast
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 65))) .char =
      .ok (.char (Char.ofNat 65)) ∧
    evalIntToIntCast
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 256))) .char =
      .error .unsupported ∧
    evalIntToIntCast
        (.scalar (bvToScalar .i32 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))) .char =
      .error .unsupported ∧
    evalIntToIntCast (.char (Char.ofNat 300)) .char = .error .unsupported ∧
    evalIntToIntCast .unit (.int .i32 false) = .error .unsupported ∧
    evalIntToIntCast (.bool b1) .bool = .error .unsupported := by
  have hSrange :
      Anneal.BitVecArith.sle (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5) x32 →
      Anneal.BitVecArith.sle x32 (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20) →
      Anneal.BitVecArith.sle
        (Anneal.BitVecArith.neg (BitVec.ofNat (8 * IntWidth.i32.byteSize) 20))
        (Anneal.BitVecArith.neg x32) ∧
      Anneal.BitVecArith.sle
        (Anneal.BitVecArith.neg x32)
        (Anneal.BitVecArith.neg (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5)) := by
    intro hLo hHi
    have hSlt :
        Anneal.BitVecArith.slt
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize))
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5) :=
      Anneal.BitVecArith.slt_of_msb_true_false
        (by decide : Anneal.BitVecArith.msb
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize)) = true)
        (by decide : Anneal.BitVecArith.msb
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 5) = false)
    exact (evalUnOp_neg_srange_sound .i32 hSlt hLo hHi).2
  have hCast65 :
      evalIntToIntCast
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 65))) .char =
        .ok (.char (Char.ofNat 65)) := by
    rw [evalIntToIntCast_unsigned_to_char]
    rfl
  have hCast256 :
      evalIntToIntCast
          (.scalar (bvToScalar .i32 false
            (BitVec.ofNat (8 * IntWidth.i32.byteSize) 256))) .char =
        .error .unsupported := by
    rw [evalIntToIntCast_unsigned_to_char]
    rfl
  have hCastNeg1 :
      evalIntToIntCast
          (.scalar (bvToScalar .i32 true
            (Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))) .char =
        .error .unsupported := by
    refine evalIntToIntCast_signed_neg_to_char_unsupported .i32 ?_
    rw [Anneal.BitVecArith.msb_eq_true_iff (by decide :
        0 < 8 * IntWidth.i32.byteSize),
      Anneal.BitVec.toNat_allOnes]
    decide
  have hCastChar300 :
      evalIntToIntCast (.char (Char.ofNat 300)) .char = .error .unsupported := by
    rw [evalIntToIntCast_char_to_char]
    rfl
  exact ⟨evalBinOp_ne_eq .i32 true x32 y32,
    evalBinOp_gt_unsigned_eq .i32 x32 y32,
    evalBinOp_ge_unsigned_eq .i32 x32 y32,
    evalBinOp_cmp_unsigned_eq .i32 x32 y32,
    evalBinOp_cmp_signed_eq .i32 x32 y32,
    evalBinOp_nonShift_mismatch_unsupported (op := .add) rfl rfl,
    evalBinOp_offset_scalar_unsupported (bvToScalar .i32 false x32)
      (bvToScalar .i32 false y32),
    evalBinOp_bool_bitXor_eq b1 b2,
    evalBinOp_bool_cmp_unsupported b1 b2,
    evalBinOp_char_cmp_eq c1 c2,
    evalBinOp_char_unsupported (op := .add)
      ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
       (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
       (fun h => by cases h)⟩ c1 c2,
    evalUnOp_not_bool_eq b1,
    evalUnOp_char_unsupported .neg c1,
    evalUnOp_ptrMetadata_unsupported (.scalar (bvToScalar .i32 false x32)),
    evalUnOp_neg_tnum_sound hm,
    hSrange,
    evalIntToIntCast_bool_to_int true .i32 false,
    hCast65, hCast256, hCastNeg1, hCastChar300,
    evalIntToIntCast_unsupported_source (v := .unit) rfl (.int .i32 false),
    evalIntToIntCast_unsupported_target (.bool b1)
      (fun _ _ h => by cases h) (fun h => by cases h)⟩

private theorem evalRvalue_i32Div {v1 v2 res : Val}
    (hBin : evalBinOp .div v1 v2 = .ok res) :
    evalRvalue bodyI32Div.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory coreI32Ty
      (.binaryOp .div (.copy (coreLocalPlace 1)) (.copy (coreLocalPlace 2))) =
      .ok (res, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := by
  unfold evalRvalue
  dsimp only
  have hP1 : evalPrimitiveOperand bodyI32Div.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory (.copy (coreLocalPlace 1)) =
      .ok (v1, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := rfl
  have hP2 : evalPrimitiveOperand bodyI32Div.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory (.copy (coreLocalPlace 2)) =
      .ok (v2, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := rfl
  rw [hP1]
  dsimp only
  rw [hP2]
  dsimp only
  rw [hBin]

private theorem evalRvalue_i32Div_fault {v1 v2 : Val} {fk : FaultKind}
    (hBin : evalBinOp .div v1 v2 = .error fk) :
    evalRvalue bodyI32Div.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory coreI32Ty
      (.binaryOp .div (.copy (coreLocalPlace 1)) (.copy (coreLocalPlace 2))) =
      .error fk := by
  unfold evalRvalue
  dsimp only
  have hP1 : evalPrimitiveOperand bodyI32Div.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory (.copy (coreLocalPlace 1)) =
      .ok (v1, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := rfl
  have hP2 : evalPrimitiveOperand bodyI32Div.locals
      [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory (.copy (coreLocalPlace 2)) =
      .ok (v2, [.immediate none, .immediate (some v1), .immediate (some v2)],
        entryMemory) := rfl
  rw [hP1]
  dsimp only
  rw [hP2]
  dsimp only
  rw [hBin]

private theorem writePlace_ret_i32Div {v1 v2 res : Val}
    (hChk : checkVal res coreI32Ty = true) :
    writePlace [.immediate none, .immediate (some v1), .immediate (some v2)]
      entryMemory 0 coreI32Ty res =
      .ok ([.immediate (some res), .immediate (some v1),
            .immediate (some v2)], entryMemory) := by
  unfold writePlace
  rw [hChk]
  rfl

private theorem execOutcomeState_succ {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} :
    execOutcomeState p onDone onFault (fuel + 1) s =
      (match evalStep p 0 s with
      | .step st' => execOutcomeState p onDone onFault fuel st'
      | .done out => onDone out
      | .fault k => onFault k) := by
  dsimp only [execOutcomeState, Anneal.Framework.StepWp.execStepOutcome]
  rw [Anneal.Framework.StepWp.execStepPred_succ_iff]
  cases evalStep p 0 s <;> rfl

private theorem evalStep_i32Div_return {v0 v1 v2 : Val} :
    evalStep (bodyProg bodyI32Div) 0 {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 1
        locals := [.immediate (some v0), .immediate (some v1),
          .immediate (some v2)]
      }]
      callerMem := ⟨[]⟩
      mem := entryMemory
    } = .done (.returned ⟨v0, ⟨[]⟩⟩) := rfl

private theorem bodyI32Div_pos_canary
    (x y : BitVec (8 * IntWidth.i32.byteSize)) (hy : y.toNat ≠ 0)
    (hNoOvf : ¬ (x = Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize) ∧
      y = Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize))) :
    PositiveCanaryClaim (bodyProg bodyI32Div)
      { args := [.scalar (bvToScalar .i32 true x),
                 .scalar (bvToScalar .i32 true y)] }
      (.scalar (bvToScalar .i32 true (bvSdiv x y))) := by
  have hBody : Trusted.MirSemantics.getElem? [bodyI32Div] 0 =
      some bodyI32Div := rfl
  have hBb : Trusted.MirSemantics.getElem? bodyI32Div.basicBlocks 0 =
      some {
        statements := [
          .assign (coreLocalPlace 0)
            (.binaryOp .div (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 2)))
        ]
        terminator := .return_
        cleanup := false
      } := rfl
  have hStmt :
      Trusted.MirSemantics.getElem?
        [StatementKind.assign (coreLocalPlace 0)
          (.binaryOp .div (.copy (coreLocalPlace 1))
            (.copy (coreLocalPlace 2)))]
        0 =
        some (.assign (coreLocalPlace 0)
          (.binaryOp .div (.copy (coreLocalPlace 1))
            (.copy (coreLocalPlace 2)))) := rfl
  have hLoc0 : Trusted.MirSemantics.getElem? bodyI32Div.locals 0 =
      some coreI32Ty := rfl
  have hProj : (!(coreLocalPlace 0).projection.isEmpty) = false := rfl
  have hId0 : (coreLocalPlace 0).localId = 0 := rfl
  have hIfFalse : ∀ {α : Type} (a b : α),
      (if (false = true) then a else b) = b := fun _ _ => rfl
  have hChkX :
      checkVal (.scalar (bvToScalar .i32 true x)) coreI32Ty = true :=
    checkVal_bvToScalar .i32 true x
  have hChkY :
      checkVal (.scalar (bvToScalar .i32 true y)) coreI32Ty = true :=
    checkVal_bvToScalar .i32 true y
  have hChkQ :
      checkVal (.scalar (bvToScalar .i32 true (bvSdiv x y))) coreI32Ty =
        true :=
    checkVal_bvToScalar .i32 true (bvSdiv x y)
  have hArgs :
      ValidEntryArgs bodyI32Div
        [.scalar (bvToScalar .i32 true x),
         .scalar (bvToScalar .i32 true y)] := by
    unfold ValidEntryArgs
    change checkArgsMatch
        [.scalar (bvToScalar .i32 true x),
         .scalar (bvToScalar .i32 true y)]
        [coreI32Ty, coreI32Ty] = true
    unfold checkArgsMatch
    rw [hChkX]
    unfold checkArgsMatch
    rw [hChkY]
    rfl
  have hInit :
      initState (bodyProg bodyI32Div)
        { args := [.scalar (bvToScalar .i32 true x),
                   .scalar (bvToScalar .i32 true y)] } =
        .ok {
          frames := [{
            defId := 0
            blockIdx := 0
            stmtIdx := 0
            locals := [
              .immediate none,
              .immediate (some (.scalar (bvToScalar .i32 true x))),
              .immediate (some (.scalar (bvToScalar .i32 true y)))
            ]
          }]
          callerMem := ⟨[]⟩
          mem := entryMemory
        } :=
    initState_eq_ok (body := bodyI32Div) rfl rfl hArgs
  have hStep1 :
      evalStep (bodyProg bodyI32Div) 0 {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [
            .immediate none,
            .immediate (some (.scalar (bvToScalar .i32 true x))),
            .immediate (some (.scalar (bvToScalar .i32 true y)))
          ]
        }]
        callerMem := ⟨[]⟩
        mem := entryMemory
      } =
      .step {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 1
          locals := [
            .immediate (some (.scalar (bvToScalar .i32 true (bvSdiv x y)))),
            .immediate (some (.scalar (bvToScalar .i32 true x))),
            .immediate (some (.scalar (bvToScalar .i32 true y)))
          ]
        }]
        callerMem := ⟨[]⟩
        mem := entryMemory
      } := by
    unfold evalStep evalStatement bodyProg
    dsimp only [activeFrameBody, attachCallers]
    rw [hBody]
    dsimp only
    rw [hBb]
    dsimp only
    rw [hStmt]
    dsimp only
    rw [hProj, hId0, hIfFalse, hLoc0]
    dsimp only
    rw [evalRvalue_i32Div (evalBinOp_div_signed_eq .i32 hy hNoOvf)]
    dsimp only
    rw [writePlace_ret_i32Div hChkQ]
  have hExec : execProg (bodyProg bodyI32Div) 2
      { args := [.scalar (bvToScalar .i32 true x),
                 .scalar (bvToScalar .i32 true y)] }
      (fun out => out = .returned
        ⟨.scalar (bvToScalar .i32 true (bvSdiv x y)), ⟨[]⟩⟩) := by
    unfold execProg execState
    rw [hInit]
    dsimp only
    rw [execOutcomeState_succ, hStep1]
    dsimp only
    rw [execOutcomeState_succ, evalStep_i32Div_return]
  exact positiveCanary_of_exec hExec

private theorem bodyI32Div_neg_canary :
    NegativeCanaryClaim (bodyProg bodyI32Div)
      { args := [.scalar (bvToScalar .i32 true
                   (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize))),
                 .scalar (bvToScalar .i32 true
                   (Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))] }
      .undefined .unsupported := by
  have hBody : Trusted.MirSemantics.getElem? [bodyI32Div] 0 =
      some bodyI32Div := rfl
  have hBb : Trusted.MirSemantics.getElem? bodyI32Div.basicBlocks 0 =
      some {
        statements := [
          .assign (coreLocalPlace 0)
            (.binaryOp .div (.copy (coreLocalPlace 1))
              (.copy (coreLocalPlace 2)))
        ]
        terminator := .return_
        cleanup := false
      } := rfl
  have hStmt :
      Trusted.MirSemantics.getElem?
        [StatementKind.assign (coreLocalPlace 0)
          (.binaryOp .div (.copy (coreLocalPlace 1))
            (.copy (coreLocalPlace 2)))]
        0 =
        some (.assign (coreLocalPlace 0)
          (.binaryOp .div (.copy (coreLocalPlace 1))
            (.copy (coreLocalPlace 2)))) := rfl
  have hLoc0 : Trusted.MirSemantics.getElem? bodyI32Div.locals 0 =
      some coreI32Ty := rfl
  have hProj : (!(coreLocalPlace 0).projection.isEmpty) = false := rfl
  have hId0 : (coreLocalPlace 0).localId = 0 := rfl
  have hIfFalse : ∀ {α : Type} (a b : α),
      (if (false = true) then a else b) = b := fun _ _ => rfl
  let sb := Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize)
  let all1 := Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)
  have hChkSb : checkVal (.scalar (bvToScalar .i32 true sb)) coreI32Ty =
      true :=
    checkVal_bvToScalar .i32 true sb
  have hChkAll1 :
      checkVal (.scalar (bvToScalar .i32 true all1)) coreI32Ty = true :=
    checkVal_bvToScalar .i32 true all1
  have hArgs :
      ValidEntryArgs bodyI32Div
        [.scalar (bvToScalar .i32 true sb),
         .scalar (bvToScalar .i32 true all1)] := by
    unfold ValidEntryArgs
    change checkArgsMatch
        [.scalar (bvToScalar .i32 true sb),
         .scalar (bvToScalar .i32 true all1)]
        [coreI32Ty, coreI32Ty] = true
    unfold checkArgsMatch
    rw [hChkSb]
    unfold checkArgsMatch
    rw [hChkAll1]
    rfl
  have hInit :
      initState (bodyProg bodyI32Div)
        { args := [.scalar (bvToScalar .i32 true sb),
                   .scalar (bvToScalar .i32 true all1)] } =
        .ok {
          frames := [{
            defId := 0
            blockIdx := 0
            stmtIdx := 0
            locals := [
              .immediate none,
              .immediate (some (.scalar (bvToScalar .i32 true sb))),
              .immediate (some (.scalar (bvToScalar .i32 true all1)))
            ]
          }]
          callerMem := ⟨[]⟩
          mem := entryMemory
        } :=
    initState_eq_ok (body := bodyI32Div) rfl rfl hArgs
  have hStepFault :
      evalStep (bodyProg bodyI32Div) 0 {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [
            .immediate none,
            .immediate (some (.scalar (bvToScalar .i32 true sb))),
            .immediate (some (.scalar (bvToScalar .i32 true all1)))
          ]
        }]
        callerMem := ⟨[]⟩
        mem := entryMemory
      } = .fault .undefined := by
    unfold evalStep evalStatement bodyProg
    dsimp only [activeFrameBody, attachCallers]
    rw [hBody]
    dsimp only
    rw [hBb]
    dsimp only
    rw [hStmt]
    dsimp only
    rw [hProj, hId0, hIfFalse, hLoc0]
    dsimp only
    rw [evalRvalue_i32Div_fault (evalBinOp_div_signed_min_neg_one_fault .i32)]
  refine negativeCanary_of_execFault (fuel := 1) (by intro h; cases h) ?_
  unfold execFaultProg
  rw [hInit]
  dsimp only [execFaultState]
  rw [execOutcomeState_succ, hStepFault]

/-- End-to-end signed MIR `Body` execution canary (`bodyI32Div`): succeeds
with `bvSdiv x y` whenever `y ≠ 0` and `¬ (x = signBit ∧ y = allOnes)`, and
faults with `FaultKind.undefined` on `i32::MIN / -1`. -/
theorem bodyI32Div_bvToScalar_and_fault_canary
    (x y : BitVec (8 * IntWidth.i32.byteSize)) (hy : y.toNat ≠ 0)
    (hNoOvf : ¬ (x = Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize) ∧
      y = Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize))) :
    PositiveCanaryClaim (bodyProg bodyI32Div)
      { args := [.scalar (bvToScalar .i32 true x),
                 .scalar (bvToScalar .i32 true y)] }
      (.scalar (bvToScalar .i32 true (bvSdiv x y))) ∧
    NegativeCanaryClaim (bodyProg bodyI32Div)
      { args := [.scalar (bvToScalar .i32 true
                   (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize))),
                 .scalar (bvToScalar .i32 true
                   (Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))] }
      .undefined .unsupported :=
  ⟨bodyI32Div_pos_canary x y hy hNoOvf, bodyI32Div_neg_canary⟩

/-! ## Suite 9: Intrinsic Bit-Ops, Endian Swap, Saturating & Codec Canaries -/

/-- Symbolic `bvPopcount`, `bvCttz`, `bvCtlz`, `bvBitreverse`, Kernighan step,
`isPow2Bv`, alignment mask, and `MaskEq` tnum bound canaries on `u32` and `u64`.
-/
theorem canary_bitIntrinsic_bitops_symbolic
    (x32 m32 v32 : BitVec (8 * IntWidth.i32.byteSize))
    (x64 : BitVec (8 * IntWidth.i64.byteSize))
    (hm32 : Anneal.BitVec.MaskEq m32 x32 v32)
    (hx32 : x32 ≠ BitVec.ofNat (8 * IntWidth.i32.byteSize) 0) :
    (bvPopcount (Anneal.BitVec.and x32
        (x32 - BitVec.ofNat (8 * IntWidth.i32.byteSize) 1)) + 1 =
      bvPopcount x32) ∧
    ((isPow2Bv x32 = true ↔ bvPopcount x32 = 1) ∧
      (bvPopcount x32 = 1 ↔
        ∃ k : Nat, k < 8 * IntWidth.i32.byteSize ∧
          x32 = BitVec.ofNat (8 * IntWidth.i32.byteSize) (Nat.pow 2 k))) ∧
    ((3 ≤ bvCttz x32 ↔
        Anneal.BitVec.and x32
          (Anneal.BitVec.lowMask (8 * IntWidth.i32.byteSize) 3) =
        BitVec.ofNat (8 * IntWidth.i32.byteSize) 0) ∧
      (3 ≤ bvCttz (scalarToBv (bvToScalar .isize false
        (BitVec.ofNat (8 * IntWidth.isize.byteSize) 8))) ↔
        Nat.mod (BitVec.ofNat (8 * IntWidth.isize.byteSize) 8).toNat
          (Nat.pow 2 3) = 0)) ∧
    (bvCttz (Anneal.BitVec.or v32 m32) ≤ bvCttz x32 ∧
      bvCttz x32 ≤ bvCttz (Anneal.BitVec.and v32 (Anneal.BitVec.not m32)) ∧
      bvCtlz (Anneal.BitVec.or v32 m32) ≤ bvCtlz x32 ∧
      bvCtlz x32 ≤ bvCtlz (Anneal.BitVec.and v32 (Anneal.BitVec.not m32))) ∧
    (bvPopcount (bvBitreverse x64) = bvPopcount x64 ∧
      bvCttz (bvBitreverse x64) = bvCtlz x64 ∧
      bvCtlz (bvBitreverse x64) = bvCttz x64) := by
  refine ⟨bvPopcount_kernighan_step hx32,
    ⟨isPow2Bv_eq_true_iff_bvPopcount_eq_one x32,
      bvPopcount_eq_one_iff_exists_two_pow x32⟩,
    ⟨le_bvCttz_iff_and_lowMask_eq_zero x32 (by decide),
      le_bvCttz_scalarToBv_iff false
        (BitVec.ofNat (8 * IntWidth.isize.byteSize) 8) (by decide)⟩,
    ⟨bvCttz_tnum_lower hm32, bvCttz_tnum_upper hm32,
      bvCtlz_tnum_lower hm32, bvCtlz_tnum_upper hm32⟩,
    ⟨bvPopcount_bvBitreverse x64, bvCttz_bvBitreverse x64,
      bvCtlz_bvBitreverse x64⟩⟩

/-- Concrete positive and negative `isPow2Bv`, `bvPopcount`, `bvCttz`, and
`bvCtlz` edge-case canaries (`0`, `6`, `8 = 2^3`). -/
theorem canary_bitIntrinsic_concrete_edge :
    bvPopcount (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0) = 0 ∧
    bvPopcount (BitVec.ofNat (8 * IntWidth.i32.byteSize) (Nat.pow 2 3)) = 1 ∧
    isPow2Bv (BitVec.ofNat (8 * IntWidth.i8.byteSize) 0) = false ∧
    isPow2Bv (BitVec.ofNat (8 * IntWidth.i8.byteSize) 6) = false ∧
    isPow2Bv (BitVec.ofNat (8 * IntWidth.i8.byteSize) 8) = true ∧
    bvCttz (BitVec.ofNat (8 * IntWidth.i32.byteSize) (Nat.pow 2 3)) = 3 ∧
    bvCtlz (BitVec.ofNat (8 * IntWidth.i32.byteSize) (Nat.pow 2 3)) = 28 ∧
    bvPopcount (Anneal.BitVec.lowMask 32 5) = 5 := by
  refine ⟨bvPopcount_zero 32, bvPopcount_two_pow (w := 32) (k := 3) (by decide),
    by decide, by decide, by decide,
    bvCttz_two_pow (w := 32) (k := 3) (by decide),
    bvCtlz_two_pow (w := 32) (k := 3) (by decide),
    bvPopcount_lowMask_of_le (w := 32) (k := 5) (by decide)⟩

/-- Endian byte-swap (`bvBswap`) and `encodeVal`/`decodeVal` round-trip
canaries at `IntWidth` `.i8`, `.i32`, and `.i64`. -/
theorem canary_bitIntrinsic_bswap_endian
    (x32 : BitVec (8 * IntWidth.i32.byteSize))
    (x64 : BitVec (8 * IntWidth.i64.byteSize))
    (x8 : BitVec (8 * IntWidth.i8.byteSize)) :
    bvBswap .i8 x8 = x8 ∧
    bvBswap .i64 (bvBswap .i64 x64) = x64 ∧
    Anneal.LeBytes.toLeBytes IntWidth.i32.byteSize (toLeWidth (bvBswap .i32 x32)) =
      Anneal.LeBytes.toBeBytes IntWidth.i32.byteSize (toLeWidth x32) ∧
    (∃ bytesBe bytesLe : List AllocByte,
      encodeVal .big (.int .i32 false) (.scalar (bvToScalar .i32 false x32)) =
        .ok bytesBe ∧
      decodeVal .little (.int .i32 false) bytesBe =
        .ok (some (.scalar (bvToScalar .i32 false (bvBswap .i32 x32)))) ∧
      encodeVal .little (.int .i32 false) (.scalar (bvToScalar .i32 false x32)) =
        .ok bytesLe ∧
      decodeVal .big (.int .i32 false) bytesLe =
        .ok (some (.scalar (bvToScalar .i32 false (bvBswap .i32 x32))))) :=
  ⟨bvBswap_i8 x8, bvBswap_bvBswap .i64 x64, bvBswap_toLeBytes_eq .i32 x32,
    decodeVal_encodeVal_bvBswap_roundtrip .i32 false x32⟩

/-- Unsigned and signed saturating arithmetic clamping bounds and MIR
`evalBinOp` agreement canaries on `u32` and `i32`, plus concrete 8-bit unsigned
and signed clamp edge cases. -/
theorem canary_bitIntrinsic_saturating_arith
    (x32 y32 : BitVec (8 * IntWidth.i32.byteSize)) :
    (∃ sum : BitVec (8 * IntWidth.i32.byteSize), ∃ ovf : Bool,
      evalBinOp .addWithOverflow (.scalar (bvToScalar .i32 false x32))
          (.scalar (bvToScalar .i32 false y32)) =
        .ok (.tuple [.scalar (bvToScalar .i32 false sum), .bool ovf]) ∧
      bvSaturatingAddUnsigned x32 y32 =
        if ovf then Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)
        else sum) ∧
    (∃ diff : BitVec (8 * IntWidth.i32.byteSize), ∃ ovf : Bool,
      evalBinOp .subWithOverflow (.scalar (bvToScalar .i32 true x32))
          (.scalar (bvToScalar .i32 true y32)) =
        .ok (.tuple [.scalar (bvToScalar .i32 true diff), .bool ovf]) ∧
      bvSaturatingSubSigned x32 y32 =
        if ovf then
          if Anneal.BitVecArith.msb x32 then
            Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize)
          else signedMaxBv (8 * IntWidth.i32.byteSize)
        else diff) ∧
    (Anneal.BitVecArith.sle (Anneal.BitVecArith.signBit (w := 32))
        (bvSaturatingAddSigned x32 y32) ∧
      Anneal.BitVecArith.sle (bvSaturatingAddSigned x32 y32)
        (signedMaxBv 32)) ∧
    bvSaturatingAddUnsigned (BitVec.ofNat 8 200) (BitVec.ofNat 8 100) =
      Anneal.BitVec.allOnes 8 ∧
    bvSaturatingSubUnsigned (BitVec.ofNat 8 10) (BitVec.ofNat 8 25) =
      BitVec.ofNat 8 0 ∧
    bvSaturatingAddSigned (BitVec.ofNat 8 100) (BitVec.ofNat 8 50) =
      signedMaxBv 8 ∧
    bvSaturatingSubSigned (Anneal.BitVecArith.signBit (w := 8))
        (BitVec.ofNat 8 1) =
      Anneal.BitVecArith.signBit (w := 8) := by
  refine ⟨evalBinOp_addWithOverflow_saturating_unsigned .i32 x32 y32,
    evalBinOp_subWithOverflow_saturating_signed .i32 x32 y32,
    ⟨(bvSaturatingAddSigned_bounds (by decide : 0 < 32) x32 y32).1,
      (bvSaturatingAddSigned_bounds (by decide : 0 < 32) x32 y32).2.1⟩,
    ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

/-- Exact division (`ExactDivUnsigned` / `ExactDivSigned`) MIR `evalBinOp` and
scalar array list codec (`encodeBvListBytes` / `decodeBvListBytes` /
`chunksOf_decodeVal_encodeScalarList`) canaries, including negative `INT_MIN /
-1` and `/ 0` faults. -/
theorem canary_bitIntrinsic_exactDiv_and_listCodec
    (xu yu q32 y32 : BitVec (8 * IntWidth.i32.byteSize))
    (hExU : ExactDivUnsigned xu yu)
    (hy32 : y32.toNat ≠ 0) (hNoMulOvf : signedOverflowMulBv q32 y32 = false)
    (xs32 : List (BitVec (8 * IntWidth.i32.byteSize)))
    (xs64 : List (BitVec (8 * IntWidth.i64.byteSize))) :
    (evalBinOp .div (.scalar (bvToScalar .i32 false xu))
        (.scalar (bvToScalar .i32 false yu)) =
      .ok (.scalar (bvToScalar .i32 false (Anneal.BitVec.udiv xu yu))) ∧
      evalBinOp .mul
          (.scalar (bvToScalar .i32 false (Anneal.BitVec.udiv xu yu)))
          (.scalar (bvToScalar .i32 false yu)) =
        .ok (.scalar (bvToScalar .i32 false xu))) ∧
    bvSdiv (Anneal.BitVec.mul q32 y32) y32 = q32 ∧
    evalBinOp .div (.scalar (bvToScalar .i32 false xu))
        (.scalar (bvToScalar .i32 false
          (BitVec.ofNat (8 * IntWidth.i32.byteSize) 0))) =
      .error .undefined ∧
    evalBinOp .div
        (.scalar (bvToScalar .i32 true
          (Anneal.BitVecArith.signBit (w := 8 * IntWidth.i32.byteSize))))
        (.scalar (bvToScalar .i32 true
          (Anneal.BitVec.allOnes (8 * IntWidth.i32.byteSize)))) =
      .error .undefined ∧
    decodeBvListBytes .little .i32 (encodeBvListBytes .little .i32 xs32) =
      xs32 ∧
    decodeBvListBytes .big .i64 (encodeBvListBytes .big .i64 xs64) = xs64 ∧
    (Anneal.ListChunks.chunksOf IntWidth.i32.byteSize
        (encodeScalarListAllocBytes .little .i32 none xs32)).map
        (decodeVal .little (.int .i32 false)) =
      xs32.map (fun x => .ok (some (.scalar (bvToScalar .i32 false x)))) ∧
    (encodeBvListBytes .big .i64 xs64).length = xs64.length * 8 :=
  ⟨evalBinOp_div_mul_exact_unsigned .i32 hExU,
    bvSdiv_mul_cancel_right (by decide : 0 < 8 * IntWidth.i32.byteSize) hy32
      hNoMulOvf,
    evalBinOp_div_unsigned_zero_fault xu _ rfl,
    evalBinOp_div_signed_min_neg_one_fault .i32,
    decodeBvListBytes_encodeBvListBytes .little .i32 xs32,
    decodeBvListBytes_encodeBvListBytes .big .i64 xs64,
    chunksOf_decodeVal_encodeScalarList .little .i32 false xs32,
    length_encodeBvListBytes .big .i64 xs64⟩

end Anneal.Core

end
