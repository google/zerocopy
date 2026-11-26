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
public import Init.Data.Nat.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Trusted.MirSemantics.CanaryFixtures
public import Anneal.InitLemmas
public import Anneal.MirWp.Core
public import Anneal.MirWp.Scalars
public import Anneal.MirWp.V2Memory
public import Anneal.CnfOrd.Ord
public import Anneal.CnfOrd.Worklist
public import Anneal.StepBound

public section

/-!
# Quantitative Step-Bound Canaries (`Anneal.StepBound.Canaries`)

Non-bundled (`bundle-manifest.json`-excluded) verification suite exercising
`Anneal.StepBound` abstractions end-to-end against concrete and symbolic MIR
programs (`0` banned tactics, `0` `._unsafe_rec`, `0` `sorry`):

1. **Profile v1 (`canary_v1_progAddU32`):** Exact step bound (`2`) via
   `ExecWithinSteps` and `wellFormed_and_spec_of_execWithinSteps`.
2. **Real Profile v2 `O(N)` Slice-Cursor Loop (`progV2SliceScan`):** Symbolic
   caller `&[u8]` scanner (`sliceLen`, `switchInt`, `add`,
   `sliceGetUncheckedRangeFrom`) proved well-formed, terminating, and bounded by
   `4 * len.toNat + 6` via `v2_loop_const_bound` / `v2_adequacy_bounded`,
   `v2_loop_byte_credit`, `execWithinStepsV2_of_setup_loop`,
   `execWithinStepsV2_of_bodyCtx`, and `v2_loop_rank_const_bound`, plus a
   tight-budget (`9 < 10`) refutation on 1 byte.
3. **`CnfOrdBridge` Canaries (`progV2Lex2Loop`, `Worklist`, `progV2Tick`):**
   Exact non-wrapping `lex2Bound` quadratic step ceiling + `< ω^ω` extraction
   (`execWithinStepsV2_of_cnfOrd`), non-empty multi-tier `WorklistPool` step
   extraction (`4 -> 2 -> 0 -> []`, refuting under-budget `14 < 15`), and
   reactive per-frame prefix latency (`frames ≤ k ≤ 3 * frames`, non-trivial
   `tickYielded` predicate) on a non-terminating ticker kernel.
4. **Negative & `--panic abort` Refutation Canaries:** Divergence
   (`DivergesV2`), memory-fault (`FaultKind.undefined`), insufficient step
   budget (`bound ≤ k`), postcondition mismatch, and `EffectMaskV2.noAbort`
   `.aborted` refutation.
-/

namespace Anneal.StepBound.Canaries

open Trusted.MirAst Trusted.MirSemantics
open Anneal.InitLemmas Anneal.MirWp Anneal.CnfOrd Anneal.StepBound

@[expose] def usizeTy : MirTy := .int .isize false

@[expose] def u64Ty : MirTy := .int .i64 false

@[expose] def u8TyLocal : MirTy := .int .i8 false

@[expose] def sliceU8Ty : MirTy := .ref .shared (.slice (.int .i8 false))

@[expose] def rangeFromUsizeTy : MirTy := .rangeFrom usizeTy

@[expose] noncomputable def usizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 n)⟩

@[expose] noncomputable def u64Val (n : Nat) : Val :=
  .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 n)⟩

private theorem intWidthModulus_isize_eq :
    intWidthModulus .isize = Nat.pow 2 64 := rfl

private theorem intWidthModulus_i64_eq :
    intWidthModulus .i64 = Nat.pow 2 64 := rfl

private theorem isizeMaxBytes_lt_pow64 : isizeMaxBytes < Nat.pow 2 64 := by
  decide

private theorem usizeVal_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    usizeVal n = .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩ := by
  unfold usizeVal
  rw [truncateBits_ofNat_of_lt .isize h]

private theorem u64Val_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    u64Val n = .scalar ⟨.i64, false, BitVec.ofNat 128 n⟩ := by
  unfold u64Val
  rw [truncateBits_ofNat_of_lt .i64 h]

private theorem bv128_ofNat_toNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (BitVec.ofNat 128 n).toNat = n := by
  change Nat.mod n (Nat.pow 2 128) = n
  exact nat_mod_eq_of_lt (Nat.lt_trans h (by decide))

private theorem scalar_switch_nonzero {w : IntWidth} {k tYes tNo : Nat}
    (hk : k + 1 < Nat.pow 2 64)
    (hTrunc : truncateBits w (BitVec.ofNat 128 (k + 1)) =
      BitVec.ofNat 128 (k + 1))
    (hZero : truncateBits w (BitVec.ofNat 128 0) = BitVec.ofNat 128 0) :
    evalSwitchBranches w (BitVec.ofNat 128 (k + 1)) tNo
      [(BitVec.ofNat 128 0, tYes)] = .ok tNo := by
  unfold evalSwitchBranches
  have hGuard0 : (truncateBits w (BitVec.ofNat 128 0) != BitVec.ofNat 128 0) =
      false := by
    rw [hZero]
    rfl
  rw [ite_bool_false hGuard0]
  have hNe :
      (truncateBits w (BitVec.ofNat 128 (k + 1)) ==
        truncateBits w (BitVec.ofNat 128 0)) = false := by
    rw [hTrunc, hZero]
    cases hEq : (BitVec.ofNat 128 (k + 1) == BitVec.ofNat 128 0) with
    | false => rfl
    | true =>
      have hValEq : (BitVec.ofNat 128 (k + 1)).toNat =
          (BitVec.ofNat 128 0).toNat :=
        congrArg BitVec.toNat (beq_iff_eq.mp hEq)
      rw [bv128_ofNat_toNat_lt hk] at hValEq
      cases hValEq
  rw [ite_bool_false hNe]
  rfl

private theorem evalBinOp_sub_u64_one {m : Nat} (hm : m + 1 < Nat.pow 2 64) :
    evalBinOp .sub (.scalar ⟨.i64, false, BitVec.ofNat 128 (m + 1)⟩)
      (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩) =
    .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 m⟩) := by
  have hmLt : m < Nat.pow 2 64 := Nat.lt_of_succ_lt hm
  have h₁ : (BitVec.ofNat 128 (m + 1)).toNat < intWidthModulus .i64 := by
    rw [intWidthModulus_i64_eq, bv128_ofNat_toNat_lt hm]
    exact hm
  have h₂ : (BitVec.ofNat 128 1).toNat < intWidthModulus .i64 := by
    decide
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false (b := BinOp.sub.isShift) rfl,
    ite_bool_false (b := !(IntWidth.i64.beq .i64 && false == false)) rfl,
    decodeScalar_unsigned_of_lt h₁, decodeScalar_unsigned_of_lt h₂]
  dsimp only [evalArithOp]
  rw [bv128_ofNat_toNat_lt hm,
    bv128_ofNat_toNat_lt (by decide : 1 < Nat.pow 2 64)]
  have hDiff : Int.ofNat (m + 1) - Int.ofNat 1 = Int.ofNat m := by
    change Int.subNatNat (m + 1) 1 = Int.ofNat m
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le m)),
      Nat.add_sub_cancel]
  rw [ite_bool_false (b := (false && _)) rfl,
    ite_bool_false (b := (false && false && _)) rfl,
    hDiff, truncateScalar_unsigned_eq]
  dsimp only
  rw [ite_bool_false (b := (_ && BinOp.sub.isUnchecked)) (Bool.and_false _),
    ite_bool_false (b := BinOp.sub.isOverflowing) rfl]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨.i64, false, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBits_bvOfInt_ofNat_toNat, intWidthModulus_i64_eq,
    nat_mod_eq_of_lt hmLt, bv128_ofNat_toNat_lt hmLt]

private theorem list_append_nil {α : Type} : ∀ (xs : List α), xs ++ [] = xs
  | [] => rfl
  | x :: xs => congrArg (fun ys => x :: ys) (list_append_nil xs)

private theorem evalPrimitiveOperandV2_copy_local {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hPrim : isPrimitiveReadableTy ty = true) :
    evalPrimitiveOperandV2 bodyLocals locals mem (.copy ⟨lid, []⟩) =
      .ok (v, locals, mem) := by
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [ite_bool_false (by rw [hPrim]; rfl)]

private theorem evalPrimitiveOperandV2_const_int {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {cTy : MirTy}
    {w : IntWidth} {s : Bool} {bits : BitVec 128}
    (hCTy : cTy = .int w s)
    (hBne : (truncateBits w bits != bits) = false)
    (hTrunc : truncateBits w bits = bits)
    (hPrim : isPrimitiveReadableTy cTy = true) :
    evalPrimitiveOperandV2 bodyLocals locals mem
        (.constant ⟨cTy, .scalar bits⟩) =
      .ok (.scalar ⟨w, s, bits⟩, locals, mem) := by
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2
  dsimp only
  rw [hCTy]
  unfold evalConstLit
  dsimp only
  rw [ite_bool_false hBne]
  dsimp only
  rw [hCTy] at hPrim
  rw [ite_bool_false (by rw [hPrim]; rfl), hTrunc]

private theorem evalRvalueV2_arith_local_const {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {dstTy cTy : MirTy}
    {op : BinOp} (hOp : op = .add ∨ op = .sub)
    {lid : LocalId} {ty : MirTy} {v : Val}
    {w : IntWidth} {s : Bool} {bits : BitVec 128} {res : Val}
    (hCTy : cTy = .int w s)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hPrimL : isPrimitiveReadableTy ty = true)
    (hBne : (truncateBits w bits != bits) = false)
    (hTrunc : truncateBits w bits = bits)
    (hPrimR : isPrimitiveReadableTy cTy = true)
    (hBin : evalBinOp op v (.scalar ⟨w, s, bits⟩) = .ok res) :
    evalRvalueV2 bodyLocals locals mem dstTy
        (.binaryOp op (.copy ⟨lid, []⟩)
          (.constant ⟨cTy, .scalar bits⟩)) =
      .ok (res, locals, mem) := by
  have hL := evalPrimitiveOperandV2_copy_local (mem := mem) hTy hSlot hSup hPrimL
  have hR := evalPrimitiveOperandV2_const_int (bodyLocals := bodyLocals)
    (locals := locals) (mem := mem) (cTy := cTy) (w := w) (s := s)
    hCTy hBne hTrunc hPrimR
  cases hOp with
  | inl h | inr h =>
    rw [h] at hBin
    rw [h]
    unfold evalRvalueV2
    dsimp only
    rw [hL]
    dsimp only
    rw [hR]
    dsimp only
    rw [hBin]

private theorem checkValV2_int_scalar {w : IntWidth} {s : Bool}
    {bits : BitVec 128}
    (hTrunc : truncateBits w bits = bits) :
    checkValV2 (.scalar ⟨w, s, bits⟩) (.int w s) = true := by
  have hWf : ScalarVal.wf ⟨w, s, bits⟩ = true := by
    rw [← hTrunc]
    exact scalarWf_truncateBits w s bits
  unfold checkValV2 checkVal
  dsimp only [Val.ty?]
  rw [hWf]
  exact mirTy_beq_refl (.int w s)

private theorem checkValV2_usizeVal (n : Nat) :
    checkValV2 (usizeVal n) usizeTy = true :=
  checkValV2_int_scalar (truncateBits_idem .isize (BitVec.ofNat 128 n))

private theorem checkValV2_u64Val (n : Nat) :
    checkValV2 (u64Val n) u64Ty = true :=
  checkValV2_int_scalar (truncateBits_idem .i64 (BitVec.ofNat 128 n))

private theorem not_reachesDoneWithinV2_false {p : Program} :
    ∀ (b : Nat) (s : State), ¬ ReachesDoneWithinV2 p (fun _ => False) b s
  | 0, _, h => False.elim h
  | b + 1, s, h => by
    cases h with
    | inl hDone =>
      let ⟨_, _, hFalse⟩ := hDone
      exact False.elim hFalse
    | inr hStep =>
      let ⟨s', _, hRest⟩ := hStep
      exact not_reachesDoneWithinV2_false b s' hRest

/-! ## 1. Profile v1 Canary (`progAddU32`) -/

/-- Profile v1 positive canary: `progAddU32` on `(30, 12)` terminates within
2 steps, is `WellFormed`, returns `42`, and does not diverge. -/
theorem canary_v1_progAddU32 :
    ExecWithinSteps progAddU32 queryAdd30_12 2
      (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) ∧
    WellFormed progAddU32 queryAdd30_12 ∧
    ¬ Diverges progAddU32 queryAdd30_12 := by
  have hWithin :
      ExecWithinSteps progAddU32 queryAdd30_12 2
        (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) :=
    execWithinSteps_iff_execProg.mpr rfl
  have hSound := wellFormed_and_spec_of_execWithinSteps hWithin
  exact ⟨hWithin, hSound.1, hSound.2.2⟩

/-! ## 2. Real Profile v2 `O(N)` Linear Slice-Cursor Loop (`progV2SliceScan`) -/

/-- Safe Profile v2 MIR body modeling an iterative `&[u8]` cursor scanner:
`fn scan_slice(s: &[u8]) -> usize`. Uses `CoreCallOp.sliceLen`, `switchInt`,
`BinOp.add`, and `CoreCallOp.sliceGetUncheckedRangeFrom` (`&s[1..]`). -/
@[expose] noncomputable def bodyV2SliceScan : Body := {
  argumentCount := 1
  locals := [usizeTy, sliceU8Ty, usizeTy, rangeFromUsizeTy]
  basicBlocks := [
    {
      statements := [
        .assign ⟨0, []⟩
          (.use (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨3, []⟩
          (.aggregateRangeFrom usizeTy
            (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := []
      terminator := .coreCall .sliceLen [.copy ⟨1, []⟩] ⟨2, []⟩
        (some 2) .unreachable
    },
    {
      statements := []
      terminator := .switchInt (.copy ⟨2, []⟩) {
        branches := [(BitVec.ofNat 128 0, 4)]
        otherwise := 3
      }
    },
    {
      statements := [
        .assign ⟨0, []⟩
          (.binaryOp .add (.copy ⟨0, []⟩)
            (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .coreCall .sliceGetUncheckedRangeFrom
        [.copy ⟨1, []⟩, .copy ⟨3, []⟩] ⟨1, []⟩ (some 1) .unreachable
    },
    {
      statements := []
      terminator := .return_
    }
  ]
  isUnsafe := false
  identity := "canary_v2_slice_scan"
}

/-- Profile v2 program whose entry body is `bodyV2SliceScan`. -/
@[expose] noncomputable def progV2SliceScan : Program := {
  bodies := [bodyV2SliceScan]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

private theorem bodyV2SliceScan_admitted :
    BodyStaticAdmittedV2 progV2SliceScan bodyV2SliceScan = true := rfl

private noncomputable def sliceScanState (bIdx sIdx : Nat)
    (l0 l1 l2 l3 : LocalSlot) (cm : CallerMemory) (m : MemoryState) : State :=
  ⟨[⟨0, bIdx, sIdx, [l0, l1, l2, l3], none, none, none⟩], cm, m⟩

private noncomputable def sliceScanLoopState (bIdx sIdx acc : Nat)
    (curPtr : PtrVal) (rem : Nat) (opt2 : Option Val) (cm : CallerMemory) :
    State :=
  sliceScanState bIdx sIdx
    (.immediate (some (usizeVal acc)))
    (.immediate (some (.slicePtr curPtr (UInt64.ofNat rem))))
    (.immediate opt2)
    (.immediate (some (.rangeFrom (UInt64.ofNat 1))))
    cm
    (entryMemoryWithCaller cm)

private def SliceScanInv (q : Query) (origLen rem : Nat) (s : State) : Prop :=
  ∃ (curPtr : PtrVal) (opt2 : Option Val),
    rem ≤ origLen ∧
    origLen < isizeMaxBytes ∧
    validCallerMemory q.callerMem = true ∧
    curPtr.width = .isize ∧
    sliceFromRawPartsCheck (entryMemoryWithCaller q.callerMem) false 1 0
      curPtr (UInt64.ofNat rem) =
      .ok (.slicePtr curPtr (UInt64.ofNat rem)) ∧
    s = sliceScanLoopState 1 0 (origLen - rem) curPtr rem opt2 q.callerMem

private theorem sliceScan_setup_step0 (ptr : PtrVal) (len : UInt64)
    (cm : CallerMemory) :
    evalStepV2 progV2SliceScan
      (sliceScanState 0 0 (.immediate none)
        (.immediate (some (.slicePtr ptr len)))
        (.immediate none) (.immediate none)
        cm (entryMemoryWithCaller cm)) =
    .step
      (sliceScanState 0 1 (.immediate (some (usizeVal 0)))
        (.immediate (some (.slicePtr ptr len)))
        (.immediate none) (.immediate none)
        cm (entryMemoryWithCaller cm)) := rfl

private theorem sliceScan_setup_step1 (ptr : PtrVal) (len : UInt64)
    (cm : CallerMemory) :
    evalStepV2 progV2SliceScan
      (sliceScanState 0 1 (.immediate (some (usizeVal 0)))
        (.immediate (some (.slicePtr ptr len)))
        (.immediate none) (.immediate none)
        cm (entryMemoryWithCaller cm)) =
    .step
      (sliceScanState 0 2 (.immediate (some (usizeVal 0)))
        (.immediate (some (.slicePtr ptr len)))
        (.immediate none) (.immediate (some (.rangeFrom (UInt64.ofNat 1))))
        cm (entryMemoryWithCaller cm)) := rfl

private theorem sliceScan_setup_step2 (ptr : PtrVal) (len : UInt64)
    (cm : CallerMemory) :
    evalStepV2 progV2SliceScan
      (sliceScanState 0 2 (.immediate (some (usizeVal 0)))
        (.immediate (some (.slicePtr ptr len)))
        (.immediate none) (.immediate (some (.rangeFrom (UInt64.ofNat 1))))
        cm (entryMemoryWithCaller cm)) =
    .step
      (sliceScanState 1 0 (.immediate (some (usizeVal 0)))
        (.immediate (some (.slicePtr ptr len)))
        (.immediate none) (.immediate (some (.rangeFrom (UInt64.ofNat 1))))
        cm (entryMemoryWithCaller cm)) := rfl

private theorem sliceScan_setup_bounded {q : Query} {ptrAid : Option AllocId}
    {ptrOff len : UInt64}
    (hArgs : q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len])
    (hValid : ValidEntryArgsV2 bodyV2SliceScan q)
    {s₀ : State}
    (hInit : initStateV2 progV2SliceScan q = .ok s₀) :
    BoundedReachV2 progV2SliceScan (SliceScanInv q len.toNat len.toNat) 3 s₀ := by
  have hParams :
      (bodyV2SliceScan.locals.drop 1).take bodyV2SliceScan.argumentCount =
        [.ref .shared (.slice (.int .i8 false))] := rfl
  let ⟨pAid, pOff, len', hArgs', hCM, hRef⟩ :=
    validEntryArgsV2_slice_u8_inv hParams hValid
  rw [hArgs] at hArgs'
  cases hArgs'
  have hSlice := sliceCheck_of_refValidInMem hRef
  let ⟨_, hLenLt, _, _⟩ := sliceFromRawPartsCheck_u8_inv hSlice
  have hInitExp :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := q)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  have hEqInit := hInit.symm.trans hInitExp
  cases hEqInit
  have hDef : progV2SliceScan.entryDefId = 0 := rfl
  rw [hDef]
  have hS0 :
      ⟨[⟨0, 0, 0, initLocalsLoop bodyV2SliceScan q.args 0 bodyV2SliceScan.locals,
          none, none, none⟩], q.callerMem,
        entryMemoryForArgsV2 q.callerMem
          (List.take bodyV2SliceScan.argumentCount (List.drop 1 bodyV2SliceScan.locals))
          q.args⟩ =
      sliceScanState 0 0 (.immediate none)
        (.immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)))
        (.immediate none) (.immediate none)
        q.callerMem (entryMemoryWithCaller q.callerMem) := by
    rw [hArgs]
    rfl
  rw [hS0]
  have hSteps :
      StepsToV2 progV2SliceScan 3
        (sliceScanState 0 0 (.immediate none)
          (.immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)))
          (.immediate none) (.immediate none)
          q.callerMem (entryMemoryWithCaller q.callerMem))
        (sliceScanLoopState 1 0 (len.toNat - len.toNat)
          ⟨ptrAid, ptrOff, .isize⟩ len.toNat none q.callerMem) := by
    rw [Nat.sub_self]
    unfold sliceScanLoopState
    rw [uint64_ofNat_toNat len]
    refine StepsToV2.step
      (stepV2_iff_evalStepV2.mpr
        (sliceScan_setup_step0 ⟨ptrAid, ptrOff, .isize⟩ len q.callerMem))
      (StepsToV2.step
        (stepV2_iff_evalStepV2.mpr
          (sliceScan_setup_step1 ⟨ptrAid, ptrOff, .isize⟩ len q.callerMem))
        (StepsToV2.single
          (stepV2_iff_evalStepV2.mpr
            (sliceScan_setup_step2 ⟨ptrAid, ptrOff, .isize⟩ len q.callerMem))))
  rw [← uint64_ofNat_toNat len] at hSlice
  refine ⟨3, _, Nat.le_refl 3, hSteps,
    ⟨⟨ptrAid, ptrOff, .isize⟩, none, Nat.le_refl _, hLenLt, hCM, rfl, hSlice, rfl⟩⟩

private theorem sliceScan_bb1_sliceLen (acc rem : Nat) (curPtr : PtrVal)
    (opt2 : Option Val) (cm : CallerMemory)
    (hRemLt : rem < Nat.pow 2 64)
    (hSlice :
      sliceFromRawPartsCheck (entryMemoryWithCaller cm) false 1 0 curPtr
        (UInt64.ofNat rem) = .ok (.slicePtr curPtr (UInt64.ofNat rem))) :
    evalStepV2 progV2SliceScan
      (sliceScanLoopState 1 0 acc curPtr rem opt2 cm) =
    .step
      (sliceScanLoopState 2 0 acc curPtr rem (some (usizeVal rem)) cm) := by
  have hRef :
      refValidInMem (entryMemoryWithCaller cm) .shared
        (.slice (.int .i8 false))
        (.slicePtr curPtr (UInt64.ofNat rem)) = .ok () :=
    refValidInMem_of_sliceCheck hSlice
  have hRemNat : (UInt64.ofNat rem).toNat = rem := toNat_uint64_ofNat_lt hRemLt
  unfold evalStepV2 sliceScanLoopState sliceScanState
  change evalTerminatorV2 bodyV2SliceScan
      { statements := [],
        terminator := .coreCall .sliceLen [.copy ⟨1, []⟩] ⟨2, []⟩
          (some 2) .unreachable }
      ⟨0, 1, 0,
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat rem))),
         .immediate opt2,
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        none, none, none⟩
      (entryMemoryWithCaller cm) cm = _
  unfold evalTerminatorV2
  dsimp only
  change (match evalArgOperandsV2 bodyV2SliceScan.locals
      [.immediate (some (usizeVal acc)),
       .immediate (some (.slicePtr curPtr (UInt64.ofNat rem))),
       .immediate opt2,
       .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
      (entryMemoryWithCaller cm) [.copy ⟨1, []⟩] with
    | .error k => StepResult.fault k
    | .ok (typedArgs, locals1, mem1) =>
      match execCoreCallWithMem mem1 .sliceLen typedArgs usizeTy with
      | .error k => StepResult.fault k
      | .ok (resVal, mem1') =>
        match writePlaceV2 bodyV2SliceScan.locals locals1 mem1'
            ⟨2, []⟩ usizeTy resVal with
        | .error k => StepResult.fault k
        | .ok (locals2, mem2) =>
          jumpToBlock
            ⟨0, 1, 0, locals2, none, none, none⟩ mem2 cm 2) = _
  have hArgEval :
      evalArgOperandsV2 bodyV2SliceScan.locals
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat rem))),
         .immediate opt2,
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
        (entryMemoryWithCaller cm) [.copy ⟨1, []⟩] =
      .ok ([(sliceU8Ty, .slicePtr curPtr (UInt64.ofNat rem))],
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat rem))),
         .immediate opt2,
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        entryMemoryWithCaller cm) := rfl
  rw [hArgEval]
  dsimp only
  have hCore :
      execCoreCallOp (entryMemoryWithCaller cm) .sliceLen
        [(sliceU8Ty, .slicePtr curPtr (UInt64.ofNat rem))] usizeTy =
      .ok (usizeVal rem) := by
    unfold execCoreCallOp sliceU8Ty
    dsimp only
    rw [hRef]
    dsimp only
    rw [hRemNat]
    rfl
  unfold execCoreCallWithMem
  rw [hCore]
  dsimp only
  have hCheckUsize : checkValV2 (usizeVal rem) usizeTy = true :=
    checkValV2_usizeVal rem
  have hWrite :
      writePlaceV2 bodyV2SliceScan.locals
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat rem))),
         .immediate opt2,
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
        (entryMemoryWithCaller cm) ⟨2, []⟩ usizeTy (usizeVal rem) =
      .ok (
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat rem))),
         .immediate (some (usizeVal rem)),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        entryMemoryWithCaller cm) :=
    writePlaceV2_immediate_ok hCheckUsize rfl rfl
  rw [hWrite]
  rfl

private theorem sliceScan_bb2_zero (acc : Nat) (curPtr : PtrVal)
    (cm : CallerMemory) :
    evalStepV2 progV2SliceScan
      (sliceScanLoopState 2 0 acc curPtr 0 (some (usizeVal 0)) cm) =
    .step
      (sliceScanLoopState 4 0 acc curPtr 0 (some (usizeVal 0)) cm) := rfl

private theorem sliceScan_bb2_succ (acc k : Nat) (curPtr : PtrVal)
    (cm : CallerMemory) (hLt : k + 1 < Nat.pow 2 64) :
    evalStepV2 progV2SliceScan
      (sliceScanLoopState 2 0 acc curPtr (k + 1)
        (some (usizeVal (k + 1))) cm) =
    .step
      (sliceScanLoopState 3 0 acc curPtr (k + 1)
        (some (usizeVal (k + 1))) cm) := by
  unfold evalStepV2 sliceScanLoopState sliceScanState
  change evalTerminatorV2 bodyV2SliceScan
      { statements := [],
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 4)]
          otherwise := 3
        } }
      ⟨0, 2, 0,
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (usizeVal (k + 1))),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        none, none, none⟩
      (entryMemoryWithCaller cm) cm = _
  unfold evalTerminatorV2
  dsimp only
  rw [usizeVal_ofNat_lt hLt]
  have hOp :
      evalPrimitiveOperandV2 bodyV2SliceScan.locals
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 (k + 1)⟩)),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
        (entryMemoryWithCaller cm) (.copy ⟨2, []⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (k + 1)⟩,
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 (k + 1)⟩)),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        entryMemoryWithCaller cm) := rfl
  rw [hOp]
  dsimp only
  rw [scalar_switch_nonzero hLt (truncateBits_ofNat_of_lt .isize hLt) rfl]
  rfl

private theorem sliceScan_bb3_stmt0 (acc k : Nat) (curPtr : PtrVal)
    (cm : CallerMemory)
    (hAccLt : acc < Nat.pow 2 64)
    (hNextLt : acc + 1 < Nat.pow 2 64) :
    evalStepV2 progV2SliceScan
      (sliceScanLoopState 3 0 acc curPtr (k + 1)
        (some (usizeVal (k + 1))) cm) =
    .step
      (sliceScanLoopState 3 1 (acc + 1) curPtr (k + 1)
        (some (usizeVal (k + 1))) cm) := by
  unfold evalStepV2 sliceScanLoopState sliceScanState
  change evalStatementV2 bodyV2SliceScan
      ⟨0, 3, 0,
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (usizeVal (k + 1))),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        none, none, none⟩
      (entryMemoryWithCaller cm) cm
      (.assign ⟨0, []⟩
        (.binaryOp .add (.copy ⟨0, []⟩)
          (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩))) = _
  unfold evalStatementV2
  dsimp only
  rw [usizeVal_ofNat_lt hAccLt, usizeVal_ofNat_lt hNextLt]
  change (match evalRvalueV2 bodyV2SliceScan.locals
      [.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 acc⟩)),
       .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
       .immediate (some (usizeVal (k + 1))),
       .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
      (entryMemoryWithCaller cm) usizeTy
      (.binaryOp .add (.copy ⟨0, []⟩)
        (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩)) with
    | .error k => StepResult.fault k
    | .ok (val, locals1, mem1) =>
      match writePlaceDestV2 locals1 mem1 (.local 0) usizeTy val with
      | .error k => StepResult.fault k
      | .ok (locals2, mem2) =>
        StepResult.step
          ({ frames := [⟨0, 3, 1, locals2, none, none, none⟩],
             callerMem := cm, mem := mem2 } : State)) = _
  have hBvAcc : (BitVec.ofNat 128 acc).toNat < intWidthModulus .isize := by
    rw [intWidthModulus_isize_eq, bv128_ofNat_toNat_lt hAccLt]
    exact hAccLt
  have hBvOne : (BitVec.ofNat 128 1).toNat < intWidthModulus .isize := by
    decide
  have hBin :
      evalBinOp .add
        (.scalar ⟨.isize, false, BitVec.ofNat 128 acc⟩)
        (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (acc + 1)⟩) := by
    have hE := evalBinOp_add_unsigned_eq .isize hBvAcc hBvOne
    rw [bv128_ofNat_toNat_lt hAccLt,
      bv128_ofNat_toNat_lt (by decide : 1 < Nat.pow 2 64),
      intWidthModulus_isize_eq, nat_mod_eq_of_lt hNextLt] at hE
    exact hE
  have hRval := evalRvalueV2_arith_local_const
    (bodyLocals := bodyV2SliceScan.locals)
    (locals := [
      .immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 acc⟩)),
      .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
      .immediate (some (usizeVal (k + 1))),
      .immediate (some (.rangeFrom (UInt64.ofNat 1)))])
    (mem := entryMemoryWithCaller cm) (dstTy := usizeTy) (cTy := usizeTy)
    (op := .add) (Or.inl rfl) (lid := 0) (ty := usizeTy)
    (w := .isize) (s := false) (bits := BitVec.ofNat 128 1)
    rfl rfl rfl rfl rfl rfl rfl rfl hBin
  rw [hRval]
  dsimp only
  have hCheck :
      checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 (acc + 1)⟩)
        usizeTy = true :=
    checkValV2_int_scalar (truncateBits_ofNat_of_lt .isize hNextLt)
  have hWr :
      writePlaceDestV2
        [.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 acc⟩)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (usizeVal (k + 1))),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
        (entryMemoryWithCaller cm) (.local 0) usizeTy
        (.scalar ⟨.isize, false, BitVec.ofNat 128 (acc + 1)⟩) =
      .ok (
        [.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 (acc + 1)⟩)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (usizeVal (k + 1))),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        entryMemoryWithCaller cm) := by
    unfold writePlaceDestV2
    rw [ite_bool_false (by rw [hCheck]; rfl)]
    rfl
  rw [hWr]

private theorem sliceScan_bb3_term (acc k : Nat) (curPtr : PtrVal)
    (cm : CallerMemory)
    (hCm : validCallerMemory cm = true)
    (hCurW : curPtr.width = .isize)
    (hRemLt : k + 1 < Nat.pow 2 64)
    (hSlice :
      sliceFromRawPartsCheck (entryMemoryWithCaller cm) false 1 0 curPtr
        (UInt64.ofNat (k + 1)) =
      .ok (.slicePtr curPtr (UInt64.ofNat (k + 1)))) :
    let nextPtr : PtrVal :=
      ⟨curPtr.allocId, UInt64.ofNat (curPtr.offsetBytes.toNat + 1), .isize⟩
    evalStepV2 progV2SliceScan
      (sliceScanLoopState 3 1 acc curPtr (k + 1)
        (some (usizeVal (k + 1))) cm) =
    .step
      (sliceScanLoopState 1 0 acc nextPtr k
        (some (usizeVal (k + 1))) cm) ∧
    sliceFromRawPartsCheck (entryMemoryWithCaller cm) false 1 0 nextPtr
      (UInt64.ofNat k) = .ok (.slicePtr nextPtr (UInt64.ofNat k)) := by
  intro nextPtr
  let ⟨_, _, hNoneInv, hSomeInv⟩ := sliceFromRawPartsCheck_u8_inv hSlice
  have hLenNat : (UInt64.ofNat (k + 1)).toNat = k + 1 :=
    toNat_uint64_ofNat_lt hRemLt
  have hOffLt : curPtr.offsetBytes.toNat + 1 < Nat.pow 2 64 := by
    cases hAid : curPtr.allocId with
    | none =>
      let ⟨_, hLen0⟩ := hNoneInv hAid
      rw [hLenNat] at hLen0
      cases hLen0
    | some aid =>
      let ⟨a, hFind, _, hBnd, _, _⟩ := hSomeInv aid hAid
      have hBytesLt := entryMemoryWithCaller_bytes_lt cm hCm hFind
      have hOneLeLen : curPtr.offsetBytes.toNat + 1 ≤
          curPtr.offsetBytes.toNat + (k + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k))
          curPtr.offsetBytes.toNat
      rw [hLenNat] at hBnd
      exact Nat.lt_of_le_of_lt (Nat.le_trans hOneLeLen hBnd) hBytesLt
  have hNextSliceRaw := sliceFromRawPartsCheck_u8_to_subslice 1 k
    (fun h => h) hSlice
    (by rw [hLenNat, Nat.add_comm 1 k]; exact Nat.le_refl (k + 1)) hOffLt
  have hNextSlice :
      sliceFromRawPartsCheck (entryMemoryWithCaller cm) false 1 0 nextPtr
        (UInt64.ofNat k) = .ok (.slicePtr nextPtr (UInt64.ofNat k)) := by
    change sliceFromRawPartsCheck (entryMemoryWithCaller cm) false 1 0
        ⟨curPtr.allocId, UInt64.ofNat (curPtr.offsetBytes.toNat + 1), .isize⟩
        (UInt64.ofNat k) = _
    have hW := hNextSliceRaw
    rw [hCurW] at hW
    exact hW
  have hPtrAdd := ptrAddInMem_u8_of_sliceCheck 1 hSlice
    (by rw [hLenNat]; exact Nat.succ_le_succ (Nat.zero_le k))
  have hGet :
      sliceGetUncheckedCheck (entryMemoryWithCaller cm) curPtr
        (UInt64.ofNat (k + 1)).toNat (UInt64.ofNat 1).toNat
        (UInt64.ofNat (k + 1)).toNat =
      .ok (.slicePtr nextPtr (UInt64.ofNat k)) := by
    unfold sliceGetUncheckedCheck
    have hOneNat : (UInt64.ofNat 1).toNat = 1 :=
      toNat_uint64_ofNat_lt (by decide)
    rw [hLenNat, hOneNat]
    have hG :
        (!Nat.ble 1 (k + 1) || !Nat.ble (k + 1) (k + 1)) = false := by
      rw [Nat.ble_eq_true_of_le (Nat.succ_le_succ (Nat.zero_le k)),
        Nat.ble_eq_true_of_le (Nat.le_refl (k + 1))]
      rfl
    rw [ite_bool_false hG, hPtrAdd]
    dsimp only
    change Except.ok (Val.slicePtr
        ⟨curPtr.allocId, UInt64.ofNat (curPtr.offsetBytes.toNat + 1),
          curPtr.width⟩
        (UInt64.ofNat (k + 1 - 1))) = _
    rw [hCurW, Nat.add_sub_cancel]
  have hRef := refValidInMem_of_sliceCheck (reqMut := .shared) hSlice
  have hCore := execCoreCallOp_sliceGetUncheckedRangeFrom_shared_ok hRef hGet
  have hEval :
      evalStepV2 progV2SliceScan
        (sliceScanLoopState 3 1 acc curPtr (k + 1)
          (some (usizeVal (k + 1))) cm) =
      .step
        (sliceScanLoopState 1 0 acc nextPtr k
          (some (usizeVal (k + 1))) cm) := by
    unfold evalStepV2 sliceScanLoopState sliceScanState
    change evalTerminatorV2 bodyV2SliceScan
        { statements := [
            .assign ⟨0, []⟩
              (.binaryOp .add (.copy ⟨0, []⟩)
                (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .coreCall .sliceGetUncheckedRangeFrom
            [.copy ⟨1, []⟩, .copy ⟨3, []⟩] ⟨1, []⟩ (some 1) .unreachable }
        ⟨0, 3, 1,
          [.immediate (some (usizeVal acc)),
           .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
           .immediate (some (usizeVal (k + 1))),
           .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
          none, none, none⟩
        (entryMemoryWithCaller cm) cm = _
    unfold evalTerminatorV2
    dsimp only
    change (match evalArgOperandsV2 bodyV2SliceScan.locals
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
         .immediate (some (usizeVal (k + 1))),
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
        (entryMemoryWithCaller cm) [.copy ⟨1, []⟩, .copy ⟨3, []⟩] with
      | .error k => StepResult.fault k
      | .ok (typedArgs, locals1, mem1) =>
        match execCoreCallWithMem mem1 .sliceGetUncheckedRangeFrom typedArgs
            sliceU8Ty with
        | .error k => StepResult.fault k
        | .ok (resVal, mem1') =>
          match writePlaceV2 bodyV2SliceScan.locals locals1 mem1'
              ⟨1, []⟩ sliceU8Ty resVal with
          | .error k => StepResult.fault k
          | .ok (locals2, mem2) =>
            jumpToBlock ⟨0, 3, 1, locals2, none, none, none⟩ mem2 cm 1) = _
    have hArgsOk :
        evalArgOperandsV2 bodyV2SliceScan.locals
          [.immediate (some (usizeVal acc)),
           .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
           .immediate (some (usizeVal (k + 1))),
           .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
          (entryMemoryWithCaller cm) [.copy ⟨1, []⟩, .copy ⟨3, []⟩] =
        .ok ([(sliceU8Ty, .slicePtr curPtr (UInt64.ofNat (k + 1))),
              (rangeFromUsizeTy, .rangeFrom (UInt64.ofNat 1))],
          [.immediate (some (usizeVal acc)),
           .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
           .immediate (some (usizeVal (k + 1))),
           .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
          entryMemoryWithCaller cm) := rfl
    rw [hArgsOk]
    dsimp only [sliceU8Ty, rangeFromUsizeTy, usizeTy]
    unfold execCoreCallWithMem
    rw [hCore]
    dsimp only
    have hCheckOut :
        checkValV2 (.slicePtr nextPtr (UInt64.ofNat k))
          (.ref .shared (.slice (.int .i8 false))) = true := rfl
    have hWr :
        writePlaceV2 bodyV2SliceScan.locals
          [.immediate (some (usizeVal acc)),
           .immediate (some (.slicePtr curPtr (UInt64.ofNat (k + 1)))),
           .immediate (some (usizeVal (k + 1))),
           .immediate (some (.rangeFrom (UInt64.ofNat 1)))]
          (entryMemoryWithCaller cm) ⟨1, []⟩
          (.ref .shared (.slice (.int .i8 false)))
          (.slicePtr nextPtr (UInt64.ofNat k)) =
        .ok (
          [.immediate (some (usizeVal acc)),
           .immediate (some (.slicePtr nextPtr (UInt64.ofNat k))),
           .immediate (some (usizeVal (k + 1))),
           .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
          entryMemoryWithCaller cm) :=
      writePlaceV2_immediate_ok hCheckOut rfl rfl
    rw [hWr]
    rfl
  exact ⟨hEval, hNextSlice⟩

private theorem sliceScan_bb4_return (acc : Nat) (curPtr : PtrVal)
    (opt2 : Option Val) (cm : CallerMemory) (hCm : validCallerMemory cm = true) :
    evalStepV2 progV2SliceScan
      (sliceScanLoopState 4 0 acc curPtr 0 opt2 cm) =
    .done (.returned ⟨usizeVal acc, cm⟩) := by
  unfold evalStepV2 sliceScanLoopState sliceScanState
  change evalTerminatorV2 bodyV2SliceScan
      { statements := [], terminator := .return_ }
      ⟨0, 4, 0,
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat 0))),
         .immediate opt2,
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        none, none, none⟩
      (entryMemoryWithCaller cm) cm = _
  have hRet :=
    evalTerminatorV2_return_ok
      (body := bodyV2SliceScan)
      (bb := { statements := [], terminator := .return_ })
      (frame := ⟨0, 4, 0,
        [.immediate (some (usizeVal acc)),
         .immediate (some (.slicePtr curPtr (UInt64.ofNat 0))),
         .immediate opt2,
         .immediate (some (.rangeFrom (UInt64.ofNat 1)))],
        none, none, none⟩)
      (mem := entryMemoryWithCaller cm) (callerMem := cm)
      (ps := .unwind) (hLocal := true) (oc := false)
      (retTy := usizeTy) (retVal := usizeVal acc)
      rfl rfl rfl rfl rfl rfl rfl rfl
  rw [hRet, extractCallerMemory_entry cm hCm]

private theorem sliceScan_exit_3steps {q : Query} {origLen : Nat} {s : State}
    (hInv : SliceScanInv q origLen 0 s) :
    ReachesDoneWithinV2 progV2SliceScan
      (fun out => out = .returned ⟨usizeVal origLen, q.callerMem⟩) 3 s := by
  let ⟨curPtr, opt2, _, _, hCm, _, hSlice, hEq⟩ := hInv
  rw [hEq]
  have h0 :
      evalStepV2 progV2SliceScan
        (sliceScanLoopState 1 0 (origLen - 0) curPtr 0 opt2 q.callerMem) =
      .step
        (sliceScanLoopState 2 0 (origLen - 0) curPtr 0 (some (usizeVal 0))
          q.callerMem) :=
    sliceScan_bb1_sliceLen (origLen - 0) 0 curPtr opt2 q.callerMem
      (by decide) hSlice
  have h1 := sliceScan_bb2_zero (origLen - 0) curPtr q.callerMem
  have h2 := sliceScan_bb4_return (origLen - 0) curPtr
    (some (usizeVal 0)) q.callerMem hCm
  rw [Nat.sub_zero] at h0 h1 h2
  exact reachesDoneWithinV2_of_eval_step h0
    (reachesDoneWithinV2_of_eval_step h1
      (reachesDoneWithinV2_of_eval_done h2 rfl))

private theorem sliceScan_iter_4steps {q : Query} {origLen k : Nat} {s : State}
    (hInv : SliceScanInv q origLen (k + 1) s) :
    BoundedReachV2 progV2SliceScan (SliceScanInv q origLen k) 4 s := by
  let ⟨curPtr, opt2, hLe, hOrigLt, hCm, hCurW, hSlice, hEq⟩ := hInv
  have hRemLt : k + 1 < Nat.pow 2 64 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt hLe hOrigLt) isizeMaxBytes_lt_pow64
  have hAccLt : origLen - (k + 1) < Nat.pow 2 64 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.sub_le origLen (k + 1)) hOrigLt)
      isizeMaxBytes_lt_pow64
  have hNextEq : origLen - (k + 1) + 1 = origLen - k := by
    have hK : k + 1 ≤ origLen := hLe
    have hSub : (origLen - (k + 1)) + (k + 1) = origLen :=
      Nat.sub_add_cancel hK
    have h1 : (origLen - (k + 1) + 1) + k = origLen - k + k := by
      rw [Nat.add_assoc, Nat.add_comm 1 k, hSub,
        Nat.sub_add_cancel (Nat.le_trans (Nat.le_succ k) hK)]
    exact Nat.add_right_cancel h1
  have hNextLt : origLen - (k + 1) + 1 < Nat.pow 2 64 := by
    rw [hNextEq]
    exact Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.sub_le origLen k) hOrigLt)
      isizeMaxBytes_lt_pow64
  have h0 := sliceScan_bb1_sliceLen (origLen - (k + 1)) (k + 1) curPtr opt2
    q.callerMem hRemLt hSlice
  have h1 := sliceScan_bb2_succ (origLen - (k + 1)) k curPtr q.callerMem hRemLt
  have h2 := sliceScan_bb3_stmt0 (origLen - (k + 1)) k curPtr q.callerMem
    hAccLt hNextLt
  let ⟨h3, hNextSlice⟩ := sliceScan_bb3_term (origLen - (k + 1) + 1) k curPtr
    q.callerMem hCm hCurW hRemLt hSlice
  rw [hEq]
  have hSteps :
      StepsToV2 progV2SliceScan 4
        (sliceScanLoopState 1 0 (origLen - (k + 1)) curPtr (k + 1) opt2
          q.callerMem)
        (sliceScanLoopState 1 0 (origLen - k)
          ⟨curPtr.allocId, UInt64.ofNat (curPtr.offsetBytes.toNat + 1), .isize⟩
          k (some (usizeVal (k + 1))) q.callerMem) := by
    rw [← hNextEq]
    exact StepsToV2.step (stepV2_iff_evalStepV2.mpr h0)
      (StepsToV2.step (stepV2_iff_evalStepV2.mpr h1)
        (StepsToV2.step (stepV2_iff_evalStepV2.mpr h2)
          (StepsToV2.single (stepV2_iff_evalStepV2.mpr h3))))
  refine ⟨4, _, Nat.le_refl 4, hSteps,
    ⟨⟨curPtr.allocId, UInt64.ofNat (curPtr.offsetBytes.toNat + 1), .isize⟩,
     some (usizeVal (k + 1)),
     Nat.le_trans (Nat.le_succ k) hLe, hOrigLt, hCm, rfl, hNextSlice, rfl⟩⟩

/-- Symbolic Profile v2 `O(N)` linear WCET canary: for EVERY valid `&[u8]`
caller query `q` of arbitrary byte length `len.toNat`, `progV2SliceScan` is
`WellFormedV2`, does not diverge (`¬ DivergesV2`), returns `len.toNat` with
unchanged `q.callerMem`, and completes in at most `4 * len.toNat + 6` MIR
steps (`setup = 3`, `4` per byte, `exit = 3`). -/
theorem canary_v2_slice_scan_linear_bound (q : Query)
    (ptrAid : Option AllocId) (ptrOff len : UInt64)
    (hArgs : q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len])
    (hValid : ValidEntryArgsV2 bodyV2SliceScan q) :
    ExecWithinStepsV2 progV2SliceScan q (4 * len.toNat + 6)
      (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩) ∧
    WellFormedV2 progV2SliceScan q ∧
    BehaviorV2 progV2SliceScan q
      (.returned ⟨usizeVal len.toNat, q.callerMem⟩) ∧
    ¬ DivergesV2 progV2SliceScan q ∧
    ∀ post : TerminalOut → Prop,
      post (.returned ⟨usizeVal len.toNat, q.callerMem⟩) →
      SatisfiesPostV2 progV2SliceScan q post := by
  have hInit :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := q)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  have hSetup := sliceScan_setup_bounded hArgs hValid hInit
  have hLoop := v2_loop_const_bound (SliceScanInv q len.toNat) 4 3
    (fun _ h0 => sliceScan_exit_3steps h0)
    (fun _ _ hk => sliceScan_iter_4steps hk)
  have hBound := BoundedReachV2.bind_done hSetup
    (fun s₁ hInv => hLoop len.toNat s₁ hInv)
  have hArith : 3 + (len.toNat * 4 + 3) = 4 * len.toNat + 6 := by
    rw [Nat.mul_comm len.toNat 4, ← Nat.add_assoc,
      Nat.add_comm 3 (4 * len.toNat), Nat.add_assoc]
  rw [hArith] at hBound
  exact v2_adequacy_bounded hInit hBound

/-- `v2_loop_byte_credit` instantiation on `progV2SliceScan`: confirms clean
interoperability between `BoundedReachV2` setup and progress-weighted
`K * m + C` bounds (`4 * len.toNat + 6`). -/
theorem canary_v2_slice_scan_byte_credit (q : Query)
    (ptrAid : Option AllocId) (ptrOff len : UInt64)
    (hArgs : q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len])
    (hValid : ValidEntryArgsV2 bodyV2SliceScan q) :
    ExecWithinStepsV2 progV2SliceScan q (4 * len.toNat + 6)
      (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩) := by
  have hInit :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := q)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  have hSetup := sliceScan_setup_bounded hArgs hValid hInit
  have hCredit := v2_loop_byte_credit (SliceScanInv q len.toNat) 4 3
    (fun _ h0 => sliceScan_exit_3steps h0)
    (fun cur _ hPos hInv => by
      cases cur with
      | zero => exact False.elim (Nat.lt_irrefl 0 hPos)
      | succ k =>
        let ⟨st, s', hk, hSteps, hInv'⟩ := sliceScan_iter_4steps hInv
        refine Or.inr ⟨k, st, s', Nat.lt_succ_self k, ?_, hSteps, hInv'⟩
        rw [Nat.add_sub_cancel_left, Nat.mul_one]
        exact hk)
  have hJoin := BoundedReachV2.bind_done hSetup
    (fun s₁ hInv => hCredit len.toNat s₁ hInv)
  have hArith : 3 + (4 * len.toNat + 3) = 4 * len.toNat + 6 := by
    rw [← Nat.add_assoc, Nat.add_comm 3 (4 * len.toNat), Nat.add_assoc]
  rw [hArith] at hJoin
  exact ⟨_, hInit, hJoin⟩

/-- Flagship combinator canary on `progV2SliceScan`: exercises
`execWithinStepsV2_of_setup_loop` and `execWithinStepsV2_of_bodyCtx` directly on
symbolic `&[u8]` queries. -/
theorem canary_v2_slice_scan_setup_loop_and_bodyCtx (q : Query)
    (ptrAid : Option AllocId) (ptrOff len : UInt64)
    (hArgs : q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len])
    (hValid : ValidEntryArgsV2 bodyV2SliceScan q) :
    (ExecWithinStepsV2 progV2SliceScan q (4 * len.toNat + 6)
        (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩) ∧
      WellFormedV2 progV2SliceScan q ∧
      ¬ DivergesV2 progV2SliceScan q ∧
      SatisfiesPostV2 progV2SliceScan q
        (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩)) ∧
    (ExecWithinStepsV2 (BodyCtx.mk progV2SliceScan 0 bodyV2SliceScan).entryProg
        q (4 * len.toNat + 6)
        (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩) ∧
      WellFormedV2 (BodyCtx.mk progV2SliceScan 0 bodyV2SliceScan).entryProg q ∧
      ¬ DivergesV2 (BodyCtx.mk progV2SliceScan 0 bodyV2SliceScan).entryProg q) := by
  have hInit :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := q)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  have hSetup := sliceScan_setup_bounded hArgs hValid hInit
  have hLoop :=
    execWithinStepsV2_of_setup_loop
      (post := fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩)
      (SliceScanInv q len.toNat) 3 4 3 len.toNat hInit hSetup
      (fun _ h0 => sliceScan_exit_3steps h0)
      (fun _ _ hk => Or.inr (sliceScan_iter_4steps hk))
  have hArith : 3 + (len.toNat * 4 + 3) = 4 * len.toNat + 6 := by
    rw [Nat.mul_comm len.toNat 4, ← Nat.add_assoc,
      Nat.add_comm 3 (4 * len.toNat), Nat.add_assoc]
  rw [hArith] at hLoop
  let ctx : BodyCtx := { program := progV2SliceScan, defId := 0, body := bodyV2SliceScan }
  have hEntry : ctx.entryProg = progV2SliceScan := rfl
  have hCtx :=
    execWithinStepsV2_of_bodyCtx ctx q (4 * len.toNat + 6)
      (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩)
      rfl bodyV2SliceScan_admitted hValid
      (by
        rw [hEntry]
        let ⟨s0, hI, hR⟩ := hLoop.1
        rw [hInit] at hI
        cases hI
        exact hR)
  exact ⟨⟨hLoop.1, hLoop.2.1, hLoop.2.2.1, hLoop.2.2.2.1⟩,
    ⟨hCtx.1, hCtx.2.1, hCtx.2.2.1⟩⟩

private noncomputable def sliceScanRank (s : State) : Nat :=
  match s.frames with
  | f :: _ =>
    match f.locals with
    | _ :: .immediate (some (.slicePtr _ len)) :: _ => len.toNat
    | _ => 0
  | [] => 0

/-- Rank-combinator canary on `progV2SliceScan`: exercises
`v2_loop_rank_const_bound` using `sliceScanRank` directly on the slice pointer's
remaining length. -/
theorem canary_v2_slice_scan_rank_bound (q : Query)
    (ptrAid : Option AllocId) (ptrOff len : UInt64)
    (hArgs : q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len])
    (hValid : ValidEntryArgsV2 bodyV2SliceScan q) :
    ExecWithinStepsV2 progV2SliceScan q (4 * len.toNat + 6)
      (fun out => out = .returned ⟨usizeVal len.toNat, q.callerMem⟩) := by
  have hInit :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := q)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  have hSetup := sliceScan_setup_bounded hArgs hValid hInit
  let RankInv : State → Prop := fun s =>
    ∃ rem : Nat, SliceScanInv q len.toNat rem s
  have hRankEq : ∀ rem s, SliceScanInv q len.toNat rem s →
      sliceScanRank s = rem := by
    intro rem s ⟨curPtr, opt2, hLe, hLt, _, _, _, hEq⟩
    rw [hEq]
    unfold sliceScanRank sliceScanLoopState sliceScanState
    dsimp only
    exact toNat_uint64_ofNat_lt
      (Nat.lt_of_le_of_lt hLe (Nat.lt_trans hLt isizeMaxBytes_lt_pow64))
  have hLoop :=
    v2_loop_rank_const_bound RankInv sliceScanRank 4 3
      (fun s ⟨rem, hInv⟩ => by
        cases rem with
        | zero => exact Or.inl (sliceScan_exit_3steps hInv)
        | succ k =>
          let ⟨st, s', hk, hSteps, hInv'⟩ := sliceScan_iter_4steps hInv
          refine Or.inr ⟨st, s', hk, hSteps, ⟨k, hInv'⟩, ?_⟩
          rw [hRankEq k s' hInv', hRankEq (k + 1) s hInv]
          exact Nat.lt_succ_self k)
  let ⟨kSetup, s₁, hkSetup, hStSetup, hInvInit⟩ := hSetup
  have hRInit : sliceScanRank s₁ = len.toNat := hRankEq len.toNat s₁ hInvInit
  have hDone := hLoop s₁ ⟨len.toNat, hInvInit⟩
  rw [hRInit] at hDone
  have hJoin := reachesDoneWithinV2_of_stepsTo hStSetup hDone
  have hArith : kSetup + (len.toNat * 4 + 3) ≤ 4 * len.toNat + 6 := by
    rw [Nat.mul_comm len.toNat 4, Nat.add_comm kSetup (4 * len.toNat + 3),
      Nat.add_assoc (4 * len.toNat) 3 kSetup, Nat.add_assoc (4 * len.toNat) 3 3]
    exact Nat.add_le_add_left (Nat.add_le_add_left hkSetup 3) (4 * len.toNat)
  exact ⟨_, hInit, ReachesDoneWithinV2.mono hArith hJoin⟩

/-! ## 3. `CnfOrdBridge` Canaries: `lex2Bound`, `Worklist`, Reactive -/

/-- Nested bounded-reset Profile v2 MIR body
(`fn lex2(outer: u64, inner: u64) -> u64`): decrements `inner` when positive,
and decrements `outer` + resets
`inner := 2` when `inner == 0` and `outer > 0`. Exercises
`v2_loop_lex2_bounded_reset` (`ω^1 * outer + ω^0 * inner`,
`resetCap = 2`). -/
@[expose] noncomputable def bodyV2Lex2Loop : Body := {
  argumentCount := 2
  locals := [u64Ty, u64Ty, u64Ty]
  basicBlocks := [
    {
      statements := [
        .assign ⟨0, []⟩ (.use (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := []
      terminator := .switchInt (.copy ⟨2, []⟩) {
        branches := [(BitVec.ofNat 128 0, 3)]
        otherwise := 2
      }
    },
    {
      statements := [
        .assign ⟨2, []⟩
          (.binaryOp .sub (.copy ⟨2, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩
          (.binaryOp .add (.copy ⟨0, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) {
        branches := [(BitVec.ofNat 128 0, 5)]
        otherwise := 4
      }
    },
    {
      statements := [
        .assign ⟨1, []⟩
          (.binaryOp .sub (.copy ⟨1, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨2, []⟩
          (.use (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 2)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := []
      terminator := .return_
    }
  ]
  isUnsafe := false
  identity := "canary_v2_lex2_loop"
}

/-- Profile v2 program whose entry body is `bodyV2Lex2Loop`. -/
@[expose] noncomputable def progV2Lex2Loop : Program := {
  bodies := [bodyV2Lex2Loop]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

@[expose] noncomputable def lex2State (bIdx sIdx : Nat) (l0 l1 l2 : LocalSlot) :
    State :=
  ⟨[⟨0, bIdx, sIdx, [l0, l1, l2], none, none, none⟩], ⟨[]⟩,
    entryMemoryWithCaller ⟨[]⟩⟩

@[expose] noncomputable def lex2LoopState (bIdx sIdx acc o i : Nat) : State :=
  lex2State bIdx sIdx
    (.immediate (some (u64Val acc)))
    (.immediate (some (u64Val o)))
    (.immediate (some (u64Val i)))

private def Lex2Inv (targetTotal o i : Nat) (s : State) : Prop :=
  ∃ acc : Nat,
    o < Nat.pow 2 30 ∧
    i < Nat.pow 2 30 ∧
    acc + (2 * o + i) = targetTotal ∧
    acc < Nat.pow 2 64 ∧
    s = lex2LoopState 1 0 acc o i

private theorem lex2_bb1_zero (acc o : Nat) :
    evalStepV2 progV2Lex2Loop (lex2LoopState 1 0 acc o 0) =
    .step (lex2LoopState 3 0 acc o 0) := rfl

private theorem lex2_bb1_succ (acc o i : Nat) (hi : i + 1 < Nat.pow 2 30) :
    evalStepV2 progV2Lex2Loop (lex2LoopState 1 0 acc o (i + 1)) =
    .step (lex2LoopState 2 0 acc o (i + 1)) := by
  have hi64 : i + 1 < Nat.pow 2 64 := Nat.lt_trans hi (by decide)
  unfold evalStepV2 lex2LoopState lex2State
  change evalTerminatorV2 bodyV2Lex2Loop
      { statements := [],
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 3)]
          otherwise := 2
        } }
      ⟨0, 1, 0,
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val o)),
         .immediate (some (u64Val (i + 1)))],
        none, none, none⟩ (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩ = _
  unfold evalTerminatorV2
  dsimp only
  rw [u64Val_ofNat_lt hi64]
  have hOp :
      evalPrimitiveOperandV2 bodyV2Lex2Loop.locals
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val o)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (i + 1)⟩))]
        (entryMemoryWithCaller ⟨[]⟩) (.copy ⟨2, []⟩) =
      .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 (i + 1)⟩,
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val o)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (i + 1)⟩))],
        entryMemoryWithCaller ⟨[]⟩) := rfl
  rw [hOp]
  dsimp only
  rw [scalar_switch_nonzero hi64 (truncateBits_ofNat_of_lt .i64 hi64) rfl]
  rfl

private theorem lex2_bb2_steps (acc o i : Nat)
    (hi : i + 1 < Nat.pow 2 30) (hAcc : acc < Nat.pow 2 64) :
    StepsToV2 progV2Lex2Loop 3 (lex2LoopState 2 0 acc o (i + 1))
      (lex2LoopState 1 0 (Nat.mod (acc + 1) (Nat.pow 2 64)) o i) := by
  have hi64 : i + 1 < Nat.pow 2 64 := Nat.lt_trans hi (by decide)
  have hi'64 : i < Nat.pow 2 64 := Nat.lt_of_succ_lt hi64
  have hAccNext : Nat.mod (acc + 1) (Nat.pow 2 64) < Nat.pow 2 64 :=
    Nat.mod_lt _ (by decide)
  have hSub := evalBinOp_sub_u64_one hi64
  have hBvAcc : (BitVec.ofNat 128 acc).toNat < intWidthModulus .i64 := by
    rw [intWidthModulus_i64_eq, bv128_ofNat_toNat_lt hAcc]
    exact hAcc
  have hBvOne : (BitVec.ofNat 128 1).toNat < intWidthModulus .i64 := by
    decide
  have hAdd :
      evalBinOp .add
        (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)
        (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩) =
      .ok (.scalar ⟨.i64, false,
        BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩) := by
    have hE := evalBinOp_add_unsigned_eq .i64 hBvAcc hBvOne
    rw [bv128_ofNat_toNat_lt hAcc,
      bv128_ofNat_toNat_lt (by decide : 1 < Nat.pow 2 64),
      intWidthModulus_i64_eq] at hE
    exact hE
  have hS0 :
      evalStepV2 progV2Lex2Loop (lex2LoopState 2 0 acc o (i + 1)) =
      .step (lex2LoopState 2 1 acc o i) := by
    unfold evalStepV2 lex2LoopState lex2State
    change evalStatementV2 bodyV2Lex2Loop
        ⟨0, 2, 0,
          [.immediate (some (u64Val acc)),
           .immediate (some (u64Val o)),
           .immediate (some (u64Val (i + 1)))],
          none, none, none⟩ (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩
        (.assign ⟨2, []⟩
          (.binaryOp .sub (.copy ⟨2, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩))) = _
    unfold evalStatementV2
    dsimp only
    rw [u64Val_ofNat_lt hi64, u64Val_ofNat_lt hi'64]
    change (match evalRvalueV2 bodyV2Lex2Loop.locals
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val o)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (i + 1)⟩))]
        (entryMemoryWithCaller ⟨[]⟩) u64Ty
        (.binaryOp .sub (.copy ⟨2, []⟩)
          (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)) with
      | .error k => StepResult.fault k
      | .ok (val, locals1, mem1) =>
        match writePlaceDestV2 locals1 mem1 (.local 2) u64Ty val with
        | .error k => StepResult.fault k
        | .ok (locals2, mem2) =>
          StepResult.step
            ({ frames := [⟨0, 2, 1, locals2, none, none, none⟩],
               callerMem := ⟨[]⟩, mem := mem2 } : State)) = _
    have hRv := evalRvalueV2_arith_local_const
      (bodyLocals := bodyV2Lex2Loop.locals)
      (locals := [
        .immediate (some (u64Val acc)),
        .immediate (some (u64Val o)),
        .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (i + 1)⟩))])
      (mem := entryMemoryWithCaller ⟨[]⟩) (dstTy := u64Ty) (cTy := u64Ty)
      (op := .sub) (Or.inr rfl) (lid := 2) (ty := u64Ty)
      (w := .i64) (s := false) (bits := BitVec.ofNat 128 1)
      rfl rfl rfl rfl rfl rfl rfl rfl hSub
    rw [hRv]
    dsimp only
    have hCheck :
        checkValV2 (.scalar ⟨.i64, false, BitVec.ofNat 128 i⟩) u64Ty = true :=
      checkValV2_int_scalar (truncateBits_ofNat_of_lt .i64 hi'64)
    have hWr :
        writePlaceDestV2
          [.immediate (some (u64Val acc)),
           .immediate (some (u64Val o)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (i + 1)⟩))]
          (entryMemoryWithCaller ⟨[]⟩) (.local 2) u64Ty
          (.scalar ⟨.i64, false, BitVec.ofNat 128 i⟩) =
        .ok (
          [.immediate (some (u64Val acc)),
           .immediate (some (u64Val o)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 i⟩))],
          entryMemoryWithCaller ⟨[]⟩) := by
      unfold writePlaceDestV2
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    rw [hWr]
  have hS1 :
      evalStepV2 progV2Lex2Loop (lex2LoopState 2 1 acc o i) =
      .step (lex2LoopState 2 2 (Nat.mod (acc + 1) (Nat.pow 2 64)) o i) := by
    unfold evalStepV2 lex2LoopState lex2State
    change evalStatementV2 bodyV2Lex2Loop
        ⟨0, 2, 1,
          [.immediate (some (u64Val acc)),
           .immediate (some (u64Val o)),
           .immediate (some (u64Val i))],
          none, none, none⟩ (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩
        (.assign ⟨0, []⟩
          (.binaryOp .add (.copy ⟨0, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩))) = _
    unfold evalStatementV2
    dsimp only
    rw [u64Val_ofNat_lt hAcc, u64Val_ofNat_lt hAccNext]
    change (match evalRvalueV2 bodyV2Lex2Loop.locals
        [.immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)),
         .immediate (some (u64Val o)),
         .immediate (some (u64Val i))]
        (entryMemoryWithCaller ⟨[]⟩) u64Ty
        (.binaryOp .add (.copy ⟨0, []⟩)
          (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)) with
      | .error k => StepResult.fault k
      | .ok (val, locals1, mem1) =>
        match writePlaceDestV2 locals1 mem1 (.local 0) u64Ty val with
        | .error k => StepResult.fault k
        | .ok (locals2, mem2) =>
          StepResult.step
            ({ frames := [⟨0, 2, 2, locals2, none, none, none⟩],
               callerMem := ⟨[]⟩, mem := mem2 } : State)) = _
    have hRv := evalRvalueV2_arith_local_const
      (bodyLocals := bodyV2Lex2Loop.locals)
      (locals := [
        .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)),
        .immediate (some (u64Val o)),
        .immediate (some (u64Val i))])
      (mem := entryMemoryWithCaller ⟨[]⟩) (dstTy := u64Ty) (cTy := u64Ty)
      (op := .add) (Or.inl rfl) (lid := 0) (ty := u64Ty)
      (w := .i64) (s := false) (bits := BitVec.ofNat 128 1)
      rfl rfl rfl rfl rfl rfl rfl rfl hAdd
    rw [hRv]
    dsimp only
    have hCheck :
        checkValV2
          (.scalar ⟨.i64, false,
            BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩)
          u64Ty = true :=
      checkValV2_int_scalar (truncateBits_ofNat_of_lt .i64 hAccNext)
    have hWr :
        writePlaceDestV2
          [.immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)),
           .immediate (some (u64Val o)),
           .immediate (some (u64Val i))]
          (entryMemoryWithCaller ⟨[]⟩) (.local 0) u64Ty
          (.scalar ⟨.i64, false,
            BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩) =
        .ok (
          [.immediate (some (.scalar ⟨.i64, false,
            BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩)),
           .immediate (some (u64Val o)),
           .immediate (some (u64Val i))],
          entryMemoryWithCaller ⟨[]⟩) := by
      unfold writePlaceDestV2
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    rw [hWr]
  have hS2 :
      evalStepV2 progV2Lex2Loop
        (lex2LoopState 2 2 (Nat.mod (acc + 1) (Nat.pow 2 64)) o i) =
      .step (lex2LoopState 1 0 (Nat.mod (acc + 1) (Nat.pow 2 64)) o i) := rfl
  exact StepsToV2.step (stepV2_iff_evalStepV2.mpr hS0)
    (StepsToV2.step (stepV2_iff_evalStepV2.mpr hS1)
      (StepsToV2.single (stepV2_iff_evalStepV2.mpr hS2)))

private theorem lex2_bb3_zero (acc : Nat) :
    evalStepV2 progV2Lex2Loop (lex2LoopState 3 0 acc 0 0) =
    .step (lex2LoopState 5 0 acc 0 0) := rfl

private theorem lex2_bb3_succ (acc o : Nat) (ho : o + 1 < Nat.pow 2 30) :
    evalStepV2 progV2Lex2Loop (lex2LoopState 3 0 acc (o + 1) 0) =
    .step (lex2LoopState 4 0 acc (o + 1) 0) := by
  have ho64 : o + 1 < Nat.pow 2 64 := Nat.lt_trans ho (by decide)
  unfold evalStepV2 lex2LoopState lex2State
  change evalTerminatorV2 bodyV2Lex2Loop
      { statements := [],
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 5)]
          otherwise := 4
        } }
      ⟨0, 3, 0,
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val (o + 1))),
         .immediate (some (u64Val 0))],
        none, none, none⟩ (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩ = _
  unfold evalTerminatorV2
  dsimp only
  rw [u64Val_ofNat_lt ho64]
  have hOp :
      evalPrimitiveOperandV2 bodyV2Lex2Loop.locals
        [.immediate (some (u64Val acc)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (o + 1)⟩)),
         .immediate (some (u64Val 0))]
        (entryMemoryWithCaller ⟨[]⟩) (.copy ⟨1, []⟩) =
      .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 (o + 1)⟩,
        [.immediate (some (u64Val acc)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (o + 1)⟩)),
         .immediate (some (u64Val 0))],
        entryMemoryWithCaller ⟨[]⟩) := rfl
  rw [hOp]
  dsimp only
  rw [scalar_switch_nonzero ho64 (truncateBits_ofNat_of_lt .i64 ho64) rfl]
  rfl

private theorem lex2_bb4_steps (acc o : Nat) (ho : o + 1 < Nat.pow 2 30) :
    StepsToV2 progV2Lex2Loop 3 (lex2LoopState 4 0 acc (o + 1) 0)
      (lex2LoopState 1 0 acc o 2) := by
  have ho64 : o + 1 < Nat.pow 2 64 := Nat.lt_trans ho (by decide)
  have ho'64 : o < Nat.pow 2 64 := Nat.lt_of_succ_lt ho64
  have hSub := evalBinOp_sub_u64_one ho64
  have hS0 :
      evalStepV2 progV2Lex2Loop (lex2LoopState 4 0 acc (o + 1) 0) =
      .step (lex2LoopState 4 1 acc o 0) := by
    unfold evalStepV2 lex2LoopState lex2State
    change evalStatementV2 bodyV2Lex2Loop
        ⟨0, 4, 0,
          [.immediate (some (u64Val acc)),
           .immediate (some (u64Val (o + 1))),
           .immediate (some (u64Val 0))],
          none, none, none⟩ (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩
        (.assign ⟨1, []⟩
          (.binaryOp .sub (.copy ⟨1, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩))) = _
    unfold evalStatementV2
    dsimp only
    rw [u64Val_ofNat_lt ho64, u64Val_ofNat_lt ho'64]
    change (match evalRvalueV2 bodyV2Lex2Loop.locals
        [.immediate (some (u64Val acc)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (o + 1)⟩)),
         .immediate (some (u64Val 0))]
        (entryMemoryWithCaller ⟨[]⟩) u64Ty
        (.binaryOp .sub (.copy ⟨1, []⟩)
          (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)) with
      | .error k => StepResult.fault k
      | .ok (val, locals1, mem1) =>
        match writePlaceDestV2 locals1 mem1 (.local 1) u64Ty val with
        | .error k => StepResult.fault k
        | .ok (locals2, mem2) =>
          StepResult.step
            ({ frames := [⟨0, 4, 1, locals2, none, none, none⟩],
               callerMem := ⟨[]⟩, mem := mem2 } : State)) = _
    have hRv := evalRvalueV2_arith_local_const
      (bodyLocals := bodyV2Lex2Loop.locals)
      (locals := [
        .immediate (some (u64Val acc)),
        .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (o + 1)⟩)),
        .immediate (some (u64Val 0))])
      (mem := entryMemoryWithCaller ⟨[]⟩) (dstTy := u64Ty) (cTy := u64Ty)
      (op := .sub) (Or.inr rfl) (lid := 1) (ty := u64Ty)
      (w := .i64) (s := false) (bits := BitVec.ofNat 128 1)
      rfl rfl rfl rfl rfl rfl rfl rfl hSub
    rw [hRv]
    dsimp only
    have hCheck :
        checkValV2 (.scalar ⟨.i64, false, BitVec.ofNat 128 o⟩) u64Ty = true :=
      checkValV2_int_scalar (truncateBits_ofNat_of_lt .i64 ho'64)
    have hWr :
        writePlaceDestV2
          [.immediate (some (u64Val acc)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 (o + 1)⟩)),
           .immediate (some (u64Val 0))]
          (entryMemoryWithCaller ⟨[]⟩) (.local 1) u64Ty
          (.scalar ⟨.i64, false, BitVec.ofNat 128 o⟩) =
        .ok (
          [.immediate (some (u64Val acc)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 o⟩)),
           .immediate (some (u64Val 0))],
          entryMemoryWithCaller ⟨[]⟩) := by
      unfold writePlaceDestV2
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    rw [hWr]
  have hS1 :
      evalStepV2 progV2Lex2Loop (lex2LoopState 4 1 acc o 0) =
      .step (lex2LoopState 4 2 acc o 2) := rfl
  have hS2 :
      evalStepV2 progV2Lex2Loop (lex2LoopState 4 2 acc o 2) =
      .step (lex2LoopState 1 0 acc o 2) := rfl
  exact StepsToV2.step (stepV2_iff_evalStepV2.mpr hS0)
    (StepsToV2.step (stepV2_iff_evalStepV2.mpr hS1)
      (StepsToV2.single (stepV2_iff_evalStepV2.mpr hS2)))

private theorem lex2_bb5_return (acc : Nat) :
    evalStepV2 progV2Lex2Loop (lex2LoopState 5 0 acc 0 0) =
    .done (.returned ⟨u64Val acc, ⟨[]⟩⟩) := by
  unfold evalStepV2 lex2LoopState lex2State
  change evalTerminatorV2 bodyV2Lex2Loop
      { statements := [], terminator := .return_ }
      ⟨0, 5, 0,
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val 0)),
         .immediate (some (u64Val 0))],
        none, none, none⟩ (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩ = _
  have hRet :=
    evalTerminatorV2_return_ok
      (body := bodyV2Lex2Loop)
      (bb := { statements := [], terminator := .return_ })
      (frame := ⟨0, 5, 0,
        [.immediate (some (u64Val acc)),
         .immediate (some (u64Val 0)),
         .immediate (some (u64Val 0))],
        none, none, none⟩)
      (mem := entryMemoryWithCaller ⟨[]⟩) (callerMem := ⟨[]⟩)
      (ps := .unwind) (hLocal := true) (oc := false)
      (retTy := u64Ty) (retVal := u64Val acc)
      rfl rfl rfl rfl rfl rfl rfl rfl
  rw [hRet]
  rfl

private theorem lex2_total_lt_pow64 {o i : Nat}
    (ho : o < Nat.pow 2 30) (hi : i < Nat.pow 2 30) :
    2 * o + i < Nat.pow 2 64 := by
  have h1 : 2 * o < Nat.pow 2 31 := by
    have hMul : 2 * o < 2 * Nat.pow 2 30 := Nat.mul_lt_mul_of_pos_left ho (by decide)
    exact Nat.lt_of_lt_of_eq hMul (by decide)
  have h2 : i < Nat.pow 2 31 := Nat.lt_trans hi (by decide)
  exact Nat.lt_trans (Nat.add_lt_add h1 h2) (by decide)

private theorem lex2_setup_exact (outer inner : Nat)
    (hOuter : outer < Nat.pow 2 30) (hInner : inner < Nat.pow 2 30) :
    let q : Query := { args := [u64Val outer, u64Val inner] }
    ValidEntryArgsV2 bodyV2Lex2Loop q ∧
    ∃ s₀ : State,
      initStateV2 progV2Lex2Loop q = .ok s₀ ∧
      BoundedReachV2 progV2Lex2Loop (Lex2Inv (2 * outer + inner) outer inner)
        2 s₀ := by
  intro q
  have hArgsVal : checkArgsMatchV2 q.args [u64Ty, u64Ty] = true := by
    unfold q checkArgsMatchV2
    unfold checkArgsMatchV2
    unfold checkArgsMatchV2
    rw [checkValV2_u64Val outer, checkValV2_u64Val inner]
    rfl
  have hValid : ValidEntryArgsV2 bodyV2Lex2Loop q :=
    ⟨rfl, hArgsVal, rfl, rfl⟩
  have hInit :=
    initStateV2_ok_of_admitted (p := progV2Lex2Loop) (q := q)
      (body := bodyV2Lex2Loop) rfl rfl hValid
  dsimp only [progV2Lex2Loop] at hInit
  refine ⟨hValid, _, hInit, ?_⟩
  have hS0 :
      ⟨[⟨0, 0, 0, initLocalsLoop bodyV2Lex2Loop q.args 0 bodyV2Lex2Loop.locals,
          none, none, none⟩], q.callerMem,
        entryMemoryForArgsV2 q.callerMem
          (List.take bodyV2Lex2Loop.argumentCount (List.drop 1 bodyV2Lex2Loop.locals))
          q.args⟩ =
      lex2State 0 0 (.immediate none) (.immediate (some (u64Val outer)))
        (.immediate (some (u64Val inner))) := rfl
  rw [hS0]
  have hStep0 :
      evalStepV2 progV2Lex2Loop
        (lex2State 0 0 (.immediate none) (.immediate (some (u64Val outer)))
          (.immediate (some (u64Val inner)))) =
      .step (lex2LoopState 0 1 0 outer inner) := rfl
  have hStep1 :
      evalStepV2 progV2Lex2Loop (lex2LoopState 0 1 0 outer inner) =
      .step (lex2LoopState 1 0 0 outer inner) := rfl
  refine ⟨2, _, Nat.le_refl 2,
    StepsToV2.step (stepV2_iff_evalStepV2.mpr hStep0)
      (StepsToV2.single (stepV2_iff_evalStepV2.mpr hStep1)),
    ⟨0, hOuter, hInner, Nat.zero_add _, by decide, rfl⟩⟩

private theorem lex2_exit_exact {targetTotal : Nat} {s : State}
    (hInv : Lex2Inv targetTotal 0 0 s) :
    ReachesDoneWithinV2 progV2Lex2Loop
      (fun out => out = .returned ⟨u64Val targetTotal, ⟨[]⟩⟩) 3 s := by
  let ⟨acc, _, _, hTot, _, hs⟩ := hInv
  rw [hs]
  have hEqTot : acc = targetTotal := by
    rw [← hTot]
    rfl
  rw [hEqTot]
  exact reachesDoneWithinV2_of_eval_step (lex2_bb1_zero targetTotal 0)
    (reachesDoneWithinV2_of_eval_step (lex2_bb3_zero targetTotal)
      (reachesDoneWithinV2_of_eval_done (lex2_bb5_return targetTotal) rfl))

private theorem lex2_inner_exact {targetTotal : Nat}
    (hTotLt : targetTotal < Nat.pow 2 64) {o i : Nat} {s : State}
    (hInv : Lex2Inv targetTotal o (i + 1) s) :
    BoundedReachV2 progV2Lex2Loop (Lex2Inv targetTotal o i) 4 s := by
  let ⟨acc, ho, hi, hTot, hAcc, hs⟩ := hInv
  rw [hs]
  have hAccSuccLt : acc + 1 < Nat.pow 2 64 := by
    have h1Le : 1 ≤ 2 * o + (i + 1) := by
      rw [← Nat.add_assoc]
      exact Nat.succ_le_succ (Nat.zero_le (2 * o + i))
    have hLe : acc + 1 ≤ acc + (2 * o + (i + 1)) :=
      Nat.add_le_add_left h1Le acc
    rw [hTot] at hLe
    exact Nat.lt_of_le_of_lt hLe hTotLt
  have hMod : Nat.mod (acc + 1) (Nat.pow 2 64) = acc + 1 :=
    nat_mod_eq_of_lt hAccSuccLt
  have hNextTot : (acc + 1) + (2 * o + i) = targetTotal := by
    rw [Nat.add_assoc acc 1 (2 * o + i), Nat.add_comm 1 (2 * o + i),
      Nat.add_assoc (2 * o) i 1]
    exact hTot
  refine ⟨4, lex2LoopState 1 0 (acc + 1) o i, Nat.le_refl 4, ?_,
    ⟨acc + 1, ho, Nat.lt_of_succ_lt hi, hNextTot, hAccSuccLt, rfl⟩⟩
  have hStep := StepsToV2.step
    (stepV2_iff_evalStepV2.mpr (lex2_bb1_succ acc o i hi))
    (lex2_bb2_steps acc o i hi hAcc)
  rw [hMod] at hStep
  exact hStep

private theorem lex2_outer_exact {targetTotal o : Nat} {s : State}
    (hInv : Lex2Inv targetTotal (o + 1) 0 s) :
    BoundedReachV2 progV2Lex2Loop (Lex2Inv targetTotal o 2) 5 s := by
  let ⟨acc, ho, _, hTot, hAcc, hs⟩ := hInv
  rw [hs]
  have hNextTot : acc + (2 * o + 2) = targetTotal := by
    rw [Nat.add_zero] at hTot
    rw [Nat.mul_succ] at hTot
    exact hTot
  refine ⟨5, lex2LoopState 1 0 acc o 2, Nat.le_refl 5, ?_,
    ⟨acc, Nat.lt_of_succ_lt ho, by decide, hNextTot, hAcc, rfl⟩⟩
  exact StepsToV2.step
    (stepV2_iff_evalStepV2.mpr (lex2_bb1_zero acc (o + 1)))
    (StepsToV2.step
      (stepV2_iff_evalStepV2.mpr (lex2_bb3_succ acc o ho))
      (lex2_bb4_steps acc o ho))

/-- Symbolic Profile v2 `CnfOrdBridge.lex2Bound` canary: exercises
`execWithinStepsV2_of_lex2_bounded_reset` (`resetCap = 2`, `kInner = 4`,
`kOuter = 5`, `kExit = 3`, `setupBound = 2`) for arbitrary `outer < 2^30` and
`inner < 2^30`, proving exact non-wrapping return value `2 * outer + inner`
alongside `cnfLex2` ordinal descent. -/
theorem canary_v2_lex2_nested_bound (outer inner : Nat)
    (hOuter : outer < Nat.pow 2 30) (hInner : inner < Nat.pow 2 30) :
    (ExecWithinStepsV2 progV2Lex2Loop
        { args := [u64Val outer, u64Val inner] }
        (2 + lex2Bound 2 4 5 3 outer inner)
        (fun out => out = .returned ⟨u64Val (2 * outer + inner), ⟨[]⟩⟩) ∧
      WellFormedV2 progV2Lex2Loop { args := [u64Val outer, u64Val inner] } ∧
      ¬ DivergesV2 progV2Lex2Loop { args := [u64Val outer, u64Val inner] }) ∧
    cnfLt (cnfLex2 outer inner) (cnfLex2 outer (inner + 1)) = true ∧
    cnfLt (cnfLex2 outer 2) (cnfLex2 (outer + 1) 0) = true := by
  let ⟨_, s₀, hInit, hSetup⟩ := lex2_setup_exact outer inner hOuter hInner
  have hTotLt := lex2_total_lt_pow64 hOuter hInner
  have hEnd :=
    execWithinStepsV2_of_lex2_bounded_reset
      (post := fun out =>
        out = .returned ⟨u64Val (2 * outer + inner), ⟨[]⟩⟩)
      (Lex2Inv (2 * outer + inner)) 2 2 4 5 3 outer inner
      hInit hSetup
      (fun _ hInv => lex2_exit_exact hInv)
      (fun _ _ _ hInv => Or.inr (lex2_inner_exact hTotLt hInv))
      (fun _ _ hInv => Or.inr ⟨2, Nat.le_refl 2, lex2_outer_exact hInv⟩)
  exact ⟨⟨hEnd.1, hEnd.2.1, hEnd.2.2.1⟩,
    cnfLex2_drop_inner outer inner, cnfLex2_drop_outer outer 0 2⟩

private noncomputable def lex2StateRawMeasure (s : State) : CnfOrd :=
  match s.frames with
  | f :: _ =>
    match f.locals with
    | _ :: .immediate (some (.scalar ⟨.i64, false, bvO⟩)) ::
        .immediate (some (.scalar ⟨.i64, false, bvI⟩)) :: _ =>
      [(1, bvO.toNat), (0, bvI.toNat)]
    | _ => []
  | [] => []

/-- Well-founded `< ω^ω` ordinal-extraction canary: exercises
`execWithinStepsV2_of_cnfOrd` directly on `progV2Lex2Loop`, extracting a
finite `Nat` step bound `B` via `CnfAcc` without using the closed-form
`lex2Bound` arithmetic helper. -/
theorem canary_v2_lex2_cnfOrd_extracted_bound (outer inner : Nat)
    (hOuter : outer < Nat.pow 2 30) (hInner : inner < Nat.pow 2 30) :
    let q : Query := { args := [u64Val outer, u64Val inner] }
    let contract : SafeContractV2 := {
      behaviorPre := fun _ => True
      effects := EffectMaskV2.noAbort
      postReturn := fun _ out => out = ⟨u64Val (2 * outer + inner), ⟨[]⟩⟩
    }
    (∃ B : Nat,
      ExecWithinStepsV2 progV2Lex2Loop q B (contract.post q)) ∧
    SatisfiesSafeContractV2 progV2Lex2Loop q contract ∧
    WellFormedV2 progV2Lex2Loop q ∧
    ¬ DivergesV2 progV2Lex2Loop q := by
  intro q contract
  let ⟨_, s₀, hInit, hSetup⟩ := lex2_setup_exact outer inner hOuter hInner
  have hTotLt := lex2_total_lt_pow64 hOuter hInner
  let CnfInv : State → Prop := fun s =>
    ∃ o i : Nat, Lex2Inv (2 * outer + inner) o i s
  have hMeas : ∀ o i s, Lex2Inv (2 * outer + inner) o i s →
      cnfNorm (lex2StateRawMeasure s) = cnfLex2 o i := by
    intro o i s ⟨acc, ho, hi, _, _, hs⟩
    have ho64 : o < Nat.pow 2 64 := Nat.lt_trans ho (by decide)
    have hi64 : i < Nat.pow 2 64 := Nat.lt_trans hi (by decide)
    rw [hs]
    unfold lex2StateRawMeasure lex2LoopState lex2State
    rw [u64Val_ofNat_lt ho64, u64Val_ofNat_lt hi64]
    dsimp only
    rw [bv128_ofNat_toNat_lt ho64, bv128_ofNat_toNat_lt hi64]
    rfl
  let ⟨B, hExec, hWf, hNdiv, _, _⟩ :=
    execWithinStepsV2_of_cnfOrd
      (post := contract.post q)
      CnfInv lex2StateRawMeasure 2 5 3 hInit
      (BoundedReachV2.weaken (fun s h => ⟨outer, inner, h⟩) hSetup)
      (fun s ⟨o, i, hInv⟩ => by
        cases i with
        | zero =>
          cases o with
          | zero =>
            exact Or.inl (ReachesDoneWithinV2.weaken
              (fun out hEq => by
                rw [hEq]
                rfl)
              (lex2_exit_exact hInv))
          | succ oPrev =>
            let ⟨k, s', hk, hSt, hInv'⟩ := lex2_outer_exact hInv
            refine Or.inr ⟨k, s', hk, hSt, ⟨oPrev, 2, hInv'⟩, ?_⟩
            rw [hMeas oPrev 2 s' hInv', hMeas (oPrev + 1) 0 s hInv]
            exact cnfLex2_drop_outer oPrev 0 2
        | succ iPrev =>
          let ⟨k, s', hk, hSt, hInv'⟩ := lex2_inner_exact hTotLt hInv
          refine Or.inr ⟨k, s', Nat.le_trans hk (by decide), hSt,
            ⟨o, iPrev, hInv'⟩, ?_⟩
          rw [hMeas o iPrev s' hInv', hMeas o (iPrev + 1) s hInv]
          exact cnfLex2_drop_inner o iPrev)
  have hSafe :=
    (satisfiesSafeContractV2_of_execWithinStepsV2 (p := progV2Lex2Loop)
      (q := q) (bound := B) (contract := contract) (fun _ => hExec)).1
  exact ⟨⟨B, hExec⟩, hSafe, hWf, hNdiv⟩

private inductive WorklistExactSteps (pol : SpawnPolicy) :
    WorklistPool → Nat → Prop where
  | quiescent (w : WorklistPool) (hEmp : poolIsNonEmpty w = false) :
      WorklistExactSteps pol w 0
  | step {w w' : WorklistPool} {n : Nat}
      (hNonEmp : poolIsNonEmpty w = true)
      (hStep : worklistStep pol w = .returned w')
      (hRest : WorklistExactSteps pol w' n) :
      WorklistExactSteps pol w (n + 1)

/-- `CnfOrdBridge` non-empty worklist canary: seeds a rank-`4` task under
`towerLookupNext [4, 2, 0] 1 0` traversing all three tiers `4 -> 2 -> 0 -> []`
in `steps = 3` transitions, lifts via `v2_steps_of_worklist_terminates` to a
`steps * 4 + 3` (`15`) step witness on `progV2Lex2Loop`, and refutes `14` steps
(and thus `steps = 0`). -/
theorem canary_worklist_v2_steps :
    (∃ (steps : Nat),
      0 < steps ∧
      ReachesDoneWithinV2 progV2Lex2Loop
        (fun out => out = .returned ⟨u64Val 3, ⟨[]⟩⟩)
        (steps * 4 + 3)
        (lex2LoopState 1 0 0 0 3)) ∧
    ¬ ReachesDoneWithinV2 progV2Lex2Loop (fun _ => True) 14
      (lex2LoopState 1 0 0 0 3) := by
  let pol : SpawnPolicy := towerLookupNext [4, 2, 0] 1 0
  have hPol : PolicyAdmissible pol :=
    towerLookupNext_admissible [4, 2, 0] 1 0 (by decide)
  let sim : WorklistPool → State → Prop := fun w s =>
    ∃ (n acc : Nat),
      n < Nat.pow 2 30 ∧ acc + n = 3 ∧
      WorklistExactSteps pol w n ∧
      s = lex2LoopState 1 0 acc 0 n
  have hDone : ∀ w s, poolIsNonEmpty w = false → sim w s →
      ReachesDoneWithinV2 progV2Lex2Loop
        (fun out => out = .returned ⟨u64Val 3, ⟨[]⟩⟩) 3 s := by
    intro w s hEmp ⟨n, acc, _, hSum, hExact, hs⟩
    cases hExact with
    | quiescent _ _ =>
      have hAcc3 : acc = 3 := by
        rw [Nat.add_zero] at hSum
        exact hSum
      rw [hs, hAcc3]
      exact reachesDoneWithinV2_of_eval_step (lex2_bb1_zero 3 0)
        (reachesDoneWithinV2_of_eval_step (lex2_bb3_zero 3)
          (reachesDoneWithinV2_of_eval_done (lex2_bb5_return 3) rfl))
    | step hNonEmp _ _ =>
      rw [hEmp] at hNonEmp
      cases hNonEmp
  have hStep : ∀ w w' s, poolIsNonEmpty w = true →
      worklistStep pol w = .returned w' → sim w s →
      BoundedReachV2 progV2Lex2Loop (sim w') 4 s := by
    intro w w' s hNonEmp hWork ⟨_, acc, hn, hSum, hExact, hs⟩
    cases hExact with
    | quiescent _ hEmp =>
      rw [hEmp] at hNonEmp
      cases hNonEmp
    | @step _ w'' m _ hWork' hRest =>
      rw [hWork'] at hWork
      cases hWork
      have hAccLt : acc < Nat.pow 2 64 := by
        have hLe : acc ≤ 3 := by
          rw [← hSum]
          exact Nat.le_add_right acc (m + 1)
        exact Nat.lt_of_le_of_lt hLe (by decide)
      have hAccSuccLt : acc + 1 < Nat.pow 2 64 := by
        have hLe : acc + 1 ≤ 3 := by
          rw [← hSum]
          exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le m)) acc
        exact Nat.lt_of_le_of_lt hLe (by decide)
      have hMod : Nat.mod (acc + 1) (Nat.pow 2 64) = acc + 1 :=
        nat_mod_eq_of_lt hAccSuccLt
      have hSumNext : (acc + 1) + m = 3 := by
        rw [Nat.add_assoc acc 1 m, Nat.add_comm 1 m]
        exact hSum
      rw [hs]
      refine ⟨4, lex2LoopState 1 0 (acc + 1) 0 m, Nat.le_refl 4, ?_,
        ⟨m, acc + 1, Nat.lt_of_succ_lt hn, hSumNext, hRest, rfl⟩⟩
      have hSt := StepsToV2.step
        (stepV2_iff_evalStepV2.mpr (lex2_bb1_succ acc 0 m hn))
        (lex2_bb2_steps acc 0 m hn hAccLt)
      rw [hMod] at hSt
      exact hSt
  let w0 : WorklistPool := {
    fifoQueue := [⟨0, 4, 0⟩]
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0
  }
  let w1 : WorklistPool := {
    fifoQueue := []
    stealDeque := [⟨1, 2, 0⟩]
    nextTaskId := 2
    completedCount := 1
    stepCount := 1
  }
  let w2 : WorklistPool := {
    fifoQueue := []
    stealDeque := [⟨2, 0, 0⟩]
    nextTaskId := 3
    completedCount := 2
    stepCount := 2
  }
  let w3 : WorklistPool := {
    fifoQueue := []
    stealDeque := []
    nextTaskId := 3
    completedCount := 3
    stepCount := 3
  }
  have hExact3 : WorklistExactSteps pol w0 3 :=
    WorklistExactSteps.step (w' := w1) rfl rfl
      (WorklistExactSteps.step (w' := w2) rfl rfl
        (WorklistExactSteps.step (w' := w3) rfl rfl
          (WorklistExactSteps.quiescent w3 rfl)))
  let ⟨steps, hReach⟩ :=
    v2_steps_of_worklist_terminates pol hPol sim 4 3 hDone hStep
      w0 (lex2LoopState 1 0 0 0 3) ⟨3, 0, by decide, rfl, hExact3, rfl⟩
  have hExactPos : 0 < steps := by
    cases steps with
    | zero =>
      have hDone14 :
          ReachesDoneWithinV2 progV2Lex2Loop (fun _ => True) 3
            (lex2LoopState 1 0 0 0 3) :=
        ReachesDoneWithinV2.mono (by decide)
          (ReachesDoneWithinV2.weaken (fun _ _ => trivial) hReach)
      have hStep0 : StepsToV2 progV2Lex2Loop 4 (lex2LoopState 1 0 0 0 3)
          (lex2LoopState 1 0 1 0 2) := by
        have hSt := StepsToV2.step
          (stepV2_iff_evalStepV2.mpr (lex2_bb1_succ 0 0 2 (by decide)))
          (lex2_bb2_steps 0 0 2 (by decide) (by decide))
        rw [nat_mod_eq_of_lt (by decide : 1 < Nat.pow 2 64)] at hSt
        exact hSt
      exact False.elim
        (not_reachesDoneWithinV2_of_stepsTo_ge hStep0 (by decide) hDone14)
    | succ sPrev => exact Nat.zero_lt_succ sPrev
  have hIter1 : StepsToV2 progV2Lex2Loop 4 (lex2LoopState 1 0 0 0 3)
      (lex2LoopState 1 0 1 0 2) := by
    have hSt := StepsToV2.step
      (stepV2_iff_evalStepV2.mpr (lex2_bb1_succ 0 0 2 (by decide)))
      (lex2_bb2_steps 0 0 2 (by decide) (by decide))
    rw [nat_mod_eq_of_lt (by decide : 1 < Nat.pow 2 64)] at hSt
    exact hSt
  have hIter2 : StepsToV2 progV2Lex2Loop 4 (lex2LoopState 1 0 1 0 2)
      (lex2LoopState 1 0 2 0 1) := by
    have hSt := StepsToV2.step
      (stepV2_iff_evalStepV2.mpr (lex2_bb1_succ 1 0 1 (by decide)))
      (lex2_bb2_steps 1 0 1 (by decide) (by decide))
    rw [nat_mod_eq_of_lt (by decide : 2 < Nat.pow 2 64)] at hSt
    exact hSt
  have hIter3 : StepsToV2 progV2Lex2Loop 4 (lex2LoopState 1 0 2 0 1)
      (lex2LoopState 1 0 3 0 0) := by
    have hSt := StepsToV2.step
      (stepV2_iff_evalStepV2.mpr (lex2_bb1_succ 2 0 0 (by decide)))
      (lex2_bb2_steps 2 0 0 (by decide) (by decide))
    rw [nat_mod_eq_of_lt (by decide : 3 < Nat.pow 2 64)] at hSt
    exact hSt
  have hTail2 : StepsToV2 progV2Lex2Loop 2 (lex2LoopState 1 0 3 0 0)
      (lex2LoopState 5 0 3 0 0) :=
    StepsToV2.step (stepV2_iff_evalStepV2.mpr (lex2_bb1_zero 3 0))
      (StepsToV2.single (stepV2_iff_evalStepV2.mpr (lex2_bb3_zero 3)))
  have hSteps14 := StepsToV2.trans (StepsToV2.trans hIter1 hIter2)
    (StepsToV2.trans hIter3 hTail2)
  exact ⟨⟨steps, hExactPos, hReach⟩,
    not_reachesDoneWithinV2_of_stepsTo_ge hSteps14 (Nat.le_refl 14)⟩

/-- Non-terminating Profile v2 reactive ticker kernel (`_0 += 1; _1 := true`
then `goto 0`) exercising `ReactiveStepContractV2` and `iterate_prefix`: never
terminates (`post := fun _ => False`), yet guarantees `1 ≤ k ≤ 3` MIR steps
per tick across arbitrary finite frame prefixes `frames : Nat` and establishes
the non-trivial `tickYielded` checkpoint predicate (`False` at
`tickState 0 0 false`, `True` after every `0 < frames` ticks). -/
@[expose] noncomputable def bodyV2Tick : Body := {
  argumentCount := 0
  locals := [u64Ty, .bool]
  basicBlocks := [
    {
      statements := [
        .assign ⟨0, []⟩
          (.binaryOp .add (.copy ⟨0, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨1, []⟩
          (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 0
    }
  ]
  isUnsafe := false
  identity := "canary_v2_tick"
}

/-- Profile v2 program whose entry body is `bodyV2Tick`. -/
@[expose] noncomputable def progV2Tick : Program := {
  bodies := [bodyV2Tick]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

@[expose] noncomputable def tickState (sIdx acc : Nat) (ticked : Bool) :
    State :=
  ⟨[⟨0, 0, sIdx,
      [.immediate (some (u64Val acc)), .immediate (some (.bool ticked))],
      none, none, none⟩],
    ⟨[]⟩, entryMemoryWithCaller ⟨[]⟩⟩

@[expose] def tickInv (s : State) : Prop :=
  ∃ (acc : Nat) (ticked : Bool),
    acc < Nat.pow 2 64 ∧ s = tickState 0 acc ticked

@[expose] def tickYielded (s : State) : Prop :=
  ∃ acc : Nat, acc < Nat.pow 2 64 ∧ s = tickState 0 acc true

/-- Reactive prefix canary: `progV2Tick` satisfies `ReactiveStepContractV2`
with `tickYielded` (`¬ tickYielded (tickState 0 0 false)`) and
`frameBound = 3`, completing `frames ≤ k ≤ frames * 3` steps and satisfying
`tickInv s' ∧ (0 < frames → tickYielded s')` for EVERY finite prefix `frames`.
-/
theorem canary_reactive_tick_prefix :
    ReactiveStepContractV2 progV2Tick tickInv tickYielded
      (fun _ => False) 3 ∧
    ¬ tickYielded (tickState 0 0 false) ∧
    ∀ frames : Nat,
      ∃ (k : Nat) (s' : State),
        frames ≤ k ∧ k ≤ frames * 3 ∧
        StepsToV2 progV2Tick k (tickState 0 0 false) s' ∧
        tickInv s' ∧ (0 < frames → tickYielded s') := by
  have hNotInit : ¬ tickYielded (tickState 0 0 false) := by
    intro ⟨acc, _, hEq⟩
    have hB := congrArg (fun st : State =>
      match st.frames with
      | f :: _ =>
        match f.locals with
        | _ :: .immediate opt :: _ => opt
        | _ => none
      | [] => none) hEq
    cases hB
  have hContract :
      ReactiveStepContractV2 progV2Tick tickInv tickYielded
        (fun _ => False) 3 := by
    intro s ⟨acc, ticked, hAcc, hs⟩
    rw [hs]
    refine Or.inr ?_
    have hBvAcc : (BitVec.ofNat 128 acc).toNat < intWidthModulus .i64 := by
      rw [intWidthModulus_i64_eq, bv128_ofNat_toNat_lt hAcc]
      exact hAcc
    have hBvOne : (BitVec.ofNat 128 1).toNat < intWidthModulus .i64 := by
      decide
    have hAccNext : Nat.mod (acc + 1) (Nat.pow 2 64) < Nat.pow 2 64 :=
      Nat.mod_lt _ (by decide)
    have hAdd :
        evalBinOp .add
          (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)
          (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩) =
        .ok (.scalar ⟨.i64, false,
          BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩) := by
      have hE := evalBinOp_add_unsigned_eq .i64 hBvAcc hBvOne
      rw [bv128_ofNat_toNat_lt hAcc,
        bv128_ofNat_toNat_lt (by decide : 1 < Nat.pow 2 64),
        intWidthModulus_i64_eq] at hE
      exact hE
    have hStep0 :
        evalStepV2 progV2Tick (tickState 0 acc ticked) =
        .step (tickState 1 (Nat.mod (acc + 1) (Nat.pow 2 64)) ticked) := by
      unfold evalStepV2 tickState
      change evalStatementV2 bodyV2Tick
          ⟨0, 0, 0,
            [.immediate (some (u64Val acc)), .immediate (some (.bool ticked))],
            none, none, none⟩
          (entryMemoryWithCaller ⟨[]⟩) ⟨[]⟩
          (.assign ⟨0, []⟩
            (.binaryOp .add (.copy ⟨0, []⟩)
              (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩))) = _
      unfold evalStatementV2
      dsimp only
      rw [u64Val_ofNat_lt hAcc, u64Val_ofNat_lt hAccNext]
      change (match evalRvalueV2 bodyV2Tick.locals
          [.immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)),
           .immediate (some (.bool ticked))]
          (entryMemoryWithCaller ⟨[]⟩) u64Ty
          (.binaryOp .add (.copy ⟨0, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)) with
        | .error k => StepResult.fault k
        | .ok (val, locals1, mem1) =>
          match writePlaceDestV2 locals1 mem1 (.local 0) u64Ty val with
          | .error k => StepResult.fault k
          | .ok (locals2, mem2) =>
            StepResult.step
              ({ frames := [⟨0, 0, 1, locals2, none, none, none⟩],
                 callerMem := ⟨[]⟩, mem := mem2 } : State)) = _
      have hRv := evalRvalueV2_arith_local_const
        (bodyLocals := bodyV2Tick.locals)
        (locals := [
          .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)),
          .immediate (some (.bool ticked))])
        (mem := entryMemoryWithCaller ⟨[]⟩) (dstTy := u64Ty) (cTy := u64Ty)
        (op := .add) (Or.inl rfl) (lid := 0) (ty := u64Ty)
        (w := .i64) (s := false) (bits := BitVec.ofNat 128 1)
        rfl rfl rfl rfl rfl rfl rfl rfl hAdd
      rw [hRv]
      dsimp only
      have hCheck :
          checkValV2
            (.scalar ⟨.i64, false,
              BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩)
            u64Ty = true :=
        checkValV2_int_scalar (truncateBits_ofNat_of_lt .i64 hAccNext)
      have hWr :
          writePlaceDestV2
            [.immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 acc⟩)),
             .immediate (some (.bool ticked))]
            (entryMemoryWithCaller ⟨[]⟩) (.local 0) u64Ty
            (.scalar ⟨.i64, false,
              BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩) =
          .ok (
            [.immediate (some (.scalar ⟨.i64, false,
              BitVec.ofNat 128 (Nat.mod (acc + 1) (Nat.pow 2 64))⟩)),
             .immediate (some (.bool ticked))],
            entryMemoryWithCaller ⟨[]⟩) := by
        unfold writePlaceDestV2
        rw [ite_bool_false (by rw [hCheck]; rfl)]
        rfl
      rw [hWr]
    have hStep1 :
        evalStepV2 progV2Tick
          (tickState 1 (Nat.mod (acc + 1) (Nat.pow 2 64)) ticked) =
        .step (tickState 2 (Nat.mod (acc + 1) (Nat.pow 2 64)) true) := rfl
    have hStep2 :
        evalStepV2 progV2Tick
          (tickState 2 (Nat.mod (acc + 1) (Nat.pow 2 64)) true) =
        .step (tickState 0 (Nat.mod (acc + 1) (Nat.pow 2 64)) true) := rfl
    refine ⟨3, tickState 0 (Nat.mod (acc + 1) (Nat.pow 2 64)) true,
      by decide, Nat.le_refl 3,
      StepsToV2.step (stepV2_iff_evalStepV2.mpr hStep0)
        (StepsToV2.step (stepV2_iff_evalStepV2.mpr hStep1)
          (StepsToV2.single (stepV2_iff_evalStepV2.mpr hStep2))),
      ⟨⟨Nat.mod (acc + 1) (Nat.pow 2 64), true, hAccNext, rfl⟩,
       ⟨Nat.mod (acc + 1) (Nat.pow 2 64), hAccNext, rfl⟩⟩⟩
  refine ⟨hContract, hNotInit, fun frames => ?_⟩
  cases hContract.iterate_prefix frames (tickState 0 0 false)
      ⟨0, false, by decide, rfl⟩ with
  | inl hDone =>
    exact False.elim
      (not_reachesDoneWithinV2_false (frames * 3) (tickState 0 0 false) hDone)
  | inr hPref =>
    exact hPref

/-! ## 4. Negative & Tight-Budget Non-Vacuity Canaries -/

@[expose] noncomputable def callerMemSlice1 : CallerMemory := {
  allocations := [{
    allocId := 1
    alignLog2 := 0
    mutability := .shared
    bytes := [.init 42 none]
    live := true
  }]
}

@[expose] noncomputable def querySlice1 : Query := {
  args := [.slicePtr ⟨some 1, 0, .isize⟩ (UInt64.ofNat 1)]
  callerMem := callerMemSlice1
}

@[expose] noncomputable def querySlice0 : Query := {
  args := [.slicePtr ⟨none, 1, .isize⟩ (UInt64.ofNat 0)]
  callerMem := ⟨[]⟩
}

/-- Tight-budget non-vacuity canary: on a 1-byte slice, `progV2SliceScan`
succeeds at `bound = 10` (`4 * 1 + 6`), yet `bound = 9` fails unconditionally
even under `post := fun _ => True`. -/
theorem canary_v2_slice_scan_1byte_tight_bound :
    ExecWithinStepsV2 progV2SliceScan querySlice1 10
      (fun out => out = .returned ⟨usizeVal 1, callerMemSlice1⟩) ∧
    ¬ ExecWithinStepsV2 progV2SliceScan querySlice1 9 (fun _ => True) := by
  let ptr0 : PtrVal := ⟨some 1, 0, .isize⟩
  let ptr1 : PtrVal := ⟨some 1, UInt64.ofNat 1, .isize⟩
  have hSlice1 :
      sliceFromRawPartsCheck (entryMemoryWithCaller callerMemSlice1) false
        1 0 ptr0 (UInt64.ofNat 1) =
      .ok (.slicePtr ptr0 (UInt64.ofNat 1)) := by
    unfold sliceFromRawPartsCheck sliceRefRawCheck entryMemoryWithCaller
      callerMemSlice1 ptr0 findAllocation isInBounds isAligned isSliceAllInit
    rfl
  have hRef1 :
      refValidInMem (entryMemoryWithCaller callerMemSlice1) .shared
        (.slice (.int .i8 false)) (.slicePtr ptr0 (UInt64.ofNat 1)) = .ok () :=
    refValidInMem_of_sliceCheck (reqMut := .shared) hSlice1
  have hValid : ValidEntryArgsV2 bodyV2SliceScan querySlice1 := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · unfold querySlice1 bodyV2SliceScan
      dsimp only [List.drop, List.take, sliceU8Ty]
      unfold refsValidInMemList
      rw [refsValidInMem_of_refValid hRef1]
      rfl
    · unfold refAccessSpansList querySlice1 bodyV2SliceScan
      dsimp only [List.drop, List.take, sliceU8Ty, refAccessSpansList]
      rw [list_append_nil]
      exact spansDisjoint_single
  have hPos := canary_v2_slice_scan_linear_bound querySlice1 (some 1) 0 1
    rfl hValid
  have hInitExp :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := querySlice1)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  have hInit :
      initStateV2 progV2SliceScan querySlice1 =
      .ok (sliceScanState 0 0 (.immediate none)
        (.immediate (some (.slicePtr ptr0 (UInt64.ofNat 1))))
        (.immediate none) (.immediate none)
        callerMemSlice1 (entryMemoryWithCaller callerMemSlice1)) := by
    have hS0Eq :
        ⟨[⟨progV2SliceScan.entryDefId, 0, 0,
            initLocalsLoop bodyV2SliceScan querySlice1.args 0
              bodyV2SliceScan.locals,
            none, none, none⟩],
          querySlice1.callerMem,
          entryMemoryForArgsV2 querySlice1.callerMem
            (List.take bodyV2SliceScan.argumentCount (List.drop 1 bodyV2SliceScan.locals))
            querySlice1.args⟩ =
        sliceScanState 0 0 (.immediate none)
          (.immediate (some (.slicePtr ptr0 (UInt64.ofNat 1))))
          (.immediate none) (.immediate none)
          callerMemSlice1 (entryMemoryWithCaller callerMemSlice1) := rfl
    rw [hS0Eq] at hInitExp
    exact hInitExp
  have hSetup3 :
      StepsToV2 progV2SliceScan 3
        (sliceScanState 0 0 (.immediate none)
          (.immediate (some (.slicePtr ptr0 (UInt64.ofNat 1))))
          (.immediate none) (.immediate none)
          callerMemSlice1 (entryMemoryWithCaller callerMemSlice1))
        (sliceScanLoopState 1 0 0 ptr0 1 none callerMemSlice1) :=
    StepsToV2.step
      (stepV2_iff_evalStepV2.mpr
        (sliceScan_setup_step0 ptr0 (UInt64.ofNat 1) callerMemSlice1))
      (StepsToV2.step
        (stepV2_iff_evalStepV2.mpr
          (sliceScan_setup_step1 ptr0 (UInt64.ofNat 1) callerMemSlice1))
        (StepsToV2.single
          (stepV2_iff_evalStepV2.mpr
            (sliceScan_setup_step2 ptr0 (UInt64.ofNat 1) callerMemSlice1))))
  have hB1a := sliceScan_bb1_sliceLen 0 1 ptr0 none callerMemSlice1
    (by decide) hSlice1
  have hB2a := sliceScan_bb2_succ 0 0 ptr0 callerMemSlice1 (by decide)
  have hB3s := sliceScan_bb3_stmt0 0 0 ptr0 callerMemSlice1
    (by decide) (by decide)
  let ⟨hB3t, hSlice0⟩ := sliceScan_bb3_term 1 0 ptr0 callerMemSlice1
    rfl rfl (by decide) hSlice1
  have hB1b := sliceScan_bb1_sliceLen 1 0 ptr1 (some (usizeVal 1))
    callerMemSlice1 (by decide) hSlice0
  have hB2b := sliceScan_bb2_zero 1 ptr1 callerMemSlice1
  have hTail6 :
      StepsToV2 progV2SliceScan 6
        (sliceScanLoopState 1 0 0 ptr0 1 none callerMemSlice1)
        (sliceScanLoopState 4 0 1 ptr1 0 (some (usizeVal 0))
          callerMemSlice1) :=
    StepsToV2.step (stepV2_iff_evalStepV2.mpr hB1a)
      (StepsToV2.step (stepV2_iff_evalStepV2.mpr hB2a)
        (StepsToV2.step (stepV2_iff_evalStepV2.mpr hB3s)
          (StepsToV2.step (stepV2_iff_evalStepV2.mpr hB3t)
            (StepsToV2.step (stepV2_iff_evalStepV2.mpr hB1b)
              (StepsToV2.single (stepV2_iff_evalStepV2.mpr hB2b))))))
  have hSteps9 := StepsToV2.trans hSetup3 hTail6
  refine ⟨hPos.1, fun ⟨s0, hI, hR⟩ => ?_⟩
  rw [hInit] at hI
  cases hI
  exact not_reachesDoneWithinV2_of_stepsTo_ge hSteps9 (Nat.le_refl 9) hR

/-- Divergence negative canary: an infinite `.goto 0` Profile v2 body proves
`DivergesV2` and refutes `ExecWithinStepsV2` at every finite step bound. -/
@[expose] noncomputable def bodyV2SpinLocal : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .goto 0 }]
  isUnsafe := false
  identity := "canary_v2_spin_local"
}

/-- Profile v2 diverging program wrapping `bodyV2SpinLocal`. -/
@[expose] noncomputable def progV2SpinLocal : Program := {
  bodies := [bodyV2SpinLocal]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

theorem canary_v2_spin_diverges_refutes_step_bound :
    DivergesV2 progV2SpinLocal { args := [] } ∧
    ∀ (bound : Nat) (post : TerminalOut → Prop),
      ¬ ExecWithinStepsV2 progV2SpinLocal { args := [] } bound post := by
  let sSpin : State :=
    ⟨[⟨0, 0, 0, [.immediate (some .unit)], none, none, none⟩], ⟨[]⟩,
      entryMemoryWithCaller ⟨[]⟩⟩
  have hInit : initStateV2 progV2SpinLocal { args := [] } = .ok sSpin := rfl
  have hStep : StepV2 progV2SpinLocal sSpin (.step sSpin) :=
    stepV2_iff_evalStepV2.mpr rfl
  have hDiv : DivergesV2 progV2SpinLocal { args := [] } :=
    ⟨sSpin, hInit, fun _ => sSpin, rfl, fun _ => hStep⟩
  exact ⟨hDiv, fun bound post =>
    not_execWithinStepsV2_of_divergesV2 hDiv bound post⟩

/-- Faulting negative canary: dereferencing a null `*const u8` pointer faults
immediately (`FaultKind.undefined`), refuting `ExecWithinStepsV2` at all
budgets. -/
@[expose] noncomputable def bodyV2LoadNullLocal : Body := {
  argumentCount := 1
  locals := [u8TyLocal, .rawPtr .shared u8TyLocal]
  basicBlocks := [{
    statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩))]
    terminator := .return_
  }]
  isUnsafe := true
  identity := "canary_v2_load_null_local"
}

/-- Profile v2 faulting program wrapping `bodyV2LoadNullLocal`. -/
@[expose] noncomputable def progV2LoadNullLocal : Program := {
  bodies := [bodyV2LoadNullLocal]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

theorem canary_v2_null_fault_refutes_step_bound :
    ∀ (bound : Nat) (post : TerminalOut → Prop),
      ¬ ExecWithinStepsV2 progV2LoadNullLocal
        { args := [.ptr ⟨none, 0, .isize⟩] } bound post := by
  intro bound post ⟨s0, hInit, hReach⟩
  have hInitEq :
      initStateV2 progV2LoadNullLocal { args := [.ptr ⟨none, 0, .isize⟩] } =
      .ok ⟨[⟨0, 0, 0,
        [.immediate none, .immediate (some (.ptr ⟨none, 0, .isize⟩))],
        none, none, none⟩], ⟨[]⟩, entryMemoryWithCaller ⟨[]⟩⟩ := rfl
  rw [hInitEq] at hInit
  cases hInit
  have hFault :
      StepV2 progV2LoadNullLocal
        ⟨[⟨0, 0, 0,
          [.immediate none, .immediate (some (.ptr ⟨none, 0, .isize⟩))],
          none, none, none⟩], ⟨[]⟩, entryMemoryWithCaller ⟨[]⟩⟩
        (.fault .undefined) :=
    stepV2_iff_evalStepV2.mpr rfl
  exact not_reachesDoneWithinV2_of_stepsTo_fault (StepsToV2.refl _) hFault hReach

/-- Postcondition-mismatch negative canary: `progV2SliceScan` on an empty slice
returns `0usize`, refuting `ExecWithinStepsV2` for any contradictory expected
return value (`1usize`) at any step budget. -/
theorem canary_v2_wrong_post_refutes_step_bound :
    ∀ (bound : Nat),
      ¬ ExecWithinStepsV2 progV2SliceScan querySlice0 bound
        (fun out => out = .returned ⟨usizeVal 1, ⟨[]⟩⟩) := by
  intro bound ⟨s0, hInit, hReach⟩
  have hValid : ValidEntryArgsV2 bodyV2SliceScan querySlice0 := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold refAccessSpansList querySlice0 bodyV2SliceScan
    dsimp only [List.drop, List.take, sliceU8Ty, refAccessSpansList]
    rw [list_append_nil]
    exact spansDisjoint_single
  have hInitExp :=
    initStateV2_ok_of_admitted (p := progV2SliceScan) (q := querySlice0)
      (body := bodyV2SliceScan) rfl bodyV2SliceScan_admitted hValid
  rw [hInitExp] at hInit
  cases hInit
  have hSetup := sliceScan_setup_bounded (ptrAid := none) (ptrOff := 1)
    (len := 0) rfl hValid hInitExp
  let ⟨k0, s1, _, hSt0, curPtr, opt2, _, _, _, _, hSlice, hEq⟩ := hSetup
  rw [hEq] at hSt0
  have hB1 := sliceScan_bb1_sliceLen 0 0 curPtr opt2 ⟨[]⟩ (by decide) hSlice
  have hB2 := sliceScan_bb2_zero 0 curPtr ⟨[]⟩
  have hB4 := sliceScan_bb4_return 0 curPtr (some (usizeVal 0)) ⟨[]⟩ rfl
  have hToEnd :=
    StepsToV2.trans hSt0
      (StepsToV2.step (stepV2_iff_evalStepV2.mpr hB1)
        (StepsToV2.single (stepV2_iff_evalStepV2.mpr hB2)))
  have hNotPost :
      ¬ (TerminalOut.returned ⟨usizeVal 0, ⟨[]⟩⟩ =
        TerminalOut.returned ⟨usizeVal 1, ⟨[]⟩⟩) := by
    intro hT
    cases hT
  exact not_reachesDoneWithinV2_of_stepsTo_done_fail hToEnd
    (stepV2_iff_evalStepV2.mpr hB4) hNotPost hReach

/-- Safe Profile v2 body that always fails a non-optional safe `Assert`,
aborting in 1 MIR step under `--panic abort`. -/
@[expose] noncomputable def bodyV2PanicAbort : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{
    statements := []
    terminator :=
      .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true
        .divByZero 0 .unreachable
  }]
  isUnsafe := false
  identity := "canary_v2_panic_abort"
}

/-- Profile v2 program running `bodyV2PanicAbort` under `--panic abort`
without a local `#[panic_handler]`. -/
@[expose] noncomputable def progV2PanicAbort : Program := {
  bodies := [bodyV2PanicAbort]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
  panicStrategy := .abort
  hasLocalPanicHandler := false
}

/-- `--panic abort` `.aborted` refutation canary: `progV2PanicAbort` steps to
`.done (.aborted ⟨[]⟩)` in 1 step (`ExecWithinStepsV2` holds when `post` admits
`.aborted`), yet every `SafeContractV2` with `EffectMaskV2.noAbort` refutes
`ExecWithinStepsV2` at every finite step budget `bound`. -/
theorem canary_v2_panic_abort_noAbort_refutes_step_bound :
    ExecWithinStepsV2 progV2PanicAbort { args := [] } 1
      (fun out => match out with | .aborted _ => True | _ => False) ∧
    ∀ (bound : Nat) (contract : SafeContractV2),
      contract.effects = EffectMaskV2.noAbort →
      ¬ ExecWithinStepsV2 progV2PanicAbort { args := [] } bound
        (contract.post { args := [] }) := by
  let sAb : State :=
    ⟨[⟨0, 0, 0, initLocalsLoop bodyV2PanicAbort [] 0 bodyV2PanicAbort.locals,
      none, none, none⟩], ⟨[]⟩, entryMemoryWithCaller ⟨[]⟩⟩
  have hAbStep : StepV2 progV2PanicAbort sAb (.done (.aborted ⟨[]⟩)) :=
    stepV2_iff_evalStepV2.mpr rfl
  have hInitExp :=
    initStateV2_ok_of_admitted (p := progV2PanicAbort) (q := { args := [] })
      (body := bodyV2PanicAbort) rfl rfl ⟨rfl, rfl, rfl, rfl⟩
  change initStateV2 progV2PanicAbort { args := [] } = .ok sAb at hInitExp
  refine ⟨⟨sAb, hInitExp, reachesDoneWithinV2_of_done hAbStep trivial⟩, ?_⟩
  intro bound contract hMask ⟨s0, hInit, hReach⟩
  have hS0 : s0 = sAb := by
    have hEq := hInit.symm.trans hInitExp
    cases hEq
    rfl
  rw [hS0] at hReach
  have hFail : ¬ contract.post { args := [] } (.aborted ⟨[]⟩) := by
    intro hPost
    unfold SafeContractV2.post at hPost
    dsimp only at hPost
    rw [hMask] at hPost
    cases hPost.1
  exact not_reachesDoneWithinV2_of_stepsTo_done_fail (StepsToV2.refl _) hAbStep
    hFail hReach

end Anneal.StepBound.Canaries

end
