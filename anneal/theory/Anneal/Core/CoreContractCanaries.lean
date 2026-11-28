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
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-!
# Core Contract Safety Theorems & Canaries (`Anneal.Core.CoreContractCanaries`)

Pass-1 proofs and executable operational canaries covering:
- `Trusted.MirSemantics.CoreContracts` safety/frame/provenance invariants
  (`sliceIndexRange`, `sliceSplitAt`, `mem::replace`, `Option::take`,
  `Option::unwrap`, `checked_{add,mul,sub}`, `is_multiple_of`,
  `saturating_add`, `wrapping_{shl,shr}`, `leading_zeros`, `overflowing_*`,
  `cmp::{min,max}`)
- Concrete `ReachesResultV2` / `evalStepV2` positive and negative witnesses.
-/

/-! ## Helper Lemmas (Pass-1 Pure Kernel) -/

private theorem findAllocation_allocId {aid : AllocId} {xs : List Allocation}
    {a : Allocation} (h : findAllocation aid xs = some a) :
    a.allocId = aid := by
  induction xs with
  | nil => cases h
  | cons x rest ih =>
    unfold findAllocation at h
    cases hEq : Nat.beq x.allocId aid with
    | false =>
      rw [hEq] at h
      exact ih h
    | true =>
      rw [hEq] at h
      injection h with hA
      subst hA
      exact Nat.eq_of_beq_eq_true hEq

private theorem findAllocation_replaceAllocation_ne {a' : Allocation}
    {aid : AllocId} {xs : List Allocation}
    (hNe : Nat.beq a'.allocId aid = false) :
    findAllocation aid (replaceAllocation a' xs) = findAllocation aid xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [replaceAllocation]
    cases hEq : Nat.beq x.allocId a'.allocId with
    | false =>
      cases hX : Nat.beq x.allocId aid with
      | false =>
        change findAllocation aid (x :: replaceAllocation a' rest) =
          findAllocation aid (x :: rest)
        unfold findAllocation
        rw [hX]
        exact ih
      | true =>
        change findAllocation aid (x :: replaceAllocation a' rest) =
          findAllocation aid (x :: rest)
        unfold findAllocation
        rw [hX]
        rfl
    | true =>
      have hxEq : x.allocId = a'.allocId := Nat.eq_of_beq_eq_true hEq
      have hxAid : Nat.beq x.allocId aid = false := by
        rw [hxEq]; exact hNe
      change findAllocation aid (a' :: rest) = findAllocation aid (x :: rest)
      unfold findAllocation
      rw [hNe, hxAid]
      rfl

private theorem writeBytes_preserves_other_allocations {m m' : MemoryState}
    {place : MemPlace} {alignLog2 : Nat} {bytes : List AllocByte}
    {aid : AllocId} (hNe : Nat.beq place.allocId aid = false)
    (hW : writeBytes m place alignLog2 bytes = .ok m') :
    findAllocation aid m'.allocations = findAllocation aid m.allocations ∧
    m'.nextAllocId = m.nextAllocId := by
  unfold writeBytes at hW
  cases hFind : findAllocation place.allocId m.allocations with
  | none => rw [hFind] at hW; cases hW
  | some a =>
    rw [hFind] at hW
    dsimp only at hW
    cases hLen : Nat.beq bytes.length 0 with
    | true =>
      rw [hLen] at hW
      cases hAl : !isAligned a place.offset alignLog2 with
      | true => rw [hAl] at hW; cases hW
      | false =>
        rw [hAl] at hW
        injection hW with hEq
        subst hEq
        exact ⟨rfl, rfl⟩
    | false =>
      rw [hLen] at hW
      cases hChk : (!a.live || !isInBounds a place.offset bytes.length ||
          !isAligned a place.offset alignLog2) with
      | true => rw [hChk] at hW; cases hW
      | false =>
        rw [hChk] at hW
        cases hMut : a.mutability
        · rw [hMut] at hW; cases hW
        · rw [hMut] at hW
          injection hW with hMem
          subst hMem
          have hAidA : a.allocId = place.allocId := findAllocation_allocId hFind
          have hNeA : Nat.beq a.allocId aid = false := by
            rw [hAidA]; exact hNe
          exact ⟨findAllocation_replaceAllocation_ne hNeA, rfl⟩

/-! ## Structural & Safety Contracts for `CoreContracts` -/

/-- `Option::unwrap` on `None` fails closed via `corePanicTrap`. -/
theorem coreContract_optionUnwrap_none_traps (m : MemoryState) (inner : MirTy) :
    execCoreContractOp m (.optionUnwrap inner)
      [(.option inner, .optionVal none)] inner = .error corePanicTrap := by
  unfold execCoreContractOp
  dsimp only
  rw [mirTy_beq_refl inner]
  rfl

/-- `slice::is_empty` agrees with `len.toNat == 0` on valid slices. -/
theorem coreContract_sliceIsEmpty_ok {m : MemoryState} {elem : MirTy}
    {reqMut : Mutability} {p : PtrVal} {len : UInt64}
    (hNoRef : isSizedNoRefV2Ty elem = true)
    (hValid : refValidInMem m reqMut (.slice elem) (.slicePtr p len) = .ok ()) :
    execCoreContractOp m (.sliceIsEmpty elem)
      [(.ref reqMut (.slice elem), .slicePtr p len)] .bool =
      .ok (.bool (Nat.beq len.toNat 0), m) := by
  unfold execCoreContractOp
  dsimp only
  rw [mirTy_beq_refl elem, hNoRef]
  have hCond : (!true || !MirTy.beq .bool .bool || !true) = false := rfl
  have hIfFalse : ∀ {α : Type} (x y : α),
      (if false = true then x else y) = y := fun _ _ => rfl
  rw [hCond, hIfFalse, hValid]

/-- Any successful `execSliceSubslice` preserves `MemoryState` and `allocId`
provenance and guarantees `startOff ≤ endOff ≤ len.toNat`. -/
theorem execSliceSubslice_preserves_prov_and_bounds {m m' : MemoryState}
    {reqMut inMut : Mutability} {elem : MirTy} {p p' : PtrVal}
    {len len' : UInt64} {startOff endOff : Nat}
    (hOk : execSliceSubslice m reqMut inMut elem p len startOff endOff =
      .ok (.slicePtr p' len', m')) :
    m' = m ∧ p'.allocId = p.allocId ∧
    startOff ≤ endOff ∧ endOff ≤ len.toNat ∧
    len'.toNat = (UInt64.ofNat (endOff - startOff)).toNat := by
  unfold execSliceSubslice at hOk
  cases hNoRef : isSizedNoRefV2Ty elem with
  | false => rw [hNoRef] at hOk; cases hOk
  | true =>
    rw [hNoRef] at hOk
    cases hMut :
        (Mutability.beq inMut .shared && Mutability.beq reqMut .mut) with
    | true => rw [hMut] at hOk; cases hOk
    | false =>
      rw [hMut] at hOk
      cases hRef : refValidInMem m inMut (.slice elem) (.slicePtr p len) with
      | error k => rw [hRef] at hOk; cases hOk
      | ok u =>
        rw [hRef] at hOk
        dsimp only at hOk
        cases hBnd :
            (!Nat.ble startOff endOff || !Nat.ble endOff len.toNat) with
        | true => rw [hBnd] at hOk; cases hOk
        | false =>
          rw [hBnd] at hOk
          cases hLay : layoutOfTyV2 elem with
          | none => rw [hLay] at hOk; cases hOk
          | some lay =>
            rw [hLay] at hOk
            dsimp only at hOk
            cases hAdd : ptrAddInMem m lay.size p startOff with
            | error k => rw [hAdd] at hOk; cases hOk
            | ok pAdd =>
              rw [hAdd] at hOk
              injection hOk with hPair
              have hEqV : Val.slicePtr pAdd (UInt64.ofNat (endOff - startOff)) =
                  Val.slicePtr p' len' := congrArg Prod.fst hPair
              have hEqM : m = m' := congrArg Prod.snd hPair
              injection hEqV with hPEq hLenEq
              have hProvEq : pAdd.allocId = p.allocId := by
                unfold ptrAddInMem at hAdd
                change (if !Nat.blt (startOff * lay.size) isizeMaxBytes then
                    Except.error FaultKind.undefined
                  else
                    match p.allocId with
                    | none =>
                      if Nat.beq (startOff * lay.size) 0 then Except.ok p
                      else .error .undefined
                    | some aid =>
                      match findAllocation aid m.allocations with
                      | none => .error .undefined
                      | some a =>
                        if !a.live || !Nat.ble (p.offsetBytes.toNat +
                            startOff * lay.size) a.bytes.length then
                          .error .undefined
                        else
                          .ok { p with
                            offsetBytes := UInt64.ofNat (p.offsetBytes.toNat +
                              startOff * lay.size) }) = .ok pAdd at hAdd
                cases hLim : Nat.blt (startOff * lay.size) isizeMaxBytes with
                | false => rw [hLim] at hAdd; cases hAdd
                | true =>
                  rw [hLim] at hAdd
                  change (match p.allocId with
                    | none =>
                      if Nat.beq (startOff * lay.size) 0 then Except.ok p
                      else Except.error FaultKind.undefined
                    | some aid =>
                      match findAllocation aid m.allocations with
                      | none => Except.error FaultKind.undefined
                      | some a =>
                        if !a.live || !Nat.ble (p.offsetBytes.toNat +
                            startOff * lay.size) a.bytes.length then
                          Except.error FaultKind.undefined
                        else
                          Except.ok { p with
                            offsetBytes := UInt64.ofNat (p.offsetBytes.toNat +
                              startOff * lay.size) }) = .ok pAdd at hAdd
                  cases hAid : p.allocId with
                  | none =>
                    rw [hAid] at hAdd
                    cases hZ : Nat.beq (startOff * lay.size) 0 with
                    | false => rw [hZ] at hAdd; cases hAdd
                    | true =>
                      rw [hZ] at hAdd
                      injection hAdd with hP0
                      rw [← hP0, hAid]
                  | some aid =>
                    rw [hAid] at hAdd
                    dsimp only at hAdd
                    cases hF : findAllocation aid m.allocations with
                    | none => rw [hF] at hAdd; cases hAdd
                    | some a =>
                      rw [hF] at hAdd
                      dsimp only at hAdd
                      cases hOkB :
                          (!a.live || !Nat.ble (p.offsetBytes.toNat +
                            startOff * lay.size) a.bytes.length) with
                      | true => rw [hOkB] at hAdd; cases hAdd
                      | false =>
                        rw [hOkB] at hAdd
                        injection hAdd with hP1
                        rw [← hP1]
              have hBle1 : Nat.ble startOff endOff = true := by
                cases h1 : Nat.ble startOff endOff with
                | true => rfl
                | false => rw [h1] at hBnd; cases hBnd
              have hBle2 : Nat.ble endOff len.toNat = true := by
                cases h2 : Nat.ble endOff len.toNat with
                | true => rfl
                | false =>
                  cases h1 : Nat.ble startOff endOff <;>
                    rw [h1, h2] at hBnd <;> cases hBnd
              refine ⟨hEqM.symm, ?_, Nat.le_of_ble_eq_true hBle1,
                Nat.le_of_ble_eq_true hBle2, ?_⟩
              · rw [← hPEq]; exact hProvEq
              · rw [← hLenEq]

/-- Out-of-bounds range subslice fails closed with `corePanicTrap`. -/
theorem execSliceSubslice_oob_traps {m : MemoryState}
    {reqMut inMut : Mutability} {elem : MirTy} {p : PtrVal} {len : UInt64}
    {startOff endOff : Nat}
    (hNoRef : isSizedNoRefV2Ty elem = true)
    (hMut :
      (Mutability.beq inMut .shared && Mutability.beq reqMut .mut) = false)
    (hValid : refValidInMem m inMut (.slice elem) (.slicePtr p len) = .ok ())
    (hOob : (!Nat.ble startOff endOff || !Nat.ble endOff len.toNat) = true) :
    execSliceSubslice m reqMut inMut elem p len startOff endOff =
      .error corePanicTrap := by
  unfold execSliceSubslice
  rw [hNoRef]
  rw [hMut]
  rw [hValid]
  dsimp only
  rw [hOob]
  rfl

/-- `mem::replace` / `Option::take` preserve every unrelated allocation id
in memory as well as `nextAllocId`. -/
theorem execMemReplace_preserves_other_allocs {m m' : MemoryState}
    {ty : MirTy} {p : PtrVal} {srcVal oldVal : Val} {aid otherId : AllocId}
    (hAlloc : p.allocId = some aid)
    (hNe : Nat.beq aid otherId = false)
    (hOk : execMemReplace m ty p srcVal = .ok (oldVal, m')) :
    findAllocation otherId m'.allocations =
      findAllocation otherId m.allocations ∧
    m'.nextAllocId = m.nextAllocId := by
  unfold execMemReplace at hOk
  cases hGuard : (!isSizedNoRefV2Ty ty || !checkValV2 srcVal ty) with
  | true => rw [hGuard] at hOk; cases hOk
  | false =>
    rw [hGuard] at hOk
    cases hRefs : refsValidInMem m ty srcVal with
    | false => rw [hRefs] at hOk; cases hOk
    | true =>
      rw [hRefs] at hOk
      cases hLay : layoutOfTyV2 ty with
      | none => rw [hLay] at hOk; cases hOk
      | some lay =>
        rw [hLay, hAlloc] at hOk
        dsimp only at hOk
        cases hFind : findAllocation aid m.allocations with
        | none => rw [hFind] at hOk; cases hOk
        | some a =>
          rw [hFind] at hOk
          dsimp only at hOk
          cases hMut : (!a.live || !Mutability.beq a.mutability .mut) with
          | true => rw [hMut] at hOk; cases hOk
          | false =>
            rw [hMut] at hOk
            cases hLoad : loadIndirectV2 m ty ⟨aid, p.offsetBytes.toNat⟩ with
            | error k => rw [hLoad] at hOk; cases hOk
            | ok optOld =>
              rw [hLoad] at hOk
              cases optOld with
              | none => cases hOk
              | some loaded =>
                let place := MemPlace.mk aid p.offsetBytes.toNat
                cases hStore : storeIndirectV2 m ty place srcVal with
                | error k => rw [hStore] at hOk; cases hOk
                | ok m1 =>
                  rw [hStore] at hOk
                  injection hOk with hPair
                  have hMemEq : m1 = m' := congrArg Prod.snd hPair
                  rw [← hMemEq]
                  unfold storeIndirectV2 at hStore
                  rw [hLay] at hStore
                  dsimp only at hStore
                  cases hEnc : encodeValV2 profileV2TargetEndian ty srcVal with
                  | error k => rw [hEnc] at hStore; cases hStore
                  | ok encBytes =>
                    rw [hEnc] at hStore
                    exact writeBytes_preserves_other_allocations hNe hStore

/-- `checked_add` agrees with `truncateScalarWithHostOverflow` overflow
detection. -/
theorem execCheckedArith_add_iff {w : IntWidth} {s : Bool}
    {lSv rSv : ScalarVal} {m : MemoryState} :
    (execCheckedArith .add w s lSv rSv m = .ok (.optionVal none, m) ↔
      ∃ sv, truncateScalarWithHostOverflow w s
        (decodeScalar lSv + decodeScalar rSv) = .ok (sv, true)) := by
  unfold execCheckedArith
  dsimp only
  cases hTr : truncateScalarWithHostOverflow w s
      (decodeScalar lSv + decodeScalar rSv) with
  | error k =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, hEq⟩ := h
      cases hEq
  | ok p =>
    cases p with
    | mk sv ovf =>
      cases ovf with
      | false =>
        constructor
        · intro h; cases h
        · intro h
          let ⟨_, hEq⟩ := h
          injection hEq with hP
          have hF : false = true := congrArg Prod.snd hP
          cases hF
      | true =>
        constructor
        · intro _; exact ⟨sv, rfl⟩
        · intro _; rfl

/-! ## Concrete Operational Canaries (`execCoreContractOp` & `StepV2`) -/

@[expose] def canaryUsizeTy : MirTy := .int .isize false
@[expose] def canaryU8Ty : MirTy := .int .i8 false
@[expose] def canaryU32Ty : MirTy := .int .i32 false
@[expose] def canaryU64Ty : MirTy := .int .i64 false

@[expose] def canaryU8Val (n : Nat) : Val :=
  .scalar ⟨.i8, false, BitVec.ofNat 128 n⟩

@[expose] def canaryUsizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

@[expose] def canaryU64Val (n : Nat) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 n⟩

@[expose] def mkCanarySliceMemAligned (alignLog2 : Nat) (bytes : List UInt8) :
    MemoryState :=
  let alloc : Allocation := {
    allocId := 2
    alignLog2 := alignLog2
    mutability := .mut
    bytes := bytes.map (fun b => AllocByte.init b none)
    live := true
  }
  { nextAllocId := 3, allocations := [alloc] }

@[expose] def mkCanarySliceMem (bytes : List UInt8) : MemoryState :=
  mkCanarySliceMemAligned 0 bytes

/-- Canary 1: `<[u8] as Index<Range<usize>>>::index` succeeds on `&s[1..3]`
with provenance preserved and pointer offset advanced by 1. -/
theorem canary_sliceIndexRange_ok :
    let m := mkCanarySliceMem [10, 20, 30, 40]
    let p : PtrVal := ⟨some 2, 0, .isize⟩
    execCoreContractOp m (.sliceIndexRange .shared canaryU8Ty)
      [(.ref .shared (.slice canaryU8Ty), .slicePtr p 4),
       (.range canaryUsizeTy, .range 1 3)]
      (.ref .shared (.slice canaryU8Ty)) =
      .ok (.slicePtr ⟨some 2, 1, .isize⟩ 2, m) := by
  unfold execCoreContractOp execSliceSubslice isSizedNoRefV2Ty
    refValidInMem sliceFromRawPartsCheck sliceRefRawCheck findAllocation
    layoutOfTyV2 layoutOfTy intLayout ptrAddInMem
    isInBounds isAligned isSliceAllInit
  rfl

/-- Canary 2: `<[u8] as Index<Range<usize>>>::index` fails closed via
`corePanicTrap` when `end > len`. -/
theorem canary_sliceIndexRange_oob_traps :
    let m := mkCanarySliceMem [10, 20, 30, 40]
    let p : PtrVal := ⟨some 2, 0, .isize⟩
    execCoreContractOp m (.sliceIndexRange .shared canaryU8Ty)
      [(.ref .shared (.slice canaryU8Ty), .slicePtr p 4),
       (.range canaryUsizeTy, .range 2 5)]
      (.ref .shared (.slice canaryU8Ty)) =
      .error corePanicTrap := by
  unfold execCoreContractOp execSliceSubslice isSizedNoRefV2Ty
    refValidInMem sliceFromRawPartsCheck sliceRefRawCheck findAllocation
    layoutOfTyV2 layoutOfTy intLayout
    isInBounds isAligned isSliceAllInit corePanicTrap
  rfl

/-- Canary 3: `core::slice::split_at` on `4`-byte slice at `mid = 2` returns
disjoint `2`-byte subslices preserving `allocId = 2`. -/
theorem canary_sliceSplitAt_ok :
    let m := mkCanarySliceMem [10, 20, 30, 40]
    let p : PtrVal := ⟨some 2, 0, .isize⟩
    let sliceRefTy := MirTy.ref .shared (.slice canaryU8Ty)
    execCoreContractOp m (.sliceSplitAt .shared canaryU8Ty)
      [(sliceRefTy, .slicePtr p 4),
       (canaryUsizeTy, canaryUsizeVal 2)]
      (.tuple [sliceRefTy, sliceRefTy]) =
      .ok (.tuple [.slicePtr p 2, .slicePtr ⟨some 2, 2, .isize⟩ 2], m) := by
  unfold execCoreContractOp execSliceSplitAtCall execSliceSplitAtOutcome
    isSizedNoRefV2Ty
    refValidInMem sliceFromRawPartsCheck sliceRefRawCheck findAllocation
    layoutOfTyV2 layoutOfTy intLayout ptrAddInMem
    isInBounds isAligned isSliceAllInit canaryUsizeVal
  rfl

/-- Canary 4: `u64::is_multiple_of` matches Rust on `(0, 0)`, `(5, 0)`, and
`(6, 3)`. -/
theorem canary_isMultipleOf_cases :
    execCoreContractOp MemoryState.empty (.numIsMultipleOf .i64 false)
      [(canaryU64Ty, canaryU64Val 0), (canaryU64Ty, canaryU64Val 0)] .bool =
      .ok (.bool true, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numIsMultipleOf .i64 false)
      [(canaryU64Ty, canaryU64Val 5), (canaryU64Ty, canaryU64Val 0)] .bool =
      .ok (.bool false, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numIsMultipleOf .i64 false)
      [(canaryU64Ty, canaryU64Val 6), (canaryU64Ty, canaryU64Val 3)] .bool =
      .ok (.bool true, MemoryState.empty) := by
  refine ⟨?_, ?_, ?_⟩ <;> (
    unfold execCoreContractOp canaryU64Val
    rfl)

/-- Canary 5: `checked_add`, `saturating_add`, `wrapping_shl`, `leading_zeros`,
and `overflowing_sub` match Rust `u8` semantics. -/
theorem canary_scalar_ops :
    execCoreContractOp MemoryState.empty (.numCheckedAdd .i8 false)
      [(canaryU8Ty, canaryU8Val 250), (canaryU8Ty, canaryU8Val 10)]
      (.option canaryU8Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numSaturatingAdd .i8 false)
      [(canaryU8Ty, canaryU8Val 250), (canaryU8Ty, canaryU8Val 10)] canaryU8Ty =
      .ok (canaryU8Val 255, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numWrappingShl .i8 false)
      [(canaryU8Ty, canaryU8Val 1),
       (canaryU32Ty, .scalar ⟨.i32, false, BitVec.ofNat 128 9⟩)]
      canaryU8Ty = .ok (canaryU8Val 2, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numLeadingZeros .i8 false)
      [(canaryU8Ty, canaryU8Val 0x0f)] canaryU32Ty =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 4⟩, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numOverflowingSub .i8 false)
      [(canaryU8Ty, canaryU8Val 0), (canaryU8Ty, canaryU8Val 1)]
      (.tuple [canaryU8Ty, .bool]) =
      .ok (.tuple [canaryU8Val 255, .bool true], MemoryState.empty) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (
    unfold execCoreContractOp execCheckedArith execOverflowingArith
      saturateScalar evalShiftOp leadingZerosFrom
      decodeScalar truncateScalar truncateBits canaryU8Val
    rfl)

/-- Canary 6: single-step `evalStepV2` constructs `Some(77u8)`, computes
`discriminant` (`1`), downcasts `(opt as Some).0`, and reaches `return_`. -/
theorem canary_evalStepV2_option_roundtrip :
    let body : Body := {
      argumentCount := 1
      locals := [canaryU8Ty, canaryU8Ty, .option canaryU8Ty, .int .isize true]
      basicBlocks := [
        {
          statements := [
            .assign ⟨2, []⟩
              (.aggregateOption 1 canaryU8Ty (some (.copy ⟨1, []⟩))),
            .assign ⟨3, []⟩ (.discriminant ⟨2, []⟩)
          ]
          terminator := .switchInt (.copy ⟨3, []⟩) {
            branches := [(1, 1)]
            otherwise := 2
          }
        },
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.copy ⟨2, [.downcast 1, .field 0 canaryU8Ty]⟩))
          ]
          terminator := .return_
        },
        {
          statements := []
          terminator := .unreachable
        }
      ]
    }
    let prog : Program := {
      bodies := [body]
      entryDefId := 0
      pointerWidthBits := 64
      mirProfileVersion := 2
      scope := .unit
    }
    let q : Query := { args := [canaryU8Val 77], callerMem := ⟨[]⟩ }
    BehaviorV2 prog q (.returned ⟨canaryU8Val 77, ⟨[]⟩⟩) := by
  intro body prog q
  exact (spec_and_behaviorV2_of_exec_eq (p := prog) (q := q)
    (out := .returned ⟨canaryU8Val 77, ⟨[]⟩⟩) (fuel := 10) rfl).2.1

/-- Canary 7: `core::mem::replace::<u8>` reads `42`, writes `99`, and
preserves memory round-trip through `loadIndirectV2`. -/
theorem canary_memReplace_roundtrip :
    let m0 := mkCanarySliceMem [42]
    let p : PtrVal := ⟨some 2, 0, .isize⟩
    match execCoreContractOp m0 (.memReplace canaryU8Ty)
        [(.ref .mut canaryU8Ty, .ptr p), (canaryU8Ty, canaryU8Val 99)]
        canaryU8Ty with
    | .ok (oldVal, m1) =>
      oldVal = canaryU8Val 42 ∧
      loadIndirectV2 m1 canaryU8Ty ⟨2, 0⟩ = .ok (some (canaryU8Val 99))
    | .error _ => False := by
  unfold execCoreContractOp execMemReplace isSizedNoRefV2Ty refValidInMem
    checkValV2 checkVal Val.ty? refsValidInMem layoutOfTyV2 layoutOfTy
    intLayout findAllocation
    loadIndirectV2 storeIndirectV2 readBytes writeBytes encodeValV2
    decodeValV2 encodeVal decodeVal replaceAllocation isInBounds isAligned
    canaryU8Val
  exact ⟨rfl, rfl⟩

/-- Canary 8: `core::cmp::min` tie returns `self` (`lSv`) and `core::cmp::max`
tie returns `other` (`rSv`), matching `library/core/src/cmp.rs:1038,1077`
(distinguished via `ScalarVal` inputs with distinct un-truncated upper bits
that decode to the same `i8`/`u8` mathematical value). -/
theorem canary_cmp_min_max_tie_break :
    let lU8 : ScalarVal := ⟨.i8, false, BitVec.ofNat 128 5⟩
    let rU8 : ScalarVal := ⟨.i8, false, BitVec.ofNat 128 261⟩
    let lI8 : ScalarVal := ⟨.i8, true, BitVec.ofNat 128 255⟩
    let rI8 : ScalarVal := ⟨.i8, true, BitVec.ofNat 128 511⟩
    execCoreContractOp MemoryState.empty (.cmpMin .i8 false)
      [(canaryU8Ty, .scalar lU8), (canaryU8Ty, .scalar rU8)] canaryU8Ty =
      .ok (.scalar lU8, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.cmpMax .i8 false)
      [(canaryU8Ty, .scalar lU8), (canaryU8Ty, .scalar rU8)] canaryU8Ty =
      .ok (.scalar rU8, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.cmpMin .i8 true)
      [(.int .i8 true, .scalar lI8), (.int .i8 true, .scalar rI8)]
      (.int .i8 true) =
      .ok (.scalar lI8, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.cmpMax .i8 true)
      [(.int .i8 true, .scalar lI8), (.int .i8 true, .scalar rI8)]
      (.int .i8 true) =
      .ok (.scalar rI8, MemoryState.empty) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (
    unfold execCoreContractOp decodeScalar truncateBits
    rfl)

/-- Canary 9: `isSizedNoRefV2Ty` and `isNicheFreeOptionPayloadV2` fail closed
on `#[repr(Rust)]` tuples (`(u8, u32, u8)` and `OverflowPair`), ranges
(`Range<usize>`, `RangeTo<usize>`, `RangeFrom<usize>`), and nested options
(`&Option<Option<u8>>`), and `BodyStaticAdmittedV2` rejects a body containing
`&(u8, u32, u8)`. -/
theorem canary_univariant_and_nested_option_refused :
    let reorderedTuple :=
      MirTy.tuple [canaryU8Ty, canaryU32Ty, canaryU8Ty]
    let overflowPair := MirTy.tuple [canaryU8Ty, .bool]
    let sliceTuple := MirTy.tuple [canaryU8Ty, canaryU32Ty]
    let badBody : Body := {
      identity := "canary::bad_tuple_ref"
      argumentCount := 1
      locals := [.unit, .ref .shared reorderedTuple]
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let prog : Program := {
      bodies := [badBody]
      entryDefId := 0
      pointerWidthBits := 64
      mirProfileVersion := 2
      scope := .unit
    }
    isSizedNoRefV2Ty reorderedTuple = false ∧
    isSizedNoRefV2Ty overflowPair = false ∧
    isSizedNoRefV2Ty (.range canaryUsizeTy) = false ∧
    isSizedNoRefV2Ty (.rangeTo canaryUsizeTy) = false ∧
    isSizedNoRefV2Ty (.rangeFrom canaryUsizeTy) = false ∧
    isSizedNoRefV2Ty (.option (.option canaryU8Ty)) = false ∧
    isNicheFreeOptionPayloadV2 reorderedTuple = false ∧
    isNicheFreeOptionPayloadV2 (.range canaryUsizeTy) = false ∧
    isSupportedV2LocalTy (.ref .shared reorderedTuple) = false ∧
    isSupportedV2LocalTy (.option reorderedTuple) = false ∧
    isSupportedV2LocalTy (.ref .shared (.slice sliceTuple)) = false ∧
    isSupportedV2LocalTy (.ref .shared (.option (.option canaryU8Ty))) = false ∧
    BodyStaticAdmittedV2 prog badBody = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hAll :
      ({
        identity := "canary::bad_tuple_ref"
        argumentCount := 1
        locals := [.unit,
          .ref .shared (MirTy.tuple [canaryU8Ty, canaryU32Ty, canaryU8Ty])]
        basicBlocks := [{ statements := [], terminator := .return_ }]
      } : Body).locals.all isSupportedV2LocalTy = false := rfl
  unfold BodyStaticAdmittedV2
  dsimp only
  rw [hAll, Bool.and_false]

/-- Canary 10: local tuples (`(bool, u64, u32)`, `(&[u8], &[u8])`), local
`Range<usize>`, `Option<u64>`, and `&mut Option<u64>` remain admitted. -/
theorem canary_supported_locals_and_opt_ref_preserved :
    isSupportedV2LocalTy (.tuple [.bool, canaryU64Ty, canaryU32Ty]) = true ∧
    isSupportedV2LocalTy
      (.tuple [.ref .shared (.slice canaryU8Ty),
        .ref .shared (.slice canaryU8Ty)]) = true ∧
    isSupportedV2LocalTy (.option canaryU64Ty) = true ∧
    isSupportedV2LocalTy (.range canaryUsizeTy) = true ∧
    isSupportedV2LocalTy (.ref .mut (.option canaryU64Ty)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 11: 128-bit checked, saturating, and overflowing arithmetic preserve
mathematical host overflow detection (`intHostOverflow`) alongside in-bounds
execution. -/
theorem canary_i128_overflow_contracts :
    let u128Ty : MirTy := .int .i128 false
    let i128Ty : MirTy := .int .i128 true
    let u128Max : ScalarVal :=
      ⟨.i128, false, BitVec.ofNat 128 340282366920938463463374607431768211455⟩
    let u128Zero : ScalarVal := ⟨.i128, false, 0⟩
    let u128One : ScalarVal := ⟨.i128, false, 1⟩
    let u128Two : ScalarVal := ⟨.i128, false, 2⟩
    let u128Three : ScalarVal := ⟨.i128, false, 3⟩
    let i128Max : ScalarVal :=
      ⟨.i128, true, BitVec.ofNat 128 170141183460469231731687303715884105727⟩
    let i128Min : ScalarVal :=
      ⟨.i128, true, BitVec.ofNat 128 170141183460469231731687303715884105728⟩
    let i128One : ScalarVal := ⟨.i128, true, 1⟩
    let i128NegOne : ScalarVal :=
      ⟨.i128, true, BitVec.ofNat 128 340282366920938463463374607431768211455⟩
    execCoreCallWithMem MemoryState.empty (.numCheckedAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedSub .i128 false)
      [(u128Ty, .scalar u128Zero), (u128Ty, .scalar u128One)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedAdd .i128 true)
      [(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)]
      (.option i128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedMul .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128Two)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedAdd .i128 false)
      [(u128Ty, .scalar u128One), (u128Ty, .scalar u128Two)]
      (.option u128Ty) =
      .ok (.optionVal (some (.scalar u128Three)), MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numSaturatingAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)] u128Ty =
      .ok (.scalar u128Max, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numSaturatingAdd .i128 true)
      [(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)] i128Ty =
      .ok (.scalar i128Max, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numSaturatingAdd .i128 true)
      [(i128Ty, .scalar i128Min), (i128Ty, .scalar i128NegOne)] i128Ty =
      .ok (.scalar i128Min, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numOverflowingAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar u128Zero, .bool true], MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numOverflowingSub .i128 false)
      [(u128Ty, .scalar u128Zero), (u128Ty, .scalar u128One)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar u128Max, .bool true], MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numOverflowingAdd .i128 true)
      [(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)]
      (.tuple [i128Ty, .bool]) =
      .ok (.tuple [.scalar i128Min, .bool true], MemoryState.empty) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 12: `&[Option<u64>]` containing `None` (with `.uninit` inactive
payload bytes matching `encodeValV2`) passes `refValidInMem`,
`execSliceSubslice` (`&s[1..2]`), and `execSliceSplitAtOutcome`
(`split_at(1)`), while uninitialized `None` tag bytes or uninitialized `Some`
payload bytes fail closed with `.undefined`; and `isInhabitedV2Ty` /
`refValidInMem` reject
positive-length slices of uninhabited types (`!`, `[!; 1]`, `((), !)`) while
admitting empty `&[] : &[!]` and inhabited ZSTs (`()`, `[!; 0]`). -/
theorem canary_slice_option_none_and_uninhabited :
    let optU64Ty := MirTy.option canaryU64Ty
    let noneBytes :=
      List.replicate 8 (AllocByte.init 0 none) ++
        List.replicate 8 AllocByte.uninit
    let some42Bytes :=
      (AllocByte.init 1 none :: List.replicate 7 (AllocByte.init 0 none)) ++
        (AllocByte.init 42 none :: List.replicate 7 (AllocByte.init 0 none))
    let mGood : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2
        alignLog2 := 3
        mutability := .mut
        bytes := noneBytes ++ some42Bytes
        live := true
      }]
    }
    let mBadTag : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2
        alignLog2 := 3
        mutability := .mut
        bytes := (AllocByte.uninit :: List.replicate 15 (AllocByte.init 0 none))
        live := true
      }]
    }
    let mBadSome : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2
        alignLog2 := 3
        mutability := .mut
        bytes := (AllocByte.init 1 none ::
          List.replicate 7 (AllocByte.init 0 none)) ++
          List.replicate 8 AllocByte.uninit
        live := true
      }]
    }
    let pAlloc : PtrVal := ⟨some 2, 0, .isize⟩
    let pDang : PtrVal := ⟨none, 8, .isize⟩
    let sliceRefTy := MirTy.ref .shared (.slice optU64Ty)
    encodeValV2 profileV2TargetEndian optU64Ty (.optionVal none) =
      .ok noneBytes ∧
    refValidInMem mGood .shared (.slice optU64Ty) (.slicePtr pAlloc 2) =
      .ok () ∧
    execCoreContractOp mGood (.sliceIndexRange .shared optU64Ty)
      [(sliceRefTy, .slicePtr pAlloc 2),
       (.range canaryUsizeTy, .range 1 2)]
      sliceRefTy =
      .ok (.slicePtr ⟨some 2, 16, .isize⟩ 1, mGood) ∧
    execCoreContractOp mGood (.sliceSplitAt .shared optU64Ty)
      [(sliceRefTy, .slicePtr pAlloc 2),
       (canaryUsizeTy, canaryUsizeVal 1)]
      (.tuple [sliceRefTy, sliceRefTy]) =
      .ok (.tuple [.slicePtr pAlloc 1, .slicePtr ⟨some 2, 16, .isize⟩ 1],
        mGood) ∧
    refValidInMem mBadTag .shared (.slice optU64Ty) (.slicePtr pAlloc 1) =
      .error .undefined ∧
    refValidInMem mBadSome .shared (.slice optU64Ty) (.slicePtr pAlloc 1) =
      .error .undefined ∧
    isInhabitedV2Ty .never = false ∧
    isInhabitedV2Ty (.array .never 1) = false ∧
    isInhabitedV2Ty (.array .never 0) = true ∧
    isInhabitedV2Ty (.tuple [.unit, .never]) = false ∧
    isInhabitedV2Ty (.option .never) = true ∧
    refValidInMem MemoryState.empty .shared (.slice .never)
      (.slicePtr pDang 1) = .error .undefined ∧
    refValidInMem mGood .mut (.slice .never)
      (.slicePtr pAlloc 1) = .error .undefined ∧
    refValidInMem MemoryState.empty .shared (.slice .never)
      (.slicePtr pDang 0) = .ok () ∧
    refValidInMem MemoryState.empty .shared (.slice .unit)
      (.slicePtr pDang 3) = .ok () :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 13: projected `Option` discriminants (`*opt_ref` via `.deref` and
`pair.0` via `.field 0`) evaluate to `0isize`/`1isize` and enforce
`dstTy = isize`, while `Option::unwrap` validates reference payloads via
`refsValidInMem` (rejecting dangling references as `.undefined`). -/
theorem canary_option_projected_discriminant_and_unwrap_ref :
    let optU64Ty := MirTy.option canaryU64Ty
    let refOptTy := MirTy.ref .shared optU64Ty
    let refU8Ty := MirTy.ref .shared canaryU8Ty
    let tupTy := MirTy.tuple [optU64Ty, canaryU64Ty]
    let noneBytes :=
      List.replicate 8 (AllocByte.init 0 none) ++
        List.replicate 8 AllocByte.uninit
    let someBytes :=
      (AllocByte.init 1 none :: List.replicate 7 (AllocByte.init 0 none)) ++
        (AllocByte.init 7 none :: List.replicate 7 (AllocByte.init 0 none))
    let optMem : MemoryState := {
      nextAllocId := 4
      allocations := [
        { allocId := 2, alignLog2 := 3, mutability := .shared,
          bytes := noneBytes, live := true },
        { allocId := 3, alignLog2 := 3, mutability := .shared,
          bytes := someBytes, live := true }
      ]
    }
    let deadRefMem : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2, alignLog2 := 0, mutability := .shared,
        bytes := [.init 5 none], live := false
      }]
    }
    let derefPlace : Place := { localId := 0, projection := [.deref] }
    let fieldPlace : Place := { localId := 0, projection := [.field 0 optU64Ty] }
    let isizeTy : MirTy := .int .isize true
    evalRvalueV2 [refOptTy] [.immediate (some (.ptr ⟨some 2, 0, .isize⟩))]
      optMem isizeTy (.discriminant derefPlace) =
      .ok (.scalar ⟨.isize, true, 0⟩,
        [.immediate (some (.ptr ⟨some 2, 0, .isize⟩))], optMem) ∧
    evalRvalueV2 [refOptTy] [.immediate (some (.ptr ⟨some 3, 0, .isize⟩))]
      optMem isizeTy (.discriminant derefPlace) =
      .ok (.scalar ⟨.isize, true, 1⟩,
        [.immediate (some (.ptr ⟨some 3, 0, .isize⟩))], optMem) ∧
    evalRvalueV2 [tupTy]
      [.immediate (some (.tuple [.optionVal (some (canaryU64Val 9)),
        canaryU64Val 1]))]
      MemoryState.empty isizeTy (.discriminant fieldPlace) =
      .ok (.scalar ⟨.isize, true, 1⟩,
        [.immediate (some (.tuple [.optionVal (some (canaryU64Val 9)),
          canaryU64Val 1]))],
        MemoryState.empty) ∧
    evalRvalueV2 [optU64Ty] [.immediate (some (.optionVal none))]
      MemoryState.empty canaryU8Ty (.discriminant { localId := 0 }) =
      .error .unsupported ∧
    execCoreContractOp deadRefMem (.optionUnwrap refU8Ty)
      [(.option refU8Ty, .optionVal (some (.ptr ⟨some 2, 0, .isize⟩)))]
      refU8Ty = .error .undefined :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 14: `Range<usize>` projected field assignments (`r.start = x` and
`r.end = y`) update the respective bound via `writePlaceV2`
(`validatePlaceProjV2` + `updateValAtProjV2`), out-of-bounds field `2` fails
closed, and indirect-local `Option` downcast `Move` fails closed as
`.unsupported`. -/
theorem canary_range_field_assign_and_indirect_downcast_move_refused :
    let rangeTy : MirTy := .range canaryUsizeTy
    let optU64Ty : MirTy := .option canaryU64Ty
    let locals0 : List LocalSlot := [.immediate (some (.range 1 5))]
    let locals1 : List LocalSlot := [.immediate (some (.range 2 5))]
    let locals2 : List LocalSlot := [.immediate (some (.range 2 9))]
    let pStart : Place := { localId := 0, projection := [.field 0 canaryUsizeTy] }
    let pEnd : Place := { localId := 0, projection := [.field 1 canaryUsizeTy] }
    let pBad : Place := { localId := 0, projection := [.field 2 canaryUsizeTy] }
    let movePlace : Place :=
      { localId := 0, projection := [.downcast 1, .field 0 canaryU64Ty] }
    writePlaceV2 [rangeTy] locals0 MemoryState.empty pStart canaryUsizeTy
      (canaryUsizeVal 2) = .ok (locals1, MemoryState.empty) ∧
    writePlaceV2 [rangeTy] locals1 MemoryState.empty pEnd canaryUsizeTy
      (canaryUsizeVal 9) = .ok (locals2, MemoryState.empty) ∧
    writePlaceV2 [rangeTy] locals0 MemoryState.empty pBad canaryUsizeTy
      (canaryUsizeVal 0) = .error .unsupported ∧
    evalOperandToSlotV2 [optU64Ty] [.indirect ⟨2, 0⟩] MemoryState.empty
      (.move movePlace) =
      .error .unsupported :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Canary 14: core scalar and slice operations (`count_ones`, `trailing_zeros`,
`next_power_of_two`, `next_multiple_of`, `overflowing_mul`, `mem::size_of`,
`from_le_bytes`, and `[u16]::get_unchecked` with `Range`/`RangeTo`/`RangeFrom`)
match pinned `core` semantics, fail closed on `next_power_of_two` overflow and
`next_multiple_of` divisor zero or overflow, and preserve 128-bit overflow
detection across `checked_add`, `saturating_add`, and `overflowing_mul`. -/
theorem canary_core_scalar_ops :
    let u128Ty := MirTy.int .i128 false
    let u128Max := ScalarVal.mk .i128 false
      (BitVec.ofNat 128 340282366920938463463374607431768211455)
    let u128One := ScalarVal.mk .i128 false (BitVec.ofNat 128 1)
    let u128Two64 := ScalarVal.mk .i128 false
      (BitVec.ofNat 128 18446744073709551616)
    let u16SliceMem := mkCanarySliceMemAligned 1 [10, 0, 20, 0, 30, 0]
    let u16Ty := MirTy.int .i16 false
    let u16SliceTy := MirTy.slice u16Ty
    execCoreCallWithMem MemoryState.empty (.numCountOnes .i8 true)
      [(.int .i8 true, .scalar ⟨.i8, true, BitVec.ofNat 128 0xff⟩)]
      canaryU32Ty =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 8⟩, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numTrailingZeros .i16 false)
      [(u16Ty, .scalar ⟨.i16, false, BitVec.ofNat 128 0⟩)]
      canaryU32Ty =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 16⟩, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numNextPowerOfTwo .i8 false)
      [(canaryU8Ty, canaryU8Val 0)] canaryU8Ty =
      .ok (canaryU8Val 1, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numNextPowerOfTwo .i8 false)
      [(canaryU8Ty, canaryU8Val 128)] canaryU8Ty =
      .ok (canaryU8Val 128, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numNextPowerOfTwo .i8 false)
      [(canaryU8Ty, canaryU8Val 129)] canaryU8Ty = .error corePanicTrap ∧
    execCoreCallWithMem MemoryState.empty (.numNextMultipleOf .i64 false)
      [(canaryU64Ty, canaryU64Val 23), (canaryU64Ty, canaryU64Val 8)]
      canaryU64Ty =
      .ok (canaryU64Val 24, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numNextMultipleOf .i8 false)
      [(canaryU8Ty, canaryU8Val 0), (canaryU8Ty, canaryU8Val 0)] canaryU8Ty =
      .error corePanicTrap ∧
    execCoreCallWithMem MemoryState.empty (.numNextMultipleOf .i8 false)
      [(canaryU8Ty, canaryU8Val 255), (canaryU8Ty, canaryU8Val 2)] canaryU8Ty =
      .error corePanicTrap ∧
    execCoreCallWithMem MemoryState.empty (.numOverflowingMul .i128 false)
      [(u128Ty, .scalar u128Two64), (u128Ty, .scalar u128Two64)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar ⟨.i128, false, 0⟩, .bool true],
        MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numSaturatingAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)]
      u128Ty =
      .ok (.scalar u128Max, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty
      (.memSizeOf (.option canaryU64Ty)) [] canaryUsizeTy =
      .ok (canaryUsizeVal 16, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty
      (.memSizeOf (.ref .shared (.slice canaryU8Ty))) [] canaryUsizeTy =
      .ok (canaryUsizeVal 16, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.intFromLeBytes .i16 false)
      [(.array canaryU8Ty 2, .array [canaryU8Val 0x34, canaryU8Val 0x12])]
      u16Ty =
      .ok (.scalar ⟨.i16, false, BitVec.ofNat 128 0x1234⟩,
        MemoryState.empty) ∧
    execCoreCallWithMem u16SliceMem .sliceGetUncheckedRange
      [(.ref .shared u16SliceTy, .slicePtr ⟨some 2, 0, .isize⟩ 3),
       (.range canaryUsizeTy, .range 1 3)]
      (.ref .shared u16SliceTy) =
      .ok (.slicePtr ⟨some 2, 2, .isize⟩ 2, u16SliceMem) ∧
    execCoreCallWithMem u16SliceMem .sliceGetUncheckedIndex
      [(.ref .shared u16SliceTy, .slicePtr ⟨some 2, 0, .isize⟩ 3),
       (canaryUsizeTy, canaryUsizeVal 2)]
      (.ref .shared u16Ty) =
      .ok (.ptr ⟨some 2, 4, .isize⟩, u16SliceMem) ∧
    execCoreCallWithMem MemoryState.empty (.numDivCeil .i64 false)
      [(canaryU64Ty, canaryU64Val 13), (canaryU64Ty, canaryU64Val 4)]
      canaryU64Ty =
      .ok (canaryU64Val 4, MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numDivCeil .i8 false)
      [(canaryU8Ty, canaryU8Val 5), (canaryU8Ty, canaryU8Val 0)] canaryU8Ty =
      .error corePanicTrap ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedShl .i8 false)
      [(canaryU8Ty, canaryU8Val 1), (canaryU32Ty, .scalar ⟨.i32, false, 7⟩)]
      (.option canaryU8Ty) =
      .ok (.optionVal (some (canaryU8Val 128)), MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedShl .i8 true)
      [(.int .i8 true, .scalar ⟨.i8, true, BitVec.ofNat 128 0xff⟩),
       (canaryU32Ty, .scalar ⟨.i32, false, 1⟩)]
      (.option (.int .i8 true)) =
      .ok (.optionVal (some (.scalar ⟨.i8, true, BitVec.ofNat 128 0xfe⟩)),
        MemoryState.empty) ∧
    execCoreCallWithMem MemoryState.empty (.numCheckedShl .i8 false)
      [(canaryU8Ty, canaryU8Val 1), (canaryU32Ty, .scalar ⟨.i32, false, 8⟩)]
      (.option canaryU8Ty) =
      .ok (.optionVal none, MemoryState.empty) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem nat_ble_refl (n : Nat) : Nat.ble n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

private theorem uint64_ofNat_toNat_of_lt {n : Nat} (h : n < UInt64.size) :
    (UInt64.ofNat n).toNat = n := by
  have h1 : (UInt64.ofNat n).toNat = n % UInt64.size := by
    rfl
  rw [h1]
  exact Nat.mod_eq_of_lt h

/-- General contract theorem for `slice::split_at_mut`
(`execSliceSplitAtOutcome` with `reqMut = .mut`): any successful split of a
preserves memory, enforces `mid ≤ len`, returns two `&mut` slices with matching
provenance `some aid` whose byte spans `[base, base + mid * size)` and
`[base + mid * size, base + len * size)` are strictly disjoint, satisfy
`spansPairwiseDisjoint`, and have union equal to the input span
`[base, base + len * size)`. -/
theorem execSliceSplitAtOutcome_mut_disjoint_and_union
    {m m' : MemoryState} {inMut : Mutability} {elem : MirTy}
    {p : PtrVal} {len : UInt64} {mid : Nat} {resVal : Val}
    {lay : LayoutData} {aid : AllocId}
    (hLay : layoutOfTyV2 elem = some lay)
    (hProv : p.allocId = some aid)
    (hAllocBound : ∀ a, findAllocation aid m.allocations = some a →
      a.bytes.length < UInt64.size)
    (hOk : execSliceSplitAtOutcome m .mut inMut elem p len mid =
      .ok resVal m') :
    m' = m ∧
    mid ≤ len.toNat ∧
    ∃ p' : PtrVal,
      p'.allocId = some aid ∧
      p'.offsetBytes.toNat = p.offsetBytes.toNat + mid * lay.size ∧
      resVal = .tuple [
        .slicePtr p (UInt64.ofNat mid),
        .slicePtr p' (UInt64.ofNat (len.toNat - mid))
      ] ∧
      spansPairwiseDisjoint
        (refAccessSpans
          (.tuple [.ref .mut (.slice elem), .ref .mut (.slice elem)])
          resVal) = true ∧
      (∀ off : Nat,
        ¬ ((p.offsetBytes.toNat ≤ off ∧
            off < p.offsetBytes.toNat + mid * lay.size) ∧
           (p'.offsetBytes.toNat ≤ off ∧
            off < p'.offsetBytes.toNat + (len.toNat - mid) * lay.size))) ∧
      (∀ off : Nat,
        ((p.offsetBytes.toNat ≤ off ∧
          off < p.offsetBytes.toNat + mid * lay.size) ∨
         (p'.offsetBytes.toNat ≤ off ∧
          off < p'.offsetBytes.toNat + (len.toNat - mid) * lay.size)) ↔
        (p.offsetBytes.toNat ≤ off ∧
          off < p.offsetBytes.toNat + len.toNat * lay.size)) := by
  unfold execSliceSplitAtOutcome at hOk
  cases hSized : !isSizedNoRefV2Ty elem with
  | true => rw [hSized] at hOk; cases hOk
  | false =>
    rw [hSized] at hOk
    dsimp only at hOk
    cases hMut : (Mutability.beq inMut .shared && Mutability.beq .mut .mut) with
    | true => rw [hMut] at hOk; cases hOk
    | false =>
      rw [hMut] at hOk
      cases hRef : refValidInMem m inMut (.slice elem) (.slicePtr p len) with
      | error k => rw [hRef] at hOk; cases hOk
      | ok u =>
        cases u
        rw [hRef] at hOk
        dsimp only at hOk
        cases hBle : Nat.ble mid len.toNat with
        | false =>
          rw [hBle] at hOk
          cases hOk
        | true =>
          rw [hBle] at hOk
          rw [hLay] at hOk
          dsimp only at hOk
          cases hAdd : ptrAddInMem m lay.size p mid with
          | error k => rw [hAdd] at hOk; cases hOk
          | ok p' =>
            rw [hAdd] at hOk
            dsimp only at hOk
            injection hOk with hRes hMem
            have hMidLe : mid ≤ len.toNat := Nat.le_of_ble_eq_true hBle
            have hMidLt : mid < UInt64.size :=
              Nat.lt_of_le_of_lt hMidLe len.toBitVec.isLt
            have hSubLt : len.toNat - mid < UInt64.size :=
              Nat.lt_of_le_of_lt (Nat.sub_le len.toNat mid) len.toBitVec.isLt
            unfold ptrAddInMem at hAdd
            dsimp only at hAdd
            cases hDelta : !Nat.blt (mid * lay.size) isizeMaxBytes with
            | true => rw [hDelta] at hAdd; cases hAdd
            | false =>
              rw [hDelta, hProv] at hAdd
              dsimp only [ite, instDecidableEqBool] at hAdd
              cases hFind : findAllocation aid m.allocations with
              | none => rw [hFind] at hAdd; cases hAdd
              | some a =>
                rw [hFind] at hAdd
                dsimp only at hAdd
                cases hLive : (!a.live ||
                    !Nat.ble (p.offsetBytes.toNat + mid * lay.size)
                      a.bytes.length) with
                | true => rw [hLive] at hAdd; cases hAdd
                | false =>
                  rw [hLive] at hAdd
                  injection hAdd with hP'
                  have hOffBle :
                      Nat.ble (p.offsetBytes.toNat + mid * lay.size)
                        a.bytes.length = true := by
                    cases h1 : a.live <;>
                      cases h2 : Nat.ble (p.offsetBytes.toNat + mid * lay.size)
                        a.bytes.length <;>
                      simp_all
                  have hOffLe :
                      p.offsetBytes.toNat + mid * lay.size ≤ a.bytes.length :=
                    Nat.le_of_ble_eq_true hOffBle
                  have hOffLt :
                      p.offsetBytes.toNat + mid * lay.size < UInt64.size :=
                    Nat.lt_of_le_of_lt hOffLe (hAllocBound a hFind)
                  have hP'Prov : p'.allocId = some aid := by
                    rw [← hP']
                  have hP'Off :
                      p'.offsetBytes.toNat =
                        p.offsetBytes.toNat + mid * lay.size := by
                    rw [← hP']
                    exact uint64_ofNat_toNat_of_lt hOffLt
                  have hTotalLen :
                      mid * lay.size + (len.toNat - mid) * lay.size =
                        len.toNat * lay.size := by
                    rw [← Nat.add_mul, Nat.add_sub_of_le hMidLe]
                  have hEndEq :
                      p'.offsetBytes.toNat + (len.toNat - mid) * lay.size =
                        p.offsetBytes.toNat + len.toNat * lay.size := by
                    rw [hP'Off, Nat.add_assoc, hTotalLen]
                  have hDisjBool :
                      spansPairwiseDisjoint
                        (refAccessSpans
                          (.tuple [.ref .mut (.slice elem),
                            .ref .mut (.slice elem)])
                          resVal) = true := by
                    rw [← hRes]
                    unfold refAccessSpans refAccessSpansList
                    unfold refAccessSpans refAccessSpansList
                    unfold refAccessSpans refAccessSpansList
                    rw [hLay, hProv, hP'Prov]
                    dsimp only [List.append]
                    unfold spansPairwiseDisjoint spanDisjointWith spanDisjoint
                    rw [uint64_ofNat_toNat_of_lt hMidLt, hP'Off]
                    cases hN1 : Nat.beq (mid * lay.size) 0 with
                    | true =>
                      simp [hN1, spanDisjointWith, spansPairwiseDisjoint]
                    | false =>
                      cases hN2 :
                          Nat.beq ((UInt64.ofNat (len.toNat - mid)).toNat *
                            lay.size) 0 with
                      | true =>
                        simp [hN1, hN2, spanDisjointWith, spansPairwiseDisjoint]
                      | false =>
                        simp [hN1, hN2, nat_ble_refl, spanDisjointWith,
                          spansPairwiseDisjoint]
                  refine ⟨hMem.symm, hMidLe, p', hP'Prov, hP'Off, hRes.symm,
                    hDisjBool, ?_, ?_⟩
                  · intro off hBoth
                    have hLt : off < p.offsetBytes.toNat + mid * lay.size :=
                      hBoth.1.2
                    have hGe : p.offsetBytes.toNat + mid * lay.size ≤ off := by
                      rw [← hP'Off]; exact hBoth.2.1
                    exact Nat.lt_irrefl off (Nat.lt_of_lt_of_le hLt hGe)
                  · intro off
                    constructor
                    · intro hOr
                      cases hOr with
                      | inl hL =>
                        have hMidMulLe :
                            mid * lay.size ≤ len.toNat * lay.size :=
                          Nat.mul_le_mul_right lay.size hMidLe
                        exact ⟨hL.1, Nat.lt_of_lt_of_le hL.2
                          (Nat.add_le_add_left hMidMulLe p.offsetBytes.toNat)⟩
                      | inr hR =>
                        have hBaseLe :
                            p.offsetBytes.toNat ≤ p'.offsetBytes.toNat := by
                          rw [hP'Off]
                          exact Nat.le_add_right _ _
                        rw [hEndEq] at hR
                        exact ⟨Nat.le_trans hBaseLe hR.1, hR.2⟩
                    · intro hIn
                      cases Nat.lt_or_ge off
                          (p.offsetBytes.toNat + mid * lay.size) with
                      | inl hLt => exact Or.inl ⟨hIn.1, hLt⟩
                      | inr hGe =>
                        refine Or.inr ⟨?_, ?_⟩
                        · rw [hP'Off]; exact hGe
                        · rw [hEndEq]; exact hIn.2

/-- Canary 15: `evalTerminatorV2` on `.coreCall (.sliceSplitAt .mut ...)`
aborts with post-mutation caller memory on `mid > len` under `--panic abort`
without a crate-local `#[panic_handler]`, stays `.fault .unsupported` under
`--panic unwind`, crate-local `#[panic_handler]`, or `.cleanup` unwind, and
produces disjoint `&mut` subslices whose union is the input span when
`mid ≤ len`. -/
theorem canary_split_at_mut_disjoint_union_and_panic_abort :
    let mutSliceTy : MirTy := .ref .mut (.slice canaryU8Ty)
    let retPairTy : MirTy := .tuple [mutSliceTy, mutSliceTy]
    let splitBb (uw : UnwindAction) : BasicBlock := {
      statements := []
      terminator := .coreCall (.sliceSplitAt .mut canaryU8Ty)
        [.copy { localId := 1 }, .copy { localId := 2 }]
        { localId := 0 } (some 1) uw
    }
    let splitBody (uw : UnwindAction) : Body := {
      argumentCount := 2
      locals := [retPairTy, mutSliceTy, canaryUsizeTy]
      basicBlocks := [splitBb uw, { statements := [], terminator := .return_ }]
    }
    let mMut : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 10 none, .init 20 none, .init 30 none],
        live := true
      }]
    }
    let cmMut : CallerMemory := ⟨mMut.allocations⟩
    let mkFrame (mid : Nat) : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [
        .immediate none,
        .immediate (some (.slicePtr ⟨some 2, 0, .isize⟩ 3)),
        .immediate (some (canaryUsizeVal mid))
      ]
    }
    evalTerminatorV2 (splitBody .unreachable) (splitBb .unreachable)
      (mkFrame 4) mMut cmMut .abort false false =
      .done (.aborted cmMut) ∧
    evalTerminatorV2 (splitBody .unreachable) (splitBb .unreachable)
      (mkFrame 4) mMut cmMut .unwind false false =
      .fault .unsupported ∧
    evalTerminatorV2 (splitBody .unreachable) (splitBb .unreachable)
      (mkFrame 4) mMut cmMut .abort true false =
      .fault .unsupported ∧
    evalTerminatorV2 (splitBody (.cleanup 1)) (splitBb (.cleanup 1))
      (mkFrame 4) mMut cmMut .abort false false =
      .fault .unsupported ∧
    execSliceSplitAtOutcome mMut .mut .mut canaryU8Ty
      ⟨some 2, 0, .isize⟩ 3 1 =
      .ok (.tuple [
        .slicePtr ⟨some 2, 0, .isize⟩ 1,
        .slicePtr ⟨some 2, 1, .isize⟩ 2
      ]) mMut ∧
    spansPairwiseDisjoint (refAccessSpans retPairTy
      (.tuple [
        .slicePtr ⟨some 2, 0, .isize⟩ 1,
        .slicePtr ⟨some 2, 1, .isize⟩ 2
      ])) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Core

end
