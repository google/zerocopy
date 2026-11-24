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
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirTotal.Ops
public import Anneal.ByteSubLens.Lens
public import Anneal.ByteRun.Copy

public section

namespace Anneal.RefFrame

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal
open Anneal.ByteSubLens Anneal.ByteRun

/-!
# 4-Way Call-Continuation `&mut` Writeback Frames (`Anneal.RefFrame.Frame`)

Provides an LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`, `0`
`omega`) `&mut` borrow writeback frame algebra directly over
`Trusted.MirAst.{TerminatorKind, UnwindAction}`, `Trusted.MirSemantics`,
`Anneal.ByteSubLens`, and `Anneal.ByteRun` (all authored declarations compile
with zero axioms `[]`; Lean-synthesized `.injEq` helpers use `propext`):

1. **`CallCont4` & `callCont4OfTerminator?`:** Extracts the `(onRet, onUnwind)`
   call-continuation descriptor from `Trusted.MirAst.TerminatorKind`.
2. **`RefFrame` & `evalRefFrameExit`:** Commits mixed-mask `AllocByte` slices
   into a caller `ByteSubLens` across all 8 `(Option BasicBlockId ×
   UnwindAction)` continuation regimes, overwriting prior pointer provenance
   without a prior-provenance-absence side condition and preserving `.uninit`
   padding runs.
3. **`refFrame_callCont4_matrix_sound` (`[]` zero axioms):** Proves `writeBytes`
   / `readBytes` / `byteSubLensGet` agreement, symmetric disjoint `ByteSubLens`
   framing, and all 16 `(onRet, onUnwind)` × `(returned, unwound)` outcome
   equations.
-/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_of_eq (a b : Nat) (h : a = b) : Nat.beq a b = true := by
  subst h
  exact natBeq_refl a

private theorem natBeq_zero_false_of_blt_zero (n : Nat)
    (h : Nat.blt 0 n = true) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (boolFalseNeTrue h)
  | succ _ => rfl

/-- 4-way call-terminator continuation descriptor `(onRet, onUnwind)` matching
`Trusted.MirAst.TerminatorKind.call callee args dst onRet onUnwind`. -/
structure CallCont4 where
  /-- Normal-return target block (`none` for diverging `-> !` calls). -/
  onRet : Option BasicBlockId
  /-- Unwind continuation action (`.continue_`, `.unreachable`, `.terminate`,
  or `.cleanup bb`). -/
  onUnwind : UnwindAction

/-- Extracts `CallCont4` from a `Trusted.MirAst.TerminatorKind`. -/
@[expose] def callCont4OfTerminator? (term : TerminatorKind) : Option CallCont4
    :=
  match term with
  | .call _ _ _ onRet onUnwind => some ⟨onRet, onUnwind⟩
  | .goto _ => none
  | .switchInt _ _ => none
  | .return_ => none
  | .unreachable => none
  | .unwindResume => none
  | .assert _ _ _ _ _ => none
  | .unsupported => none

/-- Callee exit payload carrying either a normal return `(retVal, mutSlice)` or
an unwind carrying the pre-panic partial `&mut` referent slice
`partialMutSlice`. -/
inductive CalleeExit where
  | returned (retVal : Val) (mutSlice : List AllocByte)
  | unwound (partialMutSlice : List AllocByte)

/-- Caller frame transition across all `(onRet, onUnwind)` call regimes:
- `.jumpNormal targetBb retVal mem`: commits `&mut` slice, yields `retVal`, and
  branches to `targetBb`;
- `.jumpCleanup cleanupBb mem`: writes back partial `&mut` slice without
  assuming the normal return postcondition and branches to `cleanupBb`;
- `.propagateUnwind callerMem mem`: writes back partial `&mut` slice into
  caller-visible memory and propagates frame unwind;
- `.abortTerminate mem`: writes back partial `&mut` slice at an
  `UnwindAction.terminate` abort boundary;
- `.fault kind`: operational fault (conservatively `.undefined` when returning
  into `onRet = none`, unwinding into `onUnwind = .unreachable`, or failing
  `byteSubLensPut`, including zero-sized or length-mismatched slices). -/
inductive CallerContOutcome where
  | jumpNormal (targetBb : BasicBlockId) (retVal : Val) (mem : MemoryState)
  | jumpCleanup (cleanupBb : BasicBlockId) (mem : MemoryState)
  | propagateUnwind (callerMem : CallerMemory) (mem : MemoryState)
  | abortTerminate (mem : MemoryState)
  | fault (kind : FaultKind)

/-- `&mut` borrow writeback frame pairing a `ByteSubLens` with a `CallCont4`
continuation descriptor. -/
structure RefFrame where
  /-- Sub-allocation byte lens for the borrowed `&mut` referent. -/
  refLens : ByteSubLens
  /-- Caller `(onRet, onUnwind)` continuation descriptor. -/
  cont : CallCont4

/-- Computable `RefFrame` exit transition (`0` `noncomputable`), writing back
mixed-mask `AllocByte` slices (overwriting any prior pointer provenance inside
`refLens` and preserving `.uninit` padding runs). -/
@[expose] def evalRefFrameExit (rf : RefFrame) (mem : MemoryState) (exit :
    CalleeExit) :
    CallerContOutcome :=
  match exit with
  | .returned retVal mutSlice =>
    match rf.cont.onRet with
    | none => .fault .undefined
    | some retBb =>
      match byteSubLensPut rf.refLens mem mutSlice with
      | none => .fault .undefined
      | some mem' => .jumpNormal retBb retVal mem'
  | .unwound partialMutSlice =>
    match rf.cont.onUnwind with
    | .unreachable => .fault .undefined
    | .cleanup cleanupBb =>
      match byteSubLensPut rf.refLens mem partialMutSlice with
      | none => .fault .undefined
      | some mem' => .jumpCleanup cleanupBb mem'
    | .continue_ =>
      match byteSubLensPut rf.refLens mem partialMutSlice with
      | none => .fault .undefined
      | some mem' => .propagateUnwind ⟨mem'.allocations⟩ mem'
    | .terminate =>
      match byteSubLensPut rf.refLens mem partialMutSlice with
      | none => .fault .undefined
      | some mem' => .abortTerminate mem'

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
  rw [natBeq_zero_false_of_blt_zero bs.length hPos, ite_bool_false rfl, hFind]
  dsimp only
  have hGuard :
      (!a.live || !isInBounds a place.offset bs.length ||
        !isAligned a place.offset alignLog2) = false := by
    rw [hLive, hBounds, hAlign]
    rfl
  rw [ite_bool_false hGuard, hMut, hLive]

/-- Total existence, `Trusted.MirSemantics.{writeBytes, readBytes}` agreement,
`byteSubLensGet` round-trip, and disjoint-lens framing for `byteSubLensPut` on a
valid mutable live allocation (`[]` zero axioms). -/
theorem byteSubLensPut_eq_some_of_valid (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) (a : Allocation)
    (hPos : Nat.blt 0 L.size = true)
    (hLen : bs.length = L.size)
    (hFind : findAllocation L.allocId m.allocations = some a)
    (hMut : a.mutability = .mut)
    (hLive : a.live = true)
    (hBounds : isInBounds a L.offset L.size = true)
    (hAlign : isAligned a L.offset L.alignLog2 = true) :
    ∃ m' : MemoryState,
      byteSubLensPut L m bs = some m' ∧
      writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2 bs = .ok m' ∧
      readBytes m' ⟨L.allocId, L.offset⟩ L.size L.alignLog2 = .ok bs ∧
      byteSubLensGet L m' = some bs ∧
      (∀ (otherL : ByteSubLens),
        byteLensDisjoint L otherL = true →
        byteSubLensGet otherL m' = byteSubLensGet otherL m ∧
        readBytes m' ⟨otherL.allocId, otherL.offset⟩ otherL.size
            otherL.alignLog2 =
          readBytes m ⟨otherL.allocId, otherL.offset⟩ otherL.size
            otherL.alignLog2) := by
  have hBsPos : Nat.blt 0 bs.length = true := by
    rw [hLen]
    exact hPos
  have hBsBounds : isInBounds a L.offset bs.length = true := by
    dsimp only [isInBounds]
    rw [hLen]
    exact hBounds
  let m' := MemoryState.mk m.nextAllocId
    (replaceAllocation
      (Allocation.mk a.allocId a.alignLog2 .mut
        (a.bytes.take L.offset ++ bs ++ a.bytes.drop (L.offset + bs.length))
        true)
      m.allocations)
  have hWrite : writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2 bs = .ok m' :=
    writeBytes_ok_of_valid m ⟨L.allocId, L.offset⟩ L.alignLog2 bs a
      hBsPos hFind hMut hLive hBsBounds hAlign
  have hPut : byteSubLensPut L m bs = some m' := by
    rw [byteSubLensPut_eq_mir, hPos, natBeq_of_eq bs.length L.size hLen]
    dsimp only [Bool.and]
    rw [hWrite]
  have hRead : readBytes m' ⟨L.allocId, L.offset⟩ L.size L.alignLog2 = .ok bs :=
    by
    rw [← hLen]
    exact readBytes_after_writeBytes_same m m' ⟨L.allocId, L.offset⟩
      L.alignLog2 bs hBsPos hWrite
  have hGet' : byteSubLensGet L m' = some bs :=
    (byteSubLens_lawful L).put_get m m' bs hPut
  refine ⟨m', hPut, hWrite, hRead, hGet', ?_⟩
  intro otherL hDisj
  have hDisjBs :
      (!Nat.beq L.allocId otherL.allocId ||
        Anneal.ByteRun.rangesDisjoint L.offset bs.length otherL.offset
          otherL.size) = true := by
    rw [hLen]
    exact hDisj
  exact ⟨(byteSubLens_lawful L).get_put_disjoint otherL m m' bs hDisj hPut,
    readBytes_after_writeBytes_disjoint m m' ⟨L.allocId, L.offset⟩
      ⟨otherL.allocId, otherL.offset⟩ L.alignLog2 otherL.size otherL.alignLog2
      bs hBsPos hDisjBs hWrite⟩

/-- Complete 8-regime `(Option BasicBlockId × UnwindAction)` `RefFrame`
continuation matrix (`[]` zero axioms) characterizing `evalRefFrameExit` and
its agreement with `Trusted.MirSemantics.{writeBytes, readBytes}` under the
eight validity hypotheses for `MemoryState` `m`, `ByteSubLens` `L` (overwriting
prior pointer provenance inside `L`), and mixed-mask `normalRuns` /
`partialRuns`. -/
theorem refFrame_callCont4_matrix_sound
    (L : ByteSubLens) (m : MemoryState) (a : Allocation)
    (retBb cleanupBb : BasicBlockId) (retVal : Val)
    (normalRuns partialRuns : List ByteRun)
    (hPos : Nat.blt 0 L.size = true)
    (hNormLen : runsByteLen normalRuns = L.size)
    (hPartLen : runsByteLen partialRuns = L.size)
    (hFind : findAllocation L.allocId m.allocations = some a)
    (hMut : a.mutability = .mut)
    (hLive : a.live = true)
    (hBounds : isInBounds a L.offset L.size = true)
    (hAlign : isAligned a L.offset L.alignLog2 = true) :
    ∃ (mNorm mUnw : MemoryState),
      writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2
        (flattenByteRuns normalRuns) = .ok mNorm ∧
      readBytes mNorm ⟨L.allocId, L.offset⟩ L.size L.alignLog2 =
        .ok (flattenByteRuns normalRuns) ∧
      byteSubLensGet L mNorm = some (flattenByteRuns normalRuns) ∧
      writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2
        (flattenByteRuns partialRuns) = .ok mUnw ∧
      readBytes mUnw ⟨L.allocId, L.offset⟩ L.size L.alignLog2 =
        .ok (flattenByteRuns partialRuns) ∧
      byteSubLensGet L mUnw = some (flattenByteRuns partialRuns) ∧
      (∀ otherL : ByteSubLens, byteLensDisjoint L otherL = true →
        byteSubLensGet otherL mNorm = byteSubLensGet otherL m ∧
        byteSubLensGet otherL mUnw = byteSubLensGet otherL m ∧
        readBytes mNorm ⟨otherL.allocId, otherL.offset⟩ otherL.size
            otherL.alignLog2 =
          readBytes m ⟨otherL.allocId, otherL.offset⟩ otherL.size
            otherL.alignLog2 ∧
        readBytes mUnw ⟨otherL.allocId, otherL.offset⟩ otherL.size
            otherL.alignLog2 =
          readBytes m ⟨otherL.allocId, otherL.offset⟩ otherL.size
            otherL.alignLog2) ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .cleanup cleanupBb⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .cleanup cleanupBb⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) =
        .jumpCleanup cleanupBb mUnw ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .continue_⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .continue_⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) =
        .propagateUnwind ⟨mUnw.allocations⟩ mUnw ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .unreachable⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .unreachable⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) = .fault .undefined ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .terminate⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .terminate⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) = .abortTerminate mUnw ∧
      evalRefFrameExit ⟨L, ⟨none, .cleanup cleanupBb⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) = .fault .undefined ∧
      evalRefFrameExit ⟨L, ⟨none, .cleanup cleanupBb⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) =
        .jumpCleanup cleanupBb mUnw ∧
      evalRefFrameExit ⟨L, ⟨none, .continue_⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) = .fault .undefined ∧
      evalRefFrameExit ⟨L, ⟨none, .continue_⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) =
        .propagateUnwind ⟨mUnw.allocations⟩ mUnw ∧
      evalRefFrameExit ⟨L, ⟨none, .unreachable⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) = .fault .undefined ∧
      evalRefFrameExit ⟨L, ⟨none, .unreachable⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) = .fault .undefined ∧
      evalRefFrameExit ⟨L, ⟨none, .terminate⟩⟩ m
        (.returned retVal (flattenByteRuns normalRuns)) = .fault .undefined ∧
      evalRefFrameExit ⟨L, ⟨none, .terminate⟩⟩ m
        (.unwound (flattenByteRuns partialRuns)) = .abortTerminate mUnw := by
  cases byteSubLensPut_eq_some_of_valid L m (flattenByteRuns normalRuns) a
      hPos hNormLen hFind hMut hLive hBounds hAlign with
  | intro mNorm hN =>
    cases byteSubLensPut_eq_some_of_valid L m (flattenByteRuns partialRuns) a
        hPos hPartLen hFind hMut hLive hBounds hAlign with
    | intro mUnw hU =>
      have hPutN := hN.1
      have hWriteN := hN.2.1
      have hReadN := hN.2.2.1
      have hGetN := hN.2.2.2.1
      have hFrameN := hN.2.2.2.2
      have hPutU := hU.1
      have hWriteU := hU.2.1
      have hReadU := hU.2.2.1
      have hGetU := hU.2.2.2.1
      have hFrameU := hU.2.2.2.2
      refine ⟨mNorm, mUnw, hWriteN, hReadN, hGetN,
        hWriteU, hReadU, hGetU, ?_,
        ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_,
        rfl, ?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
      · intro otherL hDisj
        have hFN := hFrameN otherL hDisj
        have hFU := hFrameU otherL hDisj
        exact ⟨hFN.1, hFU.1, hFN.2, hFU.2⟩
      · unfold evalRefFrameExit; dsimp only; rw [hPutN]
      · unfold evalRefFrameExit; dsimp only; rw [hPutU]
      · unfold evalRefFrameExit; dsimp only; rw [hPutN]
      · unfold evalRefFrameExit; dsimp only; rw [hPutU]
      · unfold evalRefFrameExit; dsimp only; rw [hPutN]
      · unfold evalRefFrameExit; dsimp only; rw [hPutN]
      · unfold evalRefFrameExit; dsimp only; rw [hPutU]
      · unfold evalRefFrameExit; dsimp only; rw [hPutU]
      · unfold evalRefFrameExit; dsimp only; rw [hPutU]
      · unfold evalRefFrameExit; dsimp only; rw [hPutU]

end Anneal.RefFrame

end
