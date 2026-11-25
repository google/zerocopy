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
public import Anneal.PureLift.SpatialMem.MirMemMirror
public import Anneal.PureLift.SpatialMem.Soundness

public section

/-!
# Computable MIR Memory Mirrors (`Anneal.MirMemComp.Memory`)

Thin re-export and framing layer over the computable
`Trusted.MirSemantics.Memory` mirrors in
`Anneal.PureLift.SpatialMem.{MirMemMirror, Soundness}` (`execMemoryEmpty`,
`execFindAllocation`, `execReplaceAllocation`, `execReserveAllocId`,
`execAllocateStack`, `execDeallocateStack`, `execIsInBounds`, `execIsAligned`,
`execReadBytes`, `execWriteBytes`, `execWriteUninit`, and `memAllocIdsLt`).

Re-exports all shared computable definitions and public equational bridges via
`export Anneal.PureLift (...)` so opening both `Anneal.PureLift` and
`Anneal.MirMemComp` resolves every shared name to the same kernel constant
without ambiguity, and proves the remaining `rfl` bridges plus universal
cross-allocation stack framing and post-deallocation fault laws.

All declarations authored in this module compile with zero axioms (`[]`).
-/

namespace Anneal.MirMemComp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Re-exported Computable Mirrors and Bridges from `Anneal.PureLift` -/

export Anneal.PureLift (
  execMemoryEmpty
  execFindAllocation
  execReplaceAllocation
  execReserveAllocId
  execAllocateStack
  execDeallocateStack
  execIsInBounds
  execIsAligned
  execReadBytes
  execWriteBytes
  execWriteUninit
  memAllocIdsLt
  execFindAllocation_eq
  execReplaceAllocation_eq
  execAllocateStack_eq
  execDeallocateStack_eq
  execReadBytes_eq
  execWriteBytes_eq
  execWriteUninit_eq
)

/-! ## Additional `rfl` Bridges Against `Trusted.MirSemantics` -/

/-- `execMemoryEmpty` equals `Trusted.MirSemantics.MemoryState.empty`. -/
theorem execMemoryEmpty_eq : execMemoryEmpty = MemoryState.empty := rfl

/-- `execReserveAllocId` equals `MemoryState.reserveAllocId`. -/
theorem execReserveAllocId_eq (m : MemoryState) :
    execReserveAllocId m = MemoryState.reserveAllocId m := rfl

/-- `execIsInBounds` equals `Trusted.MirSemantics.isInBounds` (`[]` zero
axioms). -/
theorem execIsInBounds_eq (a : Allocation) (offset size : Nat) :
    execIsInBounds a offset size = isInBounds a offset size := rfl

/-- `execIsAligned` equals `Trusted.MirSemantics.isAligned` (`[]` zero axioms).
-/
theorem execIsAligned_eq (a : Allocation) (offset alignLog2 : Nat) :
    execIsAligned a offset alignLog2 = isAligned a offset alignLog2 := rfl

/-! ## Universal Allocation-ID Bound & Cross-Allocation Framing Laws -/

private theorem natBeq_false_of_ne (a b : Nat) (hNe : a ≠ b) :
    Nat.beq a b = false := by
  cases h : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (hNe (Anneal.PureLift.natEq_of_beq a b h))

private theorem listAppend_nil_left {α : Type} (xs : List α) : [] ++ xs = xs :=
  rfl

private theorem listAppend_cons {α : Type} (x : α) (xs ys : List α) :
    (x :: xs) ++ ys = x :: (xs ++ ys) :=
  rfl

private theorem execFindAllocation_cons (id : AllocId) (a : Allocation)
    (rest : List Allocation) :
    execFindAllocation id (a :: rest) =
      if Nat.beq a.allocId id then some a
      else execFindAllocation id rest := rfl

private theorem execReplaceAllocation_cons_false (a' a : Allocation)
    (rest : List Allocation) (hFalse : Nat.beq a.allocId a'.allocId = false) :
    execReplaceAllocation a' (a :: rest) =
      a :: execReplaceAllocation a' rest := by
  dsimp only [execReplaceAllocation, List.foldr]
  rw [Anneal.PureLift.ite_bool_false hFalse]

private theorem execReplaceAllocation_pair_snd (a' : Allocation)
    (allocs : List Allocation) :
    (allocs.foldr
      (fun a (tailPair : List Allocation × List Allocation) =>
        if Nat.beq a.allocId a'.allocId then
          (a' :: tailPair.2, a :: tailPair.2)
        else
          (a :: tailPair.1, a :: tailPair.2))
      ([], [])).2 = allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [List.foldr]
    cases Nat.beq a.allocId a'.allocId with
    | true =>
      rw [Anneal.PureLift.ite_bool_true rfl]
      exact congrArg (List.cons a) ih
    | false =>
      rw [Anneal.PureLift.ite_bool_false rfl]
      exact congrArg (List.cons a) ih

/-- Looking up a fresh allocation appended after `allocs` returns
`some newAlloc` whenever `memAllocIdsLt allocs newAlloc.allocId = true`. -/
theorem execFindAllocation_append_lt (allocs : List Allocation)
    (newAlloc : Allocation)
    (hLt : memAllocIdsLt allocs newAlloc.allocId = true) :
    execFindAllocation newAlloc.allocId (allocs ++ [newAlloc]) =
      some newAlloc := by
  induction allocs with
  | nil =>
    rw [listAppend_nil_left, execFindAllocation_cons,
      Anneal.PureLift.ite_bool_true (Anneal.PureLift.natBeq_refl
        newAlloc.allocId)]
  | cons a rest ih =>
    dsimp only [memAllocIdsLt, List.foldr] at hLt
    cases hBlt : Nat.blt a.allocId newAlloc.allocId with
    | false =>
      rw [hBlt] at hLt
      exact False.elim (Anneal.PureLift.boolFalseNeTrue hLt)
    | true =>
      rw [hBlt, Bool.true_and] at hLt
      have hNe : a.allocId ≠ newAlloc.allocId := fun hEq => by
        have hALt := Anneal.PureLift.natLt_of_blt a.allocId newAlloc.allocId
          hBlt
        rw [hEq] at hALt
        exact Nat.lt_irrefl newAlloc.allocId hALt
      have hBeqFalse := natBeq_false_of_ne a.allocId newAlloc.allocId hNe
      rw [listAppend_cons, execFindAllocation_cons,
        Anneal.PureLift.ite_bool_false hBeqFalse, ih hLt]

/-- Appending an allocation with a distinct `allocId` preserves lookup of every
other `id`. -/
theorem execFindAllocation_append_ne (allocs : List Allocation)
    (newAlloc : Allocation) (id : AllocId) (hNe : id ≠ newAlloc.allocId) :
    execFindAllocation id (allocs ++ [newAlloc]) =
      execFindAllocation id allocs := by
  induction allocs with
  | nil =>
    have hBeqFalse :=
      natBeq_false_of_ne newAlloc.allocId id (fun hEq => hNe hEq.symm)
    rw [listAppend_nil_left, execFindAllocation_cons,
      Anneal.PureLift.ite_bool_false hBeqFalse]
  | cons a rest ih =>
    rw [listAppend_cons, execFindAllocation_cons, execFindAllocation_cons, ih]

/-- Replacing a fresh trailing allocation preserves all earlier entries in
`allocs`. -/
theorem execReplaceAllocation_append_lt (allocs : List Allocation)
    (oldNew newNew : Allocation)
    (hLt : memAllocIdsLt allocs oldNew.allocId = true)
    (hSameId : newNew.allocId = oldNew.allocId) :
    execReplaceAllocation newNew (allocs ++ [oldNew]) = allocs ++ [newNew] := by
  induction allocs with
  | nil =>
    rw [listAppend_nil_left]
    dsimp only [execReplaceAllocation, List.foldr]
    rw [hSameId,
      Anneal.PureLift.ite_bool_true (Anneal.PureLift.natBeq_refl
        oldNew.allocId)]
    rfl
  | cons a rest ih =>
    dsimp only [memAllocIdsLt, List.foldr] at hLt
    cases hBlt : Nat.blt a.allocId oldNew.allocId with
    | false =>
      rw [hBlt] at hLt
      exact False.elim (Anneal.PureLift.boolFalseNeTrue hLt)
    | true =>
      rw [hBlt, Bool.true_and] at hLt
      have hNe : a.allocId ≠ newNew.allocId := fun hEq => by
        have hALt := Anneal.PureLift.natLt_of_blt a.allocId oldNew.allocId hBlt
        rw [hSameId] at hEq
        rw [hEq] at hALt
        exact Nat.lt_irrefl oldNew.allocId hALt
      have hBeqFalse := natBeq_false_of_ne a.allocId newNew.allocId hNe
      rw [listAppend_cons,
        execReplaceAllocation_cons_false newNew a (rest ++ [oldNew]) hBeqFalse,
        ih hLt]
      rfl

/-- Allocating a fresh stack slot preserves `readBytes` on every pre-existing
allocation whose `allocId ≠ m.nextAllocId`. -/
theorem execAllocateStack_readBytes_other (m : MemoryState)
    (layout : LayoutData) (otherPlace : MemPlace) (size alignLog2 : Nat)
    (hNe : otherPlace.allocId ≠ m.nextAllocId) :
    execReadBytes (execAllocateStack m layout).1 otherPlace size alignLog2 =
      execReadBytes m otherPlace size alignLog2 := by
  unfold execReadBytes execAllocateStack execReserveAllocId
  dsimp only
  rw [execFindAllocation_append_ne m.allocations _ otherPlace.allocId hNe]

/-- Replacing a single allocation preserves `execFindAllocation` (and hence
`readBytes`) on every allocation with a different `allocId`. -/
theorem execFindAllocation_replaceAllocation_ne (allocs : List Allocation)
    (a' : Allocation) (id : AllocId) (hNe : id ≠ a'.allocId) :
    execFindAllocation id (execReplaceAllocation a' allocs) =
      execFindAllocation id allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [execReplaceAllocation, List.foldr]
    cases hMatch : Nat.beq a.allocId a'.allocId with
    | true =>
      rw [Anneal.PureLift.ite_bool_true rfl]
      dsimp only
      rw [execReplaceAllocation_pair_snd a' rest]
      have hIdEq : a.allocId = a'.allocId :=
        Anneal.PureLift.natEq_of_beq a.allocId a'.allocId hMatch
      have hF1 : Nat.beq a'.allocId id = false :=
        natBeq_false_of_ne a'.allocId id (fun h => hNe h.symm)
      have hF2 : Nat.beq a.allocId id = false := by
        rw [hIdEq]; exact hF1
      rw [execFindAllocation_cons, execFindAllocation_cons,
        Anneal.PureLift.ite_bool_false hF1,
        Anneal.PureLift.ite_bool_false hF2]
    | false =>
      rw [Anneal.PureLift.ite_bool_false rfl]
      dsimp only
      rw [execFindAllocation_cons, execFindAllocation_cons]
      change
        (if Nat.beq a.allocId id then some a
         else execFindAllocation id (execReplaceAllocation a' rest)) =
        (if Nat.beq a.allocId id then some a else execFindAllocation id rest)
      rw [ih]

/-- After `execDeallocateStack` marks a fresh trailing stack allocation dead
(`live = false`), any subsequent positive-size `readBytes`, positive-size
`writeBytes`, or second `deallocateStack` on that allocation fails closed with
`.error .undefined`. -/
theorem execDeallocateStack_dead_faults (m : MemoryState)
    (a : Allocation) (offset size alignLog2 : Nat)
    (bytes : List AllocByte)
    (hLt : memAllocIdsLt m.allocations a.allocId = true)
    (hLive : a.live = true) (hMut : a.mutability = .mut)
    (hSizePos : Nat.beq size 0 = false)
    (hBytesPos : Nat.beq bytes.length 0 = false) :
    let mBefore : MemoryState := { m with allocations := m.allocations ++ [a] }
    let mDead : MemoryState :=
      { m with allocations := m.allocations ++ [{ a with live := false }] }
    execDeallocateStack mBefore ⟨a.allocId, 0⟩ = .ok mDead ∧
    execReadBytes mDead ⟨a.allocId, offset⟩ size alignLog2 = .error .undefined ∧
    execWriteBytes mDead ⟨a.allocId, offset⟩ alignLog2 bytes =
      .error .undefined ∧
    execDeallocateStack mDead ⟨a.allocId, 0⟩ = .error .undefined := by
  have hFindLive :
      execFindAllocation a.allocId (m.allocations ++ [a]) = some a :=
    execFindAllocation_append_lt m.allocations a hLt
  have hFindDead :
      execFindAllocation a.allocId
        (m.allocations ++ [{ a with live := false }]) =
        some { a with live := false } :=
    execFindAllocation_append_lt m.allocations { a with live := false } hLt
  have hRepDead :
      execReplaceAllocation { a with live := false } (m.allocations ++ [a]) =
        m.allocations ++ [{ a with live := false }] :=
    execReplaceAllocation_append_lt m.allocations a { a with live := false }
      hLt rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold execDeallocateStack
    dsimp only
    rw [hFindLive]
    dsimp only
    rw [hLive, hMut]
    rw [hMut] at hRepDead
    dsimp only
    rw [hRepDead]
    rfl
  · unfold execReadBytes
    dsimp only
    rw [hFindDead]
    dsimp only
    rw [hSizePos, Anneal.PureLift.ite_bool_false rfl]
    rfl
  · unfold execWriteBytes
    dsimp only
    rw [hFindDead]
    dsimp only
    rw [hBytesPos, Anneal.PureLift.ite_bool_false rfl]
    rfl
  · unfold execDeallocateStack
    dsimp only
    rw [hFindDead]
    rfl

end Anneal.MirMemComp

end
