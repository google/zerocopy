-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemAlloc
import Anneal.MirCorrespondence.ValidateLocal

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-! ## Section 5: Return-Place Memory Write, Validation, and `copyReturn` -/

def retAllocId : Miri.Memory.AllocId := ⟨1, by decide⟩

def retPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
  ⟨Size.ZERO, some (.concrete retAllocId Miri.Memory.BorTag.one)⟩

def retMemPlace : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨retPtr, .none, none⟩

theorem singleton_live_find
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit) :
    ((Array.mk [(retAllocId, entry)])).find? (fun row => row.1 == retAllocId) =
      some (retAllocId, entry) := rfl

theorem singleton_live_filter_push
    (entry1 entry2 : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit) :
    (((Array.mk [(retAllocId, entry1)])).filter (fun row => row.1 != retAllocId)).push
        (retAllocId, entry2) =
      (Array.mk [(retAllocId, entry2)]) := rfl

theorem singleton_setLiveAllocation
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc1 alloc2 : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree) :
    ({ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc1⟩)]) } :
        Miri.Memory.MemoryState Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree Unit).setLiveAllocation
        retAllocId alloc2 =
      .ok { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc2⟩)]) } := by
  rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ retAllocId
    ⟨.stack, alloc1⟩ alloc2 (singleton_live_find _)]
  rw [singleton_live_filter_push]

theorem sizeAsI64_toMiriSize (w : IntWidth) :
    Miri.Memory.sizeAsI64 (toMiriSize w) = .ok (toMiriSize w).bytes.toNat := by
  cases w <;> rfl

private theorem toMiriSize_ne_zero (w : IntWidth) :
    ((toMiriSize w).bytes.toNat : Int) ≠ 0 := by
  cases w <;> decide

theorem int_pow_eq_ofNat (b : Nat) :
    ∀ n : Nat, HPow.hPow (Int.ofNat b) n = Int.ofNat (HPow.hPow b n)
  | 0 => rfl
  | n + 1 => by
    rw [Int.pow_succ, int_pow_eq_ofNat b n, Nat.pow_succ]
    rfl

private theorem fitsI64_of_le16 (n : Nat) (hn : n ≤ 16) :
    ((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤ Int.ofNat n) &&
      (Int.ofNat n < HPow.hPow (2 : Int) (63 : Nat))) = true := by
  have h_pow : HPow.hPow (2 : Int) (63 : Nat) = Int.ofNat (HPow.hPow 2 63) :=
    int_pow_eq_ofNat 2 63
  have h_val : HPow.hPow (2 : Nat) 63 = 9223372036854775808 := by decide
  rw [h_pow, h_val]
  have h1 : Neg.neg (Int.ofNat 9223372036854775808) ≤ Int.ofNat n :=
    Int.le_trans (by decide) (Int.natCast_nonneg n)
  have h2 : Int.ofNat n < Int.ofNat 9223372036854775808 :=
    Int.ofNat_lt.mpr (Nat.lt_of_le_of_lt hn (by decide))
  rw [decide_eq_true h1, decide_eq_true h2]
  rfl

private theorem checkedBounds_retPlace (w : IntWidth) :
    Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId (toMiriSize w)
        Size.ZERO (toMiriSize w).bytes.toNat .memoryAccess =
      .ok () := by
  have h_le16 : (toMiriSize w).bytes.toNat ≤ 16 := by cases w <;> decide
  have h_fits := fitsI64_of_le16 (toMiriSize w).bytes.toNat h_le16
  dsimp only [Miri.Memory.checkedBounds]
  change
    (if (!((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤
              Int.ofNat (toMiriSize w).bytes.toNat) &&
            (Int.ofNat (toMiriSize w).bytes.toNat <
              HPow.hPow (2 : Int) (63 : Nat)))) = true
     then _ else _) = Except.ok ()
  rw [h_fits]
  cases w <;> rfl

noncomputable def singleDataRange (w : IntWidth) :
    Miri.Memory.Validity.DataRangeSet :=
  match Miri.Memory.Validity.DataRangeSet.empty.addRange Size.ZERO (toMiriSize w) with
  | .ok rs => rs
  | .error _ => .empty

private theorem dataRangeSet_empty_addRange_zero (w : IntWidth) :
    Miri.Memory.Validity.DataRangeSet.empty.addRange Size.ZERO (toMiriSize w) =
      .ok (singleDataRange w) := by
  cases w <;> rfl

private theorem singleDataRange_toArray (w : IntWidth) :
    (singleDataRange w).toArray = (Array.mk [allocRange Size.ZERO (toMiriSize w)]) := by
  cases w <;> rfl

theorem scalar_tryToScalarInt_fromScalarInt (s : ScalarInt) :
    (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance) s).tryToScalarInt =
      .ok (.integer s) := rfl

theorem placeMemoryOffset_retPlace_zero
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    Miri.Interpreter.placeMemoryOffset refPointerArithmetic
        refResolvePointerPure mem.getAllocInfo retMemPlace Size.ZERO
        .inbounds .none st =
      .ok retMemPlace st := rfl

theorem scalar_fromBool_eq (b : Bool) :
    Scalar.fromBool (Prov := Miri.Memory.Provenance) b =
      .fromScalarInt (miriScalar .i8 (if b then 1 else 0)) := by
  cases b <;> rfl

theorem miriScalar_size (w : IntWidth) (bits : BitVec 128) :
    (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).size = toMiriSize w := by
  cases w <;> rfl

private theorem subrange_self_toMiriSize (w : IntWidth) :
    (allocRange Size.ZERO (toMiriSize w)).subrange
        (allocRange Size.ZERO (toMiriSize w)) =
      .ok (allocRange Size.ZERO (toMiriSize w)) := by
  cases w <;> rfl

private theorem getPtrAllocMut_retPlace_nonGhost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut)
    (h_extra : alloc.extra =
      Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
    (h_dr : machine.dataRace = none) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) false none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  exact Miri.Memory.AllocationAccess.live_mut_of_edges mem ⟨machine, none⟩
    ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) none refAccessConfig.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
    retAllocId ⟨.stack, alloc⟩ (.concrete Miri.Memory.BorTag.one)
    (toMiriSize w).bytes.toNat
    (sizeAsI64_toMiriSize w)
    (toMiriSize_ne_zero w)
    (Miri.Interpreter.PlaceMachine.resolvePointer_ok refAccessConfig mem machine
      retPtr _ _ rfl)
    (singleton_live_find _)
    h_mut
    rfl
    (by rw [h_sz]; exact checkedBounds_retPlace w)
    rfl
    (by
      dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
      rw [h_extra]
      exact Miri.Interpreter.PlaceMachine.memoryAccess_fresh_write
        refAccessConfig machine retAllocId Miri.Memory.BorTag.one
        (toMiriSize w) h_dr rfl rfl rfl)
    (singleton_live_filter_push _ _)

private theorem getPtrAlloc_retPlace_ghost_gen (w : IntWidth) (signedSize : Int)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_sa : Miri.Memory.sizeAsI64 (toMiriSize w) = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      (toMiriSize w) Size.ZERO signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRaw mem ⟨machine, none⟩
      retAllocId none cfg.globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRaw]
    rw [h_gh]
    dsimp only [refGlobalAllocationHooks, mem, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [singleton_live_find]
  have h_rp : (Miri.Interpreter.PlaceMachine.accessHooks cfg).resolvePointer
      mem ⟨machine, none⟩ retPtr signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocId, Size.ZERO, .concrete Miri.Memory.BorTag.one⟩)⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    rw [h_res]
    rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAlloc]
  change (match Miri.Memory.sizeAsI64 (toMiriSize w) with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, mem_ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [mem_ite_false_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_sz, h_bounds]
  rfl

private theorem getPtrAlloc_retPlace_ghost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : alloc.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ :=
  getPtrAlloc_retPlace_ghost_gen w (toMiriSize w).bytes.toNat mem1 alloc machine cfg
    h_res h_gh h_sz (sizeAsI64_toMiriSize w) (by cases w <;> decide)
    (checkedBounds_retPlace w)

private theorem getPtrAllocMut_retPlace_ghost_gen (w : IntWidth) (signedSize : Int)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut)
    (h_sa : Miri.Memory.sizeAsI64 (toMiriSize w) = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      (toMiriSize w) Size.ZERO signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRawMut mem ⟨machine, none⟩
      retAllocId none refAccessConfig.globalHooks =
      ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRawMut, refAccessConfig,
      refGlobalAllocationHooks, mem, Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [singleton_live_find]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [h_mut]
    rfl
  have h_rp : (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig).resolvePointer
      mem ⟨machine, none⟩ retPtr signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocId, Size.ZERO, .concrete Miri.Memory.BorTag.one⟩)⟩ :=
    Miri.Interpreter.PlaceMachine.resolvePointer_ok refAccessConfig mem machine
      retPtr _ _ rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAllocMut]
  change (match Miri.Memory.sizeAsI64 (toMiriSize w) with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, mem_ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [mem_ite_true_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_sz, h_bounds]
  rfl

private theorem getPtrAllocMut_retPlace_ghost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ :=
  getPtrAllocMut_retPlace_ghost_gen w (toMiriSize w).bytes.toNat mem1 alloc machine
    h_sz h_mut (sizeAsI64_toMiriSize w) (by cases w <;> decide)
    (checkedBounds_retPlace w)

theorem getPlaceAlloc_sized_of_access_poly {P E K H X : Type}
    [DecidableEq K]
    (memory : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (aligned : place.mplace.misaligned = none)
    (actual : Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
      ⟨Size.ofBytes 8⟩ place.mplace.ptr place.layout.size ghost kind global access =
      ⟨memory, hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAlloc memory hooks place
        RuntimeTargetDataLayout.default ghost kind global access dynamic =
      ⟨memory, hooks, some reference, .ok (some reference)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      dsimp only at aligned
      subst aligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
              ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error => _
            | Except.ok reference? => _) = _
          rw [actual]
          dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
            RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error => _
              | Except.ok reference? => _) = _
            rw [actual]
            dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
              RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
            rw [actual]

theorem getPlaceAllocMut_sized_of_access_poly {P E K H X : Type}
    [DecidableEq K]
    (memory : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (aligned : place.mplace.misaligned = none)
    (actual : Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
      ⟨Size.ofBytes 8⟩ place.mplace.ptr place.layout.size ghost kind global access =
      ⟨memory, hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAllocMut memory hooks place
        RuntimeTargetDataLayout.default ghost kind global access dynamic =
      ⟨memory, hooks, some reference, .ok (some reference)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      dsimp only at aligned
      subst aligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
              ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error => _
            | Except.ok reference? => _) = _
          rw [actual]
          dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
            RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error => _
              | Except.ok reference? => _) = _
            rw [actual]
            dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
              RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
            rw [actual]

private theorem getPlaceAlloc_retPlace_ghost (w : IntWidth)
    (memLayout : Miri.Interpreter.MemoryOperandLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_uns : memLayout.backendRepr.isUnsized = false)
    (h_lsz : memLayout.size = toMiriSize w)
    (h_sz : alloc.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
        ⟨retMemPlace, memLayout⟩ cfg.runtime true cfg.globalKind
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  rw [h_rt, h_gk]
  have h_ptr := getPtrAlloc_retPlace_ghost w mem1 alloc machine cfg h_res h_gh h_sz
  exact getPlaceAlloc_sized_of_access_poly mem ⟨machine, none⟩
    ⟨retMemPlace, memLayout⟩ true none cfg.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩
    h_uns rfl (by dsimp only; rw [h_lsz]; exact h_ptr)

theorem getPlaceAllocMut_retPlace_ghost (w : IntWidth)
    (memLayout : Miri.Interpreter.MemoryOperandLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_uns : memLayout.backendRepr.isUnsized = false)
    (h_lsz : memLayout.size = toMiriSize w)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Interpreter.getPlaceAllocMut mem ⟨machine, none⟩
        ⟨retMemPlace, memLayout⟩ refAccessConfig.runtime true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  have h_ptr := getPtrAllocMut_retPlace_ghost w mem1 alloc machine h_sz h_mut
  exact getPlaceAllocMut_sized_of_access_poly mem ⟨machine, none⟩
    ⟨retMemPlace, memLayout⟩ true none refAccessConfig.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
    refAccessConfig.dynamicLayout
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩
    h_uns rfl (by dsimp only; rw [h_lsz]; exact h_ptr)

theorem writeMemory_retPlace_scalar (w : IntWidth)
    (layout : LocalLayout) (abi : Miri.ABI.Scalar) (bits : BitVec 128)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_backend : (localMemoryLayout layout).backendRepr = .Scalar abi)
    (h_lsz : layout.layout.size = toMiriSize w)
    (h_prim : Miri.ABI.Primitive.size abi.primitive refAccessConfig.runtime =
      .ok (toMiriSize w))
    (h_nonptr : match abi.primitive with | .Pointer _ => True | _ => True)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))⟩)]) })
    (h_dr : st.machine.dataRace = none) :
    ∃ after,
      let mem' := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig (fun _ => true)
          (.scalar (.fromScalarInt (miriScalar w bits)))
          ⟨retMemPlace, layout⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
          (Size.ofBytes 8) after = .ok () after ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE := by
  let _ := h_nonptr
  let ⟨_, h_raw_eq, h_rsz, _, _, h_rmut, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE 1 (by decide) (by decide)
  rw [h_raw] at h_raw_eq
  injection h_raw_eq with h_raw_id
  subst h_raw_id
  let alloc := rawAlloc.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
  let ⟨after, h_w, h_rd, h_cp, h_asz, h_amut, h_aal, _⟩ :=
    tryNew_writeScalar_readScalar w bits h_raw
  have h_sc_sz : (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).size = toMiriSize w := miriScalar_size w bits
  have h_lml_sz : (localMemoryLayout layout).size = toMiriSize w := h_lsz
  have h_uns : (localMemoryLayout layout).backendRepr.isUnsized = false := by
    rw [h_backend]; rfl
  have h_ptr_acc := getPtrAllocMut_retPlace_nonGhost w mem1 alloc st.machine
    h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
        ⟨st.machine, none⟩
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (localMemoryLayout layout).size, alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (localMemoryLayout layout).size, alloc⟩)⟩ := by
    refine Miri.Interpreter.getPlaceAllocMut_sized_of_access _ _ _ _
      (Size.ofBytes 8) none _ _ _ _ h_uns rfl rfl ?_
    rw [h_lml_sz]
    exact h_ptr_acc
  have h_wm_op :
      Miri.Interpreter.writeImmediateToMplaceNoValidate
        st.machine.memory ⟨st.machine, none⟩
        (.scalar (.fromScalarInt (miriScalar w bits)))
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime refAccessConfig.ghostMode
        refAccessConfig.globalKind refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout (fun _ => true) =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (localMemoryLayout layout).size, after⟩,
        .ok ()⟩ := by
    rw [h_mem]
    refine Miri.Interpreter.writeImmediate_scalar_of_access
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      ⟨st.machine, none⟩
      ⟨retMemPlace, localMemoryLayout layout⟩
      refAccessConfig.runtime none refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout (fun _ => true)
      (.fromScalarInt (miriScalar w bits)) abi retAllocId alloc after
      h_backend
      (by rw [h_sc_sz]; exact h_prim)
      (by cases abi.primitive with | Pointer _ => exact True.intro | _ => rfl)
      (by rw [h_sc_sz, h_lml_sz]; exact Nat.le_refl _)
      h_place_acc
      (by rw [h_sc_sz]; exact h_w)
      (singleton_setLiveAllocation mem1 alloc after)
  exact ⟨after,
    Miri.Interpreter.PlaceMachine.writeMemory_of_result refAccessConfig
      (fun _ => true) (.scalar (.fromScalarInt (miriScalar w bits)))
      ⟨retMemPlace, layout⟩ st
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      _ rfl h_wm_op,
    h_rd, h_cp, h_asz, h_amut, h_aal⟩

theorem writeUninit_of_access_poly {P E K H X : Type}
    [DecidableEq K] [DecidableEq P] [PointerProvenance P]
    (memory afterMemory : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (runtime : RuntimeTargetDataLayout) (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (later : Miri.Interpreter.MemoryOperandLayout → Bool)
    (ref : Miri.Memory.AllocationAccessRef P E) (after : Allocation P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (actual : Miri.Interpreter.getPlaceAllocMut memory hooks place runtime
      ghost kind global access dynamic =
      ⟨memory, hooks, some ref, .ok (some ref)⟩)
    (written : Allocation.writeUninit ref.range runtime.pointerSize
      ref.allocation = .ok () after)
    (committed : memory.setLiveAllocation ref.allocId after = .ok afterMemory) :
    Miri.Interpreter.writeImmediateToMplaceNoValidate memory hooks .uninit
        place runtime ghost kind global access dynamic later =
      ⟨afterMemory, hooks, some { ref with allocation := after }, .ok ()⟩ := by
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure]
  rw [sized]
  simp only [Bool.false_eq_true, ite_false]
  change (match (if place.layout.backendRepr.isUnsized = true then
      Except.error Miri.Interpreter.MemoryOperandError.unsizedImmediateWrite
      else Except.ok ()) with
    | Except.error error => _
    | Except.ok () => _) = _
  rw [sized]
  simp only [Bool.false_eq_true, ite_false]
  rw [actual]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  change (match (memory.setLiveAllocation ref.allocId
      (match Allocation.writeUninit ref.range runtime.pointerSize ref.allocation with
       | EStateM.Result.ok _ a => a
       | EStateM.Result.error _ a => a)) with
    | Except.ok next => _
    | Except.error error => _) = _
  rw [written]
  dsimp only
  rw [committed]
  rfl

theorem writeMemory_retPlace_uninit (w : IntWidth)
    (layout : LocalLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_uns : (localMemoryLayout layout).backendRepr.isUnsized = false)
    (h_lsz : layout.layout.size = toMiriSize w)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))⟩)]) })
    (h_dr : st.machine.dataRace = none) :
    ∃ after info,
      let mem' := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig (fun _ => true)
          .uninit ⟨retMemPlace, layout⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .error (.invalidUninitBytes info) ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE := by
  let ⟨_, h_raw_eq, h_rsz, _, _, h_rmut, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE 1 (by decide) (by decide)
  rw [h_raw] at h_raw_eq
  injection h_raw_eq with h_raw_id
  subst h_raw_id
  let alloc := rawAlloc.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
  let ⟨after, info, h_wu, h_rd, h_asz, h_amut, h_aal, _⟩ :=
    tryNew_writeUninit_readUninit w h_raw
  have h_lml_sz : (localMemoryLayout layout).size = toMiriSize w := h_lsz
  have h_ptr_acc := getPtrAllocMut_retPlace_nonGhost w mem1 alloc st.machine
    h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
        ⟨st.machine, none⟩
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
    have h_p := Miri.Interpreter.getPlaceAllocMut_sized_of_access
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      ⟨st.machine, none⟩
      ⟨retMemPlace, localMemoryLayout layout⟩
      refAccessConfig.runtime (Size.ofBytes 8) none refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout
      ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩
      h_uns rfl rfl (by rw [h_lml_sz]; exact h_ptr_acc)
    exact h_p
  have h_wm_op :
      Miri.Interpreter.writeImmediateToMplaceNoValidate
        st.machine.memory ⟨st.machine, none⟩ .uninit
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime refAccessConfig.ghostMode
        refAccessConfig.globalKind refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout (fun _ => true) =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .ok ()⟩ := by
    rw [h_mem]
    exact writeUninit_of_access_poly
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      ⟨st.machine, none⟩ ⟨retMemPlace, localMemoryLayout layout⟩
      refAccessConfig.runtime refAccessConfig.ghostMode
      refAccessConfig.globalKind refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout (fun _ => true)
      ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩ after
      h_uns h_place_acc h_wu (singleton_setLiveAllocation mem1 alloc after)
  exact ⟨after, info,
    Miri.Interpreter.PlaceMachine.writeMemory_of_result refAccessConfig
      (fun _ => true) .uninit ⟨retMemPlace, layout⟩ st
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      _ rfl h_wm_op,
    h_rd, h_asz, h_amut, h_aal⟩

private theorem readImmediateFromMplaceRaw_retPlace_I8
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 1, al,
          .Scalar (.Initialized (value := .Int .I8 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 1, al,
        .Scalar (.Initialized (value := .Int .I8 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 1)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 1)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 1)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I16
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 2, al,
          .Scalar (.Initialized (value := .Int .I16 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 2, al,
        .Scalar (.Initialized (value := .Int .I16 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 2)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 2)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 2)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I32
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 4, al,
          .Scalar (.Initialized (value := .Int .I32 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 4, al,
        .Scalar (.Initialized (value := .Int .I32 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 4)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 4)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 4)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I64
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 8, al,
          .Scalar (.Initialized (value := .Int .I64 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 8, al,
        .Scalar (.Initialized (value := .Int .I64 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 8)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 8)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 8)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I128
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 16, al,
          .Scalar (.Initialized (value := .Int .I128 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 16, al,
        .Scalar (.Initialized (value := .Int .I128 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 16)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 16)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 16)) false <;> rfl

theorem readImmediateFromMplaceRaw_retPlace_int_aux
    (w : IntWidth) (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange)
    (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨toMiriSize w, al,
          .Scalar (.Initialized (value := .Int (toMiriInteger w) s)
            (validRange := vr)),
          cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨toMiriSize w, al,
        .Scalar (.Initialized (value := .Int (toMiriInteger w) s)
          (validRange := vr)),
        cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  cases w with
  | i8 => exact readImmediateFromMplaceRaw_retPlace_I8 s al vr cty mem1 after machine cfg h_acc
  | i16 => exact readImmediateFromMplaceRaw_retPlace_I16 s al vr cty mem1 after machine cfg h_acc
  | i32 => exact readImmediateFromMplaceRaw_retPlace_I32 s al vr cty mem1 after machine cfg h_acc
  | i64 => exact readImmediateFromMplaceRaw_retPlace_I64 s al vr cty mem1 after machine cfg h_acc
  | i128 => exact readImmediateFromMplaceRaw_retPlace_I128 s al vr cty mem1 after machine cfg h_acc
  | isize => exact readImmediateFromMplaceRaw_retPlace_I64 s al vr cty mem1 after machine cfg h_acc

theorem readImmediateFromMplaceRaw_retPlace_core (types : List MirTy)
    (w : IntWidth) (ty : MirTy)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s) ∨
      (ty = .char ∧ w = .i32))
    (h_sz : after.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types ty)⟩
        RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types ty)⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_uns : (localMemoryLayout (refLocalLayoutForTy types ty)).backendRepr.isUnsized = false := by
    cases h_ty with
    | inl h => rw [h.1]; rfl
    | inr h =>
      cases h with
      | inl h => let ⟨s, hs⟩ := h; rw [hs]; cases w <;> cases s <;> rfl
      | inr h => rw [h.1]; rfl
  have h_lsz : (localMemoryLayout (refLocalLayoutForTy types ty)).size = toMiriSize w := by
    cases h_ty with
    | inl h => rw [h.1, h.2]; rfl
    | inr h =>
      cases h with
      | inl h => let ⟨s, hs⟩ := h; rw [hs]; rfl
      | inr h => rw [h.1, h.2]; rfl
  have h_acc := getPlaceAlloc_retPlace_ghost w
    (localMemoryLayout (refLocalLayoutForTy types ty))
    mem1 after machine cfg h_rt h_gk h_res h_gh h_uns h_lsz h_sz
  rw [h_rt, h_gk] at h_acc
  cases h_ty with
  | inl h =>
    let ⟨hty, hw⟩ := h
    subst hty hw
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
      Pure.pure, bind, Bind.bind]
    rw [h_acc]
    dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
      refBoolLayoutData, refBaseLayoutData, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
        (after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i8)) false)) _ _ = _
    cases after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (toMiriSize .i8)) false <;> rfl
  | inr h =>
    cases h with
    | inl h =>
      let ⟨s, hty⟩ := h
      subst hty
      exact readImmediateFromMplaceRaw_retPlace_int_aux w s
        (Miri.ABI.AbiAlign.new Align.ONE).abi
        (refFullWrappingRangeSize (toMiriSize w))
        (some (tyIdFor types (.int w s)))
        mem1 after machine cfg h_acc
    | inr h =>
      let ⟨hty, hw⟩ := h
      subst hty hw
      exact readImmediateFromMplaceRaw_retPlace_int_aux .i32 false
        (Miri.ABI.AbiAlign.new Align.ONE).abi
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 0x10ffff⟩
        (some (tyIdFor types .char))
        mem1 after machine cfg h_acc


theorem clearPlaceProvenance_mem_step {K P E H X S C Extra : Type}
    [DecidableEq K] [PointerProvenance P]
    (env : Miri.Interpreter.ValidityMemory.Environment P E K H X S)
    (placeHooks : Miri.Interpreter.PlaceHooks P S C Extra) (choice : C)
    (valInProg : Miri.Interpreter.ValidityMemory.M S Bool)
    (afterWrite : Miri.MIR.LocalId → Bool → Miri.Interpreter.ValidityMemory.M S Unit)
    (mplace : Miri.Interpreter.MemPlace P) (layout : LocalLayout) (st st1 : S)
    (mem' : Miri.Memory.MemoryState P E K) (hooks' : H)
    (ref : Miri.Memory.AllocationAccessRef P E)
    (h_acc : Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
        ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
        env.context.globalKind env.context.globalHooks
        env.context.accessHooks env.context.dynamicLayout =
      ⟨mem', hooks', some ref, .ok (some ref)⟩)
    (h_st1 : env.putTouched (env.putMemoryHooks st mem' hooks') (some ref) = st1)
    (entry : Miri.Memory.AllocId × Miri.Memory.LocalAllocation P E K)
    (h_find : (env.memory st1).live.find? (fun e => e.1 == ref.allocId) = some entry)
    (after : Allocation P E)
    (h_cp : Allocation.clearProvenance ref.range env.context.runtime.pointerSize
        entry.2.allocation = .ok () after)
    (mem'' : Miri.Memory.MemoryState P E K)
    (h_set : (env.memory st1).setLiveAllocation ref.allocId after = .ok mem'') :
    Miri.Interpreter.ValidityMemory.clearPlaceProvenance env placeHooks choice
        valInProg afterWrite ⟨.memory mplace, layout⟩ st =
      .ok () (env.putTouched (env.putMemoryHooks st1 mem'' (env.hooks st1))
        (some ⟨ref.allocId, ref.range, after⟩)) := by
  dsimp only [Miri.Interpreter.ValidityMemory.clearPlaceProvenance,
    Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    Miri.Interpreter.asMplaceOrMutableLocal,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  change ((match
      (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
        ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
        env.context.globalKind env.context.globalHooks
        env.context.accessHooks env.context.dynamicLayout).outcome with
      | Except.ok reference => (fun s => _ : S → EStateM.Result StepError S Unit)
      | Except.error error => (fun s => _ : S → EStateM.Result StepError S Unit))
      (env.putTouched (env.putMemoryHooks st
        (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
          ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
          env.context.globalKind env.context.globalHooks
          env.context.accessHooks env.context.dynamicLayout).memory
        (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
          ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
          env.context.globalKind env.context.globalHooks
          env.context.accessHooks env.context.dynamicLayout).hooks)
        (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
          ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
          env.context.globalKind env.context.globalHooks
          env.context.accessHooks env.context.dynamicLayout).touched)) = _
  rw [h_acc]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_st1]
  change ((match
      (env.memory st1).live.find?
        (fun (e : Miri.Memory.AllocId × Miri.Memory.LocalAllocation P E K) =>
          e.1 == ref.allocId) with
    | some entry => (fun s => _ : S → EStateM.Result StepError S Unit)
    | _ => (fun s => _ : S → EStateM.Result StepError S Unit)) st1) = _
  rw [h_find]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_cp]
  dsimp only
  rw [h_set]
  rfl


theorem validatePlace_mem_ub_step (types : List MirTy) (c : Choice)
    (layout : LocalLayout)
    (st st' : Miri.Interpreter.MachineHooks.State Unit RefUser) (msg : String)
    (h_vis :
      let initSess :
          Miri.Interpreter.ValidityVisitor.Session
            Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess ⟨.memory retMemPlace, layout⟩ st =
        .error (.undefinedBehavior msg) st') :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        ⟨.memory retMemPlace, layout⟩ false true st =
      .error (.undefinedBehavior msg) st' := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, mem_ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [mem_ite_false_eq, h_vis]

/-- `refHasPadding` succeeds on every canonical $M_{\text{ref}}$ layout. -/
private theorem refHasPadding_ok (types : List MirTy) (ty : MirTy) :
    ∃ b, refHasPadding (refLocalLayoutForTy types ty) = .ok b := by
  cases ty with
  | unit | never | bool | int _ _ | char | ordering | ref _ _ | rawPtr _ _
  | unsupported => exact ⟨_, rfl⟩
  | tuple fs =>
    cases refLayoutDataForTy_tuple fs with
    | inl h =>
      refine ⟨true, ?_⟩
      dsimp only [refHasPadding, refLocalLayoutForTy]
      rw [h]; rfl
    | inr h =>
      let ⟨w, _, _, h_eq⟩ := h
      dsimp only [refHasPadding, refLocalLayoutForTy]
      rw [h_eq]
      cases w <;> exact ⟨_, rfl⟩
  | enum ety =>
    dsimp only [refHasPadding, refLocalLayoutForTy, refLayoutDataForTy,
      refEnumLayoutData]
    cases ety.tagRepr <;> exact ⟨_, rfl⟩

theorem copyRuntimePlace_imm_to_mem_step (rp : RefProg) (c : Choice)
    (ty : MirTy) (imm : Immediate Miri.Memory.Provenance)
    (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (st st1 : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (res : EStateM.Result StepError
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
      (fun _ => true) imm ⟨mplace, refLocalLayoutForTy rp.types ty⟩ st =
      .ok () st1)
    (h_val :
      Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks rp.types) c 8
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ false true st1 =
          res) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    Miri.Interpreter.copyRuntimePlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
        ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ true st = res := by
  intro h
  have h_take : Miri.Interpreter.PlaceMachine.takePendingMoveDeinit true st =
      .ok false st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_pmd
        subst h_pmd
        rfl
  have h_rr : Miri.Interpreter.PlaceMachine.readRaw refAccessConfig
      ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩ st =
      .ok (.immediate
        ⟨imm, localMemoryLayout (refLocalLayoutForTy rp.types ty)⟩) st := by
    cases st with
    | mk stack machine =>
      cases machine; rfl
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_compat : h.copy.compatible (refLocalLayoutForTy rp.types ty)
      (refLocalLayoutForTy rp.types ty) = .ok true := by
    dsimp only [h, Miri.Interpreter.ExecutionMachine.withValidation,
      Miri.Interpreter.TypedMachineBindings.bindValidation,
      refExecutionConfig, refPlaceCopyHooks]
    rw [beq_self_eq_true]
  have h_wp :
      Miri.Interpreter.writePlaceImmediateNoValidate
        (Miri.Interpreter.PlaceMachine.placeHooks refAccessConfig
          refAllocationConfig (refCompilerHooks rp.types))
        c imm ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ st =
        .ok () st1 := by
    dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate,
      Miri.Interpreter.asMplaceOrMutableLocal,
      Miri.Interpreter.PlaceMachine.placeHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_sz, mem_ite_not_true_eq]
    exact h_wm
  have h_nv :
      Miri.Interpreter.copyRuntimePlaceNoValidate
        (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
        ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ true st =
        .ok () st1 := by
    dsimp only [Miri.Interpreter.copyRuntimePlaceNoValidate,
      Miri.Interpreter.ExecutionMachine.projectionHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_compat]
    change (match (EStateM.Result.ok true st :
        EStateM.Result StepError
          (Miri.Interpreter.MachineHooks.State Unit RefUser) Bool) with
      | EStateM.Result.ok a s => _
      | EStateM.Result.error e s => EStateM.Result.error e s) = _
    dsimp only
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    let ⟨pb, h_pb⟩ := refHasPadding_ok rp.types ty
    have h_pad : h.copy.hasPadding (refLocalLayoutForTy rp.types ty) = .ok pb :=
      h_pb
    rw [h_pad]
    change (EStateM.bind (EStateM.pure pb) _ st) = _
    rw [mem_eStateM_bind_pure]
    change (EStateM.bind
      (Miri.Interpreter.PlaceMachine.takePendingMoveDeinit true) _ st) = _
    rw [mem_eStateM_bind_ok h_take]
    cases pb with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      change (EStateM.bind
        (Miri.Interpreter.PlaceMachine.readRaw refAccessConfig
        ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩) _ st) = _
      rw [mem_eStateM_bind_ok h_rr]
      dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rw [h_sz, bne_self_eq_false]
      exact h_wp
    | true =>
      simp only [ite_true]
      dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rw [h_sz, bne_self_eq_false]
      exact h_wp
  have h_ev :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          h).place.enforceValidity c
        (refLocalLayoutForTy rp.types ty) st1 = .ok true st1 := rfl
  have h_v :
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.validate c
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ st1 =
      Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks rp.types) c 8
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ false true st1 := rfl
  dsimp only [Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, EStateM.bind]
  rw [h_nv]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ev]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  simp only [ite_true]
  rw [bne_self_eq_false, mem_ite_false_eq, h_v, h_val]

end Anneal.MirCorrespondence
