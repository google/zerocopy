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
import Anneal.MirCorrespondence.ValidateLocal
import Anneal.MirCorrespondence.RetPlace

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

private theorem readImmediate_mem_retPlace_core (endian : TargetEndian)
    (types : List MirTy)
    (w : IntWidth) (ty : MirTy)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = refRuntimeLayout endian)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s) ∨
      (ty = .char ∧ w = .i32))
    (h_sz : after.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediate mem ⟨machine, none⟩
        (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types ty))
        cfg.runtime true cfg.globalKind cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      match after.readScalar (refRuntimeLayout endian).base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types ty)⟩⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_raw := readImmediateFromMplaceRaw_retPlace_core endian types w ty mem1
    after machine cfg h_rt h_gk h_res h_gh h_ty h_sz
  rw [h_rt, h_gk]
  cases h_ty with
  | inl h =>
    let ⟨hty, hw⟩ := h
    subst hty hw
    dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
      Id.run, pure, Pure.pure, bind, Bind.bind]
    rw [h_raw]
    cases after.readScalar (refRuntimeLayout endian).base
        (allocRange Size.ZERO (toMiriSize .i8)) false <;> rfl
  | inr h =>
    cases h with
    | inl h =>
      let ⟨s, hty⟩ := h
      subst hty
      cases w <;> cases s <;> (
        dsimp only [Miri.Interpreter.readImmediate,
          Miri.Interpreter.readImmediateRaw,
          Id.run, pure, Pure.pure, bind, Bind.bind]
        rw [h_raw]
        cases after.readScalar (refRuntimeLayout endian).base
            (allocRange Size.ZERO _) false <;> rfl)
    | inr h =>
      let ⟨hty, hw⟩ := h
      subst hty hw
      dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
        Id.run, pure, Pure.pure, bind, Bind.bind]
      rw [h_raw]
      cases after.readScalar (refRuntimeLayout endian).base
          (allocRange Size.ZERO (toMiriSize .i32)) false <;> rfl

private theorem validityMemory_readImmediate_mem_scalar (endian : TargetEndian)
    (types : List MirTy)
    (w : IntWidth) (ty : MirTy) (sc : Scalar Miri.Memory.Provenance)
    (expected : ExpectedValue)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s) ∨
      (ty = .char ∧ w = .i32))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize w)) false = .ok sc) :
    Miri.Interpreter.ValidityMemory.readImmediate (refValidityMemoryEnv endian)
        ⟨.indirect retMemPlace, refLocalLayoutForTy types ty⟩ expected st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types ty⟩ st := by
  have h_core := readImmediate_mem_retPlace_core endian types w ty mem1 after
    st.machine (refAccessConfig endian) rfl rfl rfl rfl h_ty h_sz
  rw [h_rd] at h_core
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnv, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  have h_core' :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types ty))
        (refAccessConfig endian).runtime true none
        (refAccessConfig endian).globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfig endian))
        (refAccessConfig endian).dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types ty)⟩⟩ := h_core
  rw [h_core']
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      rfl

private theorem validityMemory_readImmediate_mem_uninit (endian : TargetEndian)
    (types : List MirTy)
    (w : IntWidth) (ty : MirTy) (info : Option Miri.Memory.BadBytesAccess)
    (expected : ExpectedValue)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s) ∨
      (ty = .char ∧ w = .i32))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize w)) false =
      .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityMemory.readImmediate (refValidityMemoryEnv endian)
          ⟨.indirect retMemPlace, refLocalLayoutForTy types ty⟩ expected st =
        .error (.undefinedBehavior msg) st := by
  have h_core := readImmediate_mem_retPlace_core endian types w ty mem1 after
    st.machine (refAccessConfig endian) rfl rfl rfl rfl h_ty h_sz
  rw [h_rd] at h_core
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnv, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  have h_core' :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types ty))
        (refAccessConfig endian).runtime true none
        (refAccessConfig endian).globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfig endian))
        (refAccessConfig endian).dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .error (.allocation (.invalidUninitBytes info))⟩ := h_core
  rw [h_core']
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      exact ⟨_, rfl⟩

private theorem placeMachine_readImmediate_mem_scalar_ghost
    (endian : TargetEndian) (types : List MirTy)
    (tagW : IntWidth) (tagS : Bool) (sc : Scalar Miri.Memory.Provenance)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize tagW)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize tagW)) false = .ok sc) :
    Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig endian with
          ghostMode := true, deinitMovedPlace := false }
        ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩ st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
  let cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser :=
    { refAccessConfig endian with
      ghostMode := true, deinitMovedPlace := false }
  have h_core := readImmediate_mem_retPlace_core endian types tagW
    (.int tagW tagS) mem1 after st.machine cfg rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨tagS, rfl⟩)) h_sz
  rw [h_rd] at h_core
  have h_take : Miri.Interpreter.PlaceMachine.takePendingMoveDeinit false st =
      .ok false st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_pmd
        subst h_pmd
        rfl
  change Miri.Interpreter.PlaceMachine.readImmediate cfg
      ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩ st = _
  dsimp only [Miri.Interpreter.PlaceMachine.readImmediate]
  change (EStateM.bind (Miri.Interpreter.PlaceMachine.takePendingMoveDeinit false) _ st) = _
  rw [mem_eStateM_bind_ok h_take]
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  have h_core' :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types (.int tagW tagS)))
        cfg.runtime cfg.ghostMode cfg.globalKind cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize tagW), after⟩,
        .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types (.int tagW tagS))⟩⟩ := h_core
  rw [h_core']
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      rfl


private theorem clearPlaceProvenance_mem_retPlace (endian : TargetEndian)
    (types : List MirTy)
    (c : Choice) (w : IntWidth) (ty : MirTy)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s) ∨
      (ty = .char ∧ w = .i32))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_mut : after.mutability = .Mut)
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) after = .ok () after) :
    (refValHooks endian types).clearProvenance c
        ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩ st =
      .ok () st := by
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
  have h_acc := getPlaceAllocMut_retPlace_ghost endian w
    (localMemoryLayout (refLocalLayoutForTy types ty))
    mem1 after st.machine h_uns h_lsz h_sz h_mut
  have h_st_eq :
      ({ st with machine := { st.machine with
          memory := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) } } } :
        Miri.Interpreter.MachineHooks.State Unit RefUser) = st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_mem
        subst h_mem
        rfl
  have h_env_acc :
      Miri.Interpreter.getPlaceAllocMut
        ((refValidityMemoryEnv endian).memory st)
        ((refValidityMemoryEnv endian).hooks st)
        ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types ty)⟩
        (refValidityMemoryEnv endian).context.runtime true
        (refValidityMemoryEnv endian).context.globalKind
        (refValidityMemoryEnv endian).context.globalHooks
        (refValidityMemoryEnv endian).context.accessHooks
        (refValidityMemoryEnv endian).context.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩)⟩ := by
    dsimp only [refValidityMemoryEnv]
    rw [h_mem]
    exact h_acc
  rw [refValHooks_clearProvenance]
  have h_res := clearPlaceProvenance_mem_step (refValidityMemoryEnv endian)
    (refBasePlaceProjectionHooks endian types).place
    c (fun st => .ok false st) (fun _ _ st => .ok () st)
    retMemPlace (refLocalLayoutForTy types ty) st st
    { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    ⟨st.machine, none⟩
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩
    h_env_acc h_st_eq (retAllocId, ⟨.stack, after⟩)
    (by dsimp only [refValidityMemoryEnv]; rw [h_mem]; exact singleton_live_find ⟨.stack, after⟩)
    after h_cp { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    (by dsimp only [refValidityMemoryEnv]; rw [h_mem]; exact singleton_setLiveAllocation mem1 after after)
  rw [h_res]
  dsimp only [refValidityMemoryEnv]
  rw [h_st_eq]

theorem visit_mem_int_ok (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (fuel : Nat)
    (path : Miri.Memory.ValidationPath) (w : IntWidth) (s : Bool)
    (sc : Scalar Miri.Memory.Provenance)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize w)) false = .ok sc)
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) after = .ok () after) :
    let sess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
        (fuel + 1) sess
        ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st =
      .ok { sess with dataBytes := some (singleDataRange w) } st := by
  intro sess
  have h_ri : (refValHooks endian types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
      ExpectedValue.integer st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types (.int w s)⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_mem_scalar endian types w (.int w s) sc
      ExpectedValue.integer mem1 after st (Or.inr (Or.inl ⟨s, rfl⟩))
      h_mem h_sz h_rd
  have h_clr := clearPlaceProvenance_mem_retPlace endian types c w (.int w s)
    mem1 after st (Or.inr (Or.inl ⟨s, rfl⟩)) h_mem h_sz h_mut h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
    ExpectedValue.integer) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure sc) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_ib :
      (Miri.Interpreter.ValidityVisitor.TypeKind.integer == .boolean) =
        false := rfl
  have h_ic :
      (Miri.Interpreter.ValidityVisitor.TypeKind.integer == .character) =
        false := rfl
  rw [h_ib, mem_ite_false_eq, h_ic, mem_ite_false_eq, mem_ite_true_eq]
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).clearProvenance c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩) _) _ st) = _
  rw [eStateM_bind_bind_ok h_clr]
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure,
    refValHooks_toOp, Miri.Interpreter.placeToOp,
    Miri.Interpreter.placeToOpCore, refLocalLayoutForTy, refLayoutDataForTy,
    refScalarLayoutData, refBaseLayoutData]
  cases w <;> rfl

theorem visit_mem_int_uninit_ub (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (w : IntWidth) (s : Bool) (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize w)) false =
      .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
          (fuel + 1) sess
          ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st =
        .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_ri_raw⟩ := validityMemory_readImmediate_mem_uninit endian types w
    (.int w s) info ExpectedValue.integer mem1 after st
    (Or.inr (Or.inl ⟨s, rfl⟩))
    h_mem h_sz h_rd
  have h_ri : (refValHooks endian types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
      ExpectedValue.integer st = .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact h_ri_raw
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
    ExpectedValue.integer) _) _ st) = _
  rw [eStateM_bind_bind_err h_ri]

theorem visit_mem_char_ok (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (fuel : Nat)
    (path : Miri.Memory.ValidationPath) (ch : Char)
    (sc : Scalar Miri.Memory.Provenance)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .char) = some .char)
    (h_char : sc.toChar = .ok ch)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize .i32)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize .i32)) false = .ok sc)
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize .i32))
      (Size.ofBytes 8) after = .ok () after) :
    let sess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
        (fuel + 1) sess ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩
        st =
      .ok { sess with dataBytes := some (singleDataRange .i32) } st := by
  intro sess
  have h_ri : (refValHooks endian types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩
      ExpectedValue.character st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types .char⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_mem_scalar endian types .i32 .char sc
      ExpectedValue.character mem1 after st (Or.inr (Or.inr ⟨rfl, rfl⟩))
      h_mem h_sz h_rd
  have h_clr := clearPlaceProvenance_mem_retPlace endian types c .i32 .char
    mem1 after st (Or.inr (Or.inr ⟨rfl, rfl⟩)) h_mem h_sz h_mut h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩
    ExpectedValue.character) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure sc) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_ib :
      (Miri.Interpreter.ValidityVisitor.TypeKind.character == .boolean) =
        false := rfl
  have h_ic :
      (Miri.Interpreter.ValidityVisitor.TypeKind.character == .character) =
        true := rfl
  rw [h_ib, mem_ite_false_eq, h_ic, mem_ite_true_eq, h_char]
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).clearProvenance c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩) _) _ st) = _
  rw [eStateM_bind_bind_ok h_clr]
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure,
    refValHooks_toOp, Miri.Interpreter.placeToOp,
    Miri.Interpreter.placeToOpCore, refLocalLayoutForTy, refLayoutDataForTy,
    refScalarLayoutData, refBaseLayoutData]
  rfl

theorem visit_mem_char_uninit_ub (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .char) = some .char)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize .i32)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize .i32)) false =
      .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
          (fuel + 1) sess ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩
          st =
        .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_ri_raw⟩ := validityMemory_readImmediate_mem_uninit endian types
    .i32 .char info ExpectedValue.character mem1 after st
    (Or.inr (Or.inr ⟨rfl, rfl⟩))
    h_mem h_sz h_rd
  have h_ri : (refValHooks endian types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩
      ExpectedValue.character st = .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact h_ri_raw
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .char⟩
    ExpectedValue.character) _) _ st) = _
  rw [eStateM_bind_bind_err h_ri]

theorem visit_mem_bool_ok (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (fuel : Nat)
    (path : Miri.Memory.ValidationPath) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize .i8)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize .i8)) false =
      .ok (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))))
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize .i8))
      (Size.ofBytes 8) after = .ok () after) :
    let sess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
        (fuel + 1) sess ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
        st =
      .ok { sess with dataBytes := some (singleDataRange .i8) } st := by
  intro sess
  have h_ri : (refValHooks endian types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
      ExpectedValue.boolean st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))),
        refLocalLayoutForTy types .bool⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_mem_scalar endian types .i8 .bool _
      ExpectedValue.boolean mem1 after st (Or.inl ⟨rfl, rfl⟩) h_mem h_sz h_rd
  have h_clr := clearPlaceProvenance_mem_retPlace endian types c .i8 .bool
    mem1 after st (Or.inl ⟨rfl, rfl⟩) h_mem h_sz h_mut h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
    ExpectedValue.boolean) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure
    (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar .i8 (if b then 1 else 0)))) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_bb :
      (Miri.Interpreter.ValidityVisitor.TypeKind.boolean == .boolean) =
        true := rfl
  have h_bc :
      (Miri.Interpreter.ValidityVisitor.TypeKind.boolean == .character) =
        false := rfl
  rw [h_bb, mem_ite_true_eq]
  cases b <;> (
    dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
    rw [h_bc, mem_ite_false_eq, mem_ite_true_eq]
    change (EStateM.bind (EStateM.bind
      ((refValHooks endian types).clearProvenance c
        ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩) _) _ st) = _
    rw [eStateM_bind_bind_ok h_clr]
    rfl)

theorem visit_mem_bool_uninit_ub (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize .i8)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize .i8)) false =
      .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
          (fuel + 1) sess ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
          st =
        .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_ri_raw⟩ := validityMemory_readImmediate_mem_uninit endian types .i8
    .bool info ExpectedValue.boolean mem1 after st (Or.inl ⟨rfl, rfl⟩)
    h_mem h_sz h_rd
  have h_ri : (refValHooks endian types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
      ExpectedValue.boolean st = .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact h_ri_raw
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks endian types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
    ExpectedValue.boolean) _) _ st) = _
  rw [eStateM_bind_bind_err h_ri]

private theorem placeDynamic_field0_mem_scalar_enum (endian : TargetEndian)
    (types : List MirTy)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_el : EnumLike types ty ety) :
    Miri.Interpreter.PlaceDynamic.field
        (refBasePlaceProjectionHooks endian types) c
        ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩ 0 st =
      .ok ⟨.memory retMemPlace,
        refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
  have h_fo : (refLocalLayoutForTy types ty).layout.fields.offset 0 =
      .ok Size.ZERO := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
    rfl
  have h_fl : (refBasePlaceProjectionHooks endian types).field c
      (refLocalLayoutForTy types ty) 0 st =
      .ok (refLocalLayoutForTy types (.int tagW tagS)) st := by
    dsimp only [refBasePlaceProjectionHooks]
    rw [enumLike_projectField0 h_el h_tr]
  have h_sz :
      (refLocalLayoutForTy types (.int tagW tagS)).layout.isSized = true :=
    refLayoutDataForTy_isSized (.int tagW tagS)
  dsimp only [Miri.Interpreter.PlaceDynamic.field, bind, Bind.bind,
    EStateM.bind]
  rw [h_fo]
  change (EStateM.bind ((refBasePlaceProjectionHooks endian types).field c
    (refLocalLayoutForTy types ty) 0) _ st) = _
  rw [mem_eStateM_bind_ok h_fl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_sz, mem_ite_not_true_eq]
  dsimp only [Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure]
  rw [placeMemoryOffset_retPlace_zero]

private theorem placeDynamic_downcast_mem_scalar_enum (endian : TargetEndian)
    (types : List MirTy)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (variant : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike types ty ety)
    (h_v_lt : variant < ety.discriminants.length) :
    Miri.Interpreter.PlaceDynamic.downcast
        (refBasePlaceProjectionHooks endian types) c
        ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩ variant st =
      .ok ⟨.memory retMemPlace,
        ⟨tyIdFor types ty,
          { refUnitLayoutData with variants := .Single variant }⟩⟩ st := by
  have h_blt : Nat.blt variant ety.discriminants.length = true :=
    Nat.ble_eq_true_of_le h_v_lt
  have h_vl : (refBasePlaceProjectionHooks endian types).variant c
      (refLocalLayoutForTy types ty) variant st =
      .ok ⟨tyIdFor types ty,
        { refUnitLayoutData with variants := .Single variant }⟩ st := by
    dsimp only [refBasePlaceProjectionHooks]
    rw [enumLike_projectVariant h_el h_v_lt]
  dsimp only [Miri.Interpreter.PlaceDynamic.downcast, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]
  change (EStateM.bind ((refBasePlaceProjectionHooks endian types).variant c
    (refLocalLayoutForTy types ty) variant) _ st) = _
  rw [mem_eStateM_bind_ok h_vl]
  change Miri.Interpreter.PlaceDynamic.offsetWithMeta
    (refBasePlaceProjectionHooks endian types) c
    ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩ Size.ZERO .inbounds
    .none ⟨tyIdFor types ty,
      { refUnitLayoutData with variants := .Single variant }⟩ st = _
  dsimp only [Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure]
  rw [placeMemoryOffset_retPlace_zero]

theorem visit_mem_scalar_enum_ok (endian : TargetEndian) (types : List MirTy)
    (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1)
    (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (variant disc : Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_el : EnumLike types ty ety)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize tagW)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize tagW)) false =
      .ok (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize tagW))
      (Size.ofBytes 8) after = .ok () after) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
        (fuel + 1) initSess ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩
        st =
      .ok { initSess with dataBytes := some (singleDataRange tagW) } st := by
  intro initSess
  have h_v_lt : variant < ety.discriminants.length :=
    mirGetElem?_lt_of_some h_get_d
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true ==
        .box) = false := rfl
  have h_fields : (refLocalLayoutForTy types ty).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
  have h_vars : (refLocalLayoutForTy types ty).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map
          (fun _ => refInhabitedVariantLayout)).toArray := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
  have h_field0 := placeDynamic_field0_mem_scalar_enum endian types c ty ety
    tagW tagS st h_tr h_el
  have h_op_field0 :
      Miri.Interpreter.OperandMachine.field
        (refValidityOperandHooks endian types) c
        ⟨.indirect retMemPlace, refLocalLayoutForTy types ty⟩ 0 st =
      .ok ⟨.indirect retMemPlace,
        refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.OperandMachine.field, refValidityOperandHooks,
      bind, Bind.bind, EStateM.bind]
    rw [h_field0]
    rfl
  have h_ri_ghost := placeMachine_readImmediate_mem_scalar_ghost endian types
    tagW tagS (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))
    mem1 after st h_pmd h_mem h_sz h_rd
  have h_rd_discr := readDiscriminant_validity_scalar_enum endian types c ty
    ety tagW tagS
    variant disc (.indirect retMemPlace)
    ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩
    st h_tr h_adm h_el h_get_d h_op_field0 h_ri_ghost
  have h_dc := placeDynamic_downcast_mem_scalar_enum endian types c ty ety
    variant st h_el h_v_lt
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, enumLike_classify endian h_el]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option
          (Miri.Interpreter.ValidityVisitor.Session
            Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_projection, h_field0]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, initSess, Bool.or]
  rw [h_fuel]
  rw [visit_mem_int_ok endian types c k
    ({ originalType := "" : Miri.Memory.ValidationPath }.push .enumTag)
    tagW tagS
    (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))
    mem1 after st (mem_resolveTy_tyIdFor_int types tagW tagS) h_mem h_sz h_mut
    h_rd h_cp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_discriminant, h_rd_discr]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_dc]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_variantPath]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [visit_local_fieldless_enum endian types c k _ _ ty ety variant st rfl
    h_el rfl rfl rfl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [enumLike_opsemInhabited endian h_el]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [mem_ite_true_eq, refValHooks_debugAssertions, mem_ite_false_eq]
  rfl

theorem visit_mem_scalar_enum_uninit_ub (endian : TargetEndian)
    (types : List MirTy)
    (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1)
    (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_el : EnumLike types ty ety)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize tagW)
    (h_rd : after.readScalar (refRuntimeLayout endian).base
      (allocRange Size.ZERO (toMiriSize tagW)) false =
      .error (.invalidUninitBytes info)) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c
          (fuel + 1) initSess
          ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩ st =
        .error (.undefinedBehavior msg) st := by
  intro initSess
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true ==
        .box) = false := rfl
  have h_fields : (refLocalLayoutForTy types ty).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
  have h_field0 := placeDynamic_field0_mem_scalar_enum endian types c ty ety
    tagW tagS st h_tr h_el
  let ⟨msg, h_v0⟩ := visit_mem_int_uninit_ub endian types c k
    { path := { originalType := "" : Miri.Memory.ValidationPath }.push .enumTag,
      flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty }
    tagW tagS info mem1 after st (mem_resolveTy_tyIdFor_int types tagW tagS)
    h_mem h_sz h_rd
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, enumLike_classify endian h_el]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option
          (Miri.Interpreter.ValidityVisitor.Session
            Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_projection, h_field0]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, initSess, Bool.or]
  rw [h_fuel, h_v0]

theorem validatePlace_mem_zst_step (endian : TargetEndian) (types : List MirTy)
    (c : Choice) (layout : LocalLayout)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_sz0 : layout.layout.size = Size.ZERO)
    (h_vis :
      let initSess :
          Miri.Interpreter.ValidityVisitor.Session
            Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c 8
        initSess ⟨.memory retMemPlace, layout⟩ st = .ok initSess st) :
    Miri.Interpreter.ValidityVisitor.validatePlace
        (refValHooks endian types) c 8
        ⟨.memory retMemPlace, layout⟩ false true st = .ok () st := by
  have h_bp :
      (refValHooks endian types).beginPadding c ⟨retMemPlace, layout⟩
          Size.ZERO st =
        .ok none st := by
    change Miri.Interpreter.ValidityMemory.beginPadding
      (refValidityMemoryEnv endian) ⟨retMemPlace, layout⟩ Size.ZERO st =
      .ok none st
    exact Miri.Interpreter.ValidityMemory.beginPadding_zero
      (refValidityMemoryEnv endian) ⟨retMemPlace, layout⟩ st
      (by
        cases endian <;> cases st with
        | mk stack machine => cases machine; rfl)
  have h_sa :
      (refValHooks endian types).sizeAndAlign c ⟨retMemPlace, layout⟩ st =
        .ok (some (Size.ZERO, layout.layout.align.abi)) st := by
    change
      EStateM.Result.ok (some (layout.layout.size, layout.layout.align.abi))
        st = _
    rw [h_sz0]
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
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [Miri.Interpreter.ValidityVisitor.resetPadding_memory_zero
    (refValHooks endian types) c _ ⟨retMemPlace, layout⟩ st rfl h_sz0 h_sa
    h_bp]
  rfl

theorem validatePlace_mem_scalar_step (endian : TargetEndian)
    (types : List MirTy) (c : Choice)
    (w : IntWidth) (layout : LocalLayout)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lsz : layout.layout.size = toMiriSize w)
    (h_vis :
      let initSess :
          Miri.Interpreter.ValidityVisitor.Session
            Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks endian types) c 8
        initSess ⟨.memory retMemPlace, layout⟩ st =
        .ok { initSess with dataBytes := some (singleDataRange w) } st) :
    Miri.Interpreter.ValidityVisitor.validatePlace
        (refValHooks endian types) c 8
        ⟨.memory retMemPlace, layout⟩ false true st = .ok () st := by
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
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases layout with
  | mk tid ldata =>
    cases ldata with
    | mk fields variants backendRepr largestNiche abiAlign prefAlign sz
        maxReprAlign =>
      dsimp only at h_lsz
      subst h_lsz
      cases endian <;> cases w <;> rfl

end Anneal.MirCorrespondence
