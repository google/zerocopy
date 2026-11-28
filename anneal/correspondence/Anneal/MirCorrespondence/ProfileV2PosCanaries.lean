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
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.LayoutAndAlign
import Anneal.MirCorrespondence.MiriMemoryBridge
import Anneal.MirCorrespondence.ProfileV2RefMachine
import Anneal.MirCorrespondence.ProfileV2Correspondence
import Anneal.MirCorrespondence.ProfileV2Witnesses
import Anneal.MirCorrespondence.ProfileV2EdgeWitnesses
import Anneal.MirCorrespondence.ProfileV2Canaries
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirWp

/-!
# Profile v2 Positive Canaries (`V2_C2`, `c1_m_anneal`, Shared Helpers)
(`Anneal.MirCorrespondence.ProfileV2PosCanaries`)

Proves end-to-end lockstep agreement between Anneal Profile v2 (`evalStepV2` /
`CallerMemory`) and `ProfileV2RefMachine` on `V2_C2` (offset + caller memory
load/cast/write), proves the Anneal side (`c1_m_anneal`) of `V2_C1` (slice
split), and provides shared stepping and validity-mirror helpers used by
`ProfileV2PosCanariesC1`.
-/

/-! ## Section 1: Shared Evaluation Helpers for Positive Canaries -/

/-- Extract the payload of an `Except` known (by evaluation) to be `.ok`. -/
def exceptOkGet {ε α : Type} : ∀ (r : Except ε α),
    (match r with | .ok _ => true | .error _ => false) = true → α
  | .ok a, _ => a
  | .error _, h => nomatch h

/-- An `.ok`-certified `Except` equals `.ok` of its extracted payload. -/
theorem exceptOkGet_eq {ε α : Type} (r : Except ε α)
    (h : (match r with | .ok _ => true | .error _ => false) = true) :
    r = .ok (exceptOkGet r h) := by
  cases r with
  | ok a => rfl
  | error e => exact nomatch h

/-- Whether an `EStateM.Result` is `.ok`. -/
def estateIsOk {ε σ α : Type} : EStateM.Result ε σ α → Bool
  | .ok _ _ => true
  | .error _ _ => false

/-- Extract the final state of an `EStateM.Result` known to be `.ok`. -/
def estateOkGet {ε σ α : Type} : ∀ (r : EStateM.Result ε σ α),
    estateIsOk r = true → σ
  | .ok _ s, _ => s
  | .error _ _, h => nomatch h

/-- An `.ok`-certified `EStateM.Result` equals `.ok ()` of its extracted state.
-/
theorem estateOkGet_eq {ε σ : Type} (r : EStateM.Result ε σ Unit)
    (h : estateIsOk r = true) : r = .ok () (estateOkGet r h) := by
  cases r with
  | ok a s => rfl
  | error e s => exact nomatch h

/-- A zero-filled uninitialized `Allocation.tryNew` result equals the concrete
`writeUninit` image `x` of the corresponding `fromBytes` allocation (all
hypotheses are closed evaluations). -/
theorem tryNew_eq_of_image_v2 (sz : Miri.ABI.Size) (al : Miri.ABI.Align)
    (ab : UInt64)
    (init x : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (hab : al.bytes = .ok ab) (hna : Miri.ABI.Align.fromBytes ab = .ok al)
    (h_nz : sz.bytes ≠ 0)
    (h_fb : Miri.Memory.Allocation.fromBytes
      (Array.replicate sz.bytes.toNat 0) al .Mut = .ok init)
    (h_wu : Miri.Memory.Allocation.writeUninit
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) (Miri.ABI.Size.ofBytes 8)
      init = .ok () x) :
    Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance) sz al
      .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok x := by
  let ⟨a, h_ok, _⟩ :=
    Miri.Memory.Allocation.tryNew_exists (P := Miri.Memory.Provenance)
      sz al ab .Uninit hab hna
  let ⟨_, init', h_fb', h_wu'⟩ :=
    Miri.Memory.Allocation.tryNew_uninit_image sz al (Miri.ABI.Size.ofBytes 8)
      a (by decide) h_ok
  rw [h_fb] at h_fb'
  injection h_fb' with h_i
  subst h_i
  rw [h_wu, ite_not_eq_false _ _ h_nz] at h_wu'
  injection h_wu' with _ h_x
  rw [h_ok, h_x]

private theorem bool_eq_false_of_ite {α : Type} {b : Bool} {t e target : α}
    (h : (if b = true then t else e) = target) (h_ne : t ≠ target) :
    b = false := by
  cases b with
  | true => exact absurd h h_ne
  | false => rfl

private theorem except_eq_ok_of_match1 {α : Type}
    {x : Except Miri.Interpreter.MemoryOperandError Unit}
    {f_err : Miri.Interpreter.MemoryOperandError → Id α}
    {f_ok : Unit → Id α} {target : α}
    (h : Miri.Interpreter.writeImmediateToMplaceNoValidate.match_1
        (fun _ => Id α) x f_err f_ok = target)
    (h_no_err : ∀ e, f_err e ≠ target) :
    x = .ok () := by
  cases x with
  | error e => exact absurd h (h_no_err e)
  | ok u => cases u; rfl

/-- A successful typed `readImmediate` determines the underlying raw read. -/
theorem readImmediateRaw_of_readImmediate_v2 {P E K H X : Type}
    [DecidableEq K] [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (memory m' : Miri.Memory.MemoryState P E K) (hooks h' : H)
    (op : Miri.Interpreter.Operand P)
    (lay : Miri.Interpreter.MemoryOperandLayout)
    (rt : Miri.ABI.RuntimeTargetDataLayout) (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (t : Option (Miri.Memory.AllocationAccessRef P E))
    (v : Miri.Interpreter.ImmediateValue P)
    (h : Miri.Interpreter.readImmediate memory hooks op lay rt ghost kind
      global access dynamic = ⟨m', h', t, .ok v⟩) :
    Miri.Interpreter.readImmediateRaw memory hooks op lay rt ghost kind
      global access dynamic = ⟨m', h', t, .ok (.immediate v)⟩ := by
  dsimp only [Miri.Interpreter.readImmediate, Id.run, bind, Bind.bind, pure,
    Pure.pure] at h
  have h_pr := bool_eq_false_of_ite h (fun hh => by cases hh)
  rw [h_pr] at h
  simp only [Bool.false_eq_true, ite_false] at h
  revert h
  cases Miri.Interpreter.readImmediateRaw memory hooks op lay rt ghost kind
    global access dynamic with
  | mk rm rh rtc ro =>
    intro h
    dsimp only at h
    cases ro with
    | error e => cases h
    | ok x =>
      cases x with
      | place p => cases h
      | immediate value =>
        dsimp only at h
        cases value with
        | mk val valLay =>
          dsimp only at h
          cases val with
          | uninit => cases h
          | scalar s => cases h; rfl
          | scalarPair a b => cases h; rfl

/-- Step `MachineHooks.run` past an `.ok` prefix action under one bind. -/
theorem mhRun_bind_ok {K U α β : Type}
    {x : Miri.Interpreter.MachineHooks.M K U α}
    {f : α → Miri.Interpreter.MachineHooks.M K U β} {a : α}
    {s s₁ : Miri.Interpreter.MachineHooks.State K U} (h : x s = .ok a s₁) :
    Miri.Interpreter.MachineHooks.run (EStateM.bind x f) s =
      Miri.Interpreter.MachineHooks.run (f a) s₁ := by
  dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
    EStateM.bind]
  rw [h]

/-- Step `MachineHooks.run` past an `.ok` prefix action under two binds. -/
theorem mhRun_bind2_ok {K U α β γ : Type}
    {x : Miri.Interpreter.MachineHooks.M K U α}
    {f : α → Miri.Interpreter.MachineHooks.M K U β}
    {g : β → Miri.Interpreter.MachineHooks.M K U γ} {a : α}
    {s s₁ : Miri.Interpreter.MachineHooks.State K U} (h : x s = .ok a s₁) :
    Miri.Interpreter.MachineHooks.run (EStateM.bind (EStateM.bind x f) g) s =
      Miri.Interpreter.MachineHooks.run (EStateM.bind (f a) g) s₁ := by
  dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
    EStateM.bind]
  rw [h]

/-- Step `MachineHooks.run` past an `.ok` prefix action under three binds. -/
theorem mhRun_bind3_ok {K U α β γ δ : Type}
    {x : Miri.Interpreter.MachineHooks.M K U α}
    {f : α → Miri.Interpreter.MachineHooks.M K U β}
    {g : β → Miri.Interpreter.MachineHooks.M K U γ}
    {k : γ → Miri.Interpreter.MachineHooks.M K U δ} {a : α}
    {s s₁ : Miri.Interpreter.MachineHooks.State K U} (h : x s = .ok a s₁) :
    Miri.Interpreter.MachineHooks.run
        (EStateM.bind (EStateM.bind (EStateM.bind x f) g) k) s =
      Miri.Interpreter.MachineHooks.run
        (EStateM.bind (EStateM.bind (f a) g) k) s₁ := by
  dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
    EStateM.bind]
  rw [h]

/-- `u8` scalar write through a mutable place access that may reorder the
live rows (`memory'`). -/
theorem writeImmediate_scalar_u8_at_v2' {P E K H X : Type}
    [DecidableEq K] [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (memory memory' afterMemory : Miri.Memory.MemoryState P E K) (hooks : H)
    (mplace : Miri.Interpreter.MemPlace P) (tyId : Option Nat)
    (s : Bool) (vr : Miri.ABI.WrappingRange) (bits : BitVec 128)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (later : Miri.Interpreter.MemoryOperandLayout → Bool)
    (ref : Miri.Memory.AllocationAccessRef P E)
    (rng : Miri.Memory.AllocRange)
    (after : Miri.Memory.Allocation P E)
    (actual : Miri.Interpreter.getPlaceAllocMut memory hooks
        ⟨mplace, ⟨Miri.ABI.Size.ofBytes 1, Miri.ABI.Align.ONE,
          .Scalar (.Initialized (value := .Int .I8 s)
            (validRange := vr)), tyId⟩⟩
        refRuntimeLayoutV2 ghost kind global access dynamic =
      ⟨memory', hooks, some ref, .ok (some ref)⟩)
    (selected : ref.range.subrange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (Miri.ABI.Size.ofBytes 1)) = .ok rng)
    (written : ref.allocation.writeScalar refRuntimeLayoutV2.base rng
      (.fromScalarInt (miriScalar .i8 bits)) = .ok () after)
    (committed :
      memory'.setLiveAllocation ref.allocId after = .ok afterMemory) :
    Miri.Interpreter.writeImmediateToMplaceNoValidate memory hooks
        (.scalar (.fromScalarInt (miriScalar .i8 bits)))
        ⟨mplace, ⟨Miri.ABI.Size.ofBytes 1, Miri.ABI.Align.ONE,
          .Scalar (.Initialized (value := .Int .I8 s)
            (validRange := vr)), tyId⟩⟩
        refRuntimeLayoutV2 ghost kind global access dynamic later =
      ⟨afterMemory, hooks, some { ref with allocation := after }, .ok ()⟩ := by
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure]
  rw [actual]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  change (match (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
      (ref.range.subrange (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (Miri.ABI.Size.ofBytes 1)))) with
    | Except.ok range => _
    | Except.error error => _) = _
  rw [selected]
  dsimp only [Except.mapError, pure, Pure.pure, Id.run]
  change (match (memory'.setLiveAllocation ref.allocId
      (match Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base rng
          (.fromScalarInt (miriScalar .i8 bits)) ref.allocation with
       | EStateM.Result.ok _ a => a
       | EStateM.Result.error _ a => a)) with
    | Except.ok next => _
    | Except.error error => _) = _
  rw [written]
  dsimp only
  rw [committed]
  rfl

/-- `u8` variant of `readImmediate_mem_u32_v2`. -/
theorem readImmediate_mem_u8_v2 (types : List MirTy)
    (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (aid : Miri.Memory.AllocId) (alloc : RefMiriAlloc)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (st : RefMiriState) (mem1 : RefMiriMem)
    (off : Miri.ABI.Size) (ghost : Bool)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_aln : mplace.misaligned = none)
    (h_ga :
      Miri.Memory.AllocationAccess.getPtrAlloc st.machine.memory
          ⟨st.machine, none⟩ ⟨Miri.ABI.Size.ofBytes 8⟩ mplace.ptr
          (Miri.ABI.Size.ofBytes 1) ghost none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
        ⟨mem1, ⟨st.machine, none⟩,
          some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1),
            alloc⟩,
          .ok (some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1),
            alloc⟩)⟩)
    (h_sub : (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1)).subrange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1)) =
      .ok (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1)))
    (h_rd : alloc.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1)) false = .ok sc) :
    let lay := refLocalLayoutForTyV2 types u8Ty
    let lml := Miri.Interpreter.localMemoryLayout lay
    Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect mplace) lml refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1), alloc⟩,
        .ok ⟨.scalar sc, lml⟩⟩ := by
  intro lay lml
  let rng := Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 1)
  let mplaceTy : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨mplace, ⟨Miri.ABI.Size.ofBytes 1, ⟨0⟩,
      .Scalar (.Initialized (value := .Int .I8 false)
        (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 1))),
      some lay.ty⟩⟩
  have h_lml : lml = mplaceTy.layout := rfl
  have h_gpl := getPlaceAlloc_sized_of_access_v2' st.machine.memory mem1
    ⟨st.machine, none⟩ mplaceTy ghost none cfg.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout
    ⟨aid, rng, alloc⟩ rfl h_aln h_ga
  have h_raw_m :
      Miri.Interpreter.readImmediateFromMplaceRaw st.machine.memory
        ⟨st.machine, none⟩ mplaceTy refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩, some ⟨aid, rng, alloc⟩,
        .ok (some ⟨.scalar sc, mplaceTy.layout⟩)⟩ := by
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_gpl]
    dsimp only [mplaceTy, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.bind
        (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
          (rng.subrange (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (Miri.ABI.Size.ofBytes 1))))
        (fun range =>
          Except.mapError Miri.Interpreter.MemoryOperandError.allocation
            (alloc.readScalar refRuntimeLayoutV2.base range false))) _ _ = _
    rw [h_sub]
    dsimp only [Except.mapError, Except.bind]
    rw [h_rd]
  rw [h_lml]
  dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [h_raw_m]
  rfl

/-- Thin-pointer variant of `readImmediate_mem_u32_v2` (reads provenance). -/
theorem readImmediate_mem_ptr_v2 (tyId : TyId)
    (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (aid : Miri.Memory.AllocId) (alloc : RefMiriAlloc)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (st : RefMiriState) (mem1 : RefMiriMem)
    (off : Miri.ABI.Size) (ghost : Bool)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_aln : mplace.misaligned = none)
    (h_ga :
      Miri.Memory.AllocationAccess.getPtrAlloc st.machine.memory
          ⟨st.machine, none⟩ ⟨Miri.ABI.Size.ofBytes 8⟩ mplace.ptr
          (Miri.ABI.Size.ofBytes 8) ghost none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
        ⟨mem1, ⟨st.machine, none⟩,
          some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8),
            alloc⟩,
          .ok (some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8),
            alloc⟩)⟩)
    (h_sub : (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)).subrange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
      .ok (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)))
    (h_rd : alloc.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)) true = .ok sc) :
    let lay : Miri.Interpreter.LocalLayout := ⟨tyId, refThinPtrLayoutDataV2⟩
    let lml := Miri.Interpreter.localMemoryLayout lay
    Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect mplace) lml refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8), alloc⟩,
        .ok ⟨.scalar sc, lml⟩⟩ := by
  intro lay lml
  let rng := Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)
  let mplaceTy : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨mplace, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
      .Scalar (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
        (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8))),
      some lay.ty⟩⟩
  have h_lml : lml = mplaceTy.layout := rfl
  have h_gpl := getPlaceAlloc_sized_of_access_v2' st.machine.memory mem1
    ⟨st.machine, none⟩ mplaceTy ghost none cfg.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout
    ⟨aid, rng, alloc⟩ rfl h_aln h_ga
  have h_raw_m :
      Miri.Interpreter.readImmediateFromMplaceRaw st.machine.memory
        ⟨st.machine, none⟩ mplaceTy refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩, some ⟨aid, rng, alloc⟩,
        .ok (some ⟨.scalar sc, mplaceTy.layout⟩)⟩ := by
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_gpl]
    dsimp only [mplaceTy, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.bind
        (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
          (rng.subrange (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (Miri.ABI.Size.ofBytes 8))))
        (fun range =>
          Except.mapError Miri.Interpreter.MemoryOperandError.allocation
            (alloc.readScalar refRuntimeLayoutV2.base range true))) _ _ = _
    rw [h_sub]
    dsimp only [Except.mapError, Except.bind]
    rw [h_rd]
  rw [h_lml]
  dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [h_raw_m]
  rfl

/-- A successful place write started from the reordered memory `memory'` is
also the result of the same write started from `memory`, when the mutable
access merely reorders the live rows. -/
theorem writeImmediateToMplace_reorder_v2 {P E K H X : Type}
    [DecidableEq K] [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (memory memory' after : Miri.Memory.MemoryState P E K) (hooks : H)
    (value : Miri.Interpreter.Immediate P)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (runtime : Miri.ABI.RuntimeTargetDataLayout) (ghost : Bool)
    (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (later : Miri.Interpreter.MemoryOperandLayout → Bool)
    (ref : Miri.Memory.AllocationAccessRef P E)
    (touched : Option (Miri.Memory.AllocationAccessRef P E))
    (h1 : Miri.Interpreter.getPlaceAllocMut memory hooks place runtime ghost
      kind global access dynamic = ⟨memory', hooks, some ref, .ok (some ref)⟩)
    (h2 : Miri.Interpreter.getPlaceAllocMut memory' hooks place runtime ghost
      kind global access dynamic =
      ⟨memory', hooks, some ref, .ok (some ref)⟩)
    (h_ok : Miri.Interpreter.writeImmediateToMplaceNoValidate memory' hooks
      value place runtime ghost kind global access dynamic later =
      ⟨after, hooks, touched, .ok ()⟩) :
    Miri.Interpreter.writeImmediateToMplaceNoValidate memory hooks value place
        runtime ghost kind global access dynamic later =
      ⟨after, hooks, touched, .ok ()⟩ := by
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure] at h_ok
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure]
  have h_uns := bool_eq_false_of_ite h_ok (fun hh => by cases hh)
  rw [h_uns] at h_ok
  rw [h_uns]
  simp only [Bool.false_eq_true, ite_false] at h_ok
  simp only [Bool.false_eq_true, ite_false]
  have h_ima := except_eq_ok_of_match1 h_ok (fun _ hh => by cases hh)
  rw [h_ima] at h_ok
  rw [h_ima]
  dsimp only at h_ok
  dsimp only
  rw [h2] at h_ok
  rw [h1]
  exact h_ok

section ValidityMirror

open Miri.ABI Miri.Memory Miri.Memory.Validity Miri.Interpreter
open Miri.Interpreter.ValidityVisitor

variable {P S C E F A Pad : Type}

/-- Public mirror of the private `ValidityVisitor.liftResult`. -/
def refLiftResultMirror {A : Type} (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Public mirror of the private `ValidityVisitor.resetPadding`. -/
def refResetPaddingMirror (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (place : RuntimePlace P) : M S Unit :=
  match session.dataBytes with
  | some ranges =>
    Bind.bind (forceAllocation h.projection.place c place) (fun memory =>
      Bind.bind (h.sizeAndAlign c memory) (fun dynamic =>
        have size :=
          (dynamic.getD
            (memory.layout.layout.size, memory.layout.layout.align.abi)).1
        have start := memory.mplace.ptr.offset
        if ranges.toArray == [allocRange start size].toArray then
          pure ()
        else
          Bind.bind (h.beginPadding c memory size) (fun optHandle =>
            match optHandle with
            | some handle =>
              Bind.bind
                (refLiftResultMirror ((paddingWrites ranges start size).mapError
                  (fun error =>
                    .invalidProgram
                      (toString "padding: " ++ toString (repr error)))))
                (fun writes =>
                  Bind.bind
                    (forIn writes PUnit.unit (fun range _ =>
                      Bind.bind (h.writePadding c handle range) (fun _ =>
                        pure (ForInStep.yield PUnit.unit))))
                    (fun _ => pure ()))
            | _ => pure ())))
  | _ => pure ()

/-- Root traversal prefix of `ValidityVisitor.validatePlace`: returns the
visited root `Session`. -/
def refValidatePreMirror [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (place : RuntimePlace P)
    (recursive reset : Bool) : M S (Session P) :=
  Bind.bind (h.typeName c place.layout.ty) (fun name =>
    have initial : Session P := {
      path := ⟨name, [].toArray⟩, flags := ⟨reset, false⟩, ctfeMode := none,
      refTracking := if recursive then some .empty else none,
      dataBytes := none }
    h.withGhostValidation
      (have session := initial
      have jp : Unit → Session P → M S (Session P) := fun _ session =>
        Bind.bind (visit h c fuel session place) (fun session =>
          Bind.bind (refResetPaddingMirror h c session place) (fun _ =>
            pure session))
      if reset then
        Bind.bind (h.toOp c place) (fun opTy =>
          match opTy.op with
          | .indirect _ => jp () { session with dataBytes := some .empty }
          | _ => jp () session)
      else
        jp () session))

/-- Tracked-pointee worklist suffix of `ValidityVisitor.validatePlace`. -/
def refValidatePostMirror [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (recursive : Bool)
    (session : Session P) : M S Unit :=
  have session := session
  if recursive then
    have remaining := fuel
    have continueLoop := true
    Bind.bind
      (forIn Lean.Loop.mk (session, remaining, continueLoop)
        (fun _ s =>
          have session := s.1
          have remaining := s.2.1
          have continueLoop := s.2.2
          if continueLoop then
            match session.refTracking.bind RefTracking.next with
            | none =>
              have continueLoop := false
              pure (ForInStep.yield (session, remaining, continueLoop))
            | some ((key, path), tracking) =>
              have jp : Unit → M S (ForInStep (Session P × Nat × Bool)) :=
                fun _ =>
                  have remaining := remaining - 1
                  have session := { session with refTracking := some tracking }
                  have childSession : Session P := {
                    path, flags := ⟨false, true⟩, ctfeMode := none,
                    refTracking := none, dataBytes := none }
                  Bind.bind
                    (h.withGhostValidation
                      (have child : RuntimePlace P :=
                        ⟨.memory key.mplace, key.layout⟩
                      Bind.bind (visit h c fuel childSession child)
                        (fun visited => refResetPaddingMirror h c visited child)))
                    (fun _ =>
                      pure (ForInStep.yield (session, remaining, continueLoop)))
              if remaining == 0 then
                Bind.bind
                  (throw (.resourceExhaustion "recursive validity tracker fuel"))
                  jp
              else
                jp ()
          else
            pure (ForInStep.done (session, remaining, continueLoop))))
      (fun _ => pure ())
  else
    pure ()

end ValidityMirror

/-- `validatePlace` on `refValHooksV2` splits into the mirrored root traversal
followed by the mirrored tracked-pointee worklist. -/
theorem refValidatePlace_split_v2 (types : List MirTy) (fuel : Nat)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (st : RefMiriState) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types) 0 fuel
        place true true st =
      EStateM.bind
        (refValidatePreMirror (refValHooksV2 types) 0 fuel place true true)
        (refValidatePostMirror (refValHooksV2 types) 0 fuel true) st := rfl

/-- The mirrored worklist exits immediately when no tracked pointee is pending.
-/
theorem refValidatePost_done_v2 (types : List MirTy) (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (st : RefMiriState)
    (h_next : sess.refTracking.bind Miri.Memory.Validity.RefTracking.next =
      none) :
    refValidatePostMirror (refValHooksV2 types) 0 fuel true sess st =
      .ok () st := by
  dsimp only [refValidatePostMirror, bind, Bind.bind, pure, Pure.pure]
  rw [ite_true_eq, eStateM_loop_forIn_eq st]
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
  rw [h_next]
  dsimp only
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_loop_forIn_eq st, ite_false_eq]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_bind_pure]
  rfl

/-- Root validation succeeds once the mirrored root traversal evaluates to a
session with no pending tracked pointee. -/
theorem refValidatePlace_of_pre_v2 (types : List MirTy)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (st st1 : RefMiriState)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (h_pre : refValidatePreMirror (refValHooksV2 types) 0 16 place true true
      st = .ok sess st1)
    (h_next : sess.refTracking.bind Miri.Memory.Validity.RefTracking.next =
      none) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types) 0 16
        place true true st = .ok () st1 := by
  rw [refValidatePlace_split_v2]
  exact eStateM_apply_bind _ _ sess st st1 h_pre
    (refValidatePost_done_v2 types 16 sess st1 h_next)

/-- One `Assign` step whose evaluation reduces to a final root validation of
`dp` in `stW`, which itself evaluates to `st'` with no pending pointee. -/
theorem execStep_assign_val_v2 (rp : RefProg) (st stW st' : RefMiriState)
    (frame frame' : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (bbId : BasicBlockId) (sIdx : Nat)
    (block : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement)
    (mirDst : Miri.MIR.Place) (mirRv : Miri.MIR.Rvalue)
    (dp : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = some stmt)
    (h_kind : stmt.kind = .Assign mirDst mirRv)
    (h_run : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 mirDst mirRv st =
      Miri.Interpreter.MachineHooks.run
        (Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 rp.types)
          0 16 dp true true) stW)
    (h_pre : refValidatePreMirror (refValHooksV2 rp.types) 0 16 dp true true
      stW = .ok sess st')
    (h_next : sess.refTracking.bind Miri.Memory.Validity.RefTracking.next =
      none)
    (h_fr' : st'.stack.frames = Array.mk [frame'])
    (h_loc' : frame'.location = .mir ⟨bbId, sIdx⟩) :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 st =
      ({ st' with
          stack :=
            ⟨Array.mk [{ frame' with location := .mir ⟨bbId, sIdx + 1⟩ }]⟩
          machine := { st'.machine with pendingMoveDeinit := false } },
        .ok true) := by
  have h_val := refValidatePlace_of_pre_v2 rp.types dp stW st' sess h_pre h_next
  have h_ass : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 mirDst mirRv st =
      (st', .ok ()) := by
    rw [h_run]
    dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [h_val]
  exact execStep_assign_ok rp st st' frame frame' bbId sIdx block stmt mirDst
    mirRv h_pmd h_fr h_loc h_bb h_st h_kind h_ass h_fr' h_loc'

/-! ## Section 2: `V2_C2` (`BinOp.offset` + caller memory load/cast/write) -/

/-- Fresh Tree Borrows tree (root tag `BorTag.one`) over `n` bytes. -/
noncomputable def c2Tree (n : UInt64) : Miri.TreeBorrows.BorrowTree :=
  Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
    (Miri.ABI.Size.ofBytes n)

/-- Concrete read-only caller allocation `alloc2` of `V2_C2`. -/
noncomputable def c2A2 : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes
    (Array.mk [1, 0, 0, 0, 0xAA, 0, 0, 0]) ⟨2⟩ .Not) rfl

/-- Concrete mutable caller allocation `alloc3` of `V2_C2` (pre-state). -/
noncomputable def c2A3 : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes
    (Array.mk [1, 2, 3, 4]) ⟨0⟩ .Mut) rfl

/-- One row of the reference memory's `live` table. -/
abbrev RefLiveRow := Miri.Memory.AllocId ×
  Miri.Memory.LocalAllocation Miri.Memory.Provenance
    Miri.TreeBorrows.BorrowTree Unit

/-- `V2_C2` reference memory with live rows `live`. -/
noncomputable def c2Mem (live : Array RefLiveRow) : RefMiriMem :=
  ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
      nextAllocId := 4, live := live
    }).setIssuedIds (Array.mk [alloc2IdV2, alloc3IdV2, retAllocIdV2])

/-- Encoded `V2_C2` program. -/
noncomputable abbrev c2Rp : RefProg := encodeProg progV2_C2_offsetWrite
/-- Entry body of the encoded `V2_C2` program. -/
noncomputable abbrev c2Body : RefBody :=
  @GetElem.getElem _ Nat _ _ _ c2Rp.bodies 0 (by decide)
/-- Local layout of `*const u32` in `V2_C2`. -/
noncomputable abbrev c2PtrC :=
  refLocalLayoutForTyV2 c2Rp.types (.rawPtr .shared u32Ty)
/-- Local layout of `*mut u8` in `V2_C2`. -/
noncomputable abbrev c2PtrM :=
  refLocalLayoutForTyV2 c2Rp.types (.rawPtr .mut u8Ty)
/-- Local layout of `u32` in `V2_C2`. -/
noncomputable abbrev c2U32 := refLocalLayoutForTyV2 c2Rp.types u32Ty
/-- Local layout of `u8` in `V2_C2`. -/
noncomputable abbrev c2U8 := refLocalLayoutForTyV2 c2Rp.types u8Ty

/-- Pointer into allocation `id` at byte offset `off` with the root tag. -/
noncomputable def c2P (id : Miri.Memory.AllocId) (off : UInt64) :
    Miri.Memory.Pointer Miri.Memory.Provenance :=
  ⟨Miri.ABI.Size.ofBytes off, .concrete id Miri.Memory.BorTag.one⟩

/-- Thin-pointer immediate for `c2P id off`. -/
noncomputable def c2Ptr (id : Miri.Memory.AllocId) (off : UInt64) :
    Miri.Interpreter.Immediate Miri.Memory.Provenance :=
  .scalar (.fromPointer refRuntimeLayoutV2.base (c2P id off))

/-- Integer immediate of width `w` holding `n`. -/
noncomputable def c2Int (w : IntWidth) (n : Nat) :
    Miri.Interpreter.Immediate Miri.Memory.Provenance :=
  .scalar (.fromScalarInt (miriScalar w (BitVec.ofNat 128 n)))

/-- `V2_C2` locals with `_0`, `_3`, `_4`, `_5` holding `i0`, `i3`, `i4`, `i5`.
-/
noncomputable def c2Locals
    (i0 i3 i4 i5 : Miri.Interpreter.Immediate Miri.Memory.Provenance) :
    List RefLocalState :=
  [⟨.live (.immediate i0), some c2PtrC⟩,
   ⟨.live (.immediate (c2Ptr alloc2IdV2 0)), some c2PtrC⟩,
   ⟨.live (.immediate (c2Ptr alloc3IdV2 1)), some c2PtrM⟩,
   ⟨.live (.immediate i3), some c2PtrC⟩,
   ⟨.live (.immediate i4), some c2U32⟩,
   ⟨.live (.immediate i5), some c2U8⟩]

/-- Root frame of `V2_C2` at statement `idx` of block `0`. -/
noncomputable def c2Frame (idx : Nat) (locals : List RefLocalState) :=
  mkRefMiriFrameV2 c2Rp.types 0 c2Body 0 idx locals ⟨retMemPlaceV2, c2PtrC⟩

/-- `V2_C2` reference state at statement `idx` of block `0`. -/
noncomputable def c2St (idx : Nat) (locals : List RefLocalState)
    (mem : RefMiriMem) : RefMiriState :=
  mkRefMiriState (c2Frame idx locals) mem refInitControl callerMemV2_C2_pre

/-- Lowered basic block `0` of `V2_C2`. -/
noncomputable abbrev c2Block : Miri.MIR.BasicBlock :=
  toMiriBasicBlockV2 c2Rp.types
    (@GetElem.getElem _ Nat _ _ _ c2Body.basicBlocks 0 (by decide))

/-- Lowered statement `i` of block `0` of `V2_C2`. -/
noncomputable abbrev c2Stmt (i : Nat) (h : i < 5 := by decide) :
    Miri.MIR.Statement :=
  toMiriStatementV2 c2Rp.types
    (@GetElem.getElem _ Nat _ _ _
      (@GetElem.getElem _ Nat _ _ _ c2Body.basicBlocks 0 (by decide)).statements
      i h)

/-- Runtime place of local `i` (layout `lay`) in the root frame of `V2_C2`. -/
noncomputable abbrev c2Local (i : Nat) (locals : List RefLocalState)
    (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.local 0 i none (c2Frame 0 locals).localsIdentity, lay⟩

/-- Concrete zero-filled uninitialized 8-byte return buffer of `V2_C2`. -/
noncomputable def c2Ret : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  estateOkGet (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
    (Miri.ABI.Size.ofBytes 8)
    (exceptOkGet (Miri.Memory.Allocation.fromBytes
      (Array.replicate 8 0) Miri.ABI.Align.EIGHT .Mut) rfl)) rfl

/-- `tryNew` of the 8-byte return buffer yields exactly `c2Ret`. -/
theorem c2Ret_tryNew :
    Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok c2Ret :=
  tryNew_eq_of_image_v2 (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT 8 _ _
    rfl rfl (by decide) (exceptOkGet_eq _ rfl) rfl

/-- Initial live rows of `V2_C2`. -/
noncomputable def c2Live0 : Array RefLiveRow :=
  Array.mk [(alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩),
    (alloc3IdV2, ⟨.machine (), c2A3.withExtra (c2Tree 4)⟩),
    (retAllocIdV2, ⟨.stack, c2Ret.withExtra (c2Tree 8)⟩)]

/-- Entry locals of `V2_C2`. -/
noncomputable def c2L0 := c2Locals .uninit .uninit .uninit .uninit

/-- Locals of `V2_C2` after statement 0. -/
noncomputable def c2L1 :=
  c2Locals .uninit (c2Ptr alloc2IdV2 4) .uninit .uninit

/-- Step 0: `_3 = Offset(copy _1, const 1_isize)`. -/
theorem c2_step0 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c2Rp)
        refLimitsV2 0 (c2St 0 c2L0 (c2Mem c2Live0)) =
      (c2St 1 c2L1 (c2Mem c2Live0), .ok true) :=
  let l1 := c2L1
  let stW := c2St 0 l1 (c2Mem c2Live0)
  execStep_assign_val_v2 c2Rp _ stW stW
    (c2Frame 0 (c2Locals .uninit .uninit .uninit .uninit)) (c2Frame 0 l1) 0 0
    c2Block (c2Stmt 0) ⟨3, Array.empty⟩
    (toMiriRvalueV2 c2Rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
      (.constant ⟨tyIdFor c2Rp.types (.int .isize true),
        .scalar (BitVec.ofNat 128 1)⟩)))
    (c2Local 3 l1 c2PtrC) _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Live rows after the load from `alloc2` (the accessed row moves last). -/
noncomputable def c2Live1 : Array RefLiveRow :=
  Array.mk [(alloc3IdV2, ⟨.machine (), c2A3.withExtra (c2Tree 4)⟩),
    (retAllocIdV2, ⟨.stack, c2Ret.withExtra (c2Tree 8)⟩),
    (alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩)]

/-- Memory place `alloc2 + 4`, the pointee of `_3`. -/
noncomputable def c2A2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨⟨Miri.ABI.Size.ofBytes 4,
    some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩, .none, none⟩

/-- Bytes `4..8` of `alloc2` decode to the `u32` value `0xAA`. -/
theorem c2_read_a2 :
    (c2A2.withExtra (c2Tree 8)).readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4)
        (Miri.ABI.Size.ofBytes 4)) false =
      .ok (.fromScalarInt (miriScalar .i32 (BitVec.ofNat 128 0xAA))) :=
  (Miri.Memory.Allocation.readScalar_int_of_bytes _ refRuntimeLayoutV2.base
    _ (Array.mk [0xAA, 0, 0, 0]) rfl rfl (by decide) (Or.inr rfl)).trans rfl

/-- The raw load of `*_3` reads `0xAA_u32` and moves the `alloc2` row last. -/
theorem c2_readRaw_a2 :
    (refExecCfgV2 c2Rp).copy.readRaw 0 ⟨.indirect c2A2Mp, c2U32⟩
        (c2St 1 c2L1 (c2Mem c2Live0)) =
      .ok (.immediate ⟨c2Int .i32 0xAA,
          Miri.Interpreter.localMemoryLayout c2U32⟩)
        (c2St 1 c2L1 (c2Mem c2Live1)) := by
  let st := c2St 1 c2L1 (c2Mem c2Live0)
  have h_find : st.machine.memory.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩) := rfl
  have h_any : (st.machine.memory.live.any (fun e => e.1 == alloc2IdV2)) =
      true := by
    rw [← Array.any_toList]; rfl
  have h_set : st.machine.memory.setLiveAllocation alloc2IdV2
      (c2A2.withExtra (c2Tree 8)) = .ok (c2Mem c2Live1) := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ h_find]
    rfl
  have h_ga := getPtrAlloc_live_nonghost_v2 c2Rp.types
    (Miri.ABI.Size.ofBytes 4) 4 st.machine.memory (c2Mem c2Live1)
    (.machine ()) (c2A2.withExtra (c2Tree 8)) st.machine alloc2IdV2
    (Miri.ABI.Size.ofBytes 4) c2A2Mp.ptr (.concrete Miri.Memory.BorTag.one)
    h_find h_any h_set rfl (by decide) rfl rfl rfl rfl
  have h_ri := readImmediate_mem_u32_v2 c2Rp.types c2A2Mp alloc2IdV2
    (c2A2.withExtra (c2Tree 8)) _ st (c2Mem c2Live1) (Miri.ABI.Size.ofBytes 4)
    false (refAccessConfigV2 c2Rp.types) rfl h_ga rfl c2_read_a2
  have h_raw := readImmediateRaw_of_readImmediate_v2 _ _ _ _ _ _ _ _ _ _ _ _
    _ _ h_ri
  change Miri.Interpreter.PlaceMachine.readRaw (refAccessConfigV2 c2Rp.types)
    ⟨.indirect c2A2Mp, c2U32⟩ st = _
  dsimp only [Miri.Interpreter.PlaceMachine.readRaw,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [show (refAccessConfigV2 c2Rp.types).ghostMode = false from rfl,
    show (refAccessConfigV2 c2Rp.types).globalKind = none from rfl,
    show (refAccessConfigV2 c2Rp.types).runtime = refRuntimeLayoutV2 from rfl,
    h_raw]
  rfl

/-- Locals of `V2_C2` after statement 1. -/
noncomputable def c2L2 :=
  c2Locals .uninit (c2Ptr alloc2IdV2 4) (c2Int .i32 0xAA) .uninit

/-- Step 1: `_4 = copy (*_3)`. -/
theorem c2_step1 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c2Rp)
        refLimitsV2 0 (c2St 1 c2L1 (c2Mem c2Live0)) =
      (c2St 2 c2L2 (c2Mem c2Live1), .ok true) := by
  let stW := c2St 1 c2L2 (c2Mem c2Live1)
  let rv := toMiriRvalueV2 c2Rp.types (.use (.copy ⟨3, [.deref]⟩))
  have h_run : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 c2Rp) refLimitsV2).assign 0 ⟨4, Array.empty⟩ rv
      (c2St 1 c2L1 (c2Mem c2Live0)) =
      Miri.Interpreter.MachineHooks.run
        (Miri.Interpreter.ValidityVisitor.validatePlace
          (refValHooksV2 c2Rp.types) 0 16 (c2Local 4 c2L2 c2U32) true true)
        stW := by
    change Miri.Interpreter.MachineHooks.run (EStateM.bind (EStateM.bind
      ((refExecCfgV2 c2Rp).copy.readRaw 0 ⟨.indirect c2A2Mp, c2U32⟩) _) _)
      (c2St 1 c2L1 (c2Mem c2Live0)) = _
    rw [mhRun_bind2_ok c2_readRaw_a2]
    rfl
  exact execStep_assign_val_v2 c2Rp _ stW stW (c2Frame 1 c2L1) (c2Frame 1 c2L2)
    0 1 c2Block (c2Stmt 1) ⟨4, Array.empty⟩ rv (c2Local 4 c2L2 c2U32) _
    rfl rfl rfl rfl rfl rfl h_run rfl rfl rfl rfl

/-- Locals of `V2_C2` after statement 2. -/
noncomputable def c2L3 :=
  c2Locals .uninit (c2Ptr alloc2IdV2 4) .uninit (c2Int .i8 0xAA)

/-- Step 2 destination: `_5` evaluates to its local place without changing the
state. -/
private theorem c2_step2_dest :
    (Miri.Interpreter.ExecutionMachine.rvalueHooks
        (Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 c2Rp) refLimitsV2) refLimitsV2).evalPlace
      0 ⟨5, Array.empty⟩ true (c2St 2 c2L2 (c2Mem c2Live1)) =
      .ok (c2Local 5 c2L2 c2U8) (c2St 2 c2L2 (c2Mem c2Live1)) := rfl

/-- Step 2 source: `move _4` reads `0xAA_u32` and leaves `_4` uninitialized. -/
private theorem c2_step2_src :
    (Miri.Interpreter.ExecutionMachine.rvalueHooks
        (Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 c2Rp) refLimitsV2) refLimitsV2).evalOperandAt
      0 (Miri.Interpreter.OperandPath.rvalue "operand")
      (toMiriOperandV2 c2Rp.types (RefOperand.move ⟨4, []⟩)) none
      (c2St 2 c2L2 (c2Mem c2Live1)) =
      .ok ⟨.immediate (c2Int .i32 0xAA), c2U32⟩
        (c2St 2 (c2Locals .uninit (c2Ptr alloc2IdV2 4) .uninit .uninit)
          (c2Mem c2Live1)) := rfl

/-- Step 2 assignment, split at the destination and operand evaluations so
that each definitional check stays small. -/
private theorem c2_step2_run :
    (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 c2Rp) refLimitsV2).assign 0 ⟨5, Array.empty⟩
      (toMiriRvalueV2 c2Rp.types
        (.cast .intToInt (.move ⟨4, []⟩) (tyIdFor c2Rp.types u8Ty)))
      (c2St 2 c2L2 (c2Mem c2Live1)) =
      Miri.Interpreter.MachineHooks.run
        (Miri.Interpreter.ValidityVisitor.validatePlace
          (refValHooksV2 c2Rp.types) 0 16 (c2Local 5 c2L3 c2U8) true true)
        (c2St 2 c2L3 (c2Mem c2Live1)) := by
  dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
    Miri.Interpreter.evalRvalueIntoPlace, toMiriRvalueV2, bind, Bind.bind]
  rw [mhRun_bind_ok c2_step2_dest, mhRun_bind_ok c2_step2_src]
  rfl

/-- Step 2: `_5 = move _4 as u8`. -/
theorem c2_step2 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c2Rp)
        refLimitsV2 0 (c2St 2 c2L2 (c2Mem c2Live1)) =
      (c2St 3 c2L3 (c2Mem c2Live1), .ok true) :=
  let stW := c2St 2 c2L3 (c2Mem c2Live1)
  execStep_assign_val_v2 c2Rp _ stW stW (c2Frame 2 c2L2) (c2Frame 2 c2L3)
    0 2 c2Block (c2Stmt 2) _ _ (c2Local 5 c2L3 c2U8) _
    rfl rfl rfl rfl rfl rfl c2_step2_run rfl rfl rfl rfl

/-- Concrete mutable caller allocation `alloc3` of `V2_C2` (post-state). -/
noncomputable def c2A3w : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes
    (Array.mk [1, 0xAA, 3, 4]) ⟨0⟩ .Mut) rfl

/-- Writing `0xAA_u8` at byte `1` of `alloc3` yields exactly `c2A3w`. -/
theorem c2_write_a3 :
    Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
        (Miri.ABI.Size.ofBytes 1))
      (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 0xAA)))
      (c2A3.withExtra (c2Tree 4)) = .ok () (c2A3w.withExtra (c2Tree 4)) := by
  let ⟨a', h_ws, h_bsz, h_len, h_mut, h_al, h_ex, h_nb, h_x1, h_x2, h_imset,
      h_x3, h_pm, h_gb, h_x4, h_pres⟩ :=
    Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base
      (c2A3.withExtra (c2Tree 4))
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
        (Miri.ABI.Size.ofBytes 1))
      (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 0xAA)))
      (.bits (BitVec.ofNat 128 0xAA)) Miri.Memory.ProvenanceMap.new
      Miri.Memory.ProvenanceMap.new
      rfl rfl rfl trivial (by decide) (by decide) (by decide) rfl
      (fun _ _ => rfl) rfl
  rw [h_ws]
  have h1 := h_gb _ rfl
  have h0 := h_pres
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1))
    (Miri.ABI.Size.ofBytes 1) rfl (by decide) (by decide) (Or.inr (by decide))
  have h2 := h_pres
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 2)
      (Miri.ABI.Size.ofBytes 2))
    (Miri.ABI.Size.ofBytes 4) rfl (by decide) (by decide) (Or.inl (by decide))
  cases a' with
  | _ rb sz pv im al mt ex nb =>
  have e_sz : sz = Miri.ABI.Size.ofBytes 4 := h_bsz
  have e_len : rb.size = 4 := h_len
  have e_mt : mt = .Mut := h_mut
  have e_al : al = ⟨0⟩ := h_al
  have e_ex : ex = c2Tree 4 := h_ex
  have e_nb : nb = none := h_nb
  have e_pv : pv = Miri.Memory.ProvenanceMap.new := h_pm
  have e_im : (Except.ok im : Except Miri.Memory.InitMaskError _) =
      .ok (c2A3w.withExtra (c2Tree 4)).initializationMask := h_imset.symm
  injection e_im with e_im
  subst e_sz e_mt e_al e_ex e_nb e_pv e_im
  cases rb with
  | mk l =>
    cases l with
    | nil =>
      have h04 : ¬ ((0 : Nat) = 4) := by decide
      exact absurd (show (0 : Nat) = 4 from e_len) h04
    | cons b0 l =>
      cases l with
      | nil =>
        have h14 : ¬ ((1 : Nat) = 4) := by decide
        exact absurd (show (1 : Nat) = 4 from e_len) h14
      | cons b1 l =>
        cases l with
        | nil =>
          have h24 : ¬ ((2 : Nat) = 4) := by decide
          exact absurd (show (2 : Nat) = 4 from e_len) h24
        | cons b2 l =>
          cases l with
          | nil =>
            have h34 : ¬ ((3 : Nat) = 4) := by decide
            exact absurd (show (3 : Nat) = 4 from e_len) h34
          | cons b3 l =>
            cases l with
            | cons b4 l =>
              have h5 : l.length + 5 = 4 := e_len
              exact absurd (Nat.le_add_left 5 l.length)
                (by rw [h5]; decide)
            | nil =>
              have g0 : (Except.ok (Array.mk [b0]) :
                  Except Miri.Memory.AllocError _) =
                  .ok (Array.mk [1]) := h0
              have g1 : (Except.ok (Array.mk [b1]) :
                  Except Miri.Memory.AllocError _) =
                  .ok (Array.mk [0xAA]) := h1
              have g2 : (Except.ok (Array.mk [b2, b3]) :
                  Except Miri.Memory.AllocError _) =
                  .ok (Array.mk [3, 4]) := h2
              injection g0 with g0
              injection g1 with g1
              injection g2 with g2
              injection g0 with g0
              injection g1 with g1
              injection g2 with g2
              injection g0 with g0
              injection g1 with g1
              injection g2 with g2 g2'
              injection g2' with g2'
              subst g0 g1 g2 g2'
              rfl

/-- Locals of `V2_C2` after statement 3. -/
noncomputable def c2L4 := c2Locals .uninit (c2Ptr alloc2IdV2 4) .uninit .uninit

/-- Live rows after the store to `alloc3` (the accessed row moves last). -/
noncomputable def c2Live3 : Array RefLiveRow :=
  Array.mk [(retAllocIdV2, ⟨.stack, c2Ret.withExtra (c2Tree 8)⟩),
    (alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩),
    (alloc3IdV2, ⟨.machine (), c2A3w.withExtra (c2Tree 4)⟩)]

/-- Memory place `alloc3 + 1`, the pointee of `_2`. -/
noncomputable def c2A3Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨⟨Miri.ABI.Size.ofBytes 1,
    some (.concrete alloc3IdV2 Miri.Memory.BorTag.one)⟩, .none, none⟩

/-- The store `*_2 = 0xAA_u8` updates `alloc3` and moves its row last. -/
theorem c2_writeMem_a3 :
    Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 c2Rp.types)
        (fun _ => true) (c2Int .i8 0xAA) ⟨c2A3Mp, c2U8⟩
        (c2St 3 c2L4 (c2Mem c2Live1)) =
      .ok () (c2St 3 c2L4 (c2Mem c2Live3)) := by
  let st := c2St 3 c2L4 (c2Mem c2Live1)
  let a := c2A3.withExtra (c2Tree 4)
  let rng := Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
    (Miri.ABI.Size.ofBytes 1)
  have h_find : st.machine.memory.live.find? (fun e => e.1 == alloc3IdV2) =
      some (alloc3IdV2, ⟨.machine (), a⟩) := rfl
  have h_any : (st.machine.memory.live.any (fun e => e.1 == alloc3IdV2)) =
      true := by
    rw [← Array.any_toList]; rfl
  let mem' : RefMiriMem := c2Mem
    (Array.mk [(retAllocIdV2, ⟨.stack, c2Ret.withExtra (c2Tree 8)⟩),
      (alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩),
      (alloc3IdV2, ⟨.machine (), a⟩)])
  have h_set : st.machine.memory.setLiveAllocation alloc3IdV2 a = .ok mem' := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ h_find]
    rfl
  have h_ga := getPtrAllocMut_live_nonghost_v2 c2Rp.types
    (Miri.ABI.Size.ofBytes 1) 1 st.machine.memory mem' (.machine ()) a
    st.machine alloc3IdV2 (Miri.ABI.Size.ofBytes 1) c2A3Mp.ptr
    (.concrete Miri.Memory.BorTag.one) h_find rfl h_any h_set rfl (by decide)
    rfl rfl rfl rfl
  have h_ga' : Miri.Memory.AllocationAccess.getPtrAllocMut st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      ⟨Miri.ABI.Size.ofBytes 8⟩ c2A3Mp.ptr (Miri.ABI.Size.ofBytes 1) false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks
        (refAccessConfigV2 c2Rp.types)) =
      ⟨mem', ⟨st.machine, none⟩, some ⟨alloc3IdV2, rng, a⟩,
        .ok (some ⟨alloc3IdV2, rng, a⟩)⟩ := h_ga
  have h_pl : Miri.Interpreter.getPlaceAllocMut st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      ⟨c2A3Mp, ⟨Miri.ABI.Size.ofBytes 1, Miri.ABI.Align.ONE,
        .Scalar (.Initialized (value := .Int .I8 false)
          (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 1))),
        some c2U8.ty⟩⟩
      refRuntimeLayoutV2 false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout =
      ⟨mem', ⟨st.machine, none⟩, some ⟨alloc3IdV2, rng, a⟩,
        .ok (some ⟨alloc3IdV2, rng, a⟩)⟩ :=
    getPlaceAllocMut_sized_of_access_v2' _ _ _ _ _ _ _ _ _ _ rfl rfl h_ga'
  have h_set' : mem'.setLiveAllocation alloc3IdV2
      (c2A3w.withExtra (c2Tree 4)) = .ok (c2Mem c2Live3) := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find mem' alloc3IdV2
      ⟨.machine (), a⟩ _ rfl]
    rfl
  have h_w : Miri.Interpreter.writeImmediateToMplaceNoValidate
      st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      (c2Int .i8 0xAA) ⟨c2A3Mp, Miri.Interpreter.localMemoryLayout c2U8⟩
      (refAccessConfigV2 c2Rp.types).runtime
      (refAccessConfigV2 c2Rp.types).ghostMode
      (refAccessConfigV2 c2Rp.types).globalKind
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout (fun _ => true) =
      ⟨c2Mem c2Live3, ⟨st.machine, none⟩,
        some ⟨alloc3IdV2, rng, c2A3w.withExtra (c2Tree 4)⟩, .ok ()⟩ := by
    refine writeImmediate_scalar_u8_at_v2' _ mem' _ _ _ _ _ _ _ _ _ _ _ _ _
      ⟨alloc3IdV2, rng, a⟩ rng _ h_pl ?_ ?_ ?_
    · rfl
    · exact c2_write_a3
    · exact h_set'
  exact Miri.Interpreter.PlaceMachine.writeMemory_of_result
    (refAccessConfigV2 c2Rp.types) (fun _ => true) (c2Int .i8 0xAA)
    ⟨c2A3Mp, c2U8⟩ st _ _ rfl h_w

/-- Runtime place `*_2` at type `u8`. -/
noncomputable abbrev c2A3Place :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.memory c2A3Mp, c2U8⟩

/-- Byte `1` of the updated `alloc3` decodes to the `u8` value `0xAA`. -/
theorem c2_read_a3w :
    Miri.Memory.Allocation.readScalar (c2A3w.withExtra (c2Tree 4))
      refRuntimeLayoutV2.base
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
        (Miri.ABI.Size.ofBytes 1)) false =
      .ok (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 0xAA))) :=
  (Miri.Memory.Allocation.readScalar_int_of_bytes _ refRuntimeLayoutV2.base
    _ (Array.mk [0xAA]) rfl rfl (by decide) (Or.inr rfl)).trans rfl

/-- The validity visitor's read of `*_2` returns `0xAA_u8`, state unchanged. -/
theorem c2_valRead_a3 :
    (refValHooksV2 c2Rp.types).readImmediate 0 c2A3Place .integer
        (c2St 3 c2L4 (c2Mem c2Live3)) =
      .ok ⟨c2Int .i8 0xAA, c2U8⟩ (c2St 3 c2L4 (c2Mem c2Live3)) := by
  let st := c2St 3 c2L4 (c2Mem c2Live3)
  let a := c2A3w.withExtra (c2Tree 4)
  let rng := Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
    (Miri.ABI.Size.ofBytes 1)
  have h_ga : Miri.Memory.AllocationAccess.getPtrAlloc st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      ⟨Miri.ABI.Size.ofBytes 8⟩ c2A3Mp.ptr (Miri.ABI.Size.ofBytes 1) true none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks
        (refAccessConfigV2 c2Rp.types)) =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨alloc3IdV2, rng, a⟩,
        .ok (some ⟨alloc3IdV2, rng, a⟩)⟩ :=
    getPtrAlloc_live_ghost_v2 (Miri.ABI.Size.ofBytes 1) 1 st.machine.memory
      (.machine ()) a st.machine alloc3IdV2 (Miri.ABI.Size.ofBytes 1)
      c2A3Mp.ptr (.concrete Miri.Memory.BorTag.one) _ _ rfl rfl rfl
      (by decide) rfl rfl
  have h_raw : Miri.Interpreter.readImmediate st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      (.indirect c2A3Mp) (Miri.Interpreter.localMemoryLayout c2U8)
      refRuntimeLayoutV2 true none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨alloc3IdV2, rng, a⟩,
        .ok ⟨c2Int .i8 0xAA, Miri.Interpreter.localMemoryLayout c2U8⟩⟩ :=
    readImmediate_mem_u8_v2 c2Rp.types c2A3Mp alloc3IdV2 a _ st
      st.machine.memory (Miri.ABI.Size.ofBytes 1) true
      (refAccessConfigV2 c2Rp.types) rfl h_ga rfl c2_read_a3w
  rw [refValHooksV2_readImmediate]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [show Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 c2Rp.types).place 0 c2A3Place st =
      .ok ⟨.indirect c2A3Mp, c2U8⟩ st from rfl]
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnvV2,
    get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [show refValidityMemoryEnv.memory st = st.machine.memory from rfl,
    show refValidityMemoryEnv.hooks st = ⟨st.machine, none⟩ from rfl,
    show (refAccessConfigV2 c2Rp.types).runtime = refRuntimeLayoutV2 from rfl,
    h_raw]
  rfl

/-- Step 3: `*_2 = move _5`. -/
theorem c2_step3 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c2Rp)
        refLimitsV2 0 (c2St 3 c2L3 (c2Mem c2Live1)) =
      (c2St 4 c2L4 (c2Mem c2Live3), .ok true) := by
  let stW := c2St 3 c2L4 (c2Mem c2Live3)
  let rv := toMiriRvalueV2 c2Rp.types (.use (.move ⟨5, []⟩))
  have h_run : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 c2Rp) refLimitsV2).assign 0
      ⟨2, Array.mk [.Deref]⟩ rv (c2St 3 c2L3 (c2Mem c2Live1)) =
      Miri.Interpreter.MachineHooks.run
        (Miri.Interpreter.ValidityVisitor.validatePlace
          (refValHooksV2 c2Rp.types) 0 16 c2A3Place true true) stW := by
    change Miri.Interpreter.MachineHooks.run (EStateM.bind
      (Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 c2Rp.types)
        (fun _ => true) (c2Int .i8 0xAA) ⟨c2A3Mp, c2U8⟩) _)
      (c2St 3 c2L4 (c2Mem c2Live1)) = _
    rw [mhRun_bind_ok c2_writeMem_a3]
    rfl
  let sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
    { path := ⟨"", Array.empty⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := some .empty,
      dataBytes := some (exceptOkGet
        (Miri.Memory.Validity.DataRangeSet.empty.addRange
          (Miri.ABI.Size.ofBytes 1) (Miri.ABI.Size.ofBytes 1)) rfl) }
  have h_p : refValidatePreMirror (refValHooksV2 c2Rp.types) 0 16
      c2A3Place true true stW = .ok sess stW := by
    change EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 c2Rp.types).readImmediate 0 c2A3Place .integer) _) _)
      _ stW = _
    rw [eStateM_bind3_ok c2_valRead_a3]
    rfl
  exact execStep_assign_val_v2 c2Rp _ stW stW (c2Frame 3 c2L3) (c2Frame 3 c2L4)
    0 3 c2Block (c2Stmt 3) ⟨2, Array.mk [.Deref]⟩ rv c2A3Place sess
    rfl rfl rfl rfl rfl rfl h_run h_p rfl rfl rfl

/-- Locals of `V2_C2` after statement 4. -/
noncomputable def c2L5 :=
  c2Locals (c2Ptr alloc2IdV2 4) .uninit .uninit .uninit

/-- Step 4 destination: `_0` evaluates to its local place without changing the
state. -/
private theorem c2_step4_dest :
    (Miri.Interpreter.ExecutionMachine.rvalueHooks
        (Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 c2Rp) refLimitsV2) refLimitsV2).evalPlace
      0 ⟨0, Array.empty⟩ true (c2St 4 c2L4 (c2Mem c2Live3)) =
      .ok (c2Local 0 c2L4 c2PtrC) (c2St 4 c2L4 (c2Mem c2Live3)) := rfl

/-- Step 4 source: `move _3` reads the pointer and leaves `_3` uninitialized. -/
private theorem c2_step4_src :
    (Miri.Interpreter.ExecutionMachine.rvalueHooks
        (Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 c2Rp) refLimitsV2) refLimitsV2).evalOperandAt
      0 (Miri.Interpreter.OperandPath.rvalue "operand")
      (toMiriOperandV2 c2Rp.types (RefOperand.move ⟨3, []⟩))
      (some ((Miri.Interpreter.ExecutionMachine.rvalueHooks
        (Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 c2Rp) refLimitsV2) refLimitsV2).placeLayout
        (c2Local 0 c2L4 c2PtrC)))
      (c2St 4 c2L4 (c2Mem c2Live3)) =
      .ok ⟨.immediate (c2Ptr alloc2IdV2 4), c2PtrC⟩
        (c2St 4 (c2Locals .uninit .uninit .uninit .uninit)
          (c2Mem c2Live3)) := rfl

/-- Step 4 assignment, split at the destination and operand evaluations so
that each definitional check stays small. -/
private theorem c2_step4_run :
    (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 c2Rp) refLimitsV2).assign 0 ⟨0, Array.empty⟩
      (toMiriRvalueV2 c2Rp.types (.use (.move ⟨3, []⟩)))
      (c2St 4 c2L4 (c2Mem c2Live3)) =
      Miri.Interpreter.MachineHooks.run
        (Miri.Interpreter.ValidityVisitor.validatePlace
          (refValHooksV2 c2Rp.types) 0 16 (c2Local 0 c2L5 c2PtrC) true true)
        (c2St 4 c2L5 (c2Mem c2Live3)) := by
  dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
    Miri.Interpreter.evalRvalueIntoPlace, toMiriRvalueV2, bind, Bind.bind]
  rw [mhRun_bind_ok c2_step4_dest, mhRun_bind_ok c2_step4_src]
  rfl

/-- Step 4: `_0 = move _3`. -/
theorem c2_step4 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c2Rp)
        refLimitsV2 0 (c2St 4 c2L4 (c2Mem c2Live3)) =
      (c2St 5 c2L5 (c2Mem c2Live3), .ok true) :=
  let stW := c2St 4 c2L5 (c2Mem c2Live3)
  execStep_assign_val_v2 c2Rp _ stW stW (c2Frame 4 c2L4) (c2Frame 4 c2L5)
    0 4 c2Block (c2Stmt 4) _ _ (c2Local 0 c2L5 c2PtrC) _
    rfl rfl rfl rfl rfl rfl c2_step4_run rfl rfl rfl rfl

/-- Writing the returned pointer into the return buffer succeeds. -/
theorem c2_retWrite_isOk :
    estateIsOk (Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      (.fromPointer refRuntimeLayoutV2.base (c2P alloc2IdV2 4))
      (c2Ret.withExtra (c2Tree 8))) = true := by
  let ⟨a', h_ws, _⟩ := alloc_writePtr_readScalar_v2
    (c2Ret.withExtra (c2Tree 8)) (c2P alloc2IdV2 4) rfl rfl rfl rfl trivial rfl
  rw [h_ws]
  rfl

/-- Return buffer of `V2_C2` after writing the returned pointer. -/
noncomputable def c2RetW : RefMiriAlloc :=
  estateOkGet _ c2_retWrite_isOk

/-- `c2RetW` is the result of the return-buffer pointer write; it keeps 8 bytes
and reads back the written pointer. -/
theorem c2RetW_spec :
    Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      (.fromPointer refRuntimeLayoutV2.base (c2P alloc2IdV2 4))
      (c2Ret.withExtra (c2Tree 8)) = .ok () c2RetW ∧
    c2RetW.byteSize = Miri.ABI.Size.ofBytes 8 ∧
    c2RetW.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      true = .ok (.fromPointer refRuntimeLayoutV2.base (c2P alloc2IdV2 4)) := by
  let ⟨a', h_ws, h_sz, h_rd⟩ := alloc_writePtr_readScalar_v2
    (c2Ret.withExtra (c2Tree 8)) (c2P alloc2IdV2 4) rfl rfl rfl rfl trivial rfl
  have h_eq : (EStateM.Result.ok () a' :
      EStateM.Result Miri.Memory.AllocError RefMiriAlloc Unit) =
      .ok () c2RetW := h_ws.symm.trans (estateOkGet_eq _ c2_retWrite_isOk)
  injection h_eq with _ h_a
  subst h_a
  exact ⟨h_ws, h_sz, h_rd⟩

/-- Final live rows of `V2_C2` (the return buffer row is last). -/
noncomputable def c2LiveR : Array RefLiveRow :=
  Array.mk [(alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩),
    (alloc3IdV2, ⟨.machine (), c2A3w.withExtra (c2Tree 4)⟩),
    (retAllocIdV2, ⟨.stack, c2RetW⟩)]

/-- `V2_C2` state after the root frame was popped (terminator control
advanced once). -/
noncomputable def c2StE (mem : RefMiriMem) : RefMiriState :=
  mkRefMiriStackState Array.empty none mem (advanceRefControl refInitControl)
    callerMemV2_C2_pre

/-- Runtime place of the return buffer at type `*const u32`. -/
noncomputable abbrev c2RetPlace :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.memory retMemPlaceV2, c2PtrC⟩

/-- The return copy writes `alloc2 + 4` into the return buffer and moves its row
last. -/
theorem c2_writeMem_ret :
    Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 c2Rp.types)
        (fun _ => true) (c2Ptr alloc2IdV2 4) ⟨retMemPlaceV2, c2PtrC⟩
        (c2StE (c2Mem c2Live3)) =
      .ok () (c2StE (c2Mem c2LiveR)) := by
  let st := c2StE (c2Mem c2Live3)
  let a := c2Ret.withExtra (c2Tree 8)
  let rng := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
  let mem' : RefMiriMem := c2Mem
    (Array.mk [(alloc2IdV2, ⟨.machine (), c2A2.withExtra (c2Tree 8)⟩),
      (alloc3IdV2, ⟨.machine (), c2A3w.withExtra (c2Tree 4)⟩),
      (retAllocIdV2, ⟨.stack, a⟩)])
  have h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, a⟩) := rfl
  have h_any : (st.machine.memory.live.any (fun e => e.1 == retAllocIdV2)) =
      true := by
    rw [← Array.any_toList]; rfl
  have h_set : st.machine.memory.setLiveAllocation retAllocIdV2 a =
      .ok mem' := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ h_find]
    rfl
  have h_find' : mem'.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, a⟩) := rfl
  have h_any' : (mem'.live.any (fun e => e.1 == retAllocIdV2)) = true := by
    rw [← Array.any_toList]; rfl
  have h_set' : mem'.setLiveAllocation retAllocIdV2 a = .ok mem' := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ h_find']
    rfl
  have h_ga : Miri.Memory.AllocationAccess.getPtrAllocMut st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 (Miri.ABI.Size.ofBytes 8) false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks
        (refAccessConfigV2 c2Rp.types)) =
      ⟨mem', ⟨st.machine, none⟩, some ⟨retAllocIdV2, rng, a⟩,
        .ok (some ⟨retAllocIdV2, rng, a⟩)⟩ :=
    getPtrAllocMut_live_nonghost_v2 c2Rp.types
      (Miri.ABI.Size.ofBytes 8) 8 st.machine.memory mem' .stack a
      st.machine retAllocIdV2 Miri.ABI.Size.ZERO retPtrV2
      (.concrete Miri.Memory.BorTag.one) h_find rfl h_any h_set rfl (by decide)
      rfl rfl rfl rfl
  have h_ga' : Miri.Memory.AllocationAccess.getPtrAllocMut mem'
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 (Miri.ABI.Size.ofBytes 8) false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks
        (refAccessConfigV2 c2Rp.types)) =
      ⟨mem', ⟨st.machine, none⟩, some ⟨retAllocIdV2, rng, a⟩,
        .ok (some ⟨retAllocIdV2, rng, a⟩)⟩ :=
    getPtrAllocMut_live_nonghost_v2 c2Rp.types
      (Miri.ABI.Size.ofBytes 8) 8 mem' mem' .stack a
      st.machine retAllocIdV2 Miri.ABI.Size.ZERO retPtrV2
      (.concrete Miri.Memory.BorTag.one) h_find' rfl h_any' h_set' rfl
      (by decide) rfl rfl rfl rfl
  let abi : Miri.ABI.Scalar :=
    .Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
      (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8))
  let pl : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
      .Scalar abi, some c2PtrC.ty⟩⟩
  have h_pl1 : Miri.Interpreter.getPlaceAllocMut st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser) pl refRuntimeLayoutV2 false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout =
      ⟨mem', ⟨st.machine, none⟩, some ⟨retAllocIdV2, rng, a⟩,
        .ok (some ⟨retAllocIdV2, rng, a⟩)⟩ :=
    getPlaceAllocMut_sized_of_access_v2' _ _ _ _ _ _ _ _ _ _ rfl rfl h_ga
  have h_pl2 : Miri.Interpreter.getPlaceAllocMut mem'
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser) pl refRuntimeLayoutV2 false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout =
      ⟨mem', ⟨st.machine, none⟩, some ⟨retAllocIdV2, rng, a⟩,
        .ok (some ⟨retAllocIdV2, rng, a⟩)⟩ :=
    getPlaceAllocMut_sized_of_access_v2' _ _ _ _ _ _ _ _ _ _ rfl rfl h_ga'
  have h_commit : mem'.setLiveAllocation retAllocIdV2 c2RetW =
      .ok (c2Mem c2LiveR) := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find mem' retAllocIdV2
      ⟨.stack, a⟩ _ h_find']
    rfl
  have h_w' : Miri.Interpreter.writeImmediateToMplaceNoValidate mem'
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser) (c2Ptr alloc2IdV2 4) pl refRuntimeLayoutV2 false none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout (fun _ => true) =
      ⟨c2Mem c2LiveR, ⟨st.machine, none⟩,
        some ⟨retAllocIdV2, rng, c2RetW⟩, .ok ()⟩ :=
    by
      refine Miri.Interpreter.writeImmediate_scalar_of_access
        (H := Miri.Interpreter.PlaceMachine.AccessState Unit RefUser)
        (X := Miri.Memory.ProvenanceExtra) mem'
        (c2Mem c2LiveR) ⟨st.machine, none⟩ pl refRuntimeLayoutV2 none _ _ _
        (fun _ => true)
        (.fromPointer refRuntimeLayoutV2.base (c2P alloc2IdV2 4)) abi
        retAllocIdV2 a c2RetW ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · exact True.intro
      · decide
      · exact h_pl2
      · exact c2RetW_spec.1
      · exact h_commit
  have h_w : Miri.Interpreter.writeImmediateToMplaceNoValidate
      st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser) (c2Ptr alloc2IdV2 4)
      ⟨retMemPlaceV2, Miri.Interpreter.localMemoryLayout c2PtrC⟩
      (refAccessConfigV2 c2Rp.types).runtime
      (refAccessConfigV2 c2Rp.types).ghostMode
      (refAccessConfigV2 c2Rp.types).globalKind
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout (fun _ => true) =
      ⟨c2Mem c2LiveR, ⟨st.machine, none⟩,
        some ⟨retAllocIdV2, rng, c2RetW⟩, .ok ()⟩ :=
    writeImmediateToMplace_reorder_v2 _ mem' _ _ _ pl _ _ _ _ _ _ _
      ⟨retAllocIdV2, rng, a⟩ _ h_pl1 h_pl2 h_w'
  exact Miri.Interpreter.PlaceMachine.writeMemory_of_result
    (refAccessConfigV2 c2Rp.types) (fun _ => true) (c2Ptr alloc2IdV2 4)
    ⟨retMemPlaceV2, c2PtrC⟩ st _ _ rfl h_w

/-- The validity visitor's read of the return buffer returns the written
pointer, state unchanged. -/
theorem c2_valRead_ret :
    (refValHooksV2 c2Rp.types).readImmediate 0 c2RetPlace .rawPointer
        (c2StE (c2Mem c2LiveR)) =
      .ok ⟨c2Ptr alloc2IdV2 4, c2PtrC⟩ (c2StE (c2Mem c2LiveR)) := by
  let st := c2StE (c2Mem c2LiveR)
  let rng := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
  have h_ga : Miri.Memory.AllocationAccess.getPtrAlloc st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 (Miri.ABI.Size.ofBytes 8) true none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks
        (refAccessConfigV2 c2Rp.types)) =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨retAllocIdV2, rng, c2RetW⟩,
        .ok (some ⟨retAllocIdV2, rng, c2RetW⟩)⟩ :=
    getPtrAlloc_live_ghost_v2 (Miri.ABI.Size.ofBytes 8) 8 st.machine.memory
      .stack c2RetW st.machine retAllocIdV2 Miri.ABI.Size.ZERO
      retPtrV2 (.concrete Miri.Memory.BorTag.one) _ _ rfl rfl rfl
      (by decide) (by rw [c2RetW_spec.2.1]; rfl) rfl
  have h_raw : Miri.Interpreter.readImmediate st.machine.memory
      (⟨st.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
        RefUser)
      (.indirect retMemPlaceV2) (Miri.Interpreter.localMemoryLayout c2PtrC)
      refRuntimeLayoutV2 true none
      (refAccessConfigV2 c2Rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 c2Rp.types))
      (refAccessConfigV2 c2Rp.types).dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩,
        some ⟨retAllocIdV2, rng, c2RetW⟩,
        .ok ⟨c2Ptr alloc2IdV2 4, Miri.Interpreter.localMemoryLayout c2PtrC⟩⟩ :=
    readImmediate_mem_ptr_v2 c2PtrC.ty retMemPlaceV2 retAllocIdV2 c2RetW _ st
      st.machine.memory Miri.ABI.Size.ZERO true
      (refAccessConfigV2 c2Rp.types) rfl h_ga rfl c2RetW_spec.2.2
  rw [refValHooksV2_readImmediate]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [show Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 c2Rp.types).place 0 c2RetPlace st =
      .ok ⟨.indirect retMemPlaceV2, c2PtrC⟩ st from rfl]
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnvV2,
    get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [show refValidityMemoryEnv.memory st = st.machine.memory from rfl,
    show refValidityMemoryEnv.hooks st = ⟨st.machine, none⟩ from rfl,
    show (refAccessConfigV2 c2Rp.types).runtime = refRuntimeLayoutV2 from rfl,
    h_raw]
  rfl

/-- Step 5: `return` (copy `_0` into the return buffer, pop the root frame).
-/
theorem c2_step5 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c2Rp)
        refLimitsV2 0 (c2St 5 c2L5 (c2Mem c2Live3)) =
      (c2StE (c2Mem c2LiveR), .ok true) := by
  let st := c2St 5 c2L5 (c2Mem c2Live3)
  let stMid : RefMiriState := mkRefMiriState (c2Frame 5 c2L5) (c2Mem c2Live3)
    (advanceRefControl refInitControl) callerMemV2_C2_pre
  let stE := c2StE (c2Mem c2LiveR)
  let sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
    { path := ⟨"", Array.empty⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := some .empty,
      dataBytes := some (exceptOkGet
        (Miri.Memory.Validity.DataRangeSet.empty.addRange
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) rfl) }
  have h_p : refValidatePreMirror (refValHooksV2 c2Rp.types) 0 16
      c2RetPlace true true stE = .ok sess stE := by
    change EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 c2Rp.types).readImmediate 0 c2RetPlace .rawPointer) _) _)
      _ stE = _
    rw [eStateM_bind3_ok c2_valRead_ret]
    rfl
  have h_val := refValidatePlace_of_pre_v2 c2Rp.types c2RetPlace stE stE sess
    h_p rfl
  have h_copy : Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 c2Rp)).place
      (refExecCfgV2 c2Rp).copy 0
      ⟨.immediate (c2Ptr alloc2IdV2 4),
        refLocalLayoutForTyV2 c2Rp.types (.rawPtr .shared u32Ty)⟩
      ⟨.memory retMemPlaceV2, c2PtrC⟩ true
      { stMid with stack := ⟨Array.empty⟩ } =
      .ok ()
      { stMid with
        stack := ⟨Array.empty⟩,
        machine := { stMid.machine with memory := c2Mem c2LiveR } } := by
    change EStateM.bind
      (Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 c2Rp.types)
        (fun _ => true) (c2Ptr alloc2IdV2 4) ⟨retMemPlaceV2, c2PtrC⟩) _
      (c2StE (c2Mem c2Live3)) = _
    rw [eStateM_bind_ok c2_writeMem_ret]
    exact h_val
  have h_term := returnFromCurrentFrame_op_at_v2 c2Rp stMid
    (.immediate (c2Ptr alloc2IdV2 4)) (.rawPtr .shared u32Ty)
    ⟨retMemPlaceV2, c2PtrC⟩ (c2Frame 5 c2L5) 0 5 _ (c2Mem c2LiveR)
    (c2Mem c2LiveR) rfl rfl rfl rfl rfl rfl rfl rfl rfl h_copy
  exact execStep_term_ok c2Rp st stMid _ (c2Frame 5 c2L5) 0 5 c2Block
    rfl rfl rfl rfl rfl rfl h_term

/-- Entry memory initialization of `V2_C2` yields `c2Mem c2Live0` and the return
place. -/
theorem c2_icm :
    refInitCallerMemoryV2 c2Rp.types callerMemV2_C2_pre
        (.rawPtr .shared u32Ty) =
      .ok (c2Mem c2Live0, ⟨retMemPlaceV2, c2PtrC⟩) := by
  let al2 := @GetElem.getElem _ Nat _ _ _ callerMemV2_C2_pre.allocations 0 (by decide)
  let al3 := @GetElem.getElem _ Nat _ _ _ callerMemV2_C2_pre.allocations 1 (by decide)
  have h_m2 : refAllocToMiriV2 al2 = .ok (c2A2.withExtra (c2Tree 8)) := by
    dsimp only [refAllocToMiriV2]
    rw [show refPlainInitBytesV2? al2.bytes =
        some [1, 0, 0, 0, 0xAA, 0, 0, 0] from rfl]
    dsimp only
    rw [show toMiriMutV2 al2.mutability = Miri.Memory.Mutability.Not from rfl,
      show ({ pow2 := al2.alignLog2 } : Miri.ABI.Align) = ⟨2⟩ from rfl,
      show al2.bytes.length = 8 from rfl,
      show Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk [1, 0, 0, 0, 0xAA, 0, 0, 0]) ⟨2⟩ .Not = .ok c2A2 from
        exceptOkGet_eq _ rfl]
    rfl
  have h_m3 : refAllocToMiriV2 al3 = .ok (c2A3.withExtra (c2Tree 4)) := by
    dsimp only [refAllocToMiriV2]
    rw [show refPlainInitBytesV2? al3.bytes = some [1, 2, 3, 4] from rfl]
    dsimp only
    rw [show toMiriMutV2 al3.mutability = Miri.Memory.Mutability.Mut from rfl,
      show ({ pow2 := al3.alignLog2 } : Miri.ABI.Align) = ⟨0⟩ from rfl,
      show al3.bytes.length = 4 from rfl,
      show Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk [1, 2, 3, 4]) ⟨0⟩ .Mut = .ok c2A3 from
        exceptOkGet_eq _ rfl]
    rfl
  dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
    ite_false]
  rw [show c2PtrC.layout.size = Miri.ABI.Size.ofBytes 8 from rfl,
    show c2PtrC.layout.align.abi = Miri.ABI.Align.EIGHT from rfl,
    c2Ret_tryNew]
  dsimp only
  rw [show callerMemV2_C2_pre.allocations = [al2, al3] from rfl]
  dsimp only [refInsertCallerAllocsV2]
  rw [show refExactAllocIdV2 al2.allocId = some alloc2IdV2 from rfl,
    show refExactAllocIdV2 al3.allocId = some alloc3IdV2 from rfl, h_m2, h_m3]
  rfl

/-- `initRefStateV2` on `V2_C2` yields the concrete entry state. -/
theorem c2_init (ms : Nat) :
    initRefStateV2 c2Rp queryV2_C2 ms =
      .ok { miri := c2St 0 c2L0 (c2Mem c2Live0),
            retTy := .rawPtr .shared u32Ty,
            retPlace := ⟨retMemPlaceV2, c2PtrC⟩,
            stepsExecuted := 0, maxSteps := ms } :=
  initRefStateV2_ok_v2 c2Rp queryV2_C2 ms c2Body
    [.rawPtr .shared u32Ty, .rawPtr .shared u32Ty, .rawPtr .mut u8Ty,
     .rawPtr .shared u32Ty, u32Ty, u8Ty]
    (.rawPtr .shared u32Ty) (c2Mem c2Live0) (c2Mem c2Live0)
    ⟨retMemPlaceV2, c2PtrC⟩ c2L0
    rfl rfl rfl rfl rfl rfl rfl rfl c2_icm rfl rfl rfl

/-- The final return buffer decodes to the pointer `alloc2 + 4`. -/
theorem c2_ret_val :
    refReadReturnValV2 (c2Mem c2LiveR) callerMemV2_C2_pre
        (.rawPtr .shared u32Ty) ⟨retMemPlaceV2, c2PtrC⟩ =
      .ok (.ptr ⟨some 2, 4, .isize⟩) := by
  dsimp only [refReadReturnValV2, retMemPlaceV2, retPtrV2,
    refTyLayoutFitsU64V2, Bool.not_true, ite_false]
  rw [show (c2Mem c2LiveR).live.find? (fun entry => entry.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, c2RetW⟩) from rfl]
  dsimp only [refReadValFromAllocV2]
  rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
    from rfl, c2RetW_spec.2.2]
  rfl

/-- The final reference memory extracts to `callerMemV2_C2_post`. -/
theorem c2_ret_mem :
    refExtractCallerMemoryV2 callerMemV2_C2_pre (c2Mem c2LiveR) =
      callerMemV2_C2_post := rfl

/-- One non-terminal `refCoreExecV2` step, as a rewrite equation. -/
theorem refCoreExecV2_step_ok_v2 {rp : RefProg} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} {n : Nat}
    {m m' : RefMiriState}
    (h_step : Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
      refLimitsV2 0 m = (m', .ok true))
    (h_ne : m'.stack.frames.isEmpty = false) :
    refCoreExecV2 rp rt rpl onRet onUb onBlk (n + 1) m =
      refCoreExecV2 rp rt rpl onRet onUb onBlk n m' := by
  change (match evalRefCoreV2 rp rt rpl m with
    | .running m' => refCoreExecV2 rp rt rpl onRet onUb onBlk n m'
    | .returned out => onRet out | .ub => onUb | .blocked => onBlk) = _
  dsimp only [evalRefCoreV2]
  rw [h_step]
  dsimp only
  rw [h_ne, ite_false_eq]

/-- Final `refCoreExecV2` step: a successful `Return` empties the stack and
the returned value decodes to `v`. -/
theorem refCoreExecV2_return_ok_v2 {rp : RefProg} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} {n : Nat}
    {m m' : RefMiriState} {v : Val}
    (h_step : Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
      refLimitsV2 0 m = (m', .ok true))
    (h_e : m'.stack.frames.isEmpty = true)
    (h_rv : refReadReturnValV2 m'.machine.memory m'.machine.user.callerMem rt
      rpl = .ok v) :
    refCoreExecV2 rp rt rpl onRet onUb onBlk (n + 1) m =
      onRet (.returned ⟨v, refExtractCallerMemoryV2
        m'.machine.user.callerMem m'.machine.memory⟩) := by
  change (match evalRefCoreV2 rp rt rpl m with
    | .running m' => refCoreExecV2 rp rt rpl onRet onUb onBlk n m'
    | .returned out => onRet out | .ub => onUb | .blocked => onBlk) = _
  dsimp only [evalRefCoreV2]
  rw [h_step]
  dsimp only
  rw [h_e, ite_true_eq, h_rv]

/-- Six reference-machine steps take the `V2_C2` entry state to `outV2_C2`. -/
theorem c2_exec :
    refCoreExecV2 c2Rp (.rawPtr .shared u32Ty) ⟨retMemPlaceV2, c2PtrC⟩
      (fun o => o = outV2_C2) False False 6
      (c2St 0 c2L0 (c2Mem c2Live0)) := by
  rw [refCoreExecV2_step_ok_v2 c2_step0 rfl,
    refCoreExecV2_step_ok_v2 c2_step1 rfl,
    refCoreExecV2_step_ok_v2 c2_step2 rfl,
    refCoreExecV2_step_ok_v2 c2_step3 rfl,
    refCoreExecV2_step_ok_v2 c2_step4 rfl,
    refCoreExecV2_return_ok_v2 c2_step5 rfl c2_ret_val]
  exact congrArg
    (fun cm => TerminalOut.returned ⟨.ptr ⟨some 2, 4, .isize⟩, cm⟩) c2_ret_mem

/-- `V2_C2` (`BinOp.offset` + caller memory load/cast/write): Anneal and the
reference machine agree on the unique returned output `outV2_C2`. -/
theorem V2_C2_offsetWrite_lockstep :
    WellFormedV2 progV2_C2_offsetWrite queryV2_C2 ∧
    BehaviorV2 progV2_C2_offsetWrite queryV2_C2 outV2_C2 ∧
    ¬ DivergesV2 progV2_C2_offsetWrite queryV2_C2 ∧
    RefWellFormedV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2 ∧
    RefBehaviorV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2 outV2_C2 ∧
    (∀ out', RefBehaviorV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2
      out' → out' = outV2_C2) ∧
    ¬ RefDivergesV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2 :=
  let ⟨h_wf, h_beh, h_nd, _⟩ := c2_m_anneal
  let ⟨h_rwf, h_rbeh, h_uniq, h_rnd⟩ := ref_ok_of_coreExec c2_init c2_exec
  ⟨h_wf, h_beh, h_nd, h_rwf, h_rbeh, h_uniq, h_rnd⟩

/-! ## Section 3: `V2_C1` on `M_anneal`, one `rfl` per `evalStepV2` step

Each transition between explicit concrete states is its own theorem, which
keeps every kernel check small (instead of one whole-run `rfl` over
`execProgV2`), and `c1a_Runs` hides the fuel from elaboration. -/

/-- `post` holds on the outcome reached from `s` after finitely many steps,
none of which faults. -/
abbrev c1a_Runs (p : Program) (post : TerminalOut → Prop) (s : State) :
    Prop :=
  ∃ fuel, execOutcomeStateV2 p post (fun _ => False) fuel s

/-- Prepend one non-faulting `evalStepV2` transition to a run. -/
theorem c1a_runs_step {p : Program} {s s' : State}
    {post : TerminalOut → Prop} (hStep : evalStepV2 p s = .step s')
    (hRest : c1a_Runs p post s') : c1a_Runs p post s :=
  let ⟨fuel, h⟩ := hRest
  ⟨fuel + 1, by
    change (match evalStepV2 p s with
      | .step s'' => execOutcomeStateV2 p post (fun _ => False) fuel s''
      | .done out => post out
      | .fault k => (fun _ => False) k)
    rw [hStep]
    exact h⟩

/-- A terminating `evalStepV2` transition whose output satisfies `post`. -/
theorem c1a_runs_done {p : Program} {s : State} {out : TerminalOut}
    {post : TerminalOut → Prop}
    (hDone : evalStepV2 p s = .done out) (hPost : post out) :
    c1a_Runs p post s :=
  ⟨1, by
    change (match evalStepV2 p s with
      | .step s'' => execOutcomeStateV2 p post (fun _ => False) 0 s''
      | .done o => post o
      | .fault k => (fun _ => False) k)
    rw [hDone]
    exact hPost⟩

/-- Package a run from the entry state as the adequacy theorem's input. -/
theorem c1a_execProgV2_of_runs {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (hInit : initStateV2 p q = .ok s₀)
    (hRuns : c1a_Runs p post s₀) : ∃ fuel, execProgV2 p fuel q post :=
  let ⟨fuel, h⟩ := hRuns
  ⟨fuel, by unfold execProgV2; rw [hInit]; exact h⟩

/-- Live, uninitialized local slot. -/
abbrev c1a_N : LocalSlot := .immediate none
/-- Initialized local slot holding `v`. -/
abbrev c1a_im (v : Val) : LocalSlot := .immediate (some v)
/-- `&[u8]` into caller allocation `2` at byte `off` with `len` elements. -/
abbrev c1a_sl (off len : UInt64) : Val := .slicePtr ⟨some 2, off, .isize⟩ len
/-- `2usize`. -/
abbrev c1a_two : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩

/-- Single-frame `V2_C1` state at statement `i` of block `b`. No step
allocates, so the memory stays the entry memory. -/
noncomputable abbrev c1a_st (b i : Nat) (l : List LocalSlot) : State :=
  ⟨[⟨0, b, i, l, none, none, none⟩], callerMemV2_C1,
    entryMemoryWithCaller callerMemV2_C1⟩

/-- `V2_C1` entry state. -/
noncomputable def c1a_s0 : State := c1a_st 0 0
  [c1a_N, c1a_im (c1a_sl 0 5), c1a_im c1a_two, c1a_N, c1a_N, c1a_N, c1a_N,
    c1a_N]
/-- `V2_C1` after `bb0[0]` (`_4 = RangeTo(copy _2)`). -/
noncomputable def c1a_s1 : State := c1a_st 0 1
  [c1a_N, c1a_im (c1a_sl 0 5), c1a_im c1a_two, c1a_N, c1a_im (.rangeTo 2),
    c1a_N, c1a_N, c1a_N]
/-- `V2_C1` after the `bb0` call (`_3 = sliceGetUncheckedRangeTo(_1, _4)`). -/
noncomputable def c1a_s2 : State := c1a_st 1 0
  [c1a_N, c1a_im (c1a_sl 0 5), c1a_im c1a_two, c1a_im (c1a_sl 0 2),
    c1a_im (.rangeTo 2), c1a_N, c1a_N, c1a_N]
/-- `V2_C1` after `bb1[0]` (`_6 = RangeFrom(move _2)`). -/
noncomputable def c1a_s3 : State := c1a_st 1 1
  [c1a_N, c1a_im (c1a_sl 0 5), c1a_N, c1a_im (c1a_sl 0 2),
    c1a_im (.rangeTo 2), c1a_N, c1a_im (.rangeFrom 2), c1a_N]
/-- `V2_C1` after the `bb1` call (`_5 = sliceGetUncheckedRangeFrom(_1, _6)`). -/
noncomputable def c1a_s4 : State := c1a_st 2 0
  [c1a_N, c1a_im (c1a_sl 0 5), c1a_N, c1a_im (c1a_sl 0 2),
    c1a_im (.rangeTo 2), c1a_im (c1a_sl 2 3), c1a_im (.rangeFrom 2), c1a_N]
/-- `V2_C1` after the `bb2` call (`_7 = sliceLen(move _3)`). -/
noncomputable def c1a_s5 : State := c1a_st 3 0
  [c1a_N, c1a_im (c1a_sl 0 5), c1a_N, c1a_N, c1a_im (.rangeTo 2),
    c1a_im (c1a_sl 2 3), c1a_im (.rangeFrom 2), c1a_im c1a_two]
/-- `V2_C1` after `bb3[0]` (`_0 = (move _5, move _7)`). -/
noncomputable def c1a_s6 : State := c1a_st 3 1
  [c1a_im (.tuple [c1a_sl 2 3, c1a_two]), c1a_im (c1a_sl 0 5), c1a_N, c1a_N,
    c1a_im (.rangeTo 2), c1a_N, c1a_im (.rangeFrom 2), c1a_N]

/-- `initStateV2` on `V2_C1` yields `c1a_s0`. -/
theorem c1a_init : initStateV2 progV2_C1_splitAt queryV2_C1 = .ok c1a_s0 :=
  rfl
/-- `V2_C1` transition `c1a_s0 → c1a_s1`. -/
theorem c1a_step0 : evalStepV2 progV2_C1_splitAt c1a_s0 = .step c1a_s1 :=
  rfl
/-- `V2_C1` transition `c1a_s1 → c1a_s2`. -/
theorem c1a_step1 : evalStepV2 progV2_C1_splitAt c1a_s1 = .step c1a_s2 :=
  rfl
/-- `V2_C1` transition `c1a_s2 → c1a_s3`. -/
theorem c1a_step2 : evalStepV2 progV2_C1_splitAt c1a_s2 = .step c1a_s3 :=
  rfl
/-- `V2_C1` transition `c1a_s3 → c1a_s4`. -/
theorem c1a_step3 : evalStepV2 progV2_C1_splitAt c1a_s3 = .step c1a_s4 :=
  rfl
/-- `V2_C1` transition `c1a_s4 → c1a_s5`. -/
theorem c1a_step4 : evalStepV2 progV2_C1_splitAt c1a_s4 = .step c1a_s5 :=
  rfl
/-- `V2_C1` transition `c1a_s5 → c1a_s6`. -/
theorem c1a_step5 : evalStepV2 progV2_C1_splitAt c1a_s5 = .step c1a_s6 :=
  rfl
/-- `V2_C1` returns `outV2_C1` from `c1a_s6`. -/
theorem c1a_step6 : evalStepV2 progV2_C1_splitAt c1a_s6 = .done outV2_C1 :=
  rfl

/-- `V2_C1` returns `outV2_C1` on `M_anneal`: it is well formed, has exactly
that behavior, does not diverge, and satisfies every postcondition that
`outV2_C1` satisfies. -/
theorem c1_m_anneal :
    WellFormedV2 progV2_C1_splitAt queryV2_C1 ∧
    BehaviorV2 progV2_C1_splitAt queryV2_C1 outV2_C1 ∧
    ¬ DivergesV2 progV2_C1_splitAt queryV2_C1 ∧
    (∀ post : TerminalOut → Prop,
      post outV2_C1 →
      SatisfiesPostV2 progV2_C1_splitAt queryV2_C1 post) :=
  let ⟨_, h⟩ := c1a_execProgV2_of_runs (post := fun o => o = outV2_C1)
    c1a_init
    (c1a_runs_step c1a_step0 (c1a_runs_step c1a_step1
      (c1a_runs_step c1a_step2 (c1a_runs_step c1a_step3
        (c1a_runs_step c1a_step4 (c1a_runs_step c1a_step5
          (c1a_runs_done c1a_step6 rfl)))))))
  spec_and_behaviorV2_of_exec_eq h

end Anneal.MirCorrespondence
