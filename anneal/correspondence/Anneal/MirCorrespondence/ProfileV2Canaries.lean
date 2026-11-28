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
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirWp

/-!
# Profile v2 Canary Definitions and Negative Locksteps (`V2_C4a`–`V2_C6`)
(`Anneal.MirCorrespondence.ProfileV2Canaries`)

Defines all seven Profile v2 canary programs, queries, and domain predicates
(`V2_C1`–`V2_C6`, counting `V2_C4a`/`V2_C4b`), proves the negative locksteps
(`V2_C4a`, `V2_C4b`, `V2_C5`, `V2_C6`) plus Anneal-side lemmas (`c2_m_anneal`,
`c3_m_anneal`), and exports shared validity helpers. Positive locksteps
(`V2_C2`, `V2_C1`, `V2_C3`) and `ProfileV2CanaryDomain` /
`ProfileV2ExtendedDomain` bundles live in `ProfileV2PosCanaries`,
`ProfileV2PosCanariesC1`, and `ProfileV2C3AndBundles`.

Query-boundary reference checks (`V2_C4a`) and return confinement/validity
checks (`V2_C6`) run in `initRefStateV2` and `refReadReturnValV2` alongside
`CallMachine.cleanup` stack deallocation, whereas in-body deref alignment
(`V2_C4b`), read-only stores (`V2_C5`), borrows (`V2_C6`), and positive
canaries (`V2_C1`–`V2_C3`) execute via `Miri.Interpreter.ExecutionMachine.step`.
-/

/-! ## Section 1: Profile v2 Canary Programs, Queries, and Domains -/

/-- `V2_C1` (Zerocopy-representative slice split): `split_at_unchecked`-style
`get_unchecked(..mid)` (`_3`) and `get_unchecked(mid..)` (`_5`) over a shared
`CallerMemory` `&[u8]` slice via `RangeTo`/`RangeFrom` aggregates, plus
`slice::len` on `_3` (`_7`), returning `(_5, _7) : (&[u8], usize)` (`24`-byte
`.Memory` tuple carrying singleton `ProvenanceMap` entry at offset `0`, keeping
within `lean-miri`'s exported `Miri.Memory.QSortProof.singleton` invariant). -/
noncomputable def progV2_C1_splitAt : Program :=
  let sliceU8 := MirTy.ref .shared (.slice u8Ty)
  let usizeTy := MirTy.int .isize false
  mkV2Prog {
    identity := "v2_c1_split_at"
    argumentCount := 2
    locals := [
      .tuple [sliceU8, usizeTy], sliceU8, usizeTy, sliceU8,
      .rangeTo usizeTy, sliceU8, .rangeFrom usizeTy, usizeTy
    ]
    basicBlocks := [
      { statements :=
          [.assign ⟨4, []⟩ (.aggregateRangeTo usizeTy (.copy ⟨2, []⟩))]
        terminator := .coreCall .sliceGetUncheckedRangeTo
          [.copy ⟨1, []⟩, .copy ⟨4, []⟩] ⟨3, []⟩ (some 1) .continue_ },
      { statements :=
          [.assign ⟨6, []⟩ (.aggregateRangeFrom usizeTy (.move ⟨2, []⟩))]
        terminator := .coreCall .sliceGetUncheckedRangeFrom
          [.copy ⟨1, []⟩, .copy ⟨6, []⟩] ⟨5, []⟩ (some 2) .continue_ },
      { statements := []
        terminator := .coreCall .sliceLen
          [.move ⟨3, []⟩] ⟨7, []⟩ (some 3) .continue_ },
      { statements :=
          [.assign ⟨0, []⟩ (.aggregateTuple [.move ⟨5, []⟩, .move ⟨7, []⟩])]
        terminator := .return_ }
    ]
  }

/-- 5-byte caller allocation `[10, 20, 30, 40, 50]` at `allocId = 2`. -/
noncomputable def callerMemV2_C1 : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 0, mutability := .shared
  bytes := [
    .init 10 none, .init 20 none, .init 30 none,
    .init 40 none, .init 50 none
  ]
  live := true
}]⟩

/-- Entry query for `V2_C1` (`s = &[10,20,30,40,50]`, `mid = 2`). -/
noncomputable def queryV2_C1 : Query := {
  args := [
    .slicePtr ⟨some 2, 0, .isize⟩ 5,
    .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩
  ]
  callerMem := callerMemV2_C1
}

/-- Expected returned pair `(&[30,40,50], 2usize)` for `V2_C1`. -/
noncomputable def outV2_C1 : TerminalOut :=
  .returned ⟨
    .tuple [.slicePtr ⟨some 2, 2, .isize⟩ 3,
            .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩],
    callerMemV2_C1⟩

/-- `V2_C2` (`BinOp.offset` + caller memory load/cast/write): reads `u32` at
element offset `+1` (`+4` bytes) from `*const u32`, truncates to `u8`, writes
through `*mut u8`, and returns the offset pointer. -/
noncomputable def progV2_C2_offsetWrite : Program :=
  mkV2Prog {
    identity := "v2_c2_offset_write"
    argumentCount := 2
    locals := [
      .rawPtr .shared u32Ty, .rawPtr .shared u32Ty, .rawPtr .mut u8Ty,
      .rawPtr .shared u32Ty, u32Ty, u8Ty
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨3, []⟩
          (.binaryOp .offset (.copy ⟨1, []⟩)
            (.constant ⟨.int .isize true, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨4, []⟩ (.use (.copy ⟨3, [.deref]⟩)),
        .assign ⟨5, []⟩ (.cast .intToInt (.move ⟨4, []⟩) u8Ty),
        .assign ⟨2, [.deref]⟩ (.use (.move ⟨5, []⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨3, []⟩))
      ]
      terminator := .return_
    }]
  }

/-- Pre-state caller memory for `V2_C2`: aligned `alloc2` + writable `alloc3`.
-/
noncomputable def callerMemV2_C2_pre : CallerMemory := ⟨[
  { allocId := 2, alignLog2 := 2, mutability := .shared
    bytes := [
      .init 1 none, .init 0 none, .init 0 none, .init 0 none,
      .init 0xAA none, .init 0 none, .init 0 none, .init 0 none
    ]
    live := true },
  { allocId := 3, alignLog2 := 0, mutability := .mut
    bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    live := true }
]⟩

/-- Post-state caller memory for `V2_C2`: byte 1 of `alloc3` updated to `0xAA`.
-/
noncomputable def callerMemV2_C2_post : CallerMemory := ⟨[
  { allocId := 2, alignLog2 := 2, mutability := .shared
    bytes := [
      .init 1 none, .init 0 none, .init 0 none, .init 0 none,
      .init 0xAA none, .init 0 none, .init 0 none, .init 0 none
    ]
    live := true },
  { allocId := 3, alignLog2 := 0, mutability := .mut
    bytes := [.init 1 none, .init 0xAA none, .init 3 none, .init 4 none]
    live := true }
]⟩

/-- Entry query for `V2_C2`. -/
noncomputable def queryV2_C2 : Query := {
  args := [.ptr ⟨some 2, 0, .isize⟩, .ptr ⟨some 3, 1, .isize⟩]
  callerMem := callerMemV2_C2_pre
}

/-- Expected return output for `V2_C2`. -/
noncomputable def outV2_C2 : TerminalOut :=
  .returned ⟨.ptr ⟨some 2, 4, .isize⟩, callerMemV2_C2_post⟩

/-- `V2_C3` (`Assign` LHS/RHS order on self-moved thin ZST pointer):
`*_1 = PtrMetadata(move _1); _0 = (); return` evaluates RHS `move _1` after
resolving LHS `*_1` to `alloc2`, preserving `alloc2` unchanged. -/
noncomputable def progV2_C3_selfPtrMetadata : Program :=
  mkV2Prog {
    identity := "v2_c3_self_ptr_metadata"
    argumentCount := 1
    locals := [.unit, .rawPtr .mut .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨1, [.deref]⟩ (.unaryOp .ptrMetadata (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))
      ]
      terminator := .return_
    }]
  }

/-- 1-byte mutable caller allocation at `allocId = 2` for `V2_C3`. -/
noncomputable def callerMemV2_C3 : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 0, mutability := .mut
  bytes := [.init 9 none]
  live := true
}]⟩

/-- Entry query for `V2_C3`. -/
noncomputable def queryV2_C3 : Query := {
  args := [.ptr ⟨some 2, 0, .isize⟩]
  callerMem := callerMemV2_C3
}

/-- Expected return output for `V2_C3`. -/
noncomputable def outV2_C3 : TerminalOut := .returned ⟨.unit, callerMemV2_C3⟩

/-- 8-byte 4-aligned shared caller allocation at `allocId = 2` for `V2_C4a`/`b`.
-/
noncomputable def callerMemV2_C4 : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 2, mutability := .shared
  bytes := [
    .init 1 none, .init 2 none, .init 3 none, .init 4 none,
    .init 5 none, .init 6 none, .init 7 none, .init 8 none
  ]
  live := true
}]⟩

/-- `V2_C4a` (Entry reference misalignment UB): passes `&[u32]` at byte offset
`1` into `callerMemV2_C4`. -/
noncomputable def progV2_C4a_entryMisalign : Program :=
  mkV2Prog {
    identity := "v2_c4a_entry_misalign"
    argumentCount := 1
    locals := [u32Ty, .ref .shared (.slice u32Ty)]
    basicBlocks := [{
      statements :=
        [.assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar 0⟩))]
      terminator := .return_
    }]
  }

/-- Entry query for `V2_C4a`. -/
noncomputable def queryV2_C4a : Query := {
  args := [.slicePtr ⟨some 2, 1, .isize⟩ 0]
  callerMem := callerMemV2_C4
}

/-- `V2_C4b` (Raw-pointer deref misalignment UB): dereferences unaligned
`*const u32` at byte offset `1` inside `callerMemV2_C4`. -/
noncomputable def progV2_C4b_derefMisalign : Program :=
  mkV2Prog {
    identity := "v2_c4b_deref_misalign"
    argumentCount := 1
    locals := [u32Ty, .rawPtr .shared u32Ty]
    basicBlocks := [{
      statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩))]
      terminator := .return_
    }]
  }

/-- Entry query for `V2_C4b`. -/
noncomputable def queryV2_C4b : Query := {
  args := [.ptr ⟨some 2, 1, .isize⟩]
  callerMem := callerMemV2_C4
}

/-- `V2_C5` (Read-only caller memory write UB): writes `7u8` through `*mut u8`
pointing into a `.shared` (immutable) caller allocation. -/
noncomputable def progV2_C5_roWrite : Program :=
  mkV2Prog {
    identity := "v2_c5_ro_write"
    argumentCount := 1
    locals := [.unit, .rawPtr .mut u8Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨1, [.deref]⟩ (.use (.constant ⟨u8Ty, .scalar 7⟩)),
        .assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))
      ]
      terminator := .return_
    }]
  }

/-- Immutable 1-byte caller allocation at `allocId = 2` for `V2_C5`. -/
noncomputable def callerMemV2_C5 : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 0, mutability := .shared
  bytes := [.init 1 none]
  live := true
}]⟩

/-- Entry query for `V2_C5`. -/
noncomputable def queryV2_C5 : Query := {
  args := [.ptr ⟨some 2, 0, .isize⟩]
  callerMem := callerMemV2_C5
}

/-- `V2_C6` (Stack-reference escape / dangling return UB): initializes
`_1 = 42u32`, borrows `_0 = &_1`, and returns `_0`. `evalStepV2` detects stack
escape via `refsStayInCallerMem`; `ProfileV2RefMachine` frees `_1` during
`CallMachine.cleanup` and rejects the return in `refReadReturnValV2`. -/
noncomputable def progV2_C6_danglingLocalRef : Program :=
  mkV2Prog {
    identity := "v2_c6_dangling_local_ref"
    argumentCount := 0
    locals := [.ref .shared u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar 42⟩)),
        .assign ⟨0, []⟩ (.ref .shared ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }

/-- Entry query for `V2_C6`. -/
noncomputable def queryV2_C6 : Query := {
  args := []
  callerMem := ⟨[]⟩
}

/-- Domain predicate containing the seven Profile v2 correspondence canaries
(`V2_C1`–`V2_C6`). -/
def ProfileV2CanaryDomain (p : Program) (q : Query) : Prop :=
  (p = progV2_C1_splitAt ∧ q = queryV2_C1) ∨
  (p = progV2_C2_offsetWrite ∧ q = queryV2_C2) ∨
  (p = progV2_C3_selfPtrMetadata ∧ q = queryV2_C3) ∨
  (p = progV2_C4a_entryMisalign ∧ q = queryV2_C4a) ∨
  (p = progV2_C4b_derefMisalign ∧ q = queryV2_C4b) ∨
  (p = progV2_C5_roWrite ∧ q = queryV2_C5) ∨
  (p = progV2_C6_danglingLocalRef ∧ q = queryV2_C6)

/-- Extended Profile v2 domain adding the three conservative-edge witnesses from
`Anneal.MirCorrespondence.ProfileV2EdgeWitnesses`. -/
def ProfileV2ExtendedDomain (p : Program) (q : Query) : Prop :=
  ProfileV2CanaryDomain p q ∨
  (p = progV2Edge1ZeroOffsetOob ∧ q = queryV2Edge1ZeroOffsetOob) ∨
  (p = progV2Edge2NullZstDeref ∧ q = queryV2Edge2NullZstDeref) ∨
  (p = progV2Edge3ConstToMutCast ∧ q = queryV2Edge3ConstToMutCast)

/-! ## Section 2: Shared Profile v2 Canary Helpers -/

theorem initRefStateV2_ub_of_invalidRefs_v2 (rp : RefProg) (q : Query)
    (ms : Nat) (rbody : RefBody) (localTys : List MirTy) (retTy : MirTy)
    (mem0 : RefMiriMem)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (h_w : rp.pointerWidthBits = 64) (h_v : rp.mirProfileVersion = 2)
    (h_cm : refValidCallerMemoryV2 q.callerMem = true)
    (h_b :
      Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId = some rbody)
    (h_lt : decodeLocalTys rp.types rbody.locals = some localTys)
    (h_chk :
      (rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount localTys.length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid localTys rbody ||
        !refCastTypesValid rp.types localTys rbody ||
        !localTys.all refIsSupportedLocalTyV2 ||
        !localTys.all refTyLayoutFitsU64V2) = false)
    (h_arg :
      checkRefArgsMatchV2 q.args ((localTys.drop 1).take rbody.argumentCount) =
        true)
    (h_r0 : Trusted.MirSemantics.getElem? localTys 0 = some retTy)
    (h_icm :
      refInitCallerMemoryV2 rp.types q.callerMem retTy = .ok (mem0, retPlace))
    (h_refs :
      refRefsValidInMiriListV2 mem0 ((localTys.drop 1).take rbody.argumentCount)
        q.args = false)
    (h_args_u64 : refValListAllocIdsFitU64V2 q.args = true := by rfl) :
    initRefStateV2 rp q ms = .error .undefined := by
  dsimp only [initRefStateV2]
  simp only [h_w, h_v, Nat.beq, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ite_false]
  simp only [h_cm, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [h_b]
  dsimp only
  rw [h_lt]
  dsimp only
  simp only [h_chk, Bool.false_eq_true, ite_false]
  simp only [h_arg, h_args_u64, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ite_false]
  rw [h_r0]
  dsimp only
  rw [refInitCallerMemoryV2_withArgs_err_of_invalidRefs rp.types q.callerMem
    retTy ((localTys.drop 1).take rbody.argumentCount) q.args mem0 retPlace
    h_icm h_refs (refMaxValListAllocIdV2 q.args)
    (refValListHasAllocIdV2 1 q.args)]

theorem misalignmentWith_alloc2_v2 (types : List MirTy)
    (ma2 : RefMiriAlloc) (st : RefMiriState) (off : Miri.ABI.Size)
    (h_sz : ma2.byteSize = Miri.ABI.Size.ofBytes 8)
    (h_al : ma2.align = ⟨2⟩)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨.machine (), ma2⟩))
    (h_off : off = Miri.ABI.Size.ofBytes 1) :
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨off, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩
    Miri.Interpreter.PointerPlaceMachine.misalignmentWith
        (refAccessConfigV2 types) refAlignCtxV2 ptr ⟨2⟩ st =
      .ok (some ⟨⟨0⟩, ⟨2⟩⟩) st := by
  intro ptr
  subst h_off
  have h_inf : st.machine.memory.getAllocInfo alloc2IdV2 =
      .ok ⟨Miri.ABI.Size.ofBytes 8, ⟨2⟩, .liveData, ma2.mutability⟩ := by
    dsimp only [Miri.Memory.MemoryState.getAllocInfo]
    rw [h_find]
    dsimp only
    rw [h_sz, h_al]
    rfl
  unfold Miri.Interpreter.PointerPlaceMachine.misalignmentWith
  dsimp only [refAlignCtxV2, get, getThe, MonadStateOf.get, EStateM.get, set,
    MonadStateOf.set, EStateM.set, bind, Bind.bind, pure, Pure.pure, EStateM.pure]
  refine eStateM_apply_bind EStateM.get _ st st st rfl ?_
  rw [show (Miri.Interpreter.ValidityMachine.AlignmentCheck.Symbolic ==
      Miri.Interpreter.ValidityMachine.AlignmentCheck.None ||
      ((⟨2⟩ : Miri.ABI.Align).pow2 == 0)) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (refAccessConfigV2 types).resolvePointer st.machine.memory ptr 0
      st.machine = .ok (.ok ⟨alloc2IdV2, Miri.ABI.Size.ofBytes 1,
        .concrete Miri.Memory.BorTag.one⟩) st.machine from rfl]
  dsimp only
  refine eStateM_apply_bind (EStateM.set _) _ () st st rfl ?_
  refine eStateM_apply_bind (EStateM.pure _) _ _ st st rfl ?_
  refine eStateM_apply_bind EStateM.get _ st st st rfl ?_
  dsimp only
  rw [h_inf]
  refine eStateM_apply_bind _ _
    (Miri.Memory.AllocationInfo.mk (Miri.ABI.Size.ofBytes 8) ⟨2⟩
      .liveData ma2.mutability) st st rfl ?_
  dsimp only [refRuntimeLayoutV2]
  refine eStateM_apply_bind _ _
    (some (Miri.Memory.Misalignment.mk ⟨0⟩ ⟨2⟩)) st st rfl ?_
  have h_is : Miri.Memory.isPtrMisaligned ptr ⟨2⟩ true
      (fun _ _ => Except.ok ⟨alloc2IdV2, Miri.ABI.Size.ofBytes 1,
        Miri.Memory.ProvenanceExtra.concrete Miri.Memory.BorTag.one⟩)
      st.machine.memory.getAllocInfo (fun _ _ _ _ _ =>
        some (Miri.Memory.Misalignment.mk ⟨0⟩ ⟨2⟩)) =
      .ok (some (Miri.Memory.Misalignment.mk ⟨0⟩ ⟨2⟩)) := by
    dsimp only [Miri.Memory.isPtrMisaligned, Except.mapError, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    rw [h_inf]
    cases ma2.mutability <;> rfl
  dsimp only [Except.mapError]
  rw [show Miri.Memory.isPtrMisaligned ptr ⟨2⟩ true
      (fun _ _ => Except.ok ⟨alloc2IdV2, Miri.ABI.Size.ofBytes 1,
        Miri.Memory.ProvenanceExtra.concrete Miri.Memory.BorTag.one⟩)
      st.machine.memory.getAllocInfo (fun _ _ _ _ _ =>
        some (Miri.Memory.Misalignment.mk ⟨0⟩ ⟨2⟩)) = _ from h_is]
  rfl

theorem memoryAccess_read_v2 (types : List MirTy)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (tree : Miri.TreeBorrows.BorrowTree) (id : Miri.Memory.AllocId)
    (_ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (prov : Miri.Memory.ProvenanceExtra) (rng : Miri.Memory.AllocRange)
    (h_dr : machine.dataRace = none)
    (h_bt : machine.borrowTracker = none) :
    Miri.Interpreter.PlaceMachine.memoryAccess (refAccessConfigV2 types) false
      ⟨machine, none⟩ tree id prov rng = ⟨⟨machine, none⟩, tree, .ok ()⟩ := by
  cases machine with
  | mk m b d t r a u pmd =>
    dsimp only at h_dr h_bt
    subst h_dr h_bt
    dsimp only [Miri.Interpreter.PlaceMachine.memoryAccess, Id.run, bind,
      Bind.bind, pure, Pure.pure,
      Miri.Interpreter.MachineHooks.memoryRaceAccess,
      refAccessConfigV2, refAccessConfig]
    rfl

theorem getPtrAlloc_live_nonghost_v2 (types : List MirTy)
    (sz : Miri.ABI.Size) (signedSize : Int)
    (mem mem' : RefMiriMem) (kind : Miri.Memory.MemoryKind Unit)
    (alloc : RefMiriAlloc)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (aid : Miri.Memory.AllocId) (off : Miri.ABI.Size)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (prov : Miri.Memory.ProvenanceExtra)
    (h_find :
      mem.live.find? (fun e => e.1 == aid) = some (aid, ⟨kind, alloc⟩))
    (h_any : (mem.live.any (fun entry => entry.1 == aid)) = true)
    (h_set : mem.setLiveAllocation aid alloc = .ok mem')
    (h_sz : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_cb : Miri.Memory.checkedBounds ⟨Miri.ABI.Size.ofBytes 8⟩ aid
      alloc.byteSize off signedSize .memoryAccess = .ok ())
    (h_rp : refResolvePointerPure ptr signedSize = .ok ⟨aid, off, prov⟩)
    (h_dr : machine.dataRace = none)
    (h_bt : machine.borrowTracker = none) :
    let acc := refAccessConfigV2 types
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz false none
        acc.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks acc) =
      ⟨mem', ⟨machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off sz, alloc⟩,
        .ok (some ⟨aid, Miri.Memory.allocRange off sz, alloc⟩)⟩ := by
  intro acc
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRaw mem ⟨machine, none⟩
      aid none acc.globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRaw, acc, refAccessConfigV2,
      refAccessConfig, refGlobalAllocationHooks, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [h_find]
  have h_res_ok :
      (Miri.Interpreter.PlaceMachine.accessHooks acc).resolvePointer
          mem ⟨machine, none⟩ ptr signedSize =
        ⟨⟨machine, none⟩, .ok (.ok ⟨aid, off, prov⟩)⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    exact Miri.Interpreter.PlaceMachine.resolvePointer_ok acc mem machine ptr
      signedSize _ (by
        dsimp only [acc, refAccessConfigV2, refAccessConfig, refResolvePointer]
        rw [h_rp])
  have h_ba :
      (Miri.Interpreter.PlaceMachine.accessHooks acc).beforeAllocationAccess
          ⟨machine, none⟩ aid = ⟨⟨machine, none⟩, .ok ()⟩ := rfl
  have h_mr :
      (Miri.Interpreter.PlaceMachine.accessHooks acc).beforeMemoryRead
          ⟨machine, none⟩ alloc.extra ptr aid prov
          (Miri.Memory.allocRange off sz) =
        ⟨⟨machine, none⟩, alloc.extra, .ok ()⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    exact memoryAccess_read_v2 types machine alloc.extra aid ptr prov
      (Miri.Memory.allocRange off sz) h_dr h_bt
  have h_se : alloc.setExtra alloc.extra = alloc := by cases alloc; rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAlloc]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sz]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_res_ok]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [ite_false_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_cb]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [show (!false) = true from rfl, ite_true_eq]
  simp only [Bool.false_eq_true, ite_false, Option.map, h_res_ok, h_ba, h_mr,
    h_any, h_se, h_set]
  rfl

theorem getPlaceAlloc_misaligned_v2 {P E K H X : Type} [DecidableEq K]
    (memory mem' : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (bad : Miri.Memory.Misalignment)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (misaligned : place.mplace.misaligned = some bad)
    (actual : Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
      ⟨Miri.ABI.Size.ofBytes 8⟩ place.mplace.ptr place.layout.size
      ghost kind global access =
      ⟨mem', hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAlloc memory hooks place
        refRuntimeLayoutV2 ghost kind global access dynamic =
      ⟨mem', hooks, some reference,
        .error (.pointerAccess (.access (.alignmentCheckFailed bad)))⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal mis =>
      dsimp only at misaligned
      subst misaligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
              ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error =>
              Miri.Interpreter.MemoryOperandResult.mk
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess error))
            | Except.ok _ =>
              Miri.Interpreter.MemoryOperandResult.mk
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess
                  (.access (.alignmentCheckFailed bad))))) = _
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error =>
                Miri.Interpreter.MemoryOperandResult.mk
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                  (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess error))
              | Except.ok _ =>
                Miri.Interpreter.MemoryOperandResult.mk
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                  (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess
                    (.access (.alignmentCheckFailed bad))))) = _
            rw [actual]

noncomputable def alloc4IdV2 : Miri.Memory.AllocId := ⟨4, by decide⟩
noncomputable def alloc5IdV2 : Miri.Memory.AllocId := ⟨5, by decide⟩

theorem placeToOp_local_imm_v2 (types : List MirTy)
    (localId : LocalId) (ty : MirTy)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (st : RefMiriState)
    (h_uns : refIsUnsizedTyV2 ty = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTyV2 types ty)⟩) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooksV2 types).place 0
        ⟨.local 0 localId none frame.localsIdentity,
          refLocalLayoutForTyV2 types ty⟩ st =
      .ok ⟨.immediate imm, refLocalLayoutForTyV2 types ty⟩ st := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_fi : (refBasePlaceProjectionHooksV2 types).place.frameIndex st =
      .ok 0 st := by
    dsimp only [refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
      Miri.Interpreter.PlaceMachine.placeHooks, bind, Bind.bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      Miri.Interpreter.Stack.frameIndex]
    rw [h_fr]; rfl
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]; rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTyV2 types ty).layout.isSized = true :=
    refLayoutDataForTyV2_isSized ty h_uns
  have h_dbg : (refBasePlaceProjectionHooksV2 types).place.debugAssertions =
      false := rfl
  have h_vip : (refBaseCompilerHooksV2 types).validationInProgress =
      (fun st => .ok false st) := rfl
  have h_ar := afterLocalRead_no_race_v2 st frame localId h_fr h_dr
  have h_lto :
      (refBasePlaceProjectionHooksV2 types).place.localToOp 0 localId st =
        .ok ⟨.immediate imm, refLocalLayoutForTyV2 types ty⟩ st := by
    dsimp only [refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
      Miri.Interpreter.PlaceMachine.placeHooks,
      Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore,
      Miri.Interpreter.PlaceMachine.layoutLocal]
    simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      h_cf, h_get, h_op, h_sz, h_vip, h_ar,
      Bool.not_true, Bool.false_eq_true, ite_false]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore]
  simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    h_fi, h_dbg, h_lto, bne_self_eq_false, Bool.false_eq_true, ite_false]

private theorem visit_local_int_ok_v2 (types : List MirTy) (fuel : Nat)
    (st : RefMiriState) (localId : LocalId) (w : IntWidth) (s : Bool)
    (bits : BitVec 128)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_tid : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (.scalar (.fromScalarInt (miriScalar w bits)))),
        some (refLocalLayoutForTyV2 types (.int w s))⟩) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 (fuel + 1)
        (refInitSessV2 false)
        ⟨.local 0 localId none frame.localsIdentity,
          refLocalLayoutForTyV2 types (.int w s)⟩ st =
      .ok (refInitSessV2 false) st := by
  let lay := refLocalLayoutForTyV2 types (.int w s)
  let imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromScalarInt (miriScalar w bits))
  let place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
    ⟨.local 0 localId none frame.localsIdentity, lay⟩
  have h_toOp := placeToOp_local_imm_v2 types localId (.int w s)
    imm frame st rfl h_fr h_dr h_get
  have h_ri_vm :
      Miri.Interpreter.ValidityMemory.readImmediate
        (refValidityMemoryEnvV2 types) ⟨.immediate imm, lay⟩ .integer st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar w bits)), lay⟩ st := by
    cases st with | mk sk mc => rfl
  have h_ri : (refValHooksV2 types).readImmediate 0 place .integer st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar w bits)), lay⟩ st := by
    rw [refValHooksV2_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_ri_vm
  have h_cls : (refValHooksV2 types).classify 0 lay.ty st =
      .ok .integer st := by
    rw [refValHooksV2_classify]
    dsimp only [lay, refLocalLayoutForTyV2]
    rw [h_tid]
  have h_cp : (refValHooksV2 types).clearProvenance 0 place st = .ok () st := by
    change Miri.Interpreter.ValidityMemory.clearPlaceProvenance
      (refValidityMemoryEnvV2 types)
      (refBasePlaceProjectionHooksV2 types).place
      0 (fun st => .ok false st) (fun _ _ st => .ok () st) place st =
      .ok () st
    dsimp only [Miri.Interpreter.ValidityMemory.clearPlaceProvenance,
      bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    rfl
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_cls]
  dsimp only
  change (EStateM.bind (EStateM.bind
    ((refValHooksV2 types).readImmediate 0 place .integer) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_ri]
  change (EStateM.bind (EStateM.bind
    ((refValHooksV2 types).clearProvenance 0 place) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_cp]
  rfl

theorem int_validate_local_v2 (types : List MirTy) (st : RefMiriState)
    (localId : LocalId) (w : IntWidth) (s : Bool) (bits : BitVec 128)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_tid : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (.scalar (.fromScalarInt (miriScalar w bits)))),
        some (refLocalLayoutForTyV2 types (.int w s))⟩) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types) 0 16
        ⟨.local 0 localId none frame.localsIdentity,
          refLocalLayoutForTyV2 types (.int w s)⟩
        true true st = .ok () st := by
  let lay := refLocalLayoutForTyV2 types (.int w s)
  let imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromScalarInt (miriScalar w bits))
  let place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
    ⟨.local 0 localId none frame.localsIdentity, lay⟩
  have h_toOp := placeToOp_local_imm_v2 types localId (.int w s)
    imm frame st rfl h_fr h_dr h_get
  have h_vis := visit_local_int_ok_v2 types 15 st localId w s bits frame
    h_fr h_dr h_tid h_get
  exact validatePlace_empty_noRanges_v2 types st st place
    ⟨.immediate imm, lay⟩ (refInitSessV2 false) (refInitSessV2 false)
    h_toOp rfl h_vis rfl rfl

theorem alloc_writeInt_spec_v2 {E : Type}
    (a : Miri.Memory.Allocation Miri.Memory.Provenance E)
    (start : Miri.ABI.Size) (w : IntWidth) (bits : BitVec 128)
    (cleared : Miri.Memory.ProvenanceMap Miri.Memory.Provenance)
    (h_sz : a.len = a.byteSize.bytes.toNat)
    (h_mut : a.mutability = .Mut)
    (h_im : a.initializationMask.len = a.byteSize)
    (h_wf : Miri.Memory.InitMask.WriteProof.WellFormed a.initializationMask)
    (h_bd : start.bytes.toNat + (toMiriSize w).bytes.toNat ≤
      a.byteSize.bytes.toNat)
    (h_clr : ∀ fullBytes : Array UInt8,
      a.getBytesUnchecked
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO a.byteSize) =
        .ok fullBytes →
      a.provenanceMap.clear (Miri.Memory.allocRange start (toMiriSize w))
        fullBytes
        (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits) =
        .ok () cleared) :
    let rng := Miri.Memory.allocRange start (toMiriSize w)
    let sc := Miri.Memory.Scalar.fromScalarInt (miriScalar w bits)
    ∃ a',
      a.writeScalar refRuntimeLayoutV2.base rng sc = .ok () a' ∧
      a'.byteSize = a.byteSize ∧
      a'.len = a.len ∧
      a'.mutability = a.mutability ∧
      a'.align = a.align ∧
      a'.extra = a.extra ∧
      a'.initializationMask.len = a.initializationMask.len ∧
      Miri.Memory.InitMask.WriteProof.WellFormed a'.initializationMask ∧
      a.initializationMask.setRange rng true = .ok a'.initializationMask ∧
      a'.initializationMask.isRangeInitialized rng = .ok (.ok ()) ∧
      a'.provenanceMap = cleared ∧
      a'.getBytesUnchecked rng =
        .ok (Array.ofFn (fun i : Fin rng.size.bytes.toNat =>
          UInt8.ofNat (Nat.mod (Nat.div
            (@truncateBits w bits).toNat (Nat.pow 2 (8 * i.1))) 256))) ∧
      (∀ (qRange : Miri.Memory.AllocRange) (qFin : Miri.ABI.Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ a.byteSize.bytes.toNat →
        (rng.start.bytes.toNat + rng.size.bytes.toNat ≤
            qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ rng.start.bytes.toNat) →
        a'.getBytesUnchecked qRange = a.getBytesUnchecked qRange) := by
  intro rng sc
  let tb : BitVec 128 := @truncateBits w bits
  have h_wnz : rng.size.bytes ≠ 0 := by
    dsimp only [rng, Miri.Memory.allocRange]; cases w <;> decide
  have h_w16 : rng.size.bytes.toNat ≤ 16 := by
    dsimp only [rng, Miri.Memory.allocRange]; cases w <;> decide
  have h_bd' : rng.start.bytes.toNat + rng.size.bytes.toNat ≤
      a.byteSize.bytes.toNat := h_bd
  have h_conv : sc.toBitsOrPtrInternal rng.size = .ok (.bits tb) := by
    rw [show tb = (miriScalar w bits).data from (miriScalar_data w bits).symm]
    cases w <;> rfl
  let ⟨a', h_ws, h_bsz, h_alen, h_amut, h_aal, h_aex, _, h_iml, h_imw, h_imset,
      h_imin, h_pm', h_gb, _, h_pres⟩ :=
    Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base a rng sc
      (.bits tb) cleared cleared h_sz h_mut h_im h_wf h_wnz h_w16 h_bd'
      h_conv h_clr rfl
  have h_gb_lit : a'.getBytesUnchecked rng =
      .ok (Array.ofFn (fun i : Fin rng.size.bytes.toNat =>
        UInt8.ofNat (Nat.mod (Nat.div tb.toNat (Nat.pow 2 (8 * i.1))) 256))) := by
    have h_g := h_gb tb rfl
    rw [show refRuntimeLayoutV2.base.endian = .little from rfl] at h_g
    exact h_g
  exact ⟨a', h_ws, h_bsz, h_alen, h_amut, h_aal, h_aex, h_iml, h_imw,
    h_imset, h_imin, h_pm', h_gb_lit, h_pres⟩

theorem c1_provMap_copy24 (p : Miri.Memory.Provenance)
    (srcPm : Miri.Memory.ProvenanceMap Miri.Memory.Provenance)
    (srcData dstData : Array UInt8)
    (h_src : Miri.Memory.ProvenanceMap.insertPtr Miri.ABI.Size.ZERO p
      (Miri.ABI.Size.ofBytes 8)
      (Miri.Memory.ProvenanceMap.new :
        Miri.Memory.ProvenanceMap Miri.Memory.Provenance) = .ok () srcPm) :
    ∃ copyPrep,
      srcPm.prepareCopy
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
        srcData (Miri.ABI.Size.ofBytes 8) = .ok copyPrep ∧
      (Miri.Memory.ProvenanceMap.new :
        Miri.Memory.ProvenanceMap Miri.Memory.Provenance).clear
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
        dstData (Miri.ABI.Size.ofBytes 8) =
        .ok () (Miri.Memory.ProvenanceMap.new :
          Miri.Memory.ProvenanceMap Miri.Memory.Provenance) ∧
      Miri.Memory.ProvenanceMap.applyCopy copyPrep
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
        1 (Miri.Memory.ProvenanceMap.new :
          Miri.Memory.ProvenanceMap Miri.Memory.Provenance) = .ok () srcPm ∧
      srcPm.readPtr Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) =
        .ok (some p) ∧
      srcPm.rangeEmpty (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 8)
        (Miri.ABI.Size.ofBytes 8)) (Miri.ABI.Size.ofBytes 8) = .ok true ∧
      srcPm.rangeEmpty (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 16)
        (Miri.ABI.Size.ofBytes 8)) (Miri.ABI.Size.ofBytes 8) = .ok true := by
  have h_ins0 := Miri.Memory.ProvenanceMap.insertPtr_new Miri.ABI.Size.ZERO
    (Miri.ABI.Size.ofBytes 8) (Miri.ABI.Size.ofBytes 8) p (by decide) rfl
  rw [h_ins0] at h_src
  injection h_src with _ h_src_eq
  let prep : Miri.Memory.ProvenanceCopy Miri.Memory.Provenance :=
    ⟨Array.mk [(Miri.ABI.Size.ZERO, p)], Array.empty⟩
  have h_prep : srcPm.prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
      srcData (Miri.ABI.Size.ofBytes 8) = .ok prep := by
    rw [← h_src_eq]; rfl
  have h_clr := provenanceMap_new_clear (Prov := Miri.Memory.Provenance)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
    dstData (Miri.ABI.Size.ofBytes 8) (by decide) (by decide)
  have h_app_eq :
      Miri.Memory.ProvenanceMap.applyCopy prep
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
        1 (Miri.Memory.ProvenanceMap.new :
          Miri.Memory.ProvenanceMap Miri.Memory.Provenance) =
      Miri.Memory.ProvenanceMap.insertPtr Miri.ABI.Size.ZERO p
        (Miri.ABI.Size.ofBytes 8)
        (Miri.Memory.ProvenanceMap.new :
          Miri.Memory.ProvenanceMap Miri.Memory.Provenance) := by
    unfold Miri.Memory.ProvenanceMap.applyCopy Miri.Memory.ProvenanceMap.insertPtr
    rw [show (Std.Legacy.Range.mk 0 (UInt64.toNat 1) 1 Nat.zero_lt_one) =
        Std.Legacy.Range.mk 0 1 1 Nat.zero_lt_one from rfl,
      Std.Legacy.Range.forIn_eq_forIn_range']
    rfl
  have h_app : Miri.Memory.ProvenanceMap.applyCopy prep
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
      1 (Miri.Memory.ProvenanceMap.new :
        Miri.Memory.ProvenanceMap Miri.Memory.Provenance) = .ok () srcPm := by
    rw [h_app_eq, h_ins0, h_src_eq]
  exact ⟨prep, h_prep, h_clr, h_app,
    by rw [← h_src_eq]; rfl,
    by rw [← h_src_eq]; rfl,
    by rw [← h_src_eq]; rfl⟩

theorem eStateM_bind2_ok {ε σ α β γ : Type} {x : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ}
    {a : α} {s s₁ : σ} (h : x s = .ok a s₁) :
    EStateM.bind (EStateM.bind x f) g s = EStateM.bind (f a) g s₁ := by
  dsimp only [EStateM.bind]; rw [h]

theorem eStateM_bind3_ok {ε σ α β γ δ : Type} {x : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ}
    {k : γ → EStateM ε σ δ} {a : α} {s s₁ : σ} (h : x s = .ok a s₁) :
    EStateM.bind (EStateM.bind (EStateM.bind x f) g) k s =
      EStateM.bind (EStateM.bind (f a) g) k s₁ := by
  dsimp only [EStateM.bind]; rw [h]

/-- Step past an `.ok` prefix action under three nested `EStateM.bind`s. -/
private theorem eStateM_bind3_apply {ε σ α β γ δ : Type} {x : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ}
    {k : γ → EStateM ε σ δ} {a : α} {s s₁ : σ}
    {res : EStateM.Result ε σ δ} (h1 : x s = .ok a s₁)
    (h2 : EStateM.bind (EStateM.bind (f a) g) k s₁ = res) :
    EStateM.bind (EStateM.bind (EStateM.bind x f) g) k s = res := by
  rw [eStateM_bind3_ok h1, h2]

theorem writeImmediate_scalar_u64_at_poly {P E K H X : Type}
    [DecidableEq K] [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (memory afterMemory : Miri.Memory.MemoryState P E K) (hooks : H)
    (mplace : Miri.Interpreter.MemPlace P) (tyId : Option Nat)
    (s : Bool) (vr : Miri.ABI.WrappingRange) (bits : BitVec 128)
    (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (later : Miri.Interpreter.MemoryOperandLayout → Bool)
    (ref : Miri.Memory.AllocationAccessRef P E)
    (rng : Miri.Memory.AllocRange)
    (after : Miri.Memory.Allocation P E)
    (actual : Miri.Interpreter.getPlaceAllocMut memory hooks
        ⟨mplace, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
          .Scalar (.Initialized (value := .Int .I64 s)
            (validRange := vr)), tyId⟩⟩
        refRuntimeLayoutV2 false kind global access dynamic =
      ⟨memory, hooks, some ref, .ok (some ref)⟩)
    (selected : ref.range.subrange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (Miri.ABI.Size.ofBytes 8)) = .ok rng)
    (written : ref.allocation.writeScalar refRuntimeLayoutV2.base rng
      (.fromScalarInt (miriScalar .isize bits)) = .ok () after)
    (committed :
      memory.setLiveAllocation ref.allocId after = .ok afterMemory) :
    Miri.Interpreter.writeImmediateToMplaceNoValidate memory hooks
        (.scalar (.fromScalarInt (miriScalar .isize bits)))
        ⟨mplace, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
          .Scalar (.Initialized (value := .Int .I64 s)
            (validRange := vr)), tyId⟩⟩
        refRuntimeLayoutV2 false kind global access dynamic later =
      ⟨afterMemory, hooks, some { ref with allocation := after }, .ok ()⟩ := by
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure]
  rw [actual]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  change (match (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
      (ref.range.subrange (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (Miri.ABI.Size.ofBytes 8)))) with
    | Except.ok range => _
    | Except.error error => _) = _
  rw [selected]
  dsimp only [Except.mapError, pure, Pure.pure, Id.run]
  change (match (memory.setLiveAllocation ref.allocId
      (match Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base rng
          (.fromScalarInt (miriScalar .isize bits)) ref.allocation with
       | EStateM.Result.ok _ a => a
       | EStateM.Result.error _ a => a)) with
    | Except.ok next => _
    | Except.error error => _) = _
  rw [written]
  dsimp only
  rw [committed]
  rfl

theorem returnFromCurrentFrame_op_at_v2 (rp : RefProg)
    (st : RefMiriState)
    (retOp : Miri.Interpreter.Operand Miri.Memory.Provenance)
    (retTy : MirTy)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (bbId sIdx : Nat)
    (stmts : Array Miri.MIR.Statement) (memMid memOut : RefMiriMem)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_rc : frame.returnContinuation = .stop true)
    (h_rp : frame.returnPlace = .memory retPlace)
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bt : st.machine.borrowTracker = none)
    (h_thr : st.machine.threads = Miri.Concurrency.ThreadManager.initial true)
    (h_bb : frame.body.basicBlocks[bbId]? = some {
      statements := stmts
      terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
      cleanup := false })
    (h_retOp :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.localToOp 0 0 st =
        .ok ⟨retOp, refLocalLayoutForTyV2 rp.types retTy⟩ st)
    (h_clean : Miri.Interpreter.CallMachine.cleanup
      { refLifecycle rp.types with storage := refStorageHooksV2 rp.types }
      0 false frame
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := memMid } } =
      .ok .normal
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := memOut } })
    (h_copy : Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0
      ⟨retOp, refLocalLayoutForTyV2 rp.types retTy⟩
      ⟨.memory retPlace.mplace, retPlace.layout⟩ true
      { st with stack := ⟨Array.empty⟩ } =
      .ok ()
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := memMid } }) :
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
      refLimitsV2).terminator 0
      { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return } st =
      ({ st with stack := ⟨Array.empty⟩,
                 machine := { st.machine with memory := memOut } },
        .ok ()) := by
  have h_scf := stack_currentFrame_single_v2 st frame h_fr
  have h_rel :
      Miri.Interpreter.FrameRelevance.beforeStackPop st = .ok () st := by
    cases st with
    | mk stack machine =>
      cases stack with
      | mk frames =>
        cases machine with
        | mk m b d threads ra as u p =>
          dsimp only at h_fr h_thr
          subst h_fr h_thr
          rfl
  have h_pop :
      Miri.Interpreter.TypedMachineBindings.popRaw
        (Miri.Interpreter.TypedMachineBindings.retagHooks
          (refExecCfgV2 rp).access (refExecCfgV2 rp).retag) st =
        .ok frame { st with stack := ⟨Array.empty⟩ } := by
    dsimp only [Miri.Interpreter.TypedMachineBindings.popRaw,
      Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure,
      get, getThe, MonadStateOf.get, EStateM.get, set,
      MonadStateOf.set, EStateM.set, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [h_bt]
    simp only [Option.isSome, Bool.false_eq_true, ite_false, EStateM.pure]
    rw [h_rel]
    dsimp only [Miri.Interpreter.Stack.popFrame]
    rw [h_fr]
    rfl
  have h_lc : (refExecCfgV2 rp).lifecycle =
      { refLifecycle rp.types with
        storage := refStorageHooksV2 rp.types } := rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
    Miri.Interpreter.ControlFlow.evalTerminator,
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
    Miri.Interpreter.ExecutionControl.hooks,
    Miri.Interpreter.Call.run, Miri.Interpreter.MachineHooks.run,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [h_scf]
  dsimp only
  rw [h_loc]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [bne_self_eq_false, ite_false_eq, Bool.false_and, ite_false_eq]
  rw [h_retOp]
  dsimp only
  rw [h_pop]
  dsimp only
  rw [Bool.not_false, ite_true_eq, h_rp]
  dsimp only [Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
  simp only [h_copy, h_lc, h_clean, h_rc]
  rfl

theorem allocateStack_sized_v2 (rp : RefProg) (st : RefMiriState)
    (lay : Miri.Interpreter.LocalLayout) (aid : Miri.Memory.AllocId)
    (rawAlloc : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (h_sz_true : lay.layout.isSized = true)
    (h_max : ¬ (lay.layout.size.bytes > refMaxSizeOfVal.bytes))
    (h_try : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      lay.layout.size lay.layout.align.abi .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_rsz : rawAlloc.byteSize = lay.layout.size)
    (h_bt : st.machine.borrowTracker = none)
    (h_dr : st.machine.dataRace = none)
    (h_avail : st.machine.memory.idSupplyExhausted = false)
    (h_nz : st.machine.memory.nextAllocId ≠ 0)
    (h_src_av : st.machine.memory.sourceAllocIdWorldActive = true →
      st.machine.memory.sourceAllocIdExhausted = false)
    (h_src_nz : st.machine.memory.sourceAllocIdWorldActive = true →
      st.machine.memory.sourceAllocIdNext ≠ 0)
    (h_iss : ∀ id, id ∈ st.machine.memory.issuedIds →
      id.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_lv : ∀ row, row ∈ st.machine.memory.live →
      row.1.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_gl : ∀ row, row ∈ st.machine.memory.globals →
      row.allocId.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_dd : ∀ row, row ∈ st.machine.memory.dead →
      row.allocId.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_aid :
      (⟨st.machine.memory.nextAllocId, h_nz⟩ : Miri.Memory.AllocId) = aid) :
    ∃ mem1,
      st.machine.memory.reserveAllocId = (mem1, .ok aid) ∧
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.allocateStack 0 lay st =
        .ok ⟨⟨⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩,
            .none, none⟩, lay⟩
          { st with
            machine := { st.machine with
              memory := { mem1 with
                live := mem1.live.push
                  (aid, ⟨.stack, rawAlloc.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      lay.layout.size)⟩) } } } := by
  let ⟨mem1, h_res_raw⟩ :=
    Miri.Memory.MemoryState.reserve_of_highWater st.machine.memory
      h_avail h_nz h_src_av h_src_nz h_iss h_lv h_gl h_dd
  have h_res : st.machine.memory.reserveAllocId = (mem1, .ok aid) := by
    rw [h_aid] at h_res_raw; exact h_res_raw
  refine ⟨mem1, h_res, ?_⟩
  cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
    dsimp only at h_bt h_dr h_res; subst h_bt h_dr
    have h_raw :
        Miri.Interpreter.PlaceMachine.allocateStackRaw refAllocationConfig
            lay.layout.size lay.layout.align.abi
            ⟨sk, { memory := m, borrowTracker := none, dataRace := none,
                   threads := t, raceAllocations := r, allocationSpans := a,
                   user := u, pendingMoveDeinit := pmd }⟩ =
          .ok ⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩
            ⟨sk, { memory := { mem1 with
                      live := mem1.live.push (aid, ⟨.stack, rawAlloc.withExtra
                        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                          lay.layout.size)⟩) },
                   borrowTracker := none, dataRace := none, threads := t,
                   raceAllocations := r, allocationSpans := a, user := u,
                   pendingMoveDeinit := pmd }⟩ := by
      dsimp only [Miri.Interpreter.PlaceMachine.allocateStackRaw]
      rw [show refAllocationConfig.nativeStorage = none from rfl,
        show refAllocationConfig.zeroedStorage =
          (fun n _ => some (Array.replicate n.bytes.toNat 0)) from rfl]
      dsimp only [bind, Bind.bind, pure, Pure.pure]
      rw [h_try, eStateM_bind_pure_fn]
      dsimp only; rw [eStateM_bind_pure_fn]
      dsimp only [tryCatch, tryCatchThe, MonadExcept.tryCatch,
        MonadExceptOf.tryCatch, EStateM.tryCatch, EarlyReturn.runK,
        ExceptT.run, ExceptT.bind, ExceptT.pure, get, getThe,
        MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
        EStateM.bind, EStateM.pure]
      rw [h_rsz,
        show refAllocationConfig.maximumObjectSize = refMaxSizeOfVal from rfl]
      simp only [h_max, ite_false]
      dsimp only [bind, Bind.bind, pure, Pure.pure,
        EStateM.bind, EStateM.pure, EStateM.get, EStateM.set,
        EStateM.modifyGet]
      rw [h_res]; rfl
    rw [show (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place.allocateStack 0 lay =
        Miri.Interpreter.PlaceMachine.allocateStack refAllocationConfig lay
      from rfl]
    dsimp only [Miri.Interpreter.PlaceMachine.allocateStack, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_sz_true]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [eStateM_bind_ok h_raw]
    rfl

theorem memoryAccess_v2 (types : List MirTy) (write : Bool)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (tree : Miri.TreeBorrows.BorrowTree) (id : Miri.Memory.AllocId)
    (prov : Miri.Memory.ProvenanceExtra) (rng : Miri.Memory.AllocRange)
    (h_dr : machine.dataRace = none)
    (h_bt : machine.borrowTracker = none) :
    Miri.Interpreter.PlaceMachine.memoryAccess (refAccessConfigV2 types) write
      ⟨machine, none⟩ tree id prov rng = ⟨⟨machine, none⟩, tree, .ok ()⟩ := by
  cases machine with
  | mk m b d t r a u pmd =>
    dsimp only at h_dr h_bt
    subst h_dr h_bt
    dsimp only [Miri.Interpreter.PlaceMachine.memoryAccess, Id.run, bind,
      Bind.bind, pure, Pure.pure,
      Miri.Interpreter.MachineHooks.memoryRaceAccess,
      refAccessConfigV2, refAccessConfig]
    cases write <;> rfl

theorem getPtrAllocMut_live_nonghost_v2 (types : List MirTy)
    (sz : Miri.ABI.Size) (signedSize : Int)
    (mem mem' : RefMiriMem) (kind : Miri.Memory.MemoryKind Unit)
    (alloc : RefMiriAlloc)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (aid : Miri.Memory.AllocId) (off : Miri.ABI.Size)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (prov : Miri.Memory.ProvenanceExtra)
    (h_find :
      mem.live.find? (fun e => e.1 == aid) = some (aid, ⟨kind, alloc⟩))
    (h_mut : alloc.mutability = .Mut)
    (h_any : (mem.live.any (fun entry => entry.1 == aid)) = true)
    (h_set : mem.setLiveAllocation aid alloc = .ok mem')
    (h_sz : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_cb : Miri.Memory.checkedBounds ⟨Miri.ABI.Size.ofBytes 8⟩ aid
      alloc.byteSize off signedSize .memoryAccess = .ok ())
    (h_rp : refResolvePointerPure ptr signedSize = .ok ⟨aid, off, prov⟩)
    (h_dr : machine.dataRace = none)
    (h_bt : machine.borrowTracker = none) :
    let acc := refAccessConfigV2 types
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz false none
        acc.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks acc) =
      ⟨mem', ⟨machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off sz, alloc⟩,
        .ok (some ⟨aid, Miri.Memory.allocRange off sz, alloc⟩)⟩ := by
  intro acc
  have h_mut_f : (alloc.mutability == .Not) = false := by rw [h_mut]; rfl
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRawMut mem ⟨machine, none⟩
      aid none acc.globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRawMut,
      Miri.Memory.MemoryLifecycle.getAllocRaw, acc, refAccessConfigV2,
      refAccessConfig, refGlobalAllocationHooks, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [h_find]
    dsimp only
    rw [h_mut_f]
    rfl
  have h_res_ok :
      (Miri.Interpreter.PlaceMachine.accessHooks acc).resolvePointer
          mem ⟨machine, none⟩ ptr signedSize =
        ⟨⟨machine, none⟩, .ok (.ok ⟨aid, off, prov⟩)⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    exact Miri.Interpreter.PlaceMachine.resolvePointer_ok acc mem machine ptr
      signedSize _ (by
        dsimp only [acc, refAccessConfigV2, refAccessConfig, refResolvePointer]
        rw [h_rp])
  have h_ba :
      (Miri.Interpreter.PlaceMachine.accessHooks acc).beforeAllocationAccess
          ⟨machine, none⟩ aid = ⟨⟨machine, none⟩, .ok ()⟩ := rfl
  have h_mw :
      (Miri.Interpreter.PlaceMachine.accessHooks acc).beforeMemoryWrite
          ⟨machine, none⟩ alloc.extra ptr aid prov
          (Miri.Memory.allocRange off sz) =
        ⟨⟨machine, none⟩, alloc.extra, .ok ()⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    exact memoryAccess_v2 types true machine alloc.extra aid prov
      (Miri.Memory.allocRange off sz) h_dr h_bt
  have h_se : alloc.setExtra alloc.extra = alloc := by cases alloc; rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAllocMut]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sz]
  change (if ((signedSize != 0) = true) then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_res_ok]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  simp only [ite_true]
  rw [h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_cb]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [show (!false) = true from rfl]
  simp only [ite_true, Option.map, h_ba, h_mw, h_any, h_se, h_set]

theorem getPtrAlloc_live_ghost_v2
    (sz : Miri.ABI.Size) (signedSize : Int)
    (mem : RefMiriMem) (kind : Miri.Memory.MemoryKind Unit)
    (alloc : RefMiriAlloc)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (aid : Miri.Memory.AllocId) (off : Miri.ABI.Size)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (prov : Miri.Memory.ProvenanceExtra)
    (globalHooks : Miri.Memory.GlobalAllocationHooks Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser))
    (accessHooks : Miri.Memory.AllocationAccessHooks Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser)
      Miri.Memory.ProvenanceExtra)
    (h_gh : globalHooks = refGlobalAllocationHooks)
    (h_find :
      mem.live.find? (fun e => e.1 == aid) = some (aid, ⟨kind, alloc⟩))
    (h_sz : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_cb : Miri.Memory.checkedBounds ⟨Miri.ABI.Size.ofBytes 8⟩ aid
      alloc.byteSize off signedSize .memoryAccess = .ok ())
    (h_rp : accessHooks.resolvePointer mem ⟨machine, none⟩ ptr signedSize =
      ⟨⟨machine, none⟩, .ok (.ok ⟨aid, off, prov⟩)⟩) :
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz true none
        globalHooks accessHooks =
      ⟨mem, ⟨machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off sz, alloc⟩,
        .ok (some ⟨aid, Miri.Memory.allocRange off sz, alloc⟩)⟩ := by
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRaw mem ⟨machine, none⟩
      aid none globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRaw]
    rw [h_gh]
    dsimp only [refGlobalAllocationHooks, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [h_find]
  dsimp only [Miri.Memory.AllocationAccess.getPtrAlloc]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sz]
  change (if ((signedSize != 0) = true) then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [ite_false_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_cb]
  rfl

theorem readImmediate_mem_u32_v2 (types : List MirTy)
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
          (Miri.ABI.Size.ofBytes 4) ghost none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
        ⟨mem1, ⟨st.machine, none⟩,
          some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4),
            alloc⟩,
          .ok (some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4),
            alloc⟩)⟩)
    (h_sub : (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4)).subrange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)) =
      .ok (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4)))
    (h_rd : alloc.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4)) false = .ok sc) :
    let lay := refLocalLayoutForTyV2 types u32Ty
    let lml := Miri.Interpreter.localMemoryLayout lay
    Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect mplace) lml refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4), alloc⟩,
        .ok ⟨.scalar sc, lml⟩⟩ := by
  intro lay lml
  let rng := Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 4)
  let mplaceTy : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨mplace, ⟨Miri.ABI.Size.ofBytes 4, ⟨2⟩,
      .Scalar (.Initialized (value := .Int .I32 false)
        (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 4))),
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
            (Miri.ABI.Size.ofBytes 4))))
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

theorem refValHooksV2_retagPointer (types : List MirTy) (c : Choice)
    (v : Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance) (tid : TyId)
    (st : RefMiriState) (h_bt : st.machine.borrowTracker = none) :
    (refValHooksV2 types).retagPointer c v tid st = .ok none st := by
  cases st with | mk sk mc => cases mc with | mk _ bt _ _ _ _ _ _ =>
    dsimp only at h_bt; subst h_bt; rfl

theorem validatePlace_ref_u32_v2 (types : List MirTy) (isMem : Bool)
    (pRef : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance)
    (pTy : TyId)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (sc42 : Miri.Memory.Scalar Miri.Memory.Provenance)
    (st : RefMiriState)
    (h_ref : isMem = true → pRef = .memory retMemPlaceV2)
    (h_toOp : Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 types).place 0
      ⟨pRef, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st =
      .ok ⟨if isMem then .indirect retMemPlaceV2
          else .immediate (.scalar (.fromPointer refRuntimeLayoutV2.base ptr)),
        ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st)
    (h_vis : Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 16
      (refInitSessV2 isMem) ⟨pRef, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st =
      .ok { refInitSessV2 isMem with
        dataBytes := if isMem then some singleDataRange64V2 else none
        refTracking := (refInitSessV2 isMem).refTracking.map
          fun tr => tr.track ⟨a2Mp, refLocalLayoutForTyV2 types u32Ty⟩
            (fun _ => ⟨"", Array.mk [.deref]⟩) } st)
    (h_cls_u32 : (refValHooksV2 types).classify 0
      (refLocalLayoutForTyV2 types u32Ty).ty st = .ok .integer st)
    (h_ri_u32 : (refValHooksV2 types).readImmediate 0
      ⟨.memory a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ .integer st =
      .ok ⟨.scalar sc42, refLocalLayoutForTyV2 types u32Ty⟩ st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types) 0 16
      ⟨pRef, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ true true st = .ok () st := by
  let lay : Miri.Interpreter.LocalLayout := ⟨pTy, refThinPtrLayoutDataV2⟩
  let place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
    ⟨pRef, lay⟩
  let u32Lay := refLocalLayoutForTyV2 types u32Ty
  let path0 : Miri.Memory.ValidationPath := ⟨"", Array.mk [.deref]⟩
  let sess1 :
      Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
    { refInitSessV2 isMem with
      dataBytes := if isMem then some singleDataRange64V2 else none
      refTracking := (refInitSessV2 isMem).refTracking.map
        fun tr => tr.track ⟨a2Mp, u32Lay⟩ (fun _ => path0) }
  let trDone : Miri.Memory.Validity.RefTracking
      (Miri.Interpreter.ValidityVisitor.Key Miri.Memory.Provenance)
      Miri.Memory.ValidationPath :=
    { seen := Array.mk [⟨a2Mp, u32Lay⟩], todo := Array.empty }
  let childSess :
      Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
    { path := path0, flags := ⟨false, true⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  have h_vis_child :
      Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 16
        childSess ⟨.memory a2Mp, u32Lay⟩ st = .ok childSess st := by
    rw [Miri.Interpreter.ValidityVisitor.visit.eq_2]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_cls_u32]
    dsimp only
    change (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).readImmediate 0
        ⟨.memory a2Mp, u32Lay⟩ .integer) _) _ st) = _
    dsimp only [EStateM.bind]
    rw [h_ri_u32]
    rfl
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok (refValHooksV2_typeName types 0 pTy st),
    refValHooksV2_withGhostValidation, ite_true_eq]
  refine eStateM_apply_bind _ _ sess1 st st ?_ ?_
  · rw [refValHooksV2_toOp, eStateM_bind_ok h_toOp]
    cases isMem
    · rw [ite_false_eq]
      dsimp only
      rw [ite_true_eq]
      have hs : (⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty, none⟩ :
          Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance) =
          refInitSessV2 false := rfl
      rw [hs, eStateM_bind_ok h_vis,
        Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges _ 0 sess1 place
          rfl]
      dsimp only [pure, Pure.pure]; rw [eStateM_bind_pure]; rfl
    · rw [ite_true_eq]
      dsimp only
      rw [ite_true_eq]
      have hs :
          (⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty, some .empty⟩ :
            Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance) =
            refInitSessV2 true := rfl
      rw [hs, eStateM_bind_ok h_vis]
      dsimp only [place]
      rw [h_ref rfl]
      rfl
  · rw [ite_true_eq, eStateM_loop_forIn_eq st]
    dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
    have h_next : sess1.refTracking.bind Miri.Memory.Validity.RefTracking.next =
        some (((⟨a2Mp, u32Lay⟩ :
          Miri.Interpreter.ValidityVisitor.Key Miri.Memory.Provenance), path0),
          trDone) := by
      dsimp only [sess1, refInitSessV2, Option.map]
      cases isMem <;>
        (rw [Miri.Memory.Validity.RefTracking.track, ← Array.any_toList]; rfl)
    rw [h_next]
    dsimp only
    rw [show (16 == 0) = false from rfl, ite_false_eq]
    refine eStateM_bind3_apply (a := ()) (s₁ := st) ?_ ?_
    · rw [refValHooksV2_withGhostValidation, eStateM_bind_ok h_vis_child,
        Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges _ 0 childSess _
          rfl]
      dsimp only [pure, Pure.pure]
      rfl
    · rw [eStateM_bind2_ok (show (EStateM.pure _ :
          EStateM Miri.Interpreter.StepError RefMiriState _) st = _ from rfl)]
      dsimp only
      rw [eStateM_loop_forIn_eq st]
      dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
      rw [show (some trDone).bind Miri.Memory.Validity.RefTracking.next =
          none from rfl]
      dsimp only
      rw [eStateM_bind_pure_fn]
      dsimp only
      rw [eStateM_loop_forIn_eq st, ite_false_eq]
      rfl

/-! ## Section 3: Negative Canary Locksteps (`V2_C4a`–`V2_C6`) -/

/-- `V2_C4a` (Entry reference misalignment UB): `&[u32]` at byte offset `1`
faults with `.undefined` in `evalStepV2` and fails entry reference validation
with `.ub` (`initRefStateV2 = .error .undefined`) in `ProfileV2RefMachine`. -/
theorem V2_C4a_entryMisalign_lockstep :
    ReachesResultV2 progV2_C4a_entryMisalign queryV2_C4a (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C4a_entryMisalign queryV2_C4a
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C4a_entryMisalign queryV2_C4a ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C4a_entryMisalign)
        queryV2_C4a ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C4a_entryMisalign)
        queryV2_C4a ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C4a_entryMisalign) queryV2_C4a := by
  let ⟨h_f, h_excl, _, _, h_nwf⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2_C4a_entryMisalign)
      (q := queryV2_C4a) (fuel := 2) (expected := .undefined) rfl
  refine ⟨h_f, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf, ?_⟩
  let rp := encodeProg progV2_C4a_entryMisalign
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let alloc2 :=
    @GetElem.getElem _ Nat _ _ _ callerMemV2_C4.allocations 0 (by decide)
  let raw : List UInt8 := [1, 2, 3, 4, 5, 6, 7, 8]
  let ⟨ma2, h_ma2, _⟩ :=
    refAllocToMiriV2_plainInit_spec alloc2 raw rfl rfl (by decide) (by decide)
  let ⟨rawRet, h_raw, _, _, _, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 4) ⟨2⟩ 4 rfl rfl
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
                  (retAllocIdV2, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (Miri.ABI.Size.ofBytes 4))⟩)] }).setIssuedIds
      (Array.mk [alloc2IdV2, retAllocIdV2])
  let u32Lay := refLocalLayoutForTyV2 rp.types u32Ty
  have h_ins :
      refInsertCallerAllocsV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
          Array.empty callerMemV2_C4.allocations =
        .ok ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩)] },
          Array.mk [alloc2IdV2]) := by
    rw [show callerMemV2_C4.allocations = [alloc2] from rfl]
    dsimp only [refInsertCallerAllocsV2]
    rw [show refExactAllocIdV2 alloc2.allocId = some alloc2IdV2 from rfl, h_ma2]
    rfl
  have h_icm : refInitCallerMemoryV2 rp.types callerMemV2_C4 u32Ty =
      .ok (mem0, ⟨retMemPlaceV2, u32Lay⟩) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show u32Lay.layout.size = Miri.ABI.Size.ofBytes 4 from rfl,
      show u32Lay.layout.align.abi = (⟨2⟩ : Miri.ABI.Align) from rfl, h_raw]
    dsimp only
    rw [h_ins]
    rfl
  have h_refs :
      refRefsValidInMiriListV2 mem0 [.ref .shared (.slice u32Ty)]
        queryV2_C4a.args = false := by
    have h_f2 : mem0.live.find? (fun e => e.1 == alloc2IdV2) =
        some (alloc2IdV2, ⟨.machine (), ma2⟩) := by
      dsimp only [mem0]
      rw [← Array.find?_toList]
      rfl
    dsimp only [refRefsValidInMiriListV2, refRefsValidInMiriV2,
      refValidateRefInMiriV2, queryV2_C4a, u32Ty]
    rw [show (!(UInt64.toNat 0 *
        (refScalarLayoutDataV2 .i32 false).size.bytes.toNat).blt
        (Nat.pow 2 63)) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show refExactAllocIdV2 2 = some alloc2IdV2 from rfl]
    dsimp only
    rw [h_f2]
    dsimp only
    rw [show (!((UInt64.toNat 1).mod
        (Nat.pow 2 (refScalarLayoutDataV2 .i32 false).align.abi.pow2)).beq 0) =
        true from rfl]
    simp only [Bool.true_or, Bool.or_true, ite_true]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2_C4a ms = .error .undefined :=
    fun ms => initRefStateV2_ub_of_invalidRefs_v2 rp queryV2_C4a ms rbody
      [u32Ty, .ref .shared (.slice u32Ty)] u32Ty mem0 ⟨retMemPlaceV2, u32Lay⟩
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm h_refs
  let ⟨h1, h2, h3, _, _⟩ := ref_ub_of_init_error h_init
  exact ⟨h1, h3, h2⟩

/-- `V2_C5` (Read-only caller memory write UB): writing through `*mut u8` into
an immutable `.shared` caller allocation faults with `.undefined` in
`evalStepV2` and `.ub` in `ProfileV2RefMachine`. -/
theorem V2_C5_roWrite_lockstep :
    ReachesResultV2 progV2_C5_roWrite queryV2_C5 (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C5_roWrite queryV2_C5 (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C5_roWrite queryV2_C5 ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C5_roWrite)
        queryV2_C5 ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C5_roWrite)
        queryV2_C5 ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C5_roWrite) queryV2_C5 := by
  let ⟨h_f, h_excl, _, _, h_nwf⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2_C5_roWrite)
      (q := queryV2_C5) (fuel := 2) (expected := .undefined) rfl
  refine ⟨h_f, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf, ?_⟩
  let rp := encodeProg progV2_C5_roWrite
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let mkMem0 (a2 rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit) :
      RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(alloc2IdV2, ⟨.machine (), a2.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (Miri.ABI.Size.ofBytes 1))⟩),
                  (retAllocIdV2, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (Miri.ABI.Size.ZERO))⟩)] }).setIssuedIds
      (Array.mk [alloc2IdV2, retAllocIdV2])
  let unitLay := refLocalLayoutForTyV2 rp.types .unit
  let ptrLay := refLocalLayoutForTyV2 rp.types (.rawPtr .mut u8Ty)
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base
      ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩)
  let mkM0 (a2 rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit) :
      RefMiriState :=
    mkRefMiriState (mkRefMiriFrameV2 rp.types 0 rbody 0 0
      [⟨.live (.immediate .uninit), some unitLay⟩,
       ⟨.live (.immediate ptrImm), some ptrLay⟩]
      ⟨retMemPlaceV2, unitLay⟩) (mkMem0 a2 rawRet) refInitControl callerMemV2_C5
  let ⟨rawRet, h_raw, _, _, _, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  have h_step_m :
      match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
          (Array.mk [1]) ⟨0⟩ .Not with
      | .ok a2 => ∃ st' msg, Miri.Interpreter.ExecutionMachine.step
          (refExecutionConfigV2 rp) refLimitsV2 0 (mkM0 a2 rawRet) =
          (st', .error (.undefinedBehavior msg))
      | .error _ => False := ⟨_, _, rfl⟩
  let ⟨a2, h_a2⟩ :
      ∃ a, Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk [1]) ⟨0⟩ .Not = .ok a := ⟨_, rfl⟩
  rw [h_a2] at h_step_m
  let ⟨st', msg, h_s⟩ := h_step_m
  let alloc2 :=
    @GetElem.getElem _ Nat _ _ _ callerMemV2_C5.allocations 0 (by decide)
  have h_icm : refInitCallerMemoryV2 rp.types callerMemV2_C5 .unit =
      .ok (mkMem0 a2 rawRet, ⟨retMemPlaceV2, unitLay⟩) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show unitLay.layout.size = Miri.ABI.Size.ZERO from rfl,
      show unitLay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_raw]
    dsimp only
    rw [show callerMemV2_C5.allocations = [alloc2] from rfl]
    dsimp only [refInsertCallerAllocsV2, refAllocToMiriV2]
    rw [show refExactAllocIdV2 alloc2.allocId = some alloc2IdV2 from rfl,
      show refPlainInitBytesV2? alloc2.bytes = some [1] from rfl]
    dsimp only
    rw [show toMiriMutV2 alloc2.mutability = Miri.Memory.Mutability.Not from rfl,
      show ({ pow2 := alloc2.alignLog2 } : Miri.ABI.Align) = ⟨0⟩ from rfl,
      show alloc2.bytes.length = 1 from rfl, h_a2]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2_C5 ms =
      .ok { miri := mkM0 a2 rawRet, retTy := .unit,
            retPlace := ⟨retMemPlaceV2, unitLay⟩,
            stepsExecuted := 0, maxSteps := ms } := by
    intro ms
    exact initRefStateV2_ok_v2 rp queryV2_C5 ms rbody
      [.unit, .rawPtr .mut u8Ty] .unit (mkMem0 a2 rawRet) (mkMem0 a2 rawRet)
      ⟨retMemPlaceV2, unitLay⟩
      [⟨.live (.immediate .uninit), some unitLay⟩,
       ⟨.live (.immediate ptrImm), some ptrLay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  have h_exec : refCoreExecV2 rp .unit ⟨retMemPlaceV2, unitLay⟩ (fun _ => False)
      True False 1 (mkM0 a2 rawRet) := by
    dsimp only [refCoreExecV2]
    change (match evalRefCoreV2 rp .unit ⟨retMemPlaceV2, unitLay⟩
        (mkM0 a2 rawRet) with
      | .running miri' => refCoreExecV2 rp .unit ⟨retMemPlaceV2, unitLay⟩
          (fun _ => False) True False 0 miri'
      | .returned _ => False | .ub => True | .blocked => False)
    dsimp only [evalRefCoreV2]
    rw [h_s]
    exact True.intro
  let ⟨h1, h2, h3, _, _⟩ := ref_ub_of_coreExec h_init h_exec
  exact ⟨h1, h3, h2⟩

/-- `V2_C4b` (Raw-pointer dereference misalignment UB): dereferencing an
unaligned `*const u32` at byte offset `1` faults with `.undefined` in
`evalStepV2` and with `.ub` (`AlignmentCheckFailed`) in `ProfileV2RefMachine`.
-/
theorem V2_C4b_derefMisalign_lockstep :
    ReachesResultV2 progV2_C4b_derefMisalign queryV2_C4b (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C4b_derefMisalign queryV2_C4b
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C4b_derefMisalign queryV2_C4b ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C4b_derefMisalign)
        queryV2_C4b ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C4b_derefMisalign)
        queryV2_C4b ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C4b_derefMisalign) queryV2_C4b := by
  let ⟨h_f, h_excl, _, _, h_nwf⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2_C4b_derefMisalign)
      (q := queryV2_C4b) (fuel := 2) (expected := .undefined) rfl
  refine ⟨h_f, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf, ?_⟩
  let rp := encodeProg progV2_C4b_derefMisalign
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let alloc2 :=
    @GetElem.getElem _ Nat _ _ _ callerMemV2_C4.allocations 0 (by decide)
  have h_fb_spec :
      match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
          (Array.mk [1, 2, 3, 4, 5, 6, 7, 8]) ⟨2⟩ .Not with
      | .ok a => a.byteSize = Miri.ABI.Size.ofBytes 8 ∧ a.align = ⟨2⟩
      | .error _ => False := ⟨rfl, rfl⟩
  let ⟨a2, h_a2⟩ :
      ∃ a, Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk [1, 2, 3, 4, 5, 6, 7, 8]) ⟨2⟩ .Not = .ok a := ⟨_, rfl⟩
  rw [h_a2] at h_fb_spec
  let ⟨h_msz, h_mal⟩ := h_fb_spec
  let ma2 := a2.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
      (Miri.ABI.Size.ofBytes 8))
  have h_ma2 : refAllocToMiriV2 alloc2 = .ok ma2 := by
    dsimp only [refAllocToMiriV2]
    rw [show refPlainInitBytesV2? alloc2.bytes =
        some [1, 2, 3, 4, 5, 6, 7, 8] from rfl]
    dsimp only
    rw [show toMiriMutV2 alloc2.mutability = Miri.Memory.Mutability.Not from rfl,
      show ({ pow2 := alloc2.alignLog2 } : Miri.ABI.Align) = ⟨2⟩ from rfl,
      show alloc2.bytes.length = 8 from rfl, h_a2]
    rfl
  let ⟨rawRet, h_raw, _, _, _, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 4) ⟨2⟩ 4 rfl rfl
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
                  (retAllocIdV2, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (Miri.ABI.Size.ofBytes 4))⟩)] }).setIssuedIds
      (Array.mk [alloc2IdV2, retAllocIdV2])
  let u32Lay := refLocalLayoutForTyV2 rp.types u32Ty
  let ptrLay := refLocalLayoutForTyV2 rp.types (.rawPtr .shared u32Ty)
  let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
    ⟨Miri.ABI.Size.ofBytes 1, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
  let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
    [⟨.live (.immediate .uninit), some u32Lay⟩,
     ⟨.live (.immediate ptrImm), some ptrLay⟩]
    ⟨retMemPlaceV2, u32Lay⟩
  let m0 := mkRefMiriState frame0 mem0 refInitControl callerMemV2_C4
  have h_ins :
      refInsertCallerAllocsV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
          Array.empty callerMemV2_C4.allocations =
        .ok ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩)] },
          Array.mk [alloc2IdV2]) := by
    rw [show callerMemV2_C4.allocations = [alloc2] from rfl]
    dsimp only [refInsertCallerAllocsV2]
    rw [show refExactAllocIdV2 alloc2.allocId = some alloc2IdV2 from rfl, h_ma2]
    rfl
  have h_icm : refInitCallerMemoryV2 rp.types callerMemV2_C4 u32Ty =
      .ok (mem0, ⟨retMemPlaceV2, u32Lay⟩) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show u32Lay.layout.size = Miri.ABI.Size.ofBytes 4 from rfl,
      show u32Lay.layout.align.abi = (⟨2⟩ : Miri.ABI.Align) from rfl, h_raw]
    dsimp only
    rw [h_ins]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2_C4b ms =
      .ok { miri := m0, retTy := u32Ty,
            retPlace := ⟨retMemPlaceV2, u32Lay⟩,
            stepsExecuted := 0, maxSteps := ms } := by
    intro ms
    exact initRefStateV2_ok_v2 rp queryV2_C4b ms rbody
      [u32Ty, .rawPtr .shared u32Ty] u32Ty mem0 mem0
      ⟨retMemPlaceV2, u32Lay⟩
      [⟨.live (.immediate .uninit), some u32Lay⟩,
       ⟨.live (.immediate ptrImm), some ptrLay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  let mem0' : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(retAllocIdV2, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (Miri.ABI.Size.ofBytes 4))⟩),
                  (alloc2IdV2, ⟨.machine (), ma2⟩)] }).setIssuedIds
      (Array.mk [alloc2IdV2, retAllocIdV2])
  let a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
    ⟨⟨Miri.ABI.Size.ofBytes 1, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩,
      .none, some ⟨⟨0⟩, ⟨2⟩⟩⟩
  have h_find2 : m0.machine.memory.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨.machine (), ma2⟩) := by
    dsimp only [m0, mem0, mkRefMiriState]
    rw [← Array.find?_toList]
    rfl
  have h_any2 : (m0.machine.memory.live.any (fun e => e.1 == alloc2IdV2)) =
      true := by
    dsimp only [m0, mem0, mkRefMiriState, Miri.Memory.MemoryState.setIssuedIds]
    rw [← Array.any_toList]
    rfl
  have h_live :
      (m0.machine.memory.live.filter (fun row => row.fst != alloc2IdV2)).push
        (alloc2IdV2, ⟨.machine (), ma2⟩) = mem0'.live := by
    apply Array.toList_inj.mp
    dsimp only [m0, mem0, mem0', mkRefMiriState, mkRefMiriStackState,
      Miri.Memory.MemoryState.setIssuedIds]
    rw [Array.toList_push, Array.toList_filter]
    dsimp only [Array.toList, List.filter]
    rw [show (alloc2IdV2 != alloc2IdV2) = false from rfl,
      show (retAllocIdV2 != alloc2IdV2) = true from rfl]
    rfl
  have h_set2 : m0.machine.memory.setLiveAllocation alloc2IdV2 ma2 = .ok mem0' := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ h_find2]
    dsimp only
    rw [h_live]
    rfl
  let m1 : RefMiriState := { m0 with machine := { m0.machine with memory := mem0' } }
  have h_ev := projPlace_evalPlace_local_v2 rp m0 frame0 0 u32Lay
    (.live (.immediate .uninit)) true rfl rfl rfl
  have h_op1 := evalOperand_local_imm_v2 rp m0 frame0 1 ptrLay ptrImm
    none (Miri.Interpreter.OperandPath.rvalue "operand") rfl rfl rfl rfl
  have h_mis := misalignmentWith_alloc2_v2 rp.types ma2 m0
    (Miri.ABI.Size.ofBytes 1) (by exact h_msz) h_mal h_find2 rfl
  have h_deref :
      (Miri.Interpreter.ExecutionMachine.operandHooks
          (refExecCfgV2 rp)).dereference 0 ⟨.immediate ptrImm, ptrLay⟩ m0 =
        .ok ⟨a2Mp, u32Lay⟩ m0 := by
    change (refOperandLeavesV2 rp.types).dereference 0
        ⟨.immediate ptrImm, ptrLay⟩ m0 = _
    dsimp only [refOperandLeavesV2, refDereferenceOpV2, refFromImmediatePtrV2,
      refTyLayoutFitsU64V2, Bool.not_true, ite_false]
    rw [show resolveTy rp.types ptrLay.ty =
        some (.rawPtr .shared u32Ty) from rfl]
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 rp.types) ⟨.immediate ptrImm, ptrLay⟩ m0 =
        .ok ⟨ptrImm, ptrLay⟩ m0 from rfl]
    dsimp only
    rw [show resolveTy rp.types ptrLay.ty =
        some (.rawPtr .shared u32Ty) from rfl]
    dsimp only
    rw [show ptrImm.toScalarAndMeta =
        .ok (.fromPointer refRuntimeLayoutV2.base ptr, .none) from rfl]
    dsimp only
    rw [show (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr).toPointer
        refRuntimeLayoutV2.base = .ok ptr.withOptionalProvenance from by
      cases ptr; rfl]
    dsimp only
    rw [show (refLocalLayoutForTyV2 rp.types u32Ty).layout.align.abi =
        (⟨2⟩ : Miri.ABI.Align) from rfl]
    have h_m' := h_mis
    dsimp only [ptr] at h_m'
    dsimp only [ptr]
    dsimp only [Miri.Memory.Pointer.withOptionalProvenance]
    rw [h_m']
    rfl
  have h_l1 :
      Miri.Interpreter.OperandMachine.localToOp
          (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp))
          0 1 none m0 =
        .ok ⟨.immediate ptrImm, ptrLay⟩ m0 := by
    have h_l1' := h_op1
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
      Miri.Interpreter.OperandMachine.evalOperandAt,
      Miri.Interpreter.OperandMachine.evalOperand,
      Miri.Interpreter.OperandMachine.evalPlaceToOp,
      toMiriOperandV2, toMiriPlaceV2, List.map,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      opHooks_deinitMovedPlace_v2, opHooks_checkPlaceType_v2,
      array_forIn_empty_v2, ite_true_eq, ite_false_eq] at h_l1'
    exact h_l1'
  have h_op :
      (Miri.Interpreter.ExecutionMachine.rvalueHooks
          (refExecCfgV2 rp) refLimitsV2).evalOperandAt 0
          (Miri.Interpreter.OperandPath.rvalue "operand")
          (toMiriOperandV2 rp.types (.copy ⟨1, [.deref]⟩))
          (some u32Lay) m0 =
        .ok ⟨.indirect a2Mp, u32Lay⟩ m0 := by
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
      Miri.Interpreter.OperandMachine.evalOperandAt,
      Miri.Interpreter.OperandMachine.evalOperand,
      Miri.Interpreter.OperandMachine.evalPlaceToOp,
      toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2, List.map,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    rw [refStepCfgV2_eq, opHooks_deinitMovedPlace_v2]
    simp only [ite_true]
    dsimp only [EStateM.bind, EStateM.modifyGet]
    rw [show { stack := m0.stack, machine := { m0.machine with
        pendingMoveDeinit := false } } = m0 from rfl]
    rw [show ({ toList := [Miri.MIR.ProjectionElem.Deref] } :
        Array Miri.MIR.ProjectionElem).isEmpty = false from rfl, ite_false_eq, h_l1]
    dsimp only
    rw [show ({ toList := [Miri.MIR.ProjectionElem.Deref] } :
        Array Miri.MIR.ProjectionElem) = Array.mk [.Deref] from rfl]
    rw [← Array.forIn_toList, List.forIn_cons]
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    have h_proj : Miri.Interpreter.OperandMachine.project
          (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)) 0
          ⟨.immediate ptrImm, ptrLay⟩ .Deref m0 =
        .ok ⟨.indirect a2Mp, u32Lay⟩ m0 := by
      dsimp only [Miri.Interpreter.OperandMachine.project,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rw [beq_self_eq_true, ite_true_eq]
      dsimp only [EStateM.bind]
      rw [h_deref]
      rfl
    rw [h_proj]
    dsimp only
    rw [List.forIn_nil]
    dsimp only [pure, Pure.pure, EStateM.pure]
    rw [opHooks_checkPlaceType_v2]
  have h_ptr_acc :
      Miri.Memory.AllocationAccess.getPtrAlloc m0.machine.memory ⟨m0.machine, none⟩
          ⟨Miri.ABI.Size.ofBytes 8⟩ ptr.withOptionalProvenance
          (Miri.ABI.Size.ofBytes 4) false none
          (refAccessConfigV2 rp.types).globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks
            (refAccessConfigV2 rp.types)) =
        ⟨mem0', ⟨m0.machine, none⟩,
          some ⟨alloc2IdV2, Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
            (Miri.ABI.Size.ofBytes 4), ma2⟩,
          .ok (some ⟨alloc2IdV2, Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
            (Miri.ABI.Size.ofBytes 4), ma2⟩)⟩ :=
    getPtrAlloc_live_nonghost_v2 rp.types (Miri.ABI.Size.ofBytes 4) 4
      m0.machine.memory mem0' (.machine ()) ma2 m0.machine alloc2IdV2
      (Miri.ABI.Size.ofBytes 1) ptr.withOptionalProvenance
      (.concrete Miri.Memory.BorTag.one) h_find2 h_any2 h_set2 rfl (by decide)
      (by
        change Miri.Memory.checkedBounds ⟨Miri.ABI.Size.ofBytes 8⟩ alloc2IdV2
          a2.byteSize (Miri.ABI.Size.ofBytes 1) 4 .memoryAccess = .ok ()
        rw [h_msz]
        decide)
      (by dsimp only [ptr]; rfl) rfl rfl
  have h_place_acc := getPlaceAlloc_misaligned_v2 m0.machine.memory mem0'
    ⟨m0.machine, none⟩ ⟨a2Mp, Miri.Interpreter.localMemoryLayout u32Lay⟩
    ⟨⟨0⟩, ⟨2⟩⟩ false none
    (refAccessConfigV2 rp.types).globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 rp.types))
    (refAccessConfigV2 rp.types).dynamicLayout
    ⟨alloc2IdV2, Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
      (Miri.ABI.Size.ofBytes 4), ma2⟩
    (by dsimp only [Miri.Interpreter.localMemoryLayout, u32Lay]; rfl) rfl
    (by
      dsimp only [a2Mp, ptr, Miri.Interpreter.localMemoryLayout, u32Lay] at h_ptr_acc
      dsimp only [a2Mp, ptr, Miri.Interpreter.localMemoryLayout, u32Lay]
      exact h_ptr_acc)
  have h_rr :
      (refExecCfgV2 rp).copy.readRaw 0 ⟨.indirect a2Mp, u32Lay⟩ m0 =
        .error (Miri.Interpreter.MemoryErrors.operand
          (.pointerAccess (.access (.alignmentCheckFailed ⟨⟨0⟩, ⟨2⟩⟩)))) m1 := by
    change Miri.Interpreter.PlaceMachine.readRaw (refAccessConfigV2 rp.types)
        ⟨.indirect a2Mp, u32Lay⟩ m0 = _
    dsimp only [Miri.Interpreter.PlaceMachine.readRaw,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      get, getThe, MonadStateOf.get, EStateM.get]
    have h_ri_raw :
        Miri.Interpreter.readImmediateRaw m0.machine.memory ⟨m0.machine, none⟩
            (.indirect a2Mp) (Miri.Interpreter.localMemoryLayout u32Lay)
            (refAccessConfigV2 rp.types).runtime false none
            (refAccessConfigV2 rp.types).globalHooks
            (Miri.Interpreter.PlaceMachine.accessHooks
              (refAccessConfigV2 rp.types))
            (refAccessConfigV2 rp.types).dynamicLayout =
          ⟨mem0', ⟨m0.machine, none⟩,
            some ⟨alloc2IdV2, Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1)
              (Miri.ABI.Size.ofBytes 4), ma2⟩,
            .error (.pointerAccess (.access (.alignmentCheckFailed ⟨⟨0⟩, ⟨2⟩⟩)))⟩ := by
      dsimp only [Miri.Interpreter.readImmediateRaw,
        Miri.Interpreter.readImmediateFromMplaceRaw, Id.run,
        bind, Bind.bind, pure, Pure.pure]
      rw [show (Miri.Interpreter.localMemoryLayout u32Lay).backendRepr.isUnsized =
          false from by dsimp only [Miri.Interpreter.localMemoryLayout, u32Lay]; rfl,
        ite_false_eq,
        show (refAccessConfigV2 rp.types).runtime = refRuntimeLayoutV2 from rfl,
        h_place_acc]
    rw [show (refAccessConfigV2 rp.types).ghostMode = false from rfl,
      show (refAccessConfigV2 rp.types).globalKind = none from rfl, h_ri_raw]
    dsimp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      refAccessConfigV2, refAccessConfig, throw, MonadExceptOf.throw,
      EStateM.throw]
    rfl
  let err := Miri.Interpreter.MemoryErrors.operand
    (.pointerAccess (.access (.alignmentCheckFailed ⟨⟨0⟩, ⟨2⟩⟩)))
  have h_err_ub : ∃ msg, err = .undefinedBehavior msg := ⟨_, rfl⟩
  have h_cp_err :
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place
          (refExecCfgV2 rp).copy 0 ⟨.indirect a2Mp, u32Lay⟩
          ⟨Miri.Interpreter.RuntimePlaceRef.local 0 0 none
            frame0.localsIdentity, u32Lay⟩ false m0 =
        .error err m1 := by
    dsimp only [Miri.Interpreter.copyRuntimePlace,
      Miri.Interpreter.copyRuntimePlaceNoValidate,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    have h_compat : (refExecCfgV2 rp).copy.compatible u32Lay u32Lay = .ok true := by
      dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
        Miri.Interpreter.TypedMachineBindings.bindValidation,
        refExecutionConfigV2, refPlaceCopyHooksV2]
      rw [beq_self_eq_true]
    have h_pad : (refExecCfgV2 rp).copy.hasPadding u32Lay = .ok false := by
      dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
        Miri.Interpreter.TypedMachineBindings.bindValidation,
        refExecutionConfigV2, refPlaceCopyHooksV2, refHasPaddingV2, u32Lay]
      rfl
    have h_tpd :
        (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place.takePendingMoveDeinit m0 =
          .ok false m0 := by
      dsimp only [Miri.Interpreter.ExecutionMachine.projectionHooks,
        Miri.Interpreter.PlaceMachine.takePendingMoveDeinit, m0, mkRefMiriState]
      rfl
    rw [h_compat, Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure, EStateM.pure]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [h_pad, Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure, EStateM.pure, EStateM.bind]
    rw [h_tpd]
    dsimp only
    rw [ite_false_eq]
    dsimp only [EStateM.bind]
    rw [show Miri.Interpreter.PlaceCopyHooks.readRaw (refExecCfgV2 rp).copy 0
        ⟨.indirect a2Mp, u32Lay⟩ m0 = .error err m1 from h_rr]
  have h_ass_err :
      (Miri.Interpreter.ExecutionMachine.stepHooks
          (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨0, Array.empty⟩
          (toMiriRvalueV2 rp.types (.use (.copy ⟨1, [.deref]⟩))) m0 =
        (m1, .error err) := by
    dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
      Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
      Miri.Interpreter.evalRvalueIntoPlace,
      toMiriRvalueV2, toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2,
      List.map, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show Miri.Interpreter.ExecutionMachine.withValidation
        (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl]
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks]
    rw [refStepCfgV2_eq, h_ev]
    dsimp only [Miri.Interpreter.RuntimePlace.layout]
    have h_op' := h_op
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
      toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2, List.map] at h_op'
    rw [refStepCfgV2_eq] at h_op'
    rw [h_op']
    dsimp only [Miri.Interpreter.MachineHooks.withRetagMode]
    rw [show (Miri.MIR.WithRetag.No == Miri.MIR.WithRetag.Yes) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [h_cp_err, show m0.machine.borrowTracker = none from rfl]
  have h_step0 := execStep_assign_err rp m0 m1 frame0 0 0
    (toMiriBasicBlockV2 rp.types
      (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
    (toMiriStatementV2 rp.types
      (@GetElem.getElem _ Nat _ _ _
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)).statements
        0 (by decide)))
    ⟨0, Array.empty⟩ (toMiriRvalueV2 rp.types (.use (.copy ⟨1, [.deref]⟩)))
    err rfl rfl rfl rfl rfl rfl h_ass_err
  let ⟨msg, h_msg⟩ := h_err_ub
  rw [h_msg] at h_step0
  have h_exec : refCoreExecV2 rp u32Ty ⟨retMemPlaceV2, u32Lay⟩ (fun _ => False)
      True False 1 m0 := by
    dsimp only [refCoreExecV2]
    change (match evalRefCoreV2 rp u32Ty ⟨retMemPlaceV2, u32Lay⟩ m0 with
      | .running miri' => refCoreExecV2 rp u32Ty ⟨retMemPlaceV2, u32Lay⟩
          (fun _ => False) True False 0 miri'
      | .returned _ => False | .ub => True | .blocked => False)
    dsimp only [evalRefCoreV2]
    rw [h_step0]
    exact True.intro
  let ⟨h1, h2, h3, _, _⟩ := ref_ub_of_coreExec h_init h_exec
  exact ⟨h1, h3, h2⟩

/-- Anneal-side fault and non-well-formedness for `V2_C6` (`evalStepV2`). -/
theorem c6_m_anneal :
    ReachesResultV2 progV2_C6_danglingLocalRef queryV2_C6 (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C6_danglingLocalRef queryV2_C6
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C6_danglingLocalRef queryV2_C6 := by
  let ⟨h_f, h_excl, _, _, h_nwf⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2_C6_danglingLocalRef)
      (q := queryV2_C6) (fuel := 4) (expected := .undefined) rfl
  exact ⟨h_f, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf⟩

/-- Anneal-side well-formedness and behavior for `V2_C3` (`evalStepV2`). -/
theorem c3_m_anneal :
    WellFormedV2 progV2_C3_selfPtrMetadata queryV2_C3 ∧
    BehaviorV2 progV2_C3_selfPtrMetadata queryV2_C3 outV2_C3 ∧
    ¬ DivergesV2 progV2_C3_selfPtrMetadata queryV2_C3 ∧
    (∀ post : TerminalOut → Prop,
      post outV2_C3 →
      SatisfiesPostV2 progV2_C3_selfPtrMetadata queryV2_C3 post) :=
  spec_and_behaviorV2_of_exec_eq (p := progV2_C3_selfPtrMetadata)
    (q := queryV2_C3) (fuel := 4) (out := outV2_C3) rfl

/-- Anneal-side well-formedness and behavior for `V2_C2` (`evalStepV2`). -/
theorem c2_m_anneal :
    WellFormedV2 progV2_C2_offsetWrite queryV2_C2 ∧
    BehaviorV2 progV2_C2_offsetWrite queryV2_C2 outV2_C2 ∧
    ¬ DivergesV2 progV2_C2_offsetWrite queryV2_C2 ∧
    (∀ post : TerminalOut → Prop,
      post outV2_C2 →
      SatisfiesPostV2 progV2_C2_offsetWrite queryV2_C2 post) :=
  spec_and_behaviorV2_of_exec_eq (p := progV2_C2_offsetWrite)
    (q := queryV2_C2) (fuel := 7) (out := outV2_C2) rfl

/-! ### `V2_C6` reference-machine helpers and lockstep -/

/-- One non-terminal `refCoreExecV2` step, stated as an equation so callers
rewrite instead of elaborating against a concrete `refCoreExecV2` goal (whose
`whnf` would run the interpreter). -/
theorem refCoreExecV2_running {rp : RefProg} {rt : MirTy}
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

/-- Final `refCoreExecV2` step whose successful `Return` empties the stack but
whose returned value fails `refReadReturnValV2` with `.undefined`. -/
private theorem refCoreExecV2_returned_ub {rp : RefProg} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} {n : Nat}
    {m m' : RefMiriState}
    (h_step : Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
      refLimitsV2 0 m = (m', .ok true))
    (h_e : m'.stack.frames.isEmpty = true)
    (h_rv : refReadReturnValV2 m'.machine.memory m'.machine.user.callerMem rt
      rpl = .error .undefined) :
    refCoreExecV2 rp rt rpl onRet onUb onBlk (n + 1) m = onUb := by
  change (match evalRefCoreV2 rp rt rpl m with
    | .running m' => refCoreExecV2 rp rt rpl onRet onUb onBlk n m'
    | .returned out => onRet out | .ub => onUb | .blocked => onBlk) = _
  dsimp only [evalRefCoreV2]
  rw [h_step]
  dsimp only
  rw [h_e, ite_true_eq, h_rv]

/-- `copyRuntimePlace` from its no-validate core plus destination validation,
for type-identical source and destination layouts. -/
theorem copyRuntimePlace_of_noValidate_v2 (rp : RefProg)
    (src : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (dest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (allow : Bool) (st st' : RefMiriState)
    (h_ty : src.layout.ty = dest.layout.ty)
    (h_cp : Miri.Interpreter.copyRuntimePlaceNoValidate
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 src dest allow st = .ok () st')
    (h_val : Miri.Interpreter.ValidityVisitor.validatePlace
      (refValHooksV2 rp.types) 0 16 dest true true st' = .ok () st') :
    Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 src dest allow st = .ok () st' := by
  dsimp only [Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_cp,
    eStateM_bind_ok (refProjPlace_enforceValidity_v2 rp 0 dest.layout st'), h_ty]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
  rw [refProjPlace_validate_v2]
  exact h_val

/-- Safe-pointer `visit` of a `&u32` (local immediate or the 8-byte return
place) that tracks its pointee for the recursive validity pass, passing the
actual sized `sizeAndAlign` result in `h_sa`. -/
private theorem visit_ref_u32_v2 (types : List MirTy) (isMem : Bool)
    (pRef : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance)
    (pTy : TyId)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (st : RefMiriState)
    (h_ref : isMem = true → pRef = .memory retMemPlaceV2)
    (h_bt : st.machine.borrowTracker = none)
    (h_cls :
      (refValHooksV2 types).classify 0 pTy st = .ok (.reference false) st)
    (h_ri : (refValHooksV2 types).readImmediate 0
        ⟨pRef, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ .reference st =
      .ok ⟨.scalar (.fromPointer refRuntimeLayoutV2.base ptr),
        ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st)
    (h_ptp : (refValHooksV2 types).ptrToPlace 0
        ⟨.scalar (.fromPointer refRuntimeLayoutV2.base ptr),
          ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st =
      .ok ⟨a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ st)
    (h_sa : (refValHooksV2 types).sizeAndAlign 0
        ⟨a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ st =
      .ok (some (Miri.ABI.Size.ofBytes 4, ⟨2⟩)) st)
    (h_acc : (refValHooksV2 types).checkPointerAccess 0 a2Mp.ptr
        (Miri.ABI.Size.ofBytes 4) st = .ok (.ok ()) st)
    (h_inh : (refValHooksV2 types).opsemInhabited 0
        (refLocalLayoutForTyV2 types u32Ty).ty st = .ok true st)
    (h_al : (refValHooksV2 types).checkPointerAlignResult 0 a2Mp.ptr ⟨2⟩ st =
      .ok (.ok ()) st)
    (h_ptr_eq : a2Mp.ptr = ptr.withOptionalProvenance) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 16
      (refInitSessV2 isMem) ⟨pRef, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st =
      .ok { refInitSessV2 isMem with
        dataBytes := if isMem then some singleDataRange64V2 else none
        refTracking := (refInitSessV2 isMem).refTracking.map
          fun tr => tr.track ⟨a2Mp, refLocalLayoutForTyV2 types u32Ty⟩
            (fun _ => ⟨"", Array.mk [.deref]⟩) } st := by
  let lay : Miri.Interpreter.LocalLayout := ⟨pTy, refThinPtrLayoutDataV2⟩
  let u32Lay := refLocalLayoutForTyV2 types u32Ty
  let basePath : Miri.Memory.ValidationPath := ⟨"", Array.empty⟩
  have h_retag := refValHooksV2_retagPointer types 0
    ⟨.scalar (.fromPointer refRuntimeLayoutV2.base ptr), lay⟩ pTy st h_bt
  have h_mbn : (refValHooksV2 types).scalarMayBeNull 0
      (.fromPointer refRuntimeLayoutV2.base ptr) st = .ok false st := rfl
  have h_rt : Miri.Interpreter.ValidityVisitor.retagSafePointer basePath
      (.reference false) (refValHooksV2 types).retagPointer 0
      ⟨.scalar (.fromPointer refRuntimeLayoutV2.base ptr), lay⟩ pTy st =
      .ok none st := by
    dsimp only [Miri.Interpreter.ValidityVisitor.retagSafePointer,
      Miri.Interpreter.ValidityVisitor.mapRetagOutcome]
    rw [h_retag]
  have h_ma :
      Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome basePath
        (.reference false)
        ((refValHooksV2 types).checkPointerAlignResult 0
          ptr.withOptionalProvenance ⟨2⟩) st =
        .ok () st := by
    dsimp only [Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome]
    rw [← h_ptr_eq, h_al]
  have h_fmp :
      (Miri.Memory.Scalar.fromMaybePointer
        (refValHooksV2 types).target.base ptr.withOptionalProvenance :
        Except Miri.Memory.ScalarError
          (Miri.Memory.Scalar Miri.Memory.Provenance)) =
        .ok (.fromPointer refRuntimeLayoutV2.base ptr) := rfl
  rw [Miri.Interpreter.ValidityVisitor.visit.eq_2]
  refine eStateM_apply_bind _ _ (.reference false) st st h_cls ?_
  cases isMem <;>
    (first | (have h := h_ref rfl; subst h) | dsimp only) <;> (
    dsimp only [refInitSessV2, bind, Bind.bind]
    change (EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).readImmediate 0 _ .reference) _) _) _ st) = _
    rw [eStateM_bind3_ok h_ri]
    simp only [ite_true]
    refine eStateM_bind3_apply (s₁ := st) rfl ?_
    dsimp only [bind, Bind.bind]
    change (EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).ptrToPlace 0 _) _) _) _ st) = _
    rw [eStateM_bind3_ok h_ptp]
    dsimp only
    rw [show u32Lay.layout.isSized = true from rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    change (EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).sizeAndAlign 0 ⟨a2Mp, u32Lay⟩) _) _) _ st) = _
    rw [eStateM_bind3_ok h_sa]
    dsimp only [Option.getD]
    simp only [ite_true]
    change (EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).checkPointerAccess 0 a2Mp.ptr
        (Miri.ABI.Size.ofBytes 4)) _) _) _ st) = _
    rw [eStateM_bind3_ok h_acc]
    dsimp only
    change (EStateM.bind (EStateM.bind (EStateM.bind
      (Miri.Interpreter.ValidityVisitor.retagSafePointer basePath
        (.reference false) (refValHooksV2 types).retagPointer 0 _ pTy)
      _) _) _ st) = _
    rw [eStateM_bind3_ok h_rt]
    dsimp only
    refine eStateM_bind3_apply (a := ()) (s₁ := st) rfl ?_
    rw [h_ptr_eq, h_fmp]
    refine eStateM_bind3_apply
      (a := .fromPointer refRuntimeLayoutV2.base ptr) (s₁ := st) rfl ?_
    change (EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).scalarMayBeNull 0
        (.fromPointer refRuntimeLayoutV2.base ptr)) _) _) _ st) = _
    rw [eStateM_bind3_ok h_mbn]
    simp only [Bool.false_eq_true, ite_false]
    change (EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).opsemInhabited 0 u32Lay.ty) _) _) _ st) = _
    rw [eStateM_bind3_ok h_inh]
    simp only [ite_true]
    change (EStateM.bind (EStateM.bind (EStateM.bind
      (Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome basePath
        (.reference false)
        ((refValHooksV2 types).checkPointerAlignResult 0
          ptr.withOptionalProvenance ⟨2⟩)) _) _) _ st) = _
    rw [eStateM_bind3_ok h_ma]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn, eStateM_bind_pure_fn]
    rfl)

/-- A 4-aligned pointer at offset `0` of `alloc2` is never misaligned. -/
private theorem misalignmentWith_alloc2_zero_v2 (types : List MirTy)
    (st : RefMiriState) (mut_ : Miri.Memory.Mutability)
    (h_inf : st.machine.memory.getAllocInfo alloc2IdV2 =
      .ok ⟨Miri.ABI.Size.ofBytes 4, ⟨2⟩, .liveData, mut_⟩) :
    Miri.Interpreter.PointerPlaceMachine.misalignmentWith
        (refAccessConfigV2 types) refAlignCtxV2
        ⟨Miri.ABI.Size.ZERO,
          some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩ ⟨2⟩ st =
      .ok none st := by
  unfold Miri.Interpreter.PointerPlaceMachine.misalignmentWith
  dsimp only [refAlignCtxV2, get, getThe, MonadStateOf.get, EStateM.get, set,
    MonadStateOf.set, EStateM.set, bind, Bind.bind, pure, Pure.pure, EStateM.pure]
  refine eStateM_apply_bind EStateM.get _ st st st rfl ?_
  rw [show (Miri.Interpreter.ValidityMachine.AlignmentCheck.Symbolic ==
      Miri.Interpreter.ValidityMachine.AlignmentCheck.None ||
      ((⟨2⟩ : Miri.ABI.Align).pow2 == 0)) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (refAccessConfigV2 types).resolvePointer st.machine.memory
      ⟨Miri.ABI.Size.ZERO,
        some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩ 0
      st.machine = .ok (.ok ⟨alloc2IdV2, Miri.ABI.Size.ZERO,
        .concrete Miri.Memory.BorTag.one⟩) st.machine from rfl]
  dsimp only
  refine eStateM_apply_bind (EStateM.set _) _ () st st rfl ?_
  refine eStateM_apply_bind (EStateM.pure _) _ _ st st rfl ?_
  refine eStateM_apply_bind EStateM.get _ st st st rfl ?_
  dsimp only
  rw [h_inf]
  refine eStateM_apply_bind _ _
    (Miri.Memory.AllocationInfo.mk (Miri.ABI.Size.ofBytes 4) ⟨2⟩
      .liveData mut_) st st rfl ?_
  dsimp only [refRuntimeLayoutV2]
  refine eStateM_apply_bind _ _ none st st rfl ?_
  have h_is : Miri.Memory.isPtrMisaligned
      (⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩ :
        Miri.Memory.Pointer (Option Miri.Memory.Provenance)) ⟨2⟩ true
      (fun _ _ => Except.ok ⟨alloc2IdV2, Miri.ABI.Size.ZERO,
        Miri.Memory.ProvenanceExtra.concrete Miri.Memory.BorTag.one⟩)
      st.machine.memory.getAllocInfo (fun _ _ _ _ _ => none) = .ok none := by
    dsimp only [Miri.Memory.isPtrMisaligned, Except.mapError, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    rw [h_inf]
    cases mut_ <;> rfl
  dsimp only [Except.mapError]
  rw [h_is]
  rfl

/-- Validity pointer hooks for a `&u32` at offset `0` of live `alloc2`:
pointee place resolution, 4-byte dereferenceability, and alignment. -/
private theorem refValHooksV2_ref_u32_alloc2_v2 (types : List MirTy)
    (st : RefMiriState) (pTy : TyId) (m : Trusted.MirAst.Mutability)
    (mut_ : Miri.Memory.Mutability)
    (h_ty : resolveTy types pTy = some (.ref m u32Ty))
    (h_inf : st.machine.memory.getAllocInfo alloc2IdV2 =
      .ok ⟨Miri.ABI.Size.ofBytes 4, ⟨2⟩, .liveData, mut_⟩) :
    let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
    let a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
      ⟨ptr.withOptionalProvenance, .none, none⟩
    (refValHooksV2 types).ptrToPlace 0
        ⟨.scalar (.fromPointer refRuntimeLayoutV2.base ptr),
          ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st =
      .ok ⟨a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ st ∧
    (refValHooksV2 types).checkPointerAccess 0 a2Mp.ptr
        (Miri.ABI.Size.ofBytes 4) st = .ok (.ok ()) st ∧
    (refValHooksV2 types).checkPointerAlignResult 0 a2Mp.ptr ⟨2⟩ st =
      .ok (.ok ()) st := by
  intro ptr a2Mp
  have h_mis := misalignmentWith_alloc2_zero_v2 types st mut_ h_inf
  refine ⟨?_, ?_, ?_⟩
  · change refFromImmediatePtrV2 types _ st = _
    dsimp only [refFromImmediatePtrV2, refTyLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [h_ty]
    change (match Miri.Interpreter.PointerPlaceMachine.misalignmentWith
        (refAccessConfigV2 types) refAlignCtxV2
        ⟨Miri.ABI.Size.ZERO,
          some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩ ⟨2⟩ st with
      | .error e st1 => _
      | .ok mis st1 => _) = _
    rw [h_mis]
  · have h_eq : (refValHooksV2 types).checkPointerAccess =
        fun _ p sz st => refCheckPointerAccessResultV2 types p sz st := rfl
    rw [h_eq]
    dsimp only [refCheckPointerAccessResultV2, Miri.Memory.checkPtrAccess,
      Miri.Memory.checkAndDerefPtr, bind, Bind.bind, Except.bind, pure,
      Pure.pure, Except.pure]
    rw [show Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes 4) = .ok 4 from rfl]
    dsimp only
    rw [show refResolvePointerPure a2Mp.ptr 4 = .ok ⟨alloc2IdV2,
      Miri.ABI.Size.ZERO, .concrete Miri.Memory.BorTag.one⟩ from rfl]
    dsimp only
    rw [h_inf]
    cases mut_ <;> rfl
  · change (match Miri.Interpreter.PointerPlaceMachine.misalignmentWith
        (refAccessConfigV2 types) refAlignCtxV2
        ⟨Miri.ABI.Size.ZERO,
          some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩ ⟨2⟩ st with
      | .error e st1 => EStateM.Result.error e st1
      | .ok none st1 => EStateM.Result.ok (Except.ok ()) st1
      | .ok (some bad) st1 => EStateM.Result.ok (Except.error bad) st1) = _
    rw [h_mis]

/-- Ghost validity read of the `u32` at offset `0` of live `alloc2`. -/
private theorem refValHooksV2_readImm_u32_alloc2_v2 (types : List MirTy)
    (st : RefMiriState) (kind : Miri.Memory.MemoryKind Unit)
    (alloc : RefMiriAlloc) (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨kind, alloc⟩))
    (h_sz : alloc.byteSize = Miri.ABI.Size.ofBytes 4)
    (h_rd : alloc.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4))
      false = .ok sc) :
    let a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
      ⟨⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩,
        .none, none⟩
    (refValHooksV2 types).readImmediate 0
        ⟨.memory a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ .integer st =
      .ok ⟨.scalar sc, refLocalLayoutForTyV2 types u32Ty⟩ st := by
  intro a2Mp
  have h_ga := getPtrAlloc_live_ghost_v2 (Miri.ABI.Size.ofBytes 4) 4
    st.machine.memory kind alloc st.machine alloc2IdV2 Miri.ABI.Size.ZERO
    a2Mp.ptr (.concrete Miri.Memory.BorTag.one)
    (refAccessConfigV2 types).globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types))
    rfl h_find rfl rfl (by rw [h_sz]; decide)
    (Miri.Interpreter.PlaceMachine.resolvePointer_ok (refAccessConfigV2 types)
      st.machine.memory st.machine a2Mp.ptr 4 _ rfl)
  have h_raw := readImmediate_mem_u32_v2 types a2Mp alloc2IdV2 alloc sc st
    st.machine.memory Miri.ABI.Size.ZERO true (refAccessConfigV2 types) rfl
    h_ga rfl h_rd
  rw [refValHooksV2_readImmediate]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [show Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 types).place 0
      ⟨.memory a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ st =
      .ok ⟨.indirect a2Mp, refLocalLayoutForTyV2 types u32Ty⟩ st from rfl]
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnvV2, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [show refValidityMemoryEnv.memory st = st.machine.memory from rfl,
    show refValidityMemoryEnv.hooks st = ⟨st.machine, none⟩ from rfl,
    show (refAccessConfigV2 types).runtime = refRuntimeLayoutV2 from rfl, h_raw]
  cases st with | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ _ => rfl

/-- Ghost validity read of the thin pointer stored in the 8-byte return place.
-/
private theorem refValHooksV2_readImm_ptr_ret_v2 (types : List MirTy)
    (st : RefMiriState) (pTy : TyId) (exp : Miri.Memory.ExpectedValue)
    (kind : Miri.Memory.MemoryKind Unit) (alloc : RefMiriAlloc)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨kind, alloc⟩))
    (h_sz : alloc.byteSize = Miri.ABI.Size.ofBytes 8)
    (h_rd : alloc.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      true = .ok sc) :
    (refValHooksV2 types).readImmediate 0
        ⟨.memory retMemPlaceV2, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ exp st =
      .ok ⟨.scalar sc, ⟨pTy, refThinPtrLayoutDataV2⟩⟩ st := by
  let lay : Miri.Interpreter.LocalLayout := ⟨pTy, refThinPtrLayoutDataV2⟩
  let rng := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
  let acc := refAccessConfigV2 types
  let mplace : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
      .Scalar (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
        (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8))),
      some pTy⟩⟩
  have h_ga := getPtrAlloc_live_ghost_v2 (Miri.ABI.Size.ofBytes 8) 8
    st.machine.memory kind alloc st.machine retAllocIdV2 Miri.ABI.Size.ZERO
    retPtrV2 (.concrete Miri.Memory.BorTag.one) acc.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks acc)
    rfl h_find rfl rfl (by rw [h_sz]; decide)
    (Miri.Interpreter.PlaceMachine.resolvePointer_ok acc
      st.machine.memory st.machine retPtrV2 8 _ rfl)
  have h_gpl := getPlaceAlloc_sized_of_access_v2' st.machine.memory
    st.machine.memory ⟨st.machine, none⟩ mplace true none acc.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks acc) acc.dynamicLayout
    ⟨retAllocIdV2, rng, alloc⟩ rfl rfl h_ga
  have h_raw_m :
      Miri.Interpreter.readImmediateFromMplaceRaw st.machine.memory
        ⟨st.machine, none⟩ mplace refRuntimeLayoutV2 true none acc.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks acc) acc.dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨retAllocIdV2, rng, alloc⟩,
        .ok (some ⟨.scalar sc, mplace.layout⟩)⟩ := by
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_gpl]
    dsimp only [mplace, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
        (alloc.readScalar refRuntimeLayoutV2.base rng true)) _ _ = _
    rw [h_rd]
    rfl
  rw [refValHooksV2_readImmediate]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [show Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 types).place 0
      ⟨.memory retMemPlaceV2, lay⟩ st = .ok ⟨.indirect retMemPlaceV2, lay⟩ st
    from rfl]
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnvV2, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [show refValidityMemoryEnv.memory st = st.machine.memory from rfl,
    show refValidityMemoryEnv.hooks st = ⟨st.machine, none⟩ from rfl,
    show (refAccessConfigV2 types).runtime = refRuntimeLayoutV2 from rfl,
    show Miri.Interpreter.localMemoryLayout lay = mplace.layout from rfl]
  dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [show (⟨retMemPlaceV2, mplace.layout⟩ :
      Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance) = mplace
    from rfl, h_raw_m]
  cases st with | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ _ => rfl

/-- Thin-pointer scalar write through a mutable place access that may have
reordered the live array (`memory'`). -/
private theorem writeImmediate_thinPtr_at_v2 {P E K H X : Type} [DecidableEq K]
    [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (memory memory' afterMemory :
      Miri.Memory.MemoryState P E K) (hooks : H)
    (mplace : Miri.Interpreter.MemPlace P)
    (tyId : Option Nat) (vr : Miri.ABI.WrappingRange)
    (ptr : Miri.Memory.Pointer P) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access :
      Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic :
      Miri.Interpreter.DynamicLayoutResolver P E K H)
    (later : Miri.Interpreter.MemoryOperandLayout → Bool)
    (ref : Miri.Memory.AllocationAccessRef P E)
    (rng : Miri.Memory.AllocRange)
    (after : Miri.Memory.Allocation P E)
    (actual : Miri.Interpreter.getPlaceAllocMut memory hooks
        ⟨mplace, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
          .Scalar (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
            (validRange := vr)), tyId⟩⟩
        refRuntimeLayoutV2 false kind global access dynamic =
      ⟨memory', hooks, some ref, .ok (some ref)⟩)
    (selected : ref.range.subrange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (Miri.ABI.Size.ofBytes 8)) = .ok rng)
    (written : ref.allocation.writeScalar refRuntimeLayoutV2.base rng
      (.fromPointer refRuntimeLayoutV2.base ptr) = .ok () after)
    (committed :
      memory'.setLiveAllocation ref.allocId after = .ok afterMemory) :
    Miri.Interpreter.writeImmediateToMplaceNoValidate memory hooks
        (.scalar (.fromPointer refRuntimeLayoutV2.base ptr))
        ⟨mplace, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
          .Scalar (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
            (validRange := vr)), tyId⟩⟩
        refRuntimeLayoutV2 false kind global access dynamic later =
      ⟨afterMemory, hooks, some { ref with allocation := after }, .ok ()⟩ := by
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure]
  rw [actual]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  change (match (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
      (ref.range.subrange (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (Miri.ABI.Size.ofBytes 8)))) with
    | Except.ok range => _
    | Except.error error => _) = _
  rw [selected]
  dsimp only [Except.mapError, pure, Pure.pure, Id.run]
  change (match (memory'.setLiveAllocation ref.allocId
      (match Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base rng
          (.fromPointer refRuntimeLayoutV2.base ptr) ref.allocation with
       | EStateM.Result.ok _ a => a
       | EStateM.Result.error _ a => a)) with
    | Except.ok next => _
    | Except.error error => _) = _
  rw [written]
  dsimp only
  rw [committed]
  rfl

/-- `V2_C6` (Stack-reference escape / dangling return UB):
`_1 = 42u32; _0 = &_1; return` faults with `.undefined` in `evalStepV2`
because `refsStayInCallerMem` rejects `_0 : &u32` against empty caller memory
(since `evalStepV2` does not pop callee stack frames). In
`ProfileV2RefMachine`, all three steps execute (borrow allocates fresh stack
`alloc2`, writes validate, and `CallMachine.cleanup` frees `alloc2` into
`dead`), and `refReadReturnValV2` rejects the escaped/dangling reference with
`.undefined` (`.ub`). -/
theorem V2_C6_danglingLocalRef_lockstep :
    ReachesResultV2 progV2_C6_danglingLocalRef queryV2_C6 (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C6_danglingLocalRef queryV2_C6
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C6_danglingLocalRef queryV2_C6 ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C6_danglingLocalRef)
        queryV2_C6 ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C6_danglingLocalRef)
        queryV2_C6 ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C6_danglingLocalRef) queryV2_C6 := by
  let ⟨h_f, h_excl, h_nwf⟩ := c6_m_anneal
  refine ⟨h_f, h_excl, h_nwf, ?_⟩
  let rp := encodeProg progV2_C6_danglingLocalRef
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let ⟨rawRet0, h_raw, h_rsz, h_rlen, h_rmut, h_ral, h_rex, h_rnb, h_rpm, h_rim,
      h_rwf, h_rgb⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT 8 rfl rfl
  cases rawRet0 with
  | _ rb sz pv im al mu ex nb =>
  have h1 : sz = Miri.ABI.Size.ofBytes 8 := h_rsz
  have h2 : mu = .Mut := h_rmut
  have h3 : al = Miri.ABI.Align.EIGHT := h_ral
  subst h1 h2 h3
  let rawRet := (⟨_, h_rsz⟩ : Subtype (fun x : Miri.Memory.Allocation
    Miri.Memory.Provenance Unit => x.byteSize = _)).1
  let refLay := refLocalLayoutForTyV2 rp.types (.ref .shared u32Ty)
  let u32Lay := refLocalLayoutForTyV2 rp.types u32Ty
  let retAlc : RefMiriAlloc := rawRet.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
      (Miri.ABI.Size.ofBytes 8))
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 2
        live := Array.mk [(retAllocIdV2, ⟨.stack, retAlc⟩)] }).setIssuedIds
      (Array.mk [retAllocIdV2])
  let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, refLay⟩
  let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
    [⟨.live (.immediate .uninit), some refLay⟩,
     ⟨.live (.immediate .uninit), some u32Lay⟩]
    retPlace
  let m0 := mkRefMiriState frame0 mem0 refInitControl ⟨[]⟩
  have h_icm : refInitCallerMemoryV2 rp.types ⟨[]⟩ (.ref .shared u32Ty) =
      .ok (mem0, retPlace) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show (refLocalLayoutForTyV2 rp.types (.ref .shared u32Ty)).layout.size =
        Miri.ABI.Size.ofBytes 8 from rfl,
      show (refLocalLayoutForTyV2 rp.types (.ref .shared u32Ty)).layout.align.abi =
        Miri.ABI.Align.EIGHT from rfl, h_raw]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2_C6 ms =
      .ok { miri := m0, retTy := .ref .shared u32Ty, retPlace := retPlace,
            stepsExecuted := 0, maxSteps := ms } := by
    intro ms
    exact initRefStateV2_ok_v2 rp queryV2_C6 ms rbody
      [.ref .shared u32Ty, u32Ty] (.ref .shared u32Ty) mem0 mem0 retPlace
      [⟨.live (.immediate .uninit), some refLay⟩,
       ⟨.live (.immediate .uninit), some u32Lay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  -- Step 0: `_1 = 42u32`.
  let imm42 : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromScalarInt (miriScalar .i32 42))
  let frame0W :=
    { frame0 with locals := (Array.mk
      [⟨.live (.immediate .uninit), some refLay⟩,
       ⟨.live (.immediate imm42), some u32Lay⟩]) }
  let m0W : RefMiriState := { m0 with stack := ⟨Array.mk [frame0W]⟩ }
  have h_ev0 := projPlace_evalPlace_local_v2 rp m0 frame0 1 u32Lay
    (.live (.immediate .uninit)) true rfl rfl rfl
  have h_opc : Miri.Interpreter.OperandMachine.evalOperandAt
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)) 0
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (toMiriOperandV2 rp.types (.constant ⟨tyIdFor rp.types u32Ty, .scalar 42⟩))
      (some u32Lay) m0 = .ok ⟨.immediate imm42, u32Lay⟩ m0 := rfl
  have h_cpnv0 : Miri.Interpreter.copyRuntimePlaceNoValidate
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 ⟨.immediate imm42, u32Lay⟩
      ⟨.local 0 1 none frame0.localsIdentity, u32Lay⟩ false m0 = .ok () m0W := rfl
  have h_val0 := int_validate_local_v2 rp.types m0W 1 .i32 false 42 frame0W
    rfl rfl rfl rfl
  have h_cp0 := copyRuntimePlace_of_noValidate_v2 rp ⟨.immediate imm42, u32Lay⟩
    ⟨.local 0 1 none frame0.localsIdentity, u32Lay⟩ false m0 m0W rfl h_cpnv0 h_val0
  let rv0 := toMiriRvalueV2 rp.types
    (.use (.constant ⟨tyIdFor rp.types u32Ty, .scalar 42⟩))
  have h_ass0 : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨1, Array.empty⟩ rv0 m0 =
      (m0W, .ok ()) := by
    have h_body : Miri.Interpreter.evalRvalueIntoPlace
        (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
          refLimitsV2) 0 rv0 ⟨1, Array.empty⟩ m0 = EStateM.Result.ok () m0W := by
      dsimp only [Miri.Interpreter.evalRvalueIntoPlace, rv0, toMiriRvalueV2]
      refine mh_apply_bind _ _ _ _ _ h_ev0 ?_
      dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
        Miri.Interpreter.RuntimePlace.layout]
      rw [refStepCfgV2_eq]
      refine mh_apply_bind _ _ _ _ _ h_opc ?_
      rw [show (Miri.MIR.WithRetag.No == Miri.MIR.WithRetag.Yes) = false from rfl]
      exact h_cp0
    dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
      Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [show Miri.Interpreter.ExecutionMachine.withValidation
        (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl, h_body]
  let frame1 :=
    { frame0W with location := .mir ⟨0, 1⟩ }
  let m1 : RefMiriState := { m0 with stack := ⟨Array.mk [frame1]⟩ }
  have h_step0 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (m1, .ok true) :=
    execStep_assign_ok rp m0 m0W frame0 frame0W 0 0
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)).statements
          0 (by decide)))
      ⟨1, Array.empty⟩ rv0 rfl rfl rfl rfl rfl rfl h_ass0 rfl rfl
  -- Step 1: `_0 = &_1` forces `_1` into the fresh stack allocation `alloc2`.
  let ⟨rawU0, h_rawU, h_usz, h_ulen, h_umut, h_ual, h_uex, h_unb, h_upm, h_uim,
      h_uwf, h_ugb⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 4) ⟨2⟩ 4 rfl rfl
  cases rawU0 with
  | _ rb sz pv im al mu ex nb =>
  have h1 : sz = Miri.ABI.Size.ofBytes 4 := h_usz
  have h2 : mu = .Mut := h_umut
  have h3 : al = ⟨2⟩ := h_ual
  subst h1 h2 h3
  let rawU := (⟨_, h_usz⟩ : Subtype (fun x : Miri.Memory.Allocation
    Miri.Memory.Provenance Unit => x.byteSize = _)).1
  have h_nxn : mem0.nextAllocId.toNat = 2 := rfl
  have h_nx_nz : mem0.nextAllocId ≠ 0 := by
    rw [show mem0.nextAllocId = 2 from rfl]; decide
  have h_lt1 : retAllocIdV2.value.toNat < 2 := by decide
  have h_iss : ∀ id, id ∈ mem0.issuedIds →
      id.value.toNat < mem0.nextAllocId.toNat := by
    intro id h_in; rw [h_nxn]
    cases h_in with | mk h_l =>
      cases h_l with | head => exact h_lt1 | tail _ h_t => cases h_t
  have h_lv : ∀ row, row ∈ mem0.live →
      row.1.value.toNat < mem0.nextAllocId.toNat := by
    intro row h_in; rw [h_nxn]
    cases h_in with | mk h_l =>
      cases h_l with | head => exact h_lt1 | tail _ h_t => cases h_t
  have h_gl : ∀ row, row ∈ mem0.globals →
      row.allocId.value.toNat < mem0.nextAllocId.toNat := by
    intro row h_in; cases h_in with | mk h_l => cases h_l
  have h_dd : ∀ row, row ∈ mem0.dead →
      row.allocId.value.toNat < mem0.nextAllocId.toNat := by
    intro row h_in; cases h_in with | mk h_l => cases h_l
  let ⟨mem1, h_res, h_as⟩ := allocateStack_sized_v2 rp m1 u32Lay alloc2IdV2 rawU
    rfl (by decide) h_rawU rfl rfl rfl rfl h_nx_nz (fun h => by cases h)
    (fun h => by cases h) h_iss h_lv h_gl h_dd rfl
  have h_m1 := reserveAllocId_live_dead_v2 mem0 mem1 alloc2IdV2 h_res
  cases mem1 with
  | mk nai idex it lv dd gt igt igr fn va bk bkr sw sn se sbr rbs os sb =>
  have h1 : lv = mem0.live := h_m1.1
  have h2 : dd = mem0.dead := h_m1.2
  subst h1 h2
  let mem1 := (⟨_, h_res⟩ : Subtype (fun x : RefMiriMem =>
    mem0.reserveAllocId = (x, _))).1
  let a2 : RefMiriAlloc := rawU.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
      (Miri.ABI.Size.ofBytes 4))
  let sc42 : Miri.Memory.Scalar Miri.Memory.Provenance :=
    .fromScalarInt (miriScalar .i32 42)
  let rng4 := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)
  let ⟨a2w0, h_ws, h_wsz, h_wlen, h_wmut, h_wal, h_wex, h_wiml, h_wwf, h_wset,
      h_winit, h_wpm, h_wgb, h_wpres⟩ :=
    alloc_writeInt_spec_v2 a2 Miri.ABI.Size.ZERO .i32 42
      Miri.Memory.ProvenanceMap.new h_ulen rfl
      (by rw [show a2.initializationMask = _ from h_uim]; rfl) h_uwf
      (Nat.le_refl 4)
      (fun fb _ => by
        rw [show a2.provenanceMap = _ from h_upm]
        exact provenanceMap_new_clear _ fb _ (by decide) (by decide))
  cases a2w0 with
  | _ rb sz pv im al mu ex nb =>
  have h1 : sz = Miri.ABI.Size.ofBytes 4 := h_wsz
  have h2 : mu = .Mut := h_wmut
  have h3 : al = ⟨2⟩ := h_wal
  subst h1 h2 h3
  let a2w := (⟨_, h_wsz⟩ : Subtype (fun x : RefMiriAlloc => x.byteSize = _)).1
  let a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
    ⟨⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩,
      .none, none⟩
  let mem2 : RefMiriMem :=
    { mem1 with live := mem1.live.push (alloc2IdV2, ⟨.stack, a2⟩) }
  let mem3 : RefMiriMem :=
    { mem1 with live := Array.mk [(retAllocIdV2, ⟨.stack, retAlc⟩),
        (alloc2IdV2, ⟨.stack, a2w⟩)] }
  let stA : RefMiriState :=
    { m1 with machine := { m1.machine with memory := mem2 } }
  let stB : RefMiriState :=
    { m1 with machine := { m1.machine with memory := mem3 } }
  have h_gpm := getPtrAllocMut_live_nonghost_v2 rp.types
    (Miri.ABI.Size.ofBytes 4) 4 mem2 mem2 .stack a2 stA.machine alloc2IdV2
    Miri.ABI.Size.ZERO a2Mp.ptr (.concrete Miri.Memory.BorTag.one) rfl rfl
    (by rw [← Array.any_toList]; rfl) rfl rfl rfl rfl rfl rfl rfl
  have h_gpam : Miri.Interpreter.getPlaceAllocMut mem2 ⟨stA.machine, none⟩
      ⟨a2Mp, Miri.Interpreter.localMemoryLayout u32Lay⟩ refRuntimeLayoutV2 false
      none (refAccessConfigV2 rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 rp.types))
      (refAccessConfigV2 rp.types).dynamicLayout =
      ⟨mem2, ⟨stA.machine, none⟩, some ⟨alloc2IdV2, rng4, a2⟩,
        .ok (some ⟨alloc2IdV2, rng4, a2⟩)⟩ :=
    Miri.Interpreter.getPlaceAllocMut_sized_of_access _ _ _ _
      (Miri.ABI.Size.ofBytes 8) _ _ _ _ _ rfl rfl rfl h_gpm
  let abi32 : Miri.ABI.Scalar := .Initialized (value := .Int .I32 false)
    (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 4))
  have h_repr32 : (Miri.Interpreter.localMemoryLayout u32Lay).backendRepr =
      .Scalar abi32 := rfl
  have h_psz32 : Miri.ABI.Primitive.size abi32.primitive refRuntimeLayoutV2 =
      .ok sc42.size := rfl
  have h_set3 : mem2.setLiveAllocation alloc2IdV2 a2w = .ok mem3 :=
    Miri.Memory.MemoryState.setLiveAllocation_of_find mem2 alloc2IdV2
      ⟨.stack, a2⟩ a2w rfl
  have h_wi : ∀ later, Miri.Interpreter.writeImmediateToMplaceNoValidate mem2
      ⟨stA.machine, none⟩ imm42
      ⟨a2Mp, Miri.Interpreter.localMemoryLayout u32Lay⟩ refRuntimeLayoutV2 false
      none (refAccessConfigV2 rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 rp.types))
      (refAccessConfigV2 rp.types).dynamicLayout later =
      ⟨mem3, ⟨stA.machine, none⟩, some ⟨alloc2IdV2, rng4, a2w⟩, .ok ()⟩ :=
    fun later => Miri.Interpreter.writeImmediate_scalar_of_access _ _ _ _ _ _ _ _
      _ later sc42 abi32 alloc2IdV2 a2 a2w h_repr32 h_psz32 rfl (Nat.le_refl 4)
      h_gpam h_ws h_set3
  have h_wm : (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.writeMemoryNoValidate 0 imm42 ⟨a2Mp, u32Lay⟩ stA =
      .ok () stB :=
    Miri.Interpreter.PlaceMachine.writeMemory_of_result
      (refAccessConfigV2 rp.types) _ imm42 ⟨a2Mp, u32Lay⟩ stA mem3
      (some ⟨alloc2IdV2, rng4, a2w⟩) rfl (h_wi _)
  let frame1A :=
    { frame1 with locals := (Array.mk
      [⟨.live (.immediate .uninit), some refLay⟩,
       ⟨.live (.indirect a2Mp), some u32Lay⟩]) }
  let m1F : RefMiriState :=
    { m1 with
      stack := ⟨Array.mk [frame1A]⟩
      machine := { m1.machine with
        memory := mem3
        allocationSpans :=
          (m1.machine.allocationSpans.filter fun e => e.1 != alloc2IdV2).push
            (alloc2IdV2, ⟨0⟩, none) } }
  let stC : RefMiriState := { m1F with stack := ⟨Array.mk [frame1]⟩ }
  have h_alm : (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.afterLocalMovedToMemory 0 1 ⟨a2Mp, u32Lay⟩ stB =
      .ok () stC := by
    change Miri.Interpreter.MachineHooks.afterLocalMovedToMemory 1
      ⟨a2Mp, u32Lay⟩ (refCompilerHooksV2 rp.types).localSpan stB = _
    dsimp only [Miri.Interpreter.MachineHooks.afterLocalMovedToMemory, a2Mp,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [currentFrame_single_v2 stB frame1 rfl]
    dsimp only
    rw [show (refCompilerHooksV2 rp.types).localSpan frame1.body 1 stB =
        .ok ⟨0⟩ stB from rfl]
    dsimp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      get, getThe, MonadStateOf.get, EStateM.get]
    rw [show stC.machine.memory.live.any (fun e => e.1 == alloc2IdV2) = true
      from by rw [← Array.any_toList]; rfl]
    rfl
  have h_cf1 := currentFrame_single_v2 m1 frame1 rfl
  have h_fi1 := frameIndex_single_v2 (rp := rp) m1 frame1 rfl
  have h_gop1 : frame1.getLocalOperand 1 = .ok (.immediate imm42) := rfl
  have h_pol1 : Miri.Interpreter.placeLayoutOfLocal
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      0 1 m1 = .ok u32Lay m1 := rfl
  have h_force : Miri.Interpreter.forceAllocation
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place 0
      ⟨.local 0 1 none frame1.localsIdentity, u32Lay⟩ m1 =
      .ok ⟨a2Mp, u32Lay⟩ m1F := by
    simp only [Miri.Interpreter.forceAllocation,
      Miri.Interpreter.requireCurrent_eq,
      Miri.Interpreter.checkLocalIdentity_debugOff _ _
        (refProjPlace_debugOff_v2 rp),
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      h_fi1, bne_self_eq_false, Bool.false_eq_true, ite_false,
      projPlace_getFrame_eq_v2, h_cf1, h_gop1, Miri.Interpreter.stackLift_ok,
      h_pol1, show u32Lay.layout.isSized = true from rfl, Bool.not_true]
    rw [h_as]
    dsimp only [imm42]
    refine eStateM_apply_bind _ _ () stA stB h_wm ?_
    refine eStateM_apply_bind _ _ () stB stC h_alm ?_
    rfl
  -- Step 1 (continued): write `&_1` into `_0` and validate the reference.
  let ptr2 : Miri.Memory.Pointer Miri.Memory.Provenance :=
    ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base ptr2)
  let frame1B :=
    { frame1 with locals := (Array.mk
      [⟨.live (.immediate ptrImm), some refLay⟩,
       ⟨.live (.indirect a2Mp), some u32Lay⟩]) }
  let m1G : RefMiriState := { m1F with stack := ⟨Array.mk [frame1B]⟩ }
  let pRef0 : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance :=
    .local 0 0 none frame1.localsIdentity
  have h_fu : (Miri.Memory.Scalar.fromUInt (@truncateBits .i32 42)
      (Miri.ABI.Size.ofBytes 4) : Except Miri.Memory.ScalarError
        (Miri.Memory.Scalar Miri.Memory.Provenance)).mapError
      Miri.Memory.AllocError.scalar =
      .ok (.fromScalarInt (miriScalar .i32 42)) := rfl
  have h_4le : (4 : Nat) ≤ 16 := by decide
  have h_42lt : (@truncateBits .i32 42).toNat < Nat.pow 2 (8 * 4) := by decide
  have h_rd42 : a2w.readScalar refRuntimeLayoutV2.base rng4 false = .ok sc42 :=
    (Miri.Memory.Allocation.readScalar_int_roundtrip a2w
      refRuntimeLayoutV2.base rng4 (@truncateBits .i32 42) h_winit
      h_4le h_42lt (Or.inl rfl) h_wgb).trans h_fu
  have h_inf1 : m1G.machine.memory.getAllocInfo alloc2IdV2 =
      .ok ⟨Miri.ABI.Size.ofBytes 4, ⟨2⟩, .liveData, .Mut⟩ := rfl
  let ⟨h_ptp1, h_acc1, h_al1⟩ := refValHooksV2_ref_u32_alloc2_v2 rp.types m1G
    refLay.ty .shared .Mut rfl h_inf1
  have h_riu1 := refValHooksV2_readImm_u32_alloc2_v2 rp.types m1G .stack a2w
    sc42 rfl rfl h_rd42
  have h_vis1 := visit_ref_u32_v2 rp.types false pRef0 refLay.ty ptr2 a2Mp m1G
    (fun h => by cases h) rfl rfl rfl h_ptp1 rfl h_acc1 rfl h_al1 rfl
  have h_val1 := validatePlace_ref_u32_v2 rp.types false pRef0 refLay.ty ptr2
    a2Mp sc42 m1G (fun h => by cases h) rfl h_vis1 rfl h_riu1
  have h_wr1 := writeLocalImmediate_direct_v2 rp m1F frame1A 0 .uninit ptrImm
    refLay frame1B rfl rfl rfl rfl rfl h_val1
  let rv1 := toMiriRvalueV2 rp.types (.ref .shared ⟨1, []⟩)
  have h_ev1d := projPlace_evalPlace_local_v2 rp m1 frame1 0 refLay
    (.live (.immediate .uninit)) true rfl rfl rfl
  have h_ev1s := projPlace_evalPlace_local_v2 rp m1 frame1 1 u32Lay
    (.live (.immediate imm42)) true rfl rfl rfl
  have h_ass1 : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨0, Array.empty⟩ rv1 m1 =
      (m1G, .ok ()) := by
    have h_body : Miri.Interpreter.evalRvalueIntoPlace
        (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
          refLimitsV2) 0 rv1 ⟨0, Array.empty⟩ m1 = EStateM.Result.ok () m1G := by
      dsimp only [Miri.Interpreter.evalRvalueIntoPlace, rv1, toMiriRvalueV2,
        toMiriPlaceV2, List.map]
      refine mh_apply_bind _ _ _ _ _ h_ev1d ?_
      refine mh_apply_bind _ _ _ _ _ h_ev1s ?_
      refine mh_apply_bind _ _ a2Mp m1 m1F
        (mh_apply_bind _ _ _ _ _ h_force rfl) ?_
      refine mh_apply_bind _ _ ptrImm m1F m1F rfl ?_
      exact h_wr1
    dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
      Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [show Miri.Interpreter.ExecutionMachine.withValidation
        (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl, h_body]
  let frame2 :=
    { frame1B with location := .mir ⟨0, 2⟩ }
  let m2 : RefMiriState := { m1G with stack := ⟨Array.mk [frame2]⟩ }
  have h_step1 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m1 = (m2, .ok true) :=
    execStep_assign_ok rp m1 m1G frame1 frame1B 0 1
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)).statements
          1 (by decide)))
      ⟨0, Array.empty⟩ rv1 rfl rfl rfl rfl rfl rfl h_ass1 rfl rfl
  -- Step 2: `return` copies `&_1` into the return place, then frees `_1`.
  let stMid : RefMiriState := { m2 with
    machine := { m2.machine with
      user := { m2.machine.user with
        control := advanceRefControl refInitControl } } }
  let stE : RefMiriState := { stMid with stack := ⟨Array.empty⟩ }
  have h_bt := beforeTerminator_initCtrl_v2 rp m2 rfl rfl
  let scP : Miri.Memory.Scalar Miri.Memory.Provenance :=
    .fromPointer refRuntimeLayoutV2.base ptr2
  let rng8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
  let ⟨retW0, h_ws2, h_asz, h_rdp⟩ := alloc_writePtr_readScalar_v2 retAlc ptr2
    rfl h_rlen rfl (by rw [show retAlc.initializationMask = _ from h_rim]; rfl)
    h_rwf h_rpm
  cases retW0 with
  | _ rb sz pv im al mu ex nb =>
  have h1 : sz = Miri.ABI.Size.ofBytes 8 := h_asz
  subst h1
  let retW := (⟨_, h_asz⟩ : Subtype (fun x : RefMiriAlloc => x.byteSize = _)).1
  let memA' : RefMiriMem :=
    { mem1 with live := Array.mk [(alloc2IdV2, ⟨.stack, a2w⟩),
        (retAllocIdV2, ⟨.stack, retAlc⟩)] }
  let memB : RefMiriMem :=
    { mem1 with live := Array.mk [(alloc2IdV2, ⟨.stack, a2w⟩),
        (retAllocIdV2, ⟨.stack, retW⟩)] }
  let stE' : RefMiriState :=
    { stE with machine := { stE.machine with memory := memB } }
  have h_gpm2 := getPtrAllocMut_live_nonghost_v2 rp.types
    (Miri.ABI.Size.ofBytes 8) 8 mem3 memA' .stack retAlc stE.machine
    retAllocIdV2 Miri.ABI.Size.ZERO retPtrV2 (.concrete Miri.Memory.BorTag.one)
    rfl rfl (by rw [← Array.any_toList]; rfl)
    (Miri.Memory.MemoryState.setLiveAllocation_of_find mem3 retAllocIdV2
      ⟨.stack, retAlc⟩ retAlc rfl) rfl rfl rfl rfl rfl rfl
  have h_gpam2 : Miri.Interpreter.getPlaceAllocMut mem3 ⟨stE.machine, none⟩
      ⟨retMemPlaceV2, Miri.Interpreter.localMemoryLayout refLay⟩
      refRuntimeLayoutV2 false none (refAccessConfigV2 rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 rp.types))
      (refAccessConfigV2 rp.types).dynamicLayout =
      ⟨memA', ⟨stE.machine, none⟩, some ⟨retAllocIdV2, rng8, retAlc⟩,
        .ok (some ⟨retAllocIdV2, rng8, retAlc⟩)⟩ :=
    getPlaceAllocMut_sized_of_access_v2' _ _ _ _ _ _ _ _ _ _ rfl rfl h_gpm2
  have h_wi2 : ∀ later, Miri.Interpreter.writeImmediateToMplaceNoValidate mem3
      ⟨stE.machine, none⟩ ptrImm
      ⟨retMemPlaceV2, Miri.Interpreter.localMemoryLayout refLay⟩
      refRuntimeLayoutV2 false none (refAccessConfigV2 rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 rp.types))
      (refAccessConfigV2 rp.types).dynamicLayout later =
      ⟨memB, ⟨stE.machine, none⟩, some ⟨retAllocIdV2, rng8, retW⟩, .ok ()⟩ :=
    fun later => writeImmediate_thinPtr_at_v2 mem3 memA' memB _ _ _ _ ptr2 none
      _ _ _ later ⟨retAllocIdV2, rng8, retAlc⟩ rng8 retW h_gpam2 rfl h_ws2
      (Miri.Memory.MemoryState.setLiveAllocation_of_find memA' retAllocIdV2
        ⟨.stack, retAlc⟩ retW rfl)
  have h_wm2 : (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.writeMemoryNoValidate 0 ptrImm
      ⟨retMemPlaceV2, refLay⟩ stE = .ok () stE' :=
    Miri.Interpreter.PlaceMachine.writeMemory_of_result
      (refAccessConfigV2 rp.types) _ ptrImm ⟨retMemPlaceV2, refLay⟩ stE memB
      (some ⟨retAllocIdV2, rng8, retW⟩) rfl (h_wi2 _)
  have h_cpnv2 : Miri.Interpreter.copyRuntimePlaceNoValidate
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 ⟨.immediate ptrImm, refLay⟩
      ⟨.memory retMemPlaceV2, refLay⟩ true stE = .ok () stE' := by
    dsimp only [Miri.Interpreter.copyRuntimePlaceNoValidate,
      bind, Bind.bind, pure, Pure.pure]
    rw [show (refExecCfgV2 rp).copy.compatible refLay refLay = .ok true from rfl,
      Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [show (refExecCfgV2 rp).copy.hasPadding refLay = .ok false from rfl,
      Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn,
      eStateM_bind_ok (show (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place.takePendingMoveDeinit stE = .ok false stE
        from rfl), ite_false_eq,
      eStateM_bind_ok (show (refExecCfgV2 rp).copy.readRaw 0
        ⟨.immediate ptrImm, refLay⟩ stE = .ok (.immediate
          ⟨ptrImm, Miri.Interpreter.localMemoryLayout refLay⟩) stE from rfl)]
    simp only [show refLay.layout.isSized = true from rfl, bne_self_eq_false,
      Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
    simp only [ite_true]
    dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate,
      Miri.Interpreter.asMplaceOrMutableLocal,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show refLay.layout.isSized = true from rfl]
    exact h_wm2
  have h_ri2 := refValHooksV2_readImm_ptr_ret_v2 rp.types stE' refLay.ty
    .reference .stack retW scP rfl rfl h_rdp
  have h_inf2 : stE'.machine.memory.getAllocInfo alloc2IdV2 =
      .ok ⟨Miri.ABI.Size.ofBytes 4, ⟨2⟩, .liveData, .Mut⟩ := rfl
  let ⟨h_ptp2, h_acc2, h_al2⟩ := refValHooksV2_ref_u32_alloc2_v2 rp.types stE'
    refLay.ty .shared .Mut rfl h_inf2
  have h_riu2 := refValHooksV2_readImm_u32_alloc2_v2 rp.types stE' .stack a2w
    sc42 rfl rfl h_rd42
  have h_vis2 := visit_ref_u32_v2 rp.types true (.memory retMemPlaceV2)
    refLay.ty ptr2 a2Mp stE' (fun _ => rfl) rfl rfl h_ri2 h_ptp2 rfl h_acc2 rfl
    h_al2 rfl
  have h_val2 := validatePlace_ref_u32_v2 rp.types true (.memory retMemPlaceV2)
    refLay.ty ptr2 a2Mp sc42 stE' (fun _ => rfl) rfl h_vis2 rfl h_riu2
  have h_copy := copyRuntimePlace_of_noValidate_v2 rp ⟨.immediate ptrImm, refLay⟩
    ⟨.memory retMemPlaceV2, refLay⟩ true stE stE' rfl h_cpnv2 h_val2
  let memC : RefMiriMem :=
    { mem1 with
      live := Array.mk [(retAllocIdV2, ⟨.stack, retW⟩)]
      dead := Array.mk [⟨alloc2IdV2, a2w.byteSize, a2w.align⟩] }
  let stEnd : RefMiriState :=
    { stE with machine := { stE.machine with memory := memC } }
  have h_dealloc : refDeallocateStackV2 a2Mp.ptr stE' = .ok () stEnd := by
    dsimp only [refDeallocateStackV2,
      Miri.Memory.MemoryLifecycle.deallocatePtrWith, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    simp only [← Array.any_toList]
    rfl
  have h_clean : Miri.Interpreter.CallMachine.cleanup
      { refLifecycle rp.types with storage := refStorageHooksV2 rp.types }
      0 false frame2 stE' = .ok .normal stEnd := by
    have h_loc_for :
        forIn (m := Miri.Interpreter.MachineHooks.M Unit RefUser)
          frame2.locals.toList PUnit.unit
          (fun slot (_ : PUnit) =>
            match slot.value with
            | .live (.indirect place) =>
              Bind.bind ((refStorageHooksV2 rp.types).deallocateStack place.ptr)
                (fun _ => pure (ForInStep.yield PUnit.unit))
            | _ => pure (ForInStep.yield PUnit.unit)) stE' =
        .ok PUnit.unit stEnd := by
      rw [show frame2.locals.toList =
          [⟨.live (.immediate ptrImm), some refLay⟩,
           ⟨.live (.indirect a2Mp), some u32Lay⟩] from rfl,
        List.forIn_cons]
      dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rw [List.forIn_cons]
      refine mh_apply_bind _ _ (ForInStep.yield PUnit.unit) stE' stEnd
        (mh_apply_bind _ _ () stE' stEnd h_dealloc rfl) ?_
      rfl
    dsimp only [Miri.Interpreter.CallMachine.cleanup]
    rw [show frame2.returnContinuation = .stop true from rfl]
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [← Array.forIn_toList]
    refine mh_apply_bind _ _ _ _ _ h_loc_for ?_
    rfl
  have h_retOp : (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.localToOp 0 0 stMid =
      .ok ⟨.immediate ptrImm, refLay⟩ stMid := rfl
  have h_rf := returnFromCurrentFrame_op_at_v2 rp stMid (.immediate ptrImm)
    (.ref .shared u32Ty) retPlace frame2 0 2
    (Array.mk ((@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
      (by decide)).statements.map (toMiriStatementV2 rp.types)))
    memB memC rfl rfl rfl rfl rfl rfl rfl h_retOp h_clean h_copy
  have h_step2 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m2 = (stEnd, .ok true) :=
    execStep_term_ok rp m2 stMid stEnd frame2 0 2
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      rfl rfl rfl rfl rfl h_bt h_rf
  have h_rv : refReadReturnValV2 stEnd.machine.memory
      stEnd.machine.user.callerMem (.ref .shared u32Ty) retPlace =
      .error .undefined := by
    dsimp only [refReadReturnValV2, retPlace, retMemPlaceV2, retPtrV2,
      refTyLayoutFitsU64V2, Bool.not_true, ite_false]
    rw [show stEnd.machine.memory.live.find?
        (fun entry => entry.1 == retAllocIdV2) =
        some (retAllocIdV2, ⟨.stack, retW⟩) from rfl]
    dsimp only [refReadValFromAllocV2]
    rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
      from rfl, h_rdp]
    rfl
  have h_ref := ref_ub_of_coreExec (fuel := 3) h_init (by
    rw [refCoreExecV2_running h_step0 rfl, refCoreExecV2_running h_step1 rfl,
      refCoreExecV2_returned_ub h_step2 rfl h_rv]
    exact True.intro)
  exact ⟨h_ref.1, h_ref.2.2.1, h_ref.2.1⟩

end Anneal.MirCorrespondence
