-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.RefFrame.Frame
public import Anneal.RefFrame.RangedTree

public section

namespace Anneal.RefFrame

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal
open Anneal.ByteSubLens Anneal.ByteRun

/-!
# `RefFrame` and `RangedBorrowTree` Canaries (`Anneal.RefFrame.Canaries`)

LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`, `0` `omega`) positive
and single-cause fail-closed negative witnesses for `Anneal.RefFrame` (all
authored declarations compile with zero axioms `[]`; Lean-synthesized `.injEq`
helpers use `propext`):

1. **Concrete 32-byte provenance-clearing & `MaybeUninit` padding writeback
   (`refFrame_concrete_clear_prov_and_preserve_maybeUninit_pad`, `[]`):**
   Overwrites prior pointer provenance `some 202` inside a 12-byte `&mut`
   referent on both normal return (replacing with `some 303`) and unwind
   (clearing to `none` without assuming the normal postcondition), while
   preserving `.uninit` padding inside the referent and framing `[0..8)` and
   `[20..32)`.
2. **3-arm `TbPermission.associatedAccess` & Miri protector-exit ordering
   (`interiorMutCell_protector_exit_emits_no_access`, `[]`):** Verifies `.Cell`
   (`accessed = true`) emits zero exit access, `.Unique`/`.Frozen` emit `.Write`
   / `.Read`, and Miri's protector-kept-during-access order catches co-frame
   aliasing UB that premature protector removal misses.
3. **Concrete shared 3-node `topo3` commutation + fault contrasts
   (`canary_shared_topo3_commutation_and_contrasts`, `[]`); the universal
   192-case theorem lives in `RangedTree.lean`.**
4. **Straddling-segment split and 3-node chain children-visit mode witnesses
   (`canary_straddling_split_and_chain_visit_modes`, `[]`).**
5. **Single-cause fail-closed `evalRefFrameExit` and `RangedBorrowTree` negative
   regressions (`canary_refFrame_negative_fail_closed_tests`, `[]`), including
   local-first precedence, `.InvariantFailure` preservation, contiguous segment
   tiling, missing-tag/dangling-parent rejection, release-path coverage, and
   zero-length / skip-children guards.**
-/

/-- 12-byte plain mixed-`InitMask` run builder (`[u8, pad3, u32, u8, pad3]`). -/
@[expose] def paddedPlain12Runs (a b3 b2 b1 b0 c : UInt8) : List ByteRun :=
  [.initPlain [a], .uninitPad 3, .initPlain [b3, b2, b1, b0],
   .initPlain [c], .uninitPad 3]

/-- 12-byte pointer-provenance mixed-`InitMask` run builder. -/
@[expose] def paddedProv12Runs (a : UInt8) (prov : AllocId)
    (p3 p2 p1 p0 c : UInt8) : List ByteRun :=
  [.initPlain [a], .uninitPad 3, .initProv prov [p3, p2, p1, p0],
   .initPlain [c], .uninitPad 3]

/-- 32-byte `MemoryState` fixture:
- `[0..8)`: caller pointer `some 101`,
- `[8..20)`: 12-byte `&mut` referent holding prior pointer `some 202` at
  `[12..16)` and `.uninit` padding at `[9..12)` and `[17..20)`,
- `[20..32)`: 12-byte `.uninit` `MaybeUninit` tail. -/
@[expose] def refFrameMem32Init : MemoryState :=
  let callerPtr08 := List.replicate 8 (AllocByte.init 0x10 (some 101))
  let priorRef820 :=
    flattenByteRuns (paddedProv12Runs 0x05 202 0xC0 0xC1 0xC2 0xC3 0x06)
  let uninitTail2032 := List.replicate 12 AllocByte.uninit
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1
         alignLog2 := 3
         mutability := .mut
         bytes := callerPtr08 ++ priorRef820 ++ uninitTail2032
         live := true }] }

/-- 12-byte `ByteSubLens` focusing `[8..20)` in `refFrameMem32Init`. -/
@[expose] def refFrameSlotLens12 : ByteSubLens := ⟨1, 8, 12, 2⟩

/-- Concrete 32-byte `RefFrame` witness (`[]` zero axioms) clearing/replacing
prior pointer provenance `some 202`, preserving `.uninit` padding, and framing
`[0..8)` and `[20..32)` across both normal return and unwind. -/
theorem refFrame_concrete_clear_prov_and_preserve_maybeUninit_pad :
    let normalSlice :=
      flattenByteRuns (paddedProv12Runs 0x42 303 0xD0 0xD1 0xD2 0xD3 0x77)
    let panicPartialSlice :=
      flattenByteRuns (paddedPlain12Runs 0x99 0xEE 0xEE 0xEE 0xEE 0x88)
    callCont4OfTerminator? (.call 1 [] ⟨0, []⟩ (some 2) (.cleanup 3)) =
      some ⟨some 2, .cleanup 3⟩ ∧
    readBytesComp refFrameMem32Init ⟨1, 12⟩ 4 2 =
      .ok [AllocByte.init 0xC0 (some 202), AllocByte.init 0xC1 (some 202),
           AllocByte.init 0xC2 (some 202), AllocByte.init 0xC3 (some 202)] ∧
    (∃ (mNorm mPanic : MemoryState),
      evalRefFrameExit ⟨refFrameSlotLens12, ⟨some 2, .cleanup 3⟩⟩
        refFrameMem32Init (.returned .unit normalSlice) =
        .jumpNormal 2 .unit mNorm ∧
      evalRefFrameExit ⟨refFrameSlotLens12, ⟨some 2, .cleanup 3⟩⟩
        refFrameMem32Init (.unwound panicPartialSlice) =
        .jumpCleanup 3 mPanic ∧
      readBytesComp mPanic ⟨1, 12⟩ 4 2 =
        .ok [AllocByte.init 0xEE none, AllocByte.init 0xEE none,
             AllocByte.init 0xEE none, AllocByte.init 0xEE none] ∧
      readBytesComp mPanic ⟨1, 9⟩ 3 0 =
        .ok (List.replicate 3 AllocByte.uninit) ∧
      readBytesComp mPanic ⟨1, 0⟩ 8 3 =
        .ok (List.replicate 8 (AllocByte.init 0x10 (some 101))) ∧
      readBytesComp mPanic ⟨1, 20⟩ 12 2 =
        .ok (List.replicate 12 AllocByte.uninit) ∧
      readBytesComp mNorm ⟨1, 12⟩ 4 2 =
        .ok [AllocByte.init 0xD0 (some 303), AllocByte.init 0xD1 (some 303),
             AllocByte.init 0xD2 (some 303), AllocByte.init 0xD3 (some 303)] ∧
      readBytesComp mNorm ⟨1, 9⟩ 3 0 =
        .ok (List.replicate 3 AllocByte.uninit) ∧
      readBytesComp mNorm ⟨1, 0⟩ 8 3 =
        .ok (List.replicate 8 (AllocByte.init 0x10 (some 101))) ∧
      readBytesComp mNorm ⟨1, 20⟩ 12 2 =
        .ok (List.replicate 12 AllocByte.uninit)) :=
  ⟨rfl, rfl,
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Tree witnessing interior-mutable `Cell` (`accessed = true`) coexisting with
an accessed co-frame protected `Unique` sibling at `[0..8)`. -/
@[expose] def cellAndUniqueAliasingTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1, 2]
    segments :=
      [⟨0, 8, [(0, ⟨.Cell, true⟩), (1, ⟨.Cell, true⟩), (2, ⟨.Unique, true⟩)]⟩] }

/-- Tree witnessing co-frame protected `Unique` and `ReservedFrz false` tags
(`[1, 2]`) on `[0..8)` plus unaccessed `[8..16)`. -/
@[expose] def coframeAliasingOrderTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1, 2]
    segments :=
      [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
               (2, ⟨.ReservedFrz false, true⟩)]⟩,
       ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
               (2, ⟨.ReservedFrz false, false⟩)]⟩] }

/-- Tree witnessing clean 3-arm exit across `[0..8)` (`Cell`), `[8..16)`
(`Unique`), and `[16..24)` (`Frozen`). -/
@[expose] def threeArmCleanExitTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1]
    segments :=
      [⟨0, 8, [(0, ⟨.Cell, true⟩), (1, ⟨.Cell, true⟩), (2, ⟨.Unique, true⟩)]⟩,
       ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
               (2, ⟨.Frozen, true⟩)]⟩,
       ⟨16, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                (2, ⟨.Unique, true⟩)]⟩] }

/-- Verifies all 3 arms of `TbPermission.associatedAccess` and Miri's
protector-kept-during-access order sensitivity (`[]` zero axioms). -/
theorem interiorMutCell_protector_exit_emits_no_access :
    TbPermission.associatedAccess .Cell = none ∧
    TbPermission.associatedAccess .Unique = some .Write ∧
    TbPermission.associatedAccess .Frozen = some .Read ∧
    TbPermission.associatedAccess (.ReservedFrz false) = some .Read ∧
    (let rRel := releaseProtectorKeepProtected cellAndUniqueAliasingTree 1
     let rExit := exitFrameWithProtectors cellAndUniqueAliasingTree [1]
     rRel.status = .Released ∧
     rRel.tree.protectedTags = [1, 2] ∧
     rRel.tree.segments = cellAndUniqueAliasingTree.segments ∧
     rExit.status = .Released ∧
     rExit.tree.protectedTags = [2] ∧
     rExit.tree.segments = cellAndUniqueAliasingTree.segments) ∧
    (let rRel3 := releaseProtectorKeepProtected threeArmCleanExitTree 1
     let rExit3 := exitFrameWithProtectors threeArmCleanExitTree [1]
     rRel3.status = .Released ∧
     rRel3.tree.protectedTags = [1] ∧
     rExit3.status = .Released ∧
     rExit3.tree.protectedTags = [] ∧
     rExit3.tree.segments =
       [⟨0, 8, [(0, ⟨.Cell, true⟩), (1, ⟨.Cell, true⟩), (2, ⟨.Unique, true⟩)]⟩,
        ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, true⟩)]⟩,
        ⟨16, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                 (2, ⟨.Frozen, true⟩)]⟩]) ∧
    (let miriOrder := exitFrameWithProtectors coframeAliasingOrderTree [2, 1]
     let prematurePop := endCallRemoveProtectors coframeAliasingOrderTree [2, 1]
     let buggyOrder := releaseProtectorKeepProtected prematurePop 2
     miriOrder.status = .AccessFailure 0 8 1 (.ProtectedDisabled .Unique) ∧
     buggyOrder.status = .Released) :=
  ⟨rfl, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl⟩⟩

/-- Canonical shared 3-node `topo3` tree with `protectedTags = [1, 2]`, `src`
`(Frozen, true)` on `[0..8)`, and `dst` `(ReservedFrz false, false)` on
`[8..16)`. -/
@[expose] def sharedTopo3Disjoint16 : RangedBorrowTree :=
  mkSharedTopo3Tree16 .Frozen true (.ReservedFrz false) false [1, 2]

/-- Concrete shared `topo3` commutation + clean protector exit alongside
`accessed = true` and single-cause overlapping-write `.ProtectedDisabled` traps
(`[]` zero axioms). -/
theorem canary_shared_topo3_commutation_and_contrasts :
    (let s1 :=
       performRangedAccess sharedTopo3Disjoint16 0 8 1 .Read
         .VisitChildrenOfAccessed
     let s12 :=
       performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
     let s2 :=
       performRangedAccess sharedTopo3Disjoint16 8 8 2 .Write
         .VisitChildrenOfAccessed
     let s21 :=
       performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
     let ex := exitFrameWithProtectors s12.tree [1, 2]
     s12.status = .Completed ∧
     s21.status = .Completed ∧
     s12.tree = s21.tree ∧
     s12.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                (2, ⟨.Disabled, false⟩)]⟩,
        ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                (2, ⟨.Unique, true⟩)]⟩] ∧
     ex.status = .Released ∧
     ex.tree.protectedTags = []) ∧
    (let treeAccTrue : RangedBorrowTree :=
       { topology := topo3
         protectedTags := [1, 2]
         segments :=
           [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                    (2, ⟨.Disabled, true⟩)]⟩,
            ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                    (2, ⟨.ReservedFrz false, false⟩)]⟩] }
     (performRangedAccess treeAccTrue 0 8 1 .Read
        .VisitChildrenOfAccessed).status =
       .TransitionError 0 8 2 (.ProtectedDisabled .Disabled)) ∧
    (let treeOverlapWrite : RangedBorrowTree :=
       { topology := topo3
         protectedTags := [1, 2]
         segments :=
           [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                    (2, ⟨.ReservedFrz false, false⟩)]⟩,
            ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                    (2, ⟨.ReservedFrz false, false⟩)]⟩] }
     (performRangedAccess treeOverlapWrite 0 8 2 .Write
        .VisitChildrenOfAccessed).status =
       .TransitionError 0 8 1 (.ProtectedDisabled .Frozen)) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Straddling-segment split (`[4..12)` inside `[0..16)`) and 3-node chain
(`0 -> 1 -> 3`) `.SkipChildrenOfAccessed` vs `.VisitChildrenOfAccessed`
witnesses (`[]` zero axioms). -/
theorem canary_straddling_split_and_chain_visit_modes :
    (let singleSeg16 : RangedBorrowTree :=
       { topology := topo3
         protectedTags := []
         segments :=
           [⟨0, 16, [(0, ⟨.Unique, true⟩), (1, ⟨.ReservedFrz false, false⟩),
                     (2, ⟨.Frozen, true⟩)]⟩] }
     let res :=
       performRangedAccess singleSeg16 4 8 1 .Write .VisitChildrenOfAccessed
     res.status = .Completed ∧
     res.tree.segments =
       [⟨0, 4, [(0, ⟨.Unique, true⟩), (1, ⟨.ReservedFrz false, false⟩),
                (2, ⟨.Frozen, true⟩)]⟩,
        ⟨4, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, true⟩)]⟩,
        ⟨12, 4, [(0, ⟨.Unique, true⟩), (1, ⟨.ReservedFrz false, false⟩),
                 (2, ⟨.Frozen, true⟩)]⟩]) ∧
    (let chainTopo : List TbTopoNode :=
       [⟨0, none⟩, ⟨1, some 0⟩, ⟨3, some 1⟩]
     let chainTree : RangedBorrowTree :=
       { topology := chainTopo
         protectedTags := []
         segments :=
           [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                    (3, ⟨.Frozen, true⟩)]⟩] }
     let skipRes :=
       performRangedAccess chainTree 0 8 1 .Write .SkipChildrenOfAccessed
     let visitRes :=
       performRangedAccess chainTree 0 8 1 .Write .VisitChildrenOfAccessed
     skipRes.status = .Completed ∧
     skipRes.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Frozen, true⟩)]⟩] ∧
     visitRes.status = .Completed ∧
     visitRes.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Disabled, true⟩)]⟩]) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Shared-mutability 32-byte `MemoryState` fixture for writeback rejection. -/
@[expose] def sharedAllocMem : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1
         alignLog2 := 3
         mutability := .shared
         bytes := List.replicate 32 (AllocByte.init 0 none)
         live := true }] }

/-- Deallocated 32-byte `MemoryState` fixture for writeback rejection. -/
@[expose] def deadAllocMem : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1
         alignLog2 := 3
         mutability := .mut
         bytes := List.replicate 32 (AllocByte.init 0 none)
         live := false }] }

/-- Single-cause fail-closed `evalRefFrameExit`, `callCont4OfTerminator?`, and
`RangedBorrowTree` regression suite (`[]` zero axioms), covering framing
faults, local-first precedence, `.InvariantFailure` preservation, contiguous
segment tiling (rejecting gaps and overlaps), missing actor/topology/parent
tags, release-path missing-tag and `.SkipChildrenOfAccessed` grandchild guards,
full-chain leaf actor fuel, `.ProtectedDisabled` write-back, protected
`ReservedFrz true` conflict marking, and zero-length access behavior. -/
theorem canary_refFrame_negative_fail_closed_tests :
    let slice12 := List.replicate 12 (AllocByte.init 0x11 none)
    let slice8 := List.replicate 8 (AllocByte.init 0x11 none)
    let localFirstTree : RangedBorrowTree :=
      { topology := topo3
        protectedTags := [1, 2]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.Frozen, true⟩)]⟩] }
    let invPresTree : RangedBorrowTree :=
      { topology := [⟨0, none⟩, ⟨1, some 0⟩, ⟨2, some 0⟩, ⟨3, some 0⟩]
        protectedTags := [1, 2, 3]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.ReservedIM, false⟩), (3, ⟨.Unique, true⟩)]⟩] }
    let partialCovTree : RangedBorrowTree :=
      { topology := topo3
        protectedTags := [1]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.Disabled, false⟩)]⟩] }
    let missingNodeTree : RangedBorrowTree :=
      { topology := topo3
        protectedTags := [1, 2]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (2, ⟨.Disabled, false⟩)]⟩] }
    let validStates8 : List (Nat × TbLocationState) :=
      [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩), (2, ⟨.Disabled, false⟩)]
    let dupOverlapTree : RangedBorrowTree :=
      ⟨topo3, [], [⟨0, 4, validStates8⟩, ⟨0, 4, validStates8⟩]⟩
    let partialOverlapTree : RangedBorrowTree :=
      ⟨topo3, [], [⟨0, 6, validStates8⟩, ⟨2, 2, validStates8⟩]⟩
    let danglingParentTree : RangedBorrowTree :=
      ⟨[⟨0, none⟩, ⟨1, some 7⟩, ⟨2, some 0⟩], [],
       [⟨0, 8, [(0, ⟨.Frozen, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, false⟩)]⟩]⟩
    let danglingChain1 : RangedBorrowTree :=
      ⟨[⟨0, some 7⟩], [0], [⟨0, 8, [(0, ⟨.Unique, true⟩)]⟩]⟩
    let danglingChain2 : RangedBorrowTree :=
      ⟨[⟨0, some 7⟩, ⟨1, some 0⟩], [1],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩)]⟩]⟩
    let actorInStatesNotTopoTree : RangedBorrowTree :=
      ⟨topo3, [], [⟨0, 8, validStates8 ++ [(99, ⟨.Unique, true⟩)]⟩]⟩
    let foreignStatelessTree : RangedBorrowTree :=
      ⟨topo3, [2], [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩)]⟩]⟩
    let unprotFrameTagTree : RangedBorrowTree :=
      ⟨topo3, [2], [⟨0, 8, validStates8⟩]⟩
    let cellMissingOtherTree : RangedBorrowTree :=
      ⟨topo3, [1], [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Cell, true⟩)]⟩]⟩
    let chainReleaseTree : RangedBorrowTree :=
      ⟨[⟨0, none⟩, ⟨1, some 0⟩, ⟨3, some 1⟩], [1],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Unique, true⟩)]⟩]⟩
    let grandchildReleaseTree : RangedBorrowTree :=
      ⟨[⟨0, none⟩, ⟨1, some 0⟩, ⟨3, some 1⟩, ⟨4, some 3⟩], [1],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Unique, true⟩), (4, ⟨.Unique, true⟩)]⟩]⟩
    let protDisabledTree : RangedBorrowTree :=
      ⟨topo3, [2],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Unique, true⟩)]⟩]⟩
    let protResFrzTree : RangedBorrowTree :=
      ⟨topo3, [2],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.ReservedFrz false, true⟩)]⟩]⟩
    callCont4OfTerminator? (.goto 1) = none ∧
    evalRefFrameExit ⟨refFrameSlotLens12, ⟨none, .cleanup 3⟩⟩
      refFrameMem32Init (.returned .unit slice12) = .fault .undefined ∧
    evalRefFrameExit ⟨refFrameSlotLens12, ⟨some 2, .unreachable⟩⟩
      refFrameMem32Init (.unwound slice12) = .fault .undefined ∧
    evalRefFrameExit ⟨refFrameSlotLens12, ⟨some 2, .cleanup 3⟩⟩
      refFrameMem32Init (.returned .unit slice8) = .fault .undefined ∧
    evalRefFrameExit ⟨⟨1, 8, 0, 0⟩, ⟨some 2, .cleanup 3⟩⟩
      refFrameMem32Init (.returned .unit []) = .fault .undefined ∧
    evalRefFrameExit ⟨⟨99, 8, 12, 2⟩, ⟨some 2, .cleanup 3⟩⟩
      refFrameMem32Init (.returned .unit slice12) = .fault .undefined ∧
    evalRefFrameExit ⟨refFrameSlotLens12, ⟨some 2, .cleanup 3⟩⟩
      sharedAllocMem (.returned .unit slice12) = .fault .undefined ∧
    evalRefFrameExit ⟨refFrameSlotLens12, ⟨some 2, .cleanup 3⟩⟩
      deadAllocMem (.unwound slice12) = .fault .undefined ∧
    evalRefFrameExit ⟨⟨1, 24, 12, 2⟩, ⟨some 2, .cleanup 3⟩⟩
      refFrameMem32Init (.returned .unit slice12) = .fault .undefined ∧
    evalRefFrameExit ⟨⟨1, 9, 12, 2⟩, ⟨some 2, .cleanup 3⟩⟩
      refFrameMem32Init (.returned .unit slice12) = .fault .undefined ∧
    (performRangedAccess sharedTopo3Disjoint16 0 8 99 .Read
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess sharedTopo3Disjoint16 100 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess ⟨topo3, [1], []⟩ 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess partialCovTree 0 16 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess missingNodeTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess dupOverlapTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess partialOverlapTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess danglingParentTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess danglingChain1 0 8 0 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (releaseProtectorKeepProtected danglingChain1 0).status = .MissingTag 0 ∧
    (performRangedAccess danglingChain2 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (releaseProtectorKeepProtected danglingChain2 1).status = .MissingTag 1 ∧
    (performRangedAccess actorInStatesNotTopoTree 0 8 99 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess actorInStatesNotTopoTree 0 0 99 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess foreignStatelessTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (exitFrameWithProtectors unprotFrameTagTree [1, 2]).status = .MissingTag 1 ∧
    performSegmentAccess topo3 [] ⟨0, 8, validStates8⟩ 99 .Write
      .VisitChildrenOfAccessed = .missingState ⟨0, 8, validStates8⟩ ∧
    (releaseProtectorKeepProtected sharedTopo3Disjoint16 99).status =
      .MissingTag 99 ∧
    (releaseProtectorKeepProtected missingNodeTree 1).status =
      .MissingTag 1 ∧
    (releaseProtectorKeepProtected cellMissingOtherTree 1).status =
      .MissingTag 1 ∧
    (releaseProtectorKeepProtected ⟨topo3, [1], []⟩ 1).status =
      .MissingTag 1 ∧
    performRangedAccess ⟨topo3, [1], []⟩ 0 0 1 .Write
      .VisitChildrenOfAccessed = ⟨⟨topo3, [1], []⟩, .Completed⟩ ∧
    (let rChain := exitFrameWithProtectors chainReleaseTree [1]
     rChain.status = .Released ∧
     rChain.tree.segments = chainReleaseTree.segments) ∧
    (let rLocal :=
       performRangedAccess localFirstTree 0 8 2 .Write .VisitChildrenOfAccessed
     rLocal.status = .TransitionError 0 8 2 (.ChildAccessForbidden .Frozen) ∧
     rLocal.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Frozen, true⟩)]⟩]) ∧
    (let rInv :=
       performRangedAccess invPresTree 0 8 1 .Write .VisitChildrenOfAccessed
     rInv.status = .InvariantFailure 0 8 2 ∧
     rInv.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.ReservedIM, false⟩), (3, ⟨.Unique, true⟩)]⟩]) ∧
    (performRangedAccess sharedTopo3Disjoint16 0 8 1 .Write
      .VisitChildrenOfAccessed).status =
      .TransitionError 0 8 1 (.ChildAccessForbidden .Frozen) ∧
    (TbLocationState.performAccess ⟨.ReservedIM, false⟩ .Read
      .ForeignAccess true) = .InvariantFailure ⟨.ReservedIM, false⟩ ∧
    (performRangedAccess chainReleaseTree 0 8 3 .Write
      .VisitChildrenOfAccessed).status = .Completed ∧
    (let rGrand := exitFrameWithProtectors grandchildReleaseTree [1]
     rGrand.status = .Released ∧
     rGrand.tree.segments = grandchildReleaseTree.segments) ∧
    (let rProtDis :=
       performRangedAccess protDisabledTree 0 8 1 .Write
         .VisitChildrenOfAccessed
     rProtDis.status = .TransitionError 0 8 2 (.ProtectedDisabled .Unique) ∧
     rProtDis.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, true⟩)]⟩]) ∧
    (let rResFrz :=
       performRangedAccess protResFrzTree 0 8 1 .Read .VisitChildrenOfAccessed
     rResFrz.status = .Completed ∧
     rResFrz.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.ReservedFrz true, true⟩)]⟩]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Anneal.RefFrame

end
