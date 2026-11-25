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
public import Init.SimpLemmas
public import Trusted.MirAst
public import Trusted.MirSemantics.Memory
public import Anneal.MirMemComp.Memory
public import Anneal.MiriTreeBorrows.Model

public section

/-!
# Miri Reborrow Pipeline & Protector Release (`Anneal.MiriTreeBorrows.Retag`)

Computable, zero-axiom (`[]`) Miri reborrow and frame-exit protector pipeline
aligned with `vendor/lean-miri/Miri/TreeBorrows/` (`RetagPolicy`,
`RetagPipeline`, `TreeState`, `GlobalState`) and
`vendor/lean-miri/Miri/Interpreter/MachineHooks.lean`:

- `miriReborrowTag` implements `RetagPipeline.runReborrow` and
  `RetagPipeline.accessTreeForReborrow` (`RetagPipeline.lean:199-320`) plus
  `BorrowTree.newChild` (`TreeState.lean:672-745`): validates inside/outside
  initial location states (rejecting non-initial permissions, protected
  `.reservedIM`, and lazy `.unique`), fails closed on unknown protector frames
  (`.missingFrame`), registers the protector before any allocation lookup
  or parent access (threading that state through every later error, as
  `RetagPipeline.lean:290-319` does), fails closed on dead or missing
  allocations (`.deadOrMissingAlloc`, even when `size = 0`), missing trees or
  uncovered `.cell` ranges
  (`.uncoveredRange`), duplicate child tags (`.duplicateTag`), missing parents
  (`.missingTag`), and `.write` reborrows on `.shared` allocations
  (`.writeToReadOnly`), executes the parent `miriAssociatedAccess` traversal
  (`miriPerformRangedAccess` through `parentTag` with
  `.visitChildrenOfAccessed`), globally weakens ancestor SIFA (`outsideLoc.sifa`
  when `size = 0`, `min(insideLoc.sifa, outsideLoc.sifa)` when `size > 0`,
  matching `TreeState.lean:616-745`), and inserts `newTag`.
- `miriBeginFrame` fails closed on a duplicate `frameId` (`.duplicateFrame`).
- `miriReleaseOneProtector`, `miriReleaseTagListForward`, and
  `miriExitCallFrame` align with `BorrowTree.releaseProtector`
  (`TreeState.lean:1036-1070`) and `MachineHooks.beforeStackPopWithEnsure`
  (`MachineHooks.lean:414-450`): fail-closed validation on missing frames,
  missing allocations in `mem` (`.deadOrMissingAlloc`), missing live allocation
  trees, and missing tags/segment entries, forward registration-order release on
  live allocations (skipping deallocated entries with `live = false`) with
  `.skipChildrenOfAccessed` while all frame protectors stay active, and
  `miriEndCall` only after every release succeeds.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and compile with zero axioms (`[]`).
-/

namespace Anneal.MiriTreeBorrows

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirMemComp

/-- Returns `true` iff `allocId` exists in `mem` with `live = true`. -/
@[expose] def miriIsAllocLive (allocId : AllocId) (mem : MemoryState) : Bool :=
  match execFindAllocation allocId mem.allocations with
  | none => false
  | some a => a.live

/-- Weakens ancestor SIFA caches along `ancPath` across `seg` to be no stronger
than `strongestAllowed` (`TreeState.lean:638-663`). -/
@[expose] def miriWeakenSegmentAncestors (ancPath : List Nat)
    (strongestAllowed : MiriSifa) (seg : MiriSegment) : MiriSegment :=
  let entries' :=
    seg.entries.map (fun e =>
      if miriNatListMem e.tag ancPath then
        { tag := e.tag
          loc := { perm := e.loc.perm
                   accessed := e.loc.accessed
                   sifa := miriSifaEnsureNoStrongerThan e.loc.sifa
                     strongestAllowed } }
      else
        e)
  { offset := seg.offset, size := seg.size, entries := entries' }

/-- Looks up a protector frame record by `frameId`. -/
@[expose] def miriFindFrame? (frameId : Nat)
    (frames : List MiriFrameProtectors) : Option MiriFrameProtectors :=
  frames.foldl (fun acc f => if Nat.beq f.frameId frameId then some f else acc)
    none

/-- Validates an optional protector `frameId` against `frames`. -/
@[expose] def miriCheckFrameOpt (frameIdOpt : Option Nat)
    (frames : List MiriFrameProtectors) : Except MiriTbError Unit :=
  match frameIdOpt with
  | none => .ok ()
  | some fid =>
    match miriFindFrame? fid frames with
    | none => .error (.missingFrame fid)
    | some _ => .ok ()

/-- Pushes a new empty protector frame onto `st.frames`, failing closed with
`.duplicateFrame frameId` (and `st` unchanged) when `frameId` is already
registered, so that the distinct-frame-ID invariant is preserved. -/
@[expose] def miriBeginFrame (st : MiriTbState) (frameId : Nat) :
    MiriTbResult MiriTbState :=
  match miriFindFrame? frameId st.frames with
  | some _ => .err st (.duplicateFrame frameId)
  | none =>
    .ok { frames := { frameId := frameId, protectedTags := [] } :: st.frames
          allocTrees := st.allocTrees }

/-- Appends `(allocId, newTag)` to the protected tags of frame `fid` when
`frameIdOpt = some fid` (`GlobalState.addProtector`,
`GlobalState.lean:137-140`); returns `st` unchanged when `frameIdOpt = none`.
-/
@[expose] def miriRegisterProtectorOpt (st : MiriTbState)
    (frameIdOpt : Option Nat) (allocId : AllocId) (newTag : Nat) :
    MiriTbState :=
  match frameIdOpt with
  | none => st
  | some fid =>
    { frames :=
        st.frames.map (fun f =>
          if Nat.beq f.frameId fid then
            { frameId := f.frameId
              protectedTags := f.protectedTags ++ [(allocId, newTag)] }
          else
            f)
      allocTrees := st.allocTrees }

/-- Registers a child borrow tag following `RetagPipeline.runReborrow`,
`RetagPipeline.accessTreeForReborrow` (`RetagPipeline.lean:199-320`), and
`BorrowTree.newChild` (`TreeState.lean:672-745`):
1. Validates `miriInitialInsideLoc` and `miriInitialOutsideLoc` (rejecting
   non-initial permissions, protected `.reservedIM`, and lazy `.unique`).
2. When `frameIdOpt = some fid`, validates that `fid` exists in `st.frames`
   (`.missingFrame`), then registers `(allocId, newTag)` as protected in
   `fid` before any allocation lookup or parent access
   (`RetagPipeline.lean:290-294`). Every later failure returns the
   registered state, matching `RetagPipeline.lean:296-319`. Step 1 errors
   still return `st` unchanged; Miri builds initial states after
   registration (`RetagPipeline.lean:305-308`).
3. Validates that `allocId` is a live allocation in `mem`
   (`.deadOrMissingAlloc`, rejected conservatively even when `size = 0`), that
   `allocId` has a tree in `st` (`.uncoveredRange`), that `newTag` is fresh in
   `atree.tree` (`.duplicateTag`), and that `parentTag` exists in `atree.tree`
   (`.missingTag`).
4. When `size > 0`: verifies contiguous range coverage `[off, off + size)` for
   `miriAssociatedAccess insidePerm = none` (`.cell`), and for `some pKind`
   rejects `.write` on `.shared` allocations (`.writeToReadOnly`) before
   executing `miriPerformRangedAccess` on `parentTag` with
   `.visitChildrenOfAccessed` (a failed parent access returns its partial
   state, which already holds the protector).
5. Weakens ancestor SIFA globally across all segments (`outsideLoc.sifa` when
   `size = 0`, `min(insideLoc.sifa, outsideLoc.sifa)` when `size > 0`, matching
   `TreeState.lean:616-745`) and inserts `newTag` (`insideLoc` inside
   `[off, off + size)`, `outsideLoc` outside). -/
@[expose] def miriReborrowTag (mem : MemoryState) (st : MiriTbState)
    (frameIdOpt : Option Nat) (allocId : AllocId) (newTag parentTag : Nat)
    (insidePerm outsidePerm : MiriPerm) (off size : Nat) :
    MiriTbResult MiriTbState :=
  let isProtected :=
    match frameIdOpt with
    | some _ => true
    | none => false
  match miriInitialInsideLoc newTag insidePerm isProtected with
  | .error err => .err st err
  | .ok insideLoc =>
    match miriInitialOutsideLoc newTag outsidePerm isProtected with
    | .error err => .err st err
    | .ok outsideLoc =>
      match miriCheckFrameOpt frameIdOpt st.frames with
      | .error err => .err st err
      | .ok () =>
        let stReg := miriRegisterProtectorOpt st frameIdOpt allocId newTag
        match miriIsAllocLive allocId mem with
        | false => .err stReg (.deadOrMissingAlloc allocId)
        | true =>
          match execFindAllocation allocId mem.allocations with
          | none => .err stReg (.deadOrMissingAlloc allocId)
          | some a =>
            match miriFindAllocTree? allocId st.allocTrees with
            | none => .err stReg (.uncoveredRange allocId)
            | some atree0 =>
              match miriFindTopoNode? newTag atree0.tree with
              | some _ => .err stReg (.duplicateTag newTag)
              | none =>
                match miriFindTopoNode? parentTag atree0.tree with
                | none => .err stReg (.missingTag parentTag)
                | some _ =>
                  let isShared : Bool :=
                    match a.mutability with
                    | .shared => true
                    | .mut => false
                  let parentStep : MiriTbResult MiriTbState :=
                    match Nat.beq size 0 with
                    | true => .ok stReg
                    | false =>
                      match miriAssociatedAccess insidePerm with
                      | none =>
                        if miriRangeIsCovered off size atree0.segments then
                          .ok stReg
                        else
                          .err stReg (.uncoveredRange allocId)
                      | some pKind =>
                        match !miriKindIsRead pKind && isShared with
                        | true => .err stReg (.writeToReadOnly allocId)
                        | false =>
                          miriPerformRangedAccess stReg allocId parentTag off
                            size pKind .visitChildrenOfAccessed
                  match parentStep with
                  | .err partialSt err => .err partialSt err
                  | .ok stAfterParent =>
                    match miriFindAllocTree? allocId stAfterParent.allocTrees
                        with
                    | none => .err stAfterParent (.uncoveredRange allocId)
                    | some atree =>
                      let ancPath := miriAncestorPath atree.tree parentTag
                      let tree' :=
                        miriInsertChildTopo atree.tree parentTag newTag
                      let splitSegs := miriSplitSegmentsAt off size
                        atree.segments
                      let minSifa :=
                        if Nat.beq size 0 then
                          outsideLoc.sifa
                        else
                          miriSifaEnsureNoStrongerThan insideLoc.sifa
                            outsideLoc.sifa
                      let segs' :=
                        splitSegs.map (fun seg =>
                          let wSeg :=
                            miriWeakenSegmentAncestors ancPath minSifa seg
                          let childLoc :=
                            if miriSegmentOverlaps off size seg then
                              insideLoc
                            else
                              outsideLoc
                          { offset := wSeg.offset
                            size := wSeg.size
                            entries :=
                              wSeg.entries ++
                                [{ tag := newTag, loc := childLoc }] })
                      .ok { frames := stAfterParent.frames
                            allocTrees :=
                              miriReplaceAllocTree
                                { allocId := allocId
                                  tree := tree'
                                  segments := segs' }
                                stAfterParent.allocTrees }

/-- `RetagMode.FnEntry` reborrow wrapper using `miriSelectRetagPerm`
(`RetagPolicy.lean:52-92`).

Precondition: the pointee's freeze status is uniform over
`[off, off + size)`. A single `frozen` bit selects one inside permission for
the whole range, as Miri does when `preciseInteriorMut = false`
(`RetagPipeline.lean:181-184`). Miri's precise mode instead builds a
per-range freeze map (`RetagPipeline.lean:185-197`), which is not modeled.
A mixed layout (frozen fields next to `UnsafeCell` bytes) is outside this
model; it cannot be emulated by several calls, since each call needs a
fresh `newTag`. `miriRegisterFnEntryArg_uniform_freeze` states the uniform
selection. -/
@[expose] def miriRegisterFnEntryArg (mem : MemoryState) (st : MiriTbState)
    (frameId : Nat) (allocId : AllocId) (newTag parentTag : Nat)
    (refKind : MiriRefKind) (frozen implicitWrites : Bool)
    (off size : Nat) : MiriTbResult MiriTbState :=
  let inPerm := miriSelectRetagPerm refKind true frozen true implicitWrites
  let outPerm := miriSelectRetagPerm refKind false frozen true implicitWrites
  miriReborrowTag mem st (some frameId) allocId newTag parentTag inPerm outPerm
    off size

/-- Fail-closed `BorrowTree.releaseProtector` (`TreeState.lean:1036-1070`,
`MachineHooks.lean:430-431`): fails closed if `allocId` is missing from
`st.allocTrees` (`.uncoveredRange`) or `tag` is absent from `atree.tree` or any
segment's `entries` (`.missingTag`), iterates forward across segments, skips
unaccessed or `.cell` segments, and emits `miriAssociatedAccess e.loc.perm`
through `tag` with `.skipChildrenOfAccessed` while all `st.frames` protectors
remain active. -/
@[expose] def miriReleaseOneProtector (st : MiriTbState) (allocId : AllocId)
    (tag : Nat) : MiriTbResult MiriTbState :=
  match miriFindAllocTree? allocId st.allocTrees with
  | none => .err st (.uncoveredRange allocId)
  | some atree =>
    match miriFindTopoNode? tag atree.tree with
    | none => .err st (.missingTag tag)
    | some _ =>
      let prot := miriProtectedTagsOnAlloc allocId st.frames
      let foldRes :=
        atree.segments.foldl
          (fun (acc : List MiriSegment × Option MiriTbError) seg =>
            match acc.2 with
            | some err => (acc.1 ++ [seg], some err)
            | none =>
              match miriFindTagEntry? tag seg.entries with
              | none => (acc.1 ++ [seg], some (.missingTag tag))
              | some e =>
                match miriAssociatedAccess e.loc.perm with
                | none => (acc.1 ++ [seg], none)
                | some rKind =>
                  if e.loc.accessed then
                    match miriPerformSegmentAccess atree.tree prot tag rKind
                        .skipChildrenOfAccessed seg with
                    | .ok seg' => (acc.1 ++ [seg'], none)
                    | .err partialSeg err => (acc.1 ++ [partialSeg], some err)
                  else
                    (acc.1 ++ [seg], none))
          ([], none)
      let st' : MiriTbState :=
        { frames := st.frames
          allocTrees :=
            miriReplaceAllocTree
              { allocId := allocId, tree := atree.tree, segments := foldRes.1 }
              st.allocTrees }
      match foldRes.2 with
      | none => .ok st'
      | some err => .err st' err

/-- Forward protector release loop (`MachineHooks.lean:422-445`): fails closed
if `allocId` is absent from `mem` (`.deadOrMissingAlloc`), skips deallocated
allocations (`live = false`), and releases each `(allocId, tag)` on live
allocations via `List.foldl`, preserving partial `MiriTbState` mutations on
failure. -/
@[expose] def miriReleaseTagListForward (mem : MemoryState) (st : MiriTbState)
    (tags : List (AllocId × Nat)) : MiriTbResult MiriTbState :=
  tags.foldl
    (fun acc pair =>
      match acc with
      | .err partialSt err => .err partialSt err
      | .ok curSt =>
        match execFindAllocation pair.1 mem.allocations with
        | none => .err curSt (.deadOrMissingAlloc pair.1)
        | some a =>
          if a.live then
            miriReleaseOneProtector curSt pair.1 pair.2
          else
            .ok curSt)
    (.ok st)

/-- Reversed-order release comparator (`tags.reverse`). -/
@[expose] def miriReleaseTagListReverse (mem : MemoryState) (st : MiriTbState)
    (tags : List (AllocId × Nat)) : MiriTbResult MiriTbState :=
  miriReleaseTagListForward mem st tags.reverse

/-- `GlobalState.endCall` (`TreeBorrows/GlobalState.lean:146-148`): removes
`frameId` from `st.frames`. -/
@[expose] def miriEndCall (st : MiriTbState) (frameId : Nat) : MiriTbState :=
  let frames' :=
    st.frames.foldl
      (fun acc f => if Nat.beq f.frameId frameId then acc else acc ++ [f])
      []
  { frames := frames', allocTrees := st.allocTrees }

/-- Fail-closed Miri `beforeStackPopWithEnsure` + `endCall`
(`MachineHooks.lean:414-450`): rejects unknown `frameId` with
`.missingFrame frameId`, releases all `frame.protectedTags` in forward order
while all protectors stay registered, and calls `miriEndCall` only if every
release succeeds. -/
@[expose] def miriExitCallFrame (mem : MemoryState) (st : MiriTbState)
    (frameId : Nat) : MiriTbResult MiriTbState :=
  match miriFindFrame? frameId st.frames with
  | none => .err st (.missingFrame frameId)
  | some frame =>
    match miriReleaseTagListForward mem st frame.protectedTags with
    | .err partialSt err => .err partialSt err
    | .ok releasedSt => .ok (miriEndCall releasedSt frameId)

/-- Universal rejection of protected `.reservedIM` inside range (`[]`). -/
theorem miriReborrowTag_rejects_protected_reservedIM (mem : MemoryState)
    (st : MiriTbState) (fid : Nat) (allocId : AllocId)
    (newTag parentTag off size : Nat) (outsidePerm : MiriPerm) :
    miriReborrowTag mem st (some fid) allocId newTag parentTag .reservedIM
      outsidePerm off size =
      .err st (.impossibleProtectedReservedIM newTag) :=
  rfl

/-- Universal rejection of `.unique` (write-associated) reborrow on a live
`.shared` allocation (`[]`, matching `RetagPipeline.lean:210-211`). The
error state retains the protector registered for `frameIdOpt`
(`RetagPipeline.lean:290-294`). -/
theorem miriReborrowTag_rejects_write_on_readonly_alloc (mem : MemoryState)
    (st : MiriTbState) (frameIdOpt : Option Nat) (allocId : AllocId)
    (newTag parentTag off size : Nat) (outsidePerm : MiriPerm)
    (a : Allocation) (atree : MiriAllocTree) (pnd : MiriTopoNode)
    (outLoc : MiriLocState)
    (hOut : miriInitialOutsideLoc newTag outsidePerm
      (match frameIdOpt with | some _ => true | none => false) = .ok outLoc)
    (hFrame : miriCheckFrameOpt frameIdOpt st.frames = .ok ())
    (hAlloc : execFindAllocation allocId mem.allocations = some a)
    (hLive : a.live = true)
    (hTree : miriFindAllocTree? allocId st.allocTrees = some atree)
    (hFresh : miriFindTopoNode? newTag atree.tree = none)
    (hParent : miriFindTopoNode? parentTag atree.tree = some pnd)
    (hSize : Nat.beq size 0 = false)
    (hMut : a.mutability = .shared) :
    miriReborrowTag mem st frameIdOpt allocId newTag parentTag .unique
      outsidePerm off size =
      .err (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
        (.writeToReadOnly allocId) := by
  unfold miriReborrowTag
  dsimp only [miriInitialInsideLoc, miriPermIsInitial, miriStrongestSifa,
    miriAssociatedAccess, miriNewAccessed]
  rw [hOut]
  dsimp only
  rw [hFrame]
  dsimp only [miriIsAllocLive]
  rw [hAlloc]
  dsimp only
  rw [hLive]
  dsimp only
  rw [hTree]
  dsimp only
  rw [hFresh]
  dsimp only
  rw [hParent]
  dsimp only
  rw [hSize]
  dsimp only [miriKindIsRead]
  rw [hMut]
  rfl

/-- Universal protector retention on allocation failure (`[]`, matching
`RetagPipeline.lean:290-298`): once the initial states and the frame check
succeed, a protected reborrow of a dead or missing allocation fails with the
protector of `newTag` already registered in frame `fid`. -/
theorem miriReborrowTag_dead_alloc_retains_protector (mem : MemoryState)
    (st : MiriTbState) (fid : Nat) (allocId : AllocId)
    (newTag parentTag off size : Nat) (insidePerm outsidePerm : MiriPerm)
    (inLoc outLoc : MiriLocState)
    (hIn : miriInitialInsideLoc newTag insidePerm true = .ok inLoc)
    (hOut : miriInitialOutsideLoc newTag outsidePerm true = .ok outLoc)
    (hFrame : miriCheckFrameOpt (some fid) st.frames = .ok ())
    (hDead : miriIsAllocLive allocId mem = false) :
    miriReborrowTag mem st (some fid) allocId newTag parentTag insidePerm
      outsidePerm off size =
      .err (miriRegisterProtectorOpt st (some fid) allocId newTag)
        (.deadOrMissingAlloc allocId) := by
  unfold miriReborrowTag
  dsimp only
  rw [hIn]
  dsimp only
  rw [hOut]
  dsimp only
  rw [hFrame]
  dsimp only
  rw [hDead]

/-- Universal duplicate-frame rejection (`[]`): `miriBeginFrame` leaves `st`
unchanged and fails with `.duplicateFrame` when `frameId` is registered. -/
theorem miriBeginFrame_rejects_duplicate (st : MiriTbState) (frameId : Nat)
    (frame : MiriFrameProtectors)
    (hDup : miriFindFrame? frameId st.frames = some frame) :
    miriBeginFrame st frameId = .err st (.duplicateFrame frameId) := by
  unfold miriBeginFrame
  rw [hDup]

/-- Uniform-freeze contract of `miriRegisterFnEntryArg` (`[]`): one inside
permission and one outside permission, both selected from the single
`frozen` bit, cover the whole reborrow. -/
theorem miriRegisterFnEntryArg_uniform_freeze (mem : MemoryState)
    (st : MiriTbState) (frameId : Nat) (allocId : AllocId)
    (newTag parentTag : Nat) (refKind : MiriRefKind)
    (frozen implicitWrites : Bool) (off size : Nat) :
    miriRegisterFnEntryArg mem st frameId allocId newTag parentTag refKind
      frozen implicitWrites off size =
      miriReborrowTag mem st (some frameId) allocId newTag parentTag
        (miriSelectRetagPerm refKind true frozen true implicitWrites)
        (miriSelectRetagPerm refKind false frozen true implicitWrites)
        off size :=
  rfl

/-- Universal dead-allocation skip in `miriExitCallFrame` (`[]`, matching
`MachineHooks.lean:427`): a frame holding a single protector on a deallocated
entry (`live = false` in `mem`) exits cleanly without invoking
`miriReleaseOneProtector`. -/
theorem miriExitCallFrame_skips_dead_alloc (mem : MemoryState)
    (st : MiriTbState) (frameId : Nat) (allocId : AllocId) (tag : Nat)
    (a : Allocation)
    (hFrame : miriFindFrame? frameId st.frames =
      some { frameId := frameId, protectedTags := [(allocId, tag)] })
    (hAlloc : execFindAllocation allocId mem.allocations = some a)
    (hDead : a.live = false) :
    miriExitCallFrame mem st frameId = .ok (miriEndCall st frameId) := by
  unfold miriExitCallFrame
  rw [hFrame]
  dsimp only [miriReleaseTagListForward, List.foldl]
  rw [hAlloc]
  dsimp only
  rw [hDead]
  rfl

/-- Universal failure propagation in `miriExitCallFrame` (`[]`): whenever
`miriReleaseTagListForward` fails, `miriExitCallFrame` returns that exact
failure without invoking `miriEndCall`. -/
theorem miriExitCallFrame_preserves_failure_without_endCall (mem : MemoryState)
    (st partialSt : MiriTbState) (frameId : Nat)
    (frame : MiriFrameProtectors) (err : MiriTbError)
    (hFrame : miriFindFrame? frameId st.frames = some frame)
    (hFail : miriReleaseTagListForward mem st frame.protectedTags =
      .err partialSt err) :
    miriExitCallFrame mem st frameId = .err partialSt err := by
  unfold miriExitCallFrame
  rw [hFrame]
  dsimp only
  rw [hFail]

end Anneal.MiriTreeBorrows

end
