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
public import Init.Control.Except
public import Trusted.MirAst

public section

/-!
# Miri Tree Borrows Permission Model (`Anneal.MiriTreeBorrows.Model`)

Computable, zero-axiom (`[]` on all authored declarations; Lean-generated
`*.injEq` lemmas use `propext`) Tree Borrows model aligned with
`vendor/lean-miri/Miri/TreeBorrows/` (`Permissions`, `LocationState`,
`Traversal`, `NormalTree`, `RangedNormalTree`, `RetagPolicy`):

- 6-constructor `MiriPerm` (`.cell`, `.reservedFrz Bool`, `.reservedIM`,
  `.unique`, `.frozen`, `.disabled` — 7 permission values), 3-arm
  `miriAssociatedAccess`, and full 56-cell
  `(MiriPerm × MiriAccessKind × MiriRelatedness × isProtected)` transition
  table.
- `MiriSifa` (`IdempotentForeignAccess`) cache tracking, `miriSkipIfKnownNoop`
  and `miriSkippedForeignNodes` subtree pruning (`.SkipSelfAndChildren`), and
  pre-error SIFA commit (`NormalTree.lean:77-93`).
- Ordered `LocalAccess`-before-`ForeignAccess` postorder traversal with
  `.visitChildrenOfAccessed` vs `.skipChildrenOfAccessed` and fail-closed
  missing-tag / uncovered-range checks.

Representation invariants assumed on `MiriAllocTree` and `MiriTbState` (matching
`vendor/lean-miri/Miri/TreeBorrows/{Traversal,RangedNormalTree}.lean`):
1. `tree` forms a finite acyclic rooted forest with unique node tags.
2. `segments` are sorted in ascending `offset` order as pairwise disjoint byte
   intervals with positive sizes.
3. Each segment's `entries` list has no duplicate tags, every entry tag occurs
   in `tree`, and frame IDs in `frames` are distinct.

Modeling boundaries: zero-size accesses (`size = 0`) succeed without segment
overlap or splitting once `allocId` and `accessedTag` exist (matching
`RangedNormalTree.lean:84-115`); malformed parent cycles terminate via
`tree.length` fuel. Only single-root trees are supported for accesses: Miri
follows the normal traversal with a wildcard traversal of every other root
(`TreeState.lean:920-963`), which is not modeled, so an access on a tree
with two or more `parent = none` nodes fails closed with `.multipleRoots`
once the normal traversal succeeds.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and compile with zero axioms (`[]`).
-/

namespace Anneal.MiriTreeBorrows

open Trusted.MirAst

/-- Fuel-bounded structural `Nat.rec` fold helper. -/
@[expose] def natFold {α : Type} (init : α) (step : Nat → α → α) : Nat → α :=
  @Nat.rec (fun _ => α) init (fun n acc => step n acc)

/-- Computable boolean membership check on `List Nat`. -/
@[expose] def miriNatListMem (x : Nat) (xs : List Nat) : Bool :=
  xs.foldl (fun acc y => acc || Nat.beq x y) false

/-- Miri 6-state Tree Borrows permission (`Permissions.lean:19-32`). -/
inductive MiriPerm where
  | cell
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | unique
  | frozen
  | disabled

/-- Miri `AccessKind` (`Permissions.lean:35-38`). -/
inductive MiriAccessKind where
  | read
  | write

/-- Miri `AccessRelatedness` (`Permissions.lean:40-45`). -/
inductive MiriRelatedness where
  | localAccess
  | foreignAccess

/-- Miri `IdempotentForeignAccess` (`Permissions.lean:165-169`). -/
inductive MiriSifa where
  | none
  | read
  | write

/-- Shared vs mutable reference kind for `RetagPolicy.selectedPermission`
(`RetagPolicy.lean:22-26`, omitting `Box`). -/
inductive MiriRefKind where
  | shared
  | mutable

/-- Miri `ChildrenVisitMode` (`Traversal.lean:17-20`). -/
inductive MiriVisitMode where
  | visitChildrenOfAccessed
  | skipChildrenOfAccessed

/-- Per-permission transition outcome (`Permissions.lean:56-60`). -/
inductive MiriPermOutcome where
  | transition (next : MiriPerm)
  | undefinedBehavior
  | impossibleProtectedReservedIM

/-- Tree Borrows transition, reborrow, frame, and coverage errors. -/
inductive MiriTbError where
  | childAccessForbidden (tag : Nat) (perm : MiriPerm)
  | protectedDisabled (tag : Nat) (perm : MiriPerm)
  | impossibleProtectedReservedIM (tag : Nat)
  | invalidLazyState (tag : Nat)
  | nonInitialPerm (tag : Nat) (perm : MiriPerm)
  | duplicateTag (tag : Nat)
  | missingFrame (frameId : Nat)
  | deadOrMissingAlloc (allocId : AllocId)
  | writeToReadOnly (allocId : AllocId)
  | missingTag (tag : Nat)
  | uncoveredRange (allocId : AllocId)
  | duplicateFrame (frameId : Nat)
  | multipleRoots (tag : Nat)

/-- State-retaining Tree Borrows outcome (`LocationState.lean:108-122`). -/
inductive MiriTbResult (α : Type) where
  | ok (val : α)
  | err (partialState : α) (error : MiriTbError)

/-- Returns `true` iff `p` is `.disabled`. -/
@[expose] def miriPermIsDisabled (p : MiriPerm) : Bool :=
  match p with
  | .cell => false
  | .reservedFrz _ => false
  | .reservedIM => false
  | .unique => false
  | .frozen => false
  | .disabled => true

/-- Returns `true` iff `p` is `.frozen`. -/
@[expose] def miriPermIsFrozen (p : MiriPerm) : Bool :=
  match p with
  | .cell => false
  | .reservedFrz _ => false
  | .reservedIM => false
  | .unique => false
  | .frozen => true
  | .disabled => false

/-- Returns `true` iff `p` is `.unique`. -/
@[expose] def miriPermIsUnique (p : MiriPerm) : Bool :=
  match p with
  | .cell => false
  | .reservedFrz _ => false
  | .reservedIM => false
  | .unique => true
  | .frozen => false
  | .disabled => false

/-- Returns `true` iff `p` is a valid initial permission
(`Permissions.lean:114-116`). -/
@[expose] def miriPermIsInitial (p : MiriPerm) : Bool :=
  match p with
  | .cell => true
  | .reservedFrz conflicted => !conflicted
  | .reservedIM => true
  | .unique => true
  | .frozen => true
  | .disabled => false

/-- Returns `true` iff `k` is `.read`. -/
@[expose] def miriKindIsRead (k : MiriAccessKind) : Bool :=
  match k with
  | .read => true
  | .write => false

/-- Returns `true` iff `r` is `.foreignAccess`. -/
@[expose] def miriRelIsForeign (r : MiriRelatedness) : Bool :=
  match r with
  | .localAccess => false
  | .foreignAccess => true

/-- Returns `true` iff `m` is `.visitChildrenOfAccessed`. -/
@[expose] def miriIsVisitChildren (m : MiriVisitMode) : Bool :=
  match m with
  | .visitChildrenOfAccessed => true
  | .skipChildrenOfAccessed => false

/-- Exact 3-arm Miri `Permission.associatedAccess` (`Permissions.lean:268-271`):
- `.cell => none`
- `.unique => some .write`
- `.reservedFrz _`, `.reservedIM`, `.frozen`, `.disabled => some .read`. -/
@[expose] def miriAssociatedAccess (perm : MiriPerm) : Option MiriAccessKind :=
  match perm with
  | .cell => none
  | .unique => some .write
  | .reservedFrz _ => some .read
  | .reservedIM => some .read
  | .frozen => some .read
  | .disabled => some .read

/-- Total order rank on `MiriSifa` (`.none < .read < .write`). -/
@[expose] def miriSifaRank (s : MiriSifa) : Nat :=
  match s with
  | .none => 0
  | .read => 1
  | .write => 2

/-- Maps a foreign `MiriAccessKind` to its `MiriSifa` level. -/
@[expose] def miriSifaFromForeign (k : MiriAccessKind) : MiriSifa :=
  match k with
  | .read => .read
  | .write => .write

/-- Returns `true` iff `happeningNow ≤ recorded` (`Permissions.lean:227-230`).
-/
@[expose] def miriSifaCanSkipForeign (recorded happeningNow : MiriSifa) :
    Bool :=
  Nat.ble (miriSifaRank happeningNow) (miriSifaRank recorded)

/-- Updates SIFA after an access (`Permissions.lean:231-233`). -/
@[expose] def miriSifaRecordNew (recorded : MiriSifa) (kind : MiriAccessKind)
    (rel : MiriRelatedness) : MiriSifa :=
  match rel with
  | .localAccess => .none
  | .foreignAccess =>
    let h := miriSifaFromForeign kind
    if Nat.ble (miriSifaRank recorded) (miriSifaRank h) then h else recorded

/-- Weakens `recorded` so it is no stronger than `strongestAllowed`
(`Permissions.lean:235-238`). -/
@[expose] def miriSifaEnsureNoStrongerThan (recorded strongestAllowed :
    MiriSifa) :
    MiriSifa :=
  if Nat.blt (miriSifaRank strongestAllowed) (miriSifaRank recorded) then
    strongestAllowed
  else
    recorded

/-- Exact Miri `Permission.strongestIdempotentForeignAccess`
(`Permissions.lean:299-309`), returning `none` for
`ImpossibleProtectedReservedIM`. -/
@[expose] def miriStrongestSifa (perm : MiriPerm) (isProtected : Bool) :
    Option MiriSifa :=
  match perm with
  | .cell => some .write
  | .reservedFrz conflicted =>
    match conflicted with
    | false => if isProtected then some .none else some .read
    | true => some .read
  | .reservedIM => if isProtected then none else some .write
  | .unique => some .none
  | .frozen => some .read
  | .disabled => some .write

/-- Miri `childRead` (`Permissions.lean:62-65`). -/
@[expose] def miriChildReadPerm (state : MiriPerm) : MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .reservedFrz c => .transition (.reservedFrz c)
  | .reservedIM => .transition .reservedIM
  | .unique => .transition .unique
  | .frozen => .transition .frozen
  | .disabled => .undefinedBehavior

/-- Miri `foreignRead` (`Permissions.lean:67-80`). -/
@[expose] def miriForeignReadPerm (state : MiriPerm) (isProtected : Bool) :
    MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .frozen => .transition .frozen
  | .disabled => .transition .disabled
  | .reservedFrz c =>
    if isProtected then .transition (.reservedFrz true)
    else .transition (.reservedFrz c)
  | .reservedIM =>
    if isProtected then .impossibleProtectedReservedIM
    else .transition .reservedIM
  | .unique =>
    if isProtected then .transition .disabled
    else .transition .frozen

/-- Miri `childWrite` (`Permissions.lean:82-91`). -/
@[expose] def miriChildWritePerm (state : MiriPerm) (isProtected : Bool) :
    MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .reservedFrz conflicted =>
    match conflicted with
    | true =>
      if isProtected then .undefinedBehavior
      else .transition .unique
    | false => .transition .unique
  | .reservedIM => .transition .unique
  | .unique => .transition .unique
  | .frozen => .undefinedBehavior
  | .disabled => .undefinedBehavior

/-- Miri `foreignWrite` (`Permissions.lean:93-100`). -/
@[expose] def miriForeignWritePerm (state : MiriPerm) (isProtected : Bool) :
    MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .reservedIM =>
    if isProtected then .impossibleProtectedReservedIM
    else .transition .reservedIM
  | .reservedFrz _ => .transition .disabled
  | .unique => .transition .disabled
  | .frozen => .transition .disabled
  | .disabled => .transition .disabled

/-- 4-way permission transition dispatch (`Permissions.lean:102-111`). -/
@[expose] def miriPerformPermAccess (kind : MiriAccessKind) (rel :
    MiriRelatedness)
    (old : MiriPerm) (isProtected : Bool) : MiriPermOutcome :=
  match kind with
  | .write =>
    match rel with
    | .foreignAccess => miriForeignWritePerm old isProtected
    | .localAccess => miriChildWritePerm old isProtected
  | .read =>
    match rel with
    | .foreignAccess => miriForeignReadPerm old isProtected
    | .localAccess => miriChildReadPerm old

/-- Per-node state at one allocation byte range (`LocationState.lean:36-40`).
-/
structure MiriLocState where
  perm : MiriPerm
  accessed : Bool
  sifa : MiriSifa

/-- `LocationState.newNonAccessed` (`LocationState.lean:53-58`): rejects
non-initial/non-disabled permissions and lazy `.unique`. -/
@[expose] def miriNewNonAccessed (tag : Nat) (perm : MiriPerm)
    (sifa : MiriSifa) : Except MiriTbError MiriLocState :=
  if miriPermIsInitial perm || miriPermIsDisabled perm then
    if miriPermIsUnique perm then .error (.invalidLazyState tag)
    else .ok ⟨perm, false, sifa⟩
  else
    .error (.invalidLazyState tag)

/-- `LocationState.newAccessed` (`LocationState.lean:61-62`). -/
@[expose] def miriNewAccessed (perm : MiriPerm) (sifa : MiriSifa) :
    MiriLocState :=
  ⟨perm, true, sifa⟩

/-- Exact `RetagPolicy.selectedPermission` (`RetagPolicy.lean:52-59`). -/
@[expose] def miriSelectRetagPerm (kind : MiriRefKind)
    (isInsideRange frozen isProtected implicitWrites : Bool) : MiriPerm :=
  match kind with
  | .shared => if frozen then .frozen else .cell
  | .mutable =>
    if implicitWrites && isInsideRange then .unique
    else if isProtected || frozen then .reservedFrz false
    else .reservedIM

/-- Inside-range initial location state (`RetagPolicy.lean:104-118`,
`TreeState.lean:719-728`): rejects non-initial permissions (`.nonInitialPerm`)
and protected `.reservedIM` (`.impossibleProtectedReservedIM`), initializes
non-`Cell` (`miriAssociatedAccess = some _`) with `accessed = true`, and
initializes `Cell` (`miriAssociatedAccess = none`) with `accessed = false`. -/
@[expose] def miriInitialInsideLoc (tag : Nat) (perm : MiriPerm) (isProtected :
    Bool) :
    Except MiriTbError MiriLocState :=
  match miriPermIsInitial perm with
  | false => .error (.nonInitialPerm tag perm)
  | true =>
    match miriStrongestSifa perm isProtected with
    | none => .error (.impossibleProtectedReservedIM tag)
    | some sifa =>
      match miriAssociatedAccess perm with
      | some _ => .ok (miriNewAccessed perm sifa)
      | none => miriNewNonAccessed tag perm sifa

/-- Outside-range initial location state (`TreeState.lean:691-699`,
`accessed = false`): rejects non-initial permissions (`.nonInitialPerm`),
protected `.reservedIM` (`.impossibleProtectedReservedIM`), and lazy `.unique`
(`.invalidLazyState`). -/
@[expose] def miriInitialOutsideLoc (tag : Nat) (outsidePerm : MiriPerm)
    (isProtected : Bool) : Except MiriTbError MiriLocState :=
  match miriPermIsInitial outsidePerm with
  | false => .error (.nonInitialPerm tag outsidePerm)
  | true =>
    match miriStrongestSifa outsidePerm isProtected with
    | none => .error (.impossibleProtectedReservedIM tag)
    | some sifa => miriNewNonAccessed tag outsidePerm sifa

/-- `LocationState.skipIfKnownNoop` (`LocationState.lean:76-88`). -/
@[expose] def miriSkipIfKnownNoop (st : MiriLocState) (kind : MiriAccessKind)
    (rel : MiriRelatedness) : Bool :=
  if miriRelIsForeign rel then
    miriSifaCanSkipForeign st.sifa (miriSifaFromForeign kind) ||
      miriPermIsDisabled st.perm ||
      (miriPermIsFrozen st.perm && miriKindIsRead kind)
  else
    false

/-- `LocationState.performAccess` (`LocationState.lean:128-149`) preceded by
`recordNewAccess` (`NormalTree.lean:77-93`): commits `recordedState` (with
updated `sifa`) even on `.childAccessForbidden`, and checks
`isProtected && nextAccessed && miriPermIsDisabled nextPerm` before committing
`nextState` on `.protectedDisabled`. -/
@[expose] def miriPerformLocAccess (tag : Nat) (st : MiriLocState)
    (kind : MiriAccessKind) (rel : MiriRelatedness) (isProtected : Bool) :
    MiriTbResult MiriLocState :=
  let recordedSifa := miriSifaRecordNew st.sifa kind rel
  let recordedState : MiriLocState := ⟨st.perm, st.accessed, recordedSifa⟩
  match miriPerformPermAccess kind rel recordedState.perm isProtected with
  | .undefinedBehavior =>
    .err recordedState (.childAccessForbidden tag recordedState.perm)
  | .impossibleProtectedReservedIM =>
    .err recordedState (.impossibleProtectedReservedIM tag)
  | .transition nextPerm =>
    let nextAccessed := recordedState.accessed || !miriRelIsForeign rel
    let nextState : MiriLocState := ⟨nextPerm, nextAccessed, recordedState.sifa⟩
    if isProtected && nextAccessed && miriPermIsDisabled nextPerm then
      .err nextState (.protectedDisabled tag recordedState.perm)
    else
      .ok nextState

/-- Ordered tree topology node (`Traversal.lean:23-26`). -/
structure MiriTopoNode where
  tag : Nat
  parent : Option Nat
  children : List Nat

/-- Tag-to-location-state entry inside a byte segment. -/
structure MiriTagEntry where
  tag : Nat
  loc : MiriLocState

/-- Uniform byte-range segment `[offset, offset + size)` across all tags. -/
structure MiriSegment where
  offset : Nat
  size : Nat
  entries : List MiriTagEntry

/-- Scheduled traversal event `(tag, relatedness)`. -/
structure MiriTraversalEvent where
  tag : Nat
  rel : MiriRelatedness

/-- Call-frame protector registration list in forward registration order. -/
structure MiriFrameProtectors where
  frameId : Nat
  protectedTags : List (AllocId × Nat)

/-- Per-allocation borrow tree (`tree` topology + disjoint positive-size
`segments`). -/
structure MiriAllocTree where
  allocId : AllocId
  tree : List MiriTopoNode
  segments : List MiriSegment

/-- Whole-machine Tree Borrows state (`frames` + per-allocation trees). -/
structure MiriTbState where
  frames : List MiriFrameProtectors
  allocTrees : List MiriAllocTree

/-- Looks up a topology node by `tag`. -/
@[expose] def miriFindTopoNode? (tag : Nat) (tree : List MiriTopoNode) :
    Option MiriTopoNode :=
  tree.foldl (fun acc n => if Nat.beq n.tag tag then some n else acc) none

/-- Returns the ordered child tags of `tag` in `tree`. -/
@[expose] def miriChildrenOfTag (tag : Nat) (tree : List MiriTopoNode) : List
    Nat :=
  match miriFindTopoNode? tag tree with
  | none => []
  | some n => n.children

/-- Appends `newTag` as a child of `parentTag` in `tree`. -/
@[expose] def miriInsertChildTopo (tree : List MiriTopoNode) (parentTag newTag :
    Nat) :
    List MiriTopoNode :=
  let updated :=
    tree.map (fun n =>
      if Nat.beq n.tag parentTag then
        { tag := n.tag, parent := n.parent, children := n.children ++ [newTag] }
      else
        n)
  updated ++ [{ tag := newTag, parent := some parentTag, children := [] }]

/-- `TraversalTree.ancestorPath` (`Traversal.lean:45-52`):
`[startTag, parent, ..., root]`. -/
@[expose] def miriAncestorPath (tree : List MiriTopoNode) (startTag : Nat) :
    List Nat :=
  let pair :=
    natFold ([], some startTag)
      (fun _ acc =>
        match acc.2 with
        | none => acc
        | some cur =>
          match miriFindTopoNode? cur tree with
          | none => (cur :: acc.1, none)
          | some n => (cur :: acc.1, n.parent))
      tree.length
  let fullRev :=
    match pair.2 with
    | none => pair.1
    | some rem => rem :: pair.1
  fullRev.reverse

/-- Filters out an optional tag `skip?` from `xs`, preserving list order. -/
@[expose] def filterOutOpt (skip? : Option Nat) (xs : List Nat) : List Nat :=
  xs.foldl
    (fun acc x =>
      match skip? with
      | none => acc ++ [x]
      | some s => if Nat.beq x s then acc else acc ++ [x])
    []

/-- `TraversalTree.initialForeignRoots` (`Traversal.lean:70-85`). -/
@[expose] def miriInitialForeignRoots (tree : List MiriTopoNode) (path : List
    Nat)
    (mode : MiriVisitMode) : List Nat :=
  let triple :=
    path.foldl
      (fun (st : List Nat × Option Nat × Bool) current =>
        let accRoots := st.1
        let prevOpt := st.2.1
        let isStart := st.2.2
        let shouldVisitChildren := (!isStart) || miriIsVisitChildren mode
        let siblings :=
          if shouldVisitChildren then
            filterOutOpt prevOpt (miriChildrenOfTag current tree).reverse
          else
            []
        (accRoots ++ siblings, some current, false))
      ([], none, true)
  triple.1

/-- `NormalTreeState.skippedForeignNodes` (`NormalTree.lean:62-69`). -/
@[expose] def miriSkippedForeignNodes (seg : MiriSegment) (kind :
    MiriAccessKind) :
    List Nat :=
  seg.entries.foldl
    (fun acc e =>
      if miriSkipIfKnownNoop e.loc kind .foreignAccess then
        acc ++ [e.tag]
      else
        acc)
    []

/-- `TraversalTree.foreignPostorder` (`Traversal.lean:89-98`): bottom-up
foreign subtree schedule pruning any node in `skipNodes` and all descendants.
-/
@[expose] def miriForeignPostorder (tree : List MiriTopoNode) (skipNodes : List
    Nat)
    (rootTag : Nat) : List MiriTraversalEvent :=
  let stepFn :=
    natFold (fun (_ : Nat) => ([] : List MiriTraversalEvent))
      (fun _ recFn idx =>
        if miriNatListMem idx skipNodes then
          []
        else
          let chRev := (miriChildrenOfTag idx tree).reverse
          let chEvents := chRev.foldl (fun acc c => acc ++ recFn c) []
          chEvents ++ [{ tag := idx, rel := .foreignAccess }])
      tree.length
  stepFn rootTag

/-- `TraversalTree.traverse` (`Traversal.lean:102-111`):
`localEvents ++ foreignEvents`. -/
@[expose] def miriTraverseSegmentEvents (tree : List MiriTopoNode) (seg :
    MiriSegment)
    (startTag : Nat) (kind : MiriAccessKind) (mode : MiriVisitMode) :
    List MiriTraversalEvent :=
  let path := miriAncestorPath tree startTag
  let localEvents := path.map (fun idx => { tag := idx, rel := .localAccess })
  let skipped := miriSkippedForeignNodes seg kind
  let fRoots := miriInitialForeignRoots tree path mode
  let foreignEvents :=
    fRoots.foldl (fun acc r => acc ++ miriForeignPostorder tree skipped r) []
  localEvents ++ foreignEvents

/-- Looks up a tag entry in a segment. -/
@[expose] def miriFindTagEntry? (tag : Nat) (entries : List MiriTagEntry) :
    Option MiriTagEntry :=
  entries.foldl (fun acc e => if Nat.beq e.tag tag then some e else acc) none

/-- Updates or appends `entry` in `entries`. -/
@[expose] def miriUpsertTagEntry (entry : MiriTagEntry) (entries : List
    MiriTagEntry) :
    List MiriTagEntry :=
  let res :=
    entries.foldl
      (fun (acc : Bool × List MiriTagEntry) e =>
        if Nat.beq e.tag entry.tag then
          (true, acc.2 ++ [entry])
        else
          (acc.1, acc.2 ++ [e]))
      (false, [])
  if res.1 then res.2 else res.2 ++ [entry]

/-- Collects all protected tags registered on `allocId` across active `frames`.
-/
@[expose] def miriProtectedTagsOnAlloc (allocId : AllocId)
    (frames : List MiriFrameProtectors) : List Nat :=
  frames.foldl
    (fun acc f =>
      f.protectedTags.foldl
        (fun acc2 p => if Nat.beq p.1 allocId then acc2 ++ [p.2] else acc2)
        acc)
    []

/-- `NormalTreeState.processEvents` (`NormalTree.lean:70-103`): steps events in
forward order, halting on the first error while retaining committed mutations,
and fails closed with `.missingTag` if any visited tag is absent from `seg`. -/
@[expose] def miriProcessSegmentEvents (protectedOnAlloc : List Nat)
    (kind : MiriAccessKind) (seg : MiriSegment)
    (events : List MiriTraversalEvent) : MiriTbResult MiriSegment :=
  events.foldl
    (fun acc ev =>
      match acc with
      | .err partialSeg err => .err partialSeg err
      | .ok curSeg =>
        match miriFindTagEntry? ev.tag curSeg.entries with
        | none => .err curSeg (.missingTag ev.tag)
        | some e =>
          let isProt := miriNatListMem ev.tag protectedOnAlloc
          match miriPerformLocAccess ev.tag e.loc kind ev.rel isProt with
          | .ok nextLoc =>
            .ok { offset := curSeg.offset
                  size := curSeg.size
                  entries :=
                    miriUpsertTagEntry { tag := ev.tag, loc := nextLoc }
                      curSeg.entries }
          | .err nextLoc err =>
            let updatedSeg : MiriSegment :=
              { offset := curSeg.offset
                size := curSeg.size
                entries :=
                  miriUpsertTagEntry { tag := ev.tag, loc := nextLoc }
                    curSeg.entries }
            .err updatedSeg err)
    (.ok seg)

/-- Returns `true` iff `tree` has two or more roots (`parent = none`). -/
@[expose] def miriTreeHasMultipleRoots (tree : List MiriTopoNode) : Bool :=
  let rootCount :=
    tree.foldl
      (fun acc n =>
        match n.parent with
        | none => acc + 1
        | some _ => acc)
      0
  Nat.blt 1 rootCount

/-- Performs a single-segment Tree Borrows access: validates `accessedTag` in
both `tree` and `seg.entries`, steps `accessedTag` locally first
(short-circuiting before any ancestor or foreign event), then steps remaining
`localEvents` and pruned `foreignEvents`.

The normal traversal covers only the component containing `accessedTag`.
Miri then visits every other root with a wildcard traversal
(`TreeState.lean:920-963`). That step is not modeled, so on a multi-root
`tree` a successful normal traversal fails closed with `.multipleRoots`,
keeping the normal traversal's updates as the partial state. -/
@[expose] def miriPerformSegmentAccess (tree : List MiriTopoNode)
    (protectedOnAlloc : List Nat) (accessedTag : Nat) (kind : MiriAccessKind)
    (mode : MiriVisitMode) (seg : MiriSegment) : MiriTbResult MiriSegment :=
  match miriFindTopoNode? accessedTag tree with
  | none => .err seg (.missingTag accessedTag)
  | some _ =>
    match miriFindTagEntry? accessedTag seg.entries with
    | none => .err seg (.missingTag accessedTag)
    | some selfEntry =>
      let isSelfProt := miriNatListMem accessedTag protectedOnAlloc
      match miriPerformLocAccess accessedTag selfEntry.loc kind .localAccess
          isSelfProt with
      | .err nextSelfLoc err =>
        .err
          { offset := seg.offset
            size := seg.size
            entries :=
              miriUpsertTagEntry { tag := accessedTag, loc := nextSelfLoc }
                seg.entries }
          err
      | .ok nextSelfLoc =>
        let segAfterSelf : MiriSegment :=
          { offset := seg.offset
            size := seg.size
            entries :=
              miriUpsertTagEntry { tag := accessedTag, loc := nextSelfLoc }
                seg.entries }
        let allEvents :=
          miriTraverseSegmentEvents tree seg accessedTag kind mode
        let tailEvents := allEvents.drop 1
        match miriProcessSegmentEvents protectedOnAlloc kind segAfterSelf
            tailEvents with
        | .err partialSeg err => .err partialSeg err
        | .ok segNormal =>
          if miriTreeHasMultipleRoots tree then
            .err segNormal (.multipleRoots accessedTag)
          else
            .ok segNormal

/-- Splits a single segment along `[cutStart, cutEnd)` (returning `[seg]`
untouched when `cutEnd ≤ cutStart`; under positive-size invariant 2, splits
overlapping segments into non-empty sub-segments). -/
@[expose] def miriSplitOneSegment (cutStart cutEnd : Nat) (seg : MiriSegment) :
    List MiriSegment :=
  let a := seg.offset
  let b := seg.offset + seg.size
  if Nat.ble cutEnd cutStart || Nat.ble b cutStart || Nat.ble cutEnd a then
    [seg]
  else
    let midStart := if Nat.ble a cutStart then cutStart else a
    let midEnd := if Nat.ble cutEnd b then cutEnd else b
    let pref :=
      if Nat.blt a midStart then
        [{ offset := a, size := midStart - a, entries := seg.entries }]
      else []
    let mid :=
      if Nat.blt midStart midEnd then
        [{ offset := midStart, size := midEnd - midStart,
           entries := seg.entries }]
      else []
    let suff :=
      if Nat.blt midEnd b then
        [{ offset := midEnd, size := b - midEnd, entries := seg.entries }]
      else []
    pref ++ mid ++ suff

/-- Forward byte-range segment splitter preserving segment order. -/
@[expose] def miriSplitSegmentsAt (off size : Nat) (segs : List MiriSegment) :
    List MiriSegment :=
  segs.foldl (fun acc seg => acc ++ miriSplitOneSegment off (off + size) seg) []

/-- Returns `true` iff `seg` overlaps `[off, off + size)` (`false` when either
interval has zero byte size). -/
@[expose] def miriSegmentOverlaps (off size : Nat) (seg : MiriSegment) :
    Bool :=
  Nat.blt 0 size && Nat.blt 0 seg.size &&
    Nat.blt seg.offset (off + size) && Nat.blt off (seg.offset + seg.size)

/-- Returns `true` iff `[off, off + size)` is contiguously tiled by `segs`
after splitting along `[off, off + size)` (`true` when `size = 0`). -/
@[expose] def miriRangeIsCovered (off size : Nat) (segs : List MiriSegment) :
    Bool :=
  let splitSegs := miriSplitSegmentsAt off size segs
  let res :=
    splitSegs.foldl
      (fun (acc : Nat × Bool) seg =>
        if !acc.2 then
          acc
        else if miriSegmentOverlaps off size seg then
          if Nat.beq seg.offset (off + acc.1) then
            (acc.1 + seg.size, true)
          else
            (acc.1, false)
        else
          acc)
      (0, true)
  res.2 && Nat.beq res.1 size

/-- Looks up an allocation's borrow tree by `allocId`. -/
@[expose] def miriFindAllocTree? (allocId : AllocId) (trees : List
    MiriAllocTree) :
    Option MiriAllocTree :=
  trees.foldl
    (fun acc t => if Nat.beq t.allocId allocId then some t else acc) none

/-- Replaces an allocation's borrow tree in `trees`. -/
@[expose] def miriReplaceAllocTree (t' : MiriAllocTree) (trees : List
    MiriAllocTree) :
    List MiriAllocTree :=
  trees.map (fun t => if Nat.beq t.allocId t'.allocId then t' else t)

/-- Forward ranged Tree Borrows access over `[off, off + size)`
(`RangedNormalTree.lean:84-115`): fails closed on missing allocation tree,
missing `accessedTag`, or uncovered range gaps (`coveredLen ≠ size`). -/
@[expose] def miriPerformRangedAccess (st : MiriTbState) (allocId : AllocId)
    (accessedTag : Nat) (off size : Nat) (kind : MiriAccessKind)
    (mode : MiriVisitMode) : MiriTbResult MiriTbState :=
  match miriFindAllocTree? allocId st.allocTrees with
  | none => .err st (.uncoveredRange allocId)
  | some atree =>
    match miriFindTopoNode? accessedTag atree.tree with
    | none => .err st (.missingTag accessedTag)
    | some _ =>
      let prot := miriProtectedTagsOnAlloc allocId st.frames
      let splitSegs := miriSplitSegmentsAt off size atree.segments
      let foldRes :=
        splitSegs.foldl
          (fun (acc : List MiriSegment × Nat × Option MiriTbError) seg =>
            match acc.2.2 with
            | some err => (acc.1 ++ [seg], acc.2.1, some err)
            | none =>
              if miriSegmentOverlaps off size seg then
                match Nat.beq seg.offset (off + acc.2.1) with
                | false =>
                  (acc.1 ++ [seg], acc.2.1, some (.uncoveredRange allocId))
                | true =>
                  match miriPerformSegmentAccess atree.tree prot accessedTag
                      kind mode seg with
                  | .ok seg' =>
                    (acc.1 ++ [seg'], acc.2.1 + seg.size, none)
                  | .err partialSeg err =>
                    (acc.1 ++ [partialSeg], acc.2.1, some err)
              else
                (acc.1 ++ [seg], acc.2.1, none))
          ([], 0, none)
      let st' : MiriTbState :=
        { frames := st.frames
          allocTrees :=
            miriReplaceAllocTree
              { allocId := allocId, tree := atree.tree, segments := foldRes.1 }
              st.allocTrees }
      match foldRes.2.2 with
      | some err => .err st' err
      | none =>
        if Nat.beq foldRes.2.1 size then
          .ok st'
        else
          .err st' (.uncoveredRange allocId)

/-- Universal `.cell` invariance (`[]`): `.cell` remains `.cell` on every
`(kind, rel, isProtected)` transition. -/
theorem miriCell_all_accesses_preserve_cell (kind : MiriAccessKind)
    (rel : MiriRelatedness) (isProtected : Bool) :
    miriPerformPermAccess kind rel .cell isProtected = .transition .cell := by
  cases kind <;> cases rel <;> rfl

/-- Universal pre-error SIFA commit on a forbidden local `.write` access to
`.frozen` (`[]`, matching `NormalTree.lean:77-93`). -/
theorem miriPerformLocAccess_local_forbidden_resets_sifa (tag : Nat)
    (acc : Bool) (sifa : MiriSifa) (isProt : Bool) :
    miriPerformLocAccess tag ⟨.frozen, acc, sifa⟩ .write .localAccess isProt =
      .err ⟨.frozen, acc, .none⟩ (.childAccessForbidden tag .frozen) :=
  rfl

/-- Universal rejection of lazy `.unique` outside-range location states (`[]`,
matching `TreeState.lean:693-694`). -/
theorem miriInitialOutsideLoc_rejects_lazy_unique (tag : Nat)
    (isProtected : Bool) :
    miriInitialOutsideLoc tag .unique isProtected =
      .error (.invalidLazyState tag) := by
  cases isProtected <;> rfl

/-- Universal local-before-foreign short-circuiting (`[]`): when the accessed
tag itself fails locally, `miriPerformSegmentAccess` halts with that local error
without modifying any other tag's entry. -/
theorem miriPerformSegmentAccess_local_short_circuits_before_foreign
    (tree : List MiriTopoNode) (prot : List Nat) (tag : Nat)
    (kind : MiriAccessKind) (mode : MiriVisitMode) (seg : MiriSegment)
    (nd : MiriTopoNode) (selfEntry : MiriTagEntry) (nextLoc : MiriLocState)
    (err : MiriTbError)
    (hTopo : miriFindTopoNode? tag tree = some nd)
    (hSelf : miriFindTagEntry? tag seg.entries = some selfEntry)
    (hFail : miriPerformLocAccess tag selfEntry.loc kind .localAccess
      (miriNatListMem tag prot) = .err nextLoc err) :
    miriPerformSegmentAccess tree prot tag kind mode seg =
      .err
        { offset := seg.offset
          size := seg.size
          entries :=
            miriUpsertTagEntry { tag := tag, loc := nextLoc } seg.entries }
        err := by
  unfold miriPerformSegmentAccess
  rw [hTopo, hSelf]
  dsimp only
  rw [hFail]

end Anneal.MiriTreeBorrows

end
