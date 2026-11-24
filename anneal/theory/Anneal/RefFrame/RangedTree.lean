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
public import Anneal.ByteSubLens.Lens

public section

namespace Anneal.RefFrame

open Anneal.ByteSubLens

/-!
# Ranged Tree Borrows Frame Protectors & Commutation (`RangedTree`)

Provides an LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`, `0`
`omega`) ranged Tree Borrows access and frame-exit protector model (all
authored declarations compile with zero axioms `[]`; Lean-synthesized `.injEq`
helpers use `propext`):

1. **3-arm `TbPermission.associatedAccess` & `TbLocationState.performAccess`:**
   Matches Miri's 6-state permission tables and `.Cell => none`,
   `.Unique => some .Write`, and `.ReservedFrz _ | .ReservedIM | .Frozen |
   .Disabled => some .Read`, with `.ProtectedDisabled` raised iff
   `isProtected && nextState.accessed && nextPermission.isDisabled`.
2. **Local-first short-circuiting traversal & fail-closed coverage
   (`performSegmentAccess`, `performRangedAccess`):** Visits `actorTag` and its
   ancestors (`LocalAccess`) before foreign nodes (`ForeignAccess`), stopping
   immediately on the first `.Error` or `.InvariantFailure` without mutating
   unvisited nodes or overwriting earlier failures. Positive-length accesses
   require `segments` to contiguously tile `[off, off + len)` (`seg.offset =
   off + covered`, total length `len`), every topology and local-chain tag to
   appear in each touched segment, and `actorTag` to exist in `topology`
   (otherwise failing closed with `.UncoveredOrMissingTag`); zero-length
   accesses on a known tag return `.Completed`. Miri's SIFA/`skipIfKnownNoop`
   foreign-skip optimization is intentionally omitted (verdict-equivalent on
   states reachable in UB-free Miri executions, such as avoiding protected
   accessed `.Disabled` nodes). Well-formed trees carry ascending
   pairwise-disjoint positive-size segments, an acyclic rooted topology, and
   duplicate-free `nodeStates` keys.
3. **Protector-kept-during-access frame exit (`releaseProtectorKeepProtected`,
   `endCallRemoveProtectors`, `exitFrameWithProtectors`):** Keeps all co-frame
   `protectedTags` active while executing implicit exit accesses (failing closed
   with `.MissingTag` on unprotected frame tags, empty trees, or segments
   omitting a topology tag) and strips `frameTags` strictly afterward.
4. **Universal shared 3-node `topo3` disjoint commutation
   (`shared_topo3_ranged_commutation_universal`, `[]` zero axioms):** Proves
   disjoint sibling reads and protected writes on a single shared 3-node
   `RangedBorrowTree` commute to the identical tree state.
-/

/-- Structural `@Nat.rec` eliminator (`0` `noncomputable`, `0` `._unsafe_rec`).
-/
@[expose] def natFold {α : Type} (zero : α) (succ : Nat → α → α) (n : Nat) : α
    :=
  @Nat.rec (fun _ => α) zero succ n

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

/-- Tree Borrows per-location permission states (`Cell`, `ReservedFrz`,
`ReservedIM`, `Unique`, `Frozen`, `Disabled`). -/
inductive TbPermission where
  | Cell
  | ReservedFrz (conflicted : Bool)
  | ReservedIM
  | Unique
  | Frozen
  | Disabled

/-- Memory access kind (`Read` or `Write`). -/
inductive TbAccessKind where
  | Read
  | Write

/-- Whether an access originates from the node/descendant (`LocalAccess`) or a
foreign cousin/ancestor (`ForeignAccess`). -/
inductive TbAccessRelatedness where
  | LocalAccess
  | ForeignAccess

/-- Returns `true` on `.ForeignAccess`. -/
@[expose] def TbAccessRelatedness.isForeign (r : TbAccessRelatedness) : Bool :=
  match r with
  | .LocalAccess => false
  | .ForeignAccess => true

/-- Returns `true` iff `p` is `.Disabled`. -/
@[expose] def TbPermission.isDisabled (p : TbPermission) : Bool :=
  match p with
  | .Disabled => true
  | .Cell | .ReservedFrz _ | .ReservedIM | .Unique | .Frozen => false

/-- 3-arm implicit protector-release access table:
- `.Cell => none` (interior-mutable `UnsafeCell`/`Cell` emits no exit access),
- `.Unique => some .Write`,
- `.ReservedFrz _ | .ReservedIM | .Frozen | .Disabled => some .Read`. -/
@[expose] def TbPermission.associatedAccess (p : TbPermission) : Option
    TbAccessKind :=
  match p with
  | .Cell => none
  | .Unique => some .Write
  | .ReservedFrz _ => some .Read
  | .ReservedIM => some .Read
  | .Frozen => some .Read
  | .Disabled => some .Read

/-- Single-permission transition outcome. -/
inductive TbAccessOutcome where
  | Transition (permission : TbPermission)
  | UndefinedBehavior
  | ImpossibleProtectedReservedIM

/-- Local/child read permission transition. -/
@[expose] def childReadPerm (old : TbPermission) : TbAccessOutcome :=
  match old with
  | .Disabled => .UndefinedBehavior
  | .Cell => .Transition .Cell
  | .ReservedFrz c => .Transition (.ReservedFrz c)
  | .ReservedIM => .Transition .ReservedIM
  | .Unique => .Transition .Unique
  | .Frozen => .Transition .Frozen

/-- Foreign read permission transition. -/
@[expose] def foreignReadPerm (old : TbPermission) (isProtected : Bool) :
    TbAccessOutcome :=
  match old with
  | .Cell => .Transition .Cell
  | .Frozen => .Transition .Frozen
  | .Disabled => .Transition .Disabled
  | .ReservedFrz c =>
    if isProtected then .Transition (.ReservedFrz true)
    else .Transition (.ReservedFrz c)
  | .ReservedIM =>
    if isProtected then .ImpossibleProtectedReservedIM
    else .Transition .ReservedIM
  | .Unique =>
    if isProtected then .Transition .Disabled
    else .Transition .Frozen

/-- Local/child write permission transition. -/
@[expose] def childWritePerm (old : TbPermission) (isProtected : Bool) :
    TbAccessOutcome :=
  match old with
  | .Cell => .Transition .Cell
  | .ReservedFrz true =>
    if isProtected then .UndefinedBehavior else .Transition .Unique
  | .ReservedFrz false => .Transition .Unique
  | .ReservedIM => .Transition .Unique
  | .Unique => .Transition .Unique
  | .Frozen => .UndefinedBehavior
  | .Disabled => .UndefinedBehavior

/-- Foreign write permission transition. -/
@[expose] def foreignWritePerm (old : TbPermission) (isProtected : Bool) :
    TbAccessOutcome :=
  match old with
  | .Cell => .Transition .Cell
  | .ReservedIM =>
    if isProtected then .ImpossibleProtectedReservedIM
    else .Transition .ReservedIM
  | .ReservedFrz _ | .Unique | .Frozen | .Disabled => .Transition .Disabled

/-- 4-way `(TbAccessKind × TbAccessRelatedness)` permission transition. -/
@[expose] def performPermAccess (kind : TbAccessKind) (rel :
    TbAccessRelatedness)
    (old : TbPermission) (isProtected : Bool) : TbAccessOutcome :=
  match kind, rel.isForeign with
  | .Write, true => foreignWritePerm old isProtected
  | .Read, true => foreignReadPerm old isProtected
  | .Write, false => childWritePerm old isProtected
  | .Read, false => childReadPerm old

/-- Per-location Tree Borrows node state `(permission, accessed)`. -/
structure TbLocationState where
  permission : TbPermission
  accessed : Bool

/-- Tree Borrows transition error classification. -/
inductive TbTransitionError where
  | ChildAccessForbidden (permission : TbPermission)
  | ProtectedDisabled (permission : TbPermission)
  | ProtectedDealloc

/-- Result of updating one `TbLocationState`. -/
inductive TbLocAccessResult where
  | Success (state : TbLocationState)
  | Error (state : TbLocationState) (err : TbTransitionError)
  | InvariantFailure (state : TbLocationState)

/-- Updates `(permission, accessed)` and reports `.ProtectedDisabled` iff
`isProtected && nextState.accessed && nextPermission.isDisabled`. -/
@[expose] def TbLocationState.performAccess (state : TbLocationState)
    (kind : TbAccessKind) (rel : TbAccessRelatedness) (isProtected : Bool) :
    TbLocAccessResult :=
  match performPermAccess kind rel state.permission isProtected with
  | .UndefinedBehavior =>
    .Error state (.ChildAccessForbidden state.permission)
  | .ImpossibleProtectedReservedIM => .InvariantFailure state
  | .Transition nextPermission =>
    let nextState : TbLocationState :=
      { permission := nextPermission
        accessed := state.accessed || !rel.isForeign }
    if isProtected && nextState.accessed && nextPermission.isDisabled then
      .Error nextState (.ProtectedDisabled state.permission)
    else
      .Success nextState

/-- Whether strict descendants of the actor are skipped during traversal. -/
inductive TbChildrenVisitMode where
  | SkipChildrenOfAccessed
  | VisitChildrenOfAccessed

/-- Borrow-tree topology node `(tag, parentTag)`. -/
structure TbTopoNode where
  tag : Nat
  parentTag : Option Nat

/-- Shared 3-node topology: root `0` with sibling children `1` (`src`) and `2`
(`dst`). -/
@[expose] def topo3 : List TbTopoNode :=
  [⟨0, none⟩, ⟨1, some 0⟩, ⟨2, some 0⟩]

/-- Looks up `tag` in `topo` via `List.foldr`. -/
@[expose] def findTopoNode (tag : Nat) (topo : List TbTopoNode) : Option
    TbTopoNode :=
  topo.foldr (fun nd acc => if Nat.beq nd.tag tag then some nd else acc) none

/-- Computable bounded ancestor walk (`0` `noncomputable`, `0` `._unsafe_rec`):
returns `true` iff `ancTag == curTag` or `ancTag` is reached within `fuel`
`parentTag` steps from `curTag`. -/
@[expose] def tbIsAncestorOrSelf (topo : List TbTopoNode) (fuel ancTag curTag :
    Nat) :
    Bool :=
  (natFold
    (fun cur => Nat.beq cur ancTag)
    (fun _ ih cur =>
      if Nat.beq cur ancTag then true
      else
        match findTopoNode cur topo with
        | none => false
        | some nd =>
          match nd.parentTag with
          | none => false
          | some pTag => ih pTag)
    fuel) curTag

/-- Computable `Nat` list membership test. -/
@[expose] def natListMem (x : Nat) (xs : List Nat) : Bool :=
  xs.foldr (fun y acc => Nat.beq x y || acc) false

/-- Contiguous byte-range segment `[offset, offset + length)` carrying per-tag
`TbLocationState`s. -/
structure RangeSegment where
  offset : Nat
  length : Nat
  nodeStates : List (Nat × TbLocationState)

/-- Ranged Tree Borrows state `(topology, protectedTags, segments)`. Well-formed
trees carry ascending pairwise-disjoint positive-size segments, an acyclic
rooted topology, and duplicate-free `nodeStates` entries. -/
structure RangedBorrowTree where
  topology : List TbTopoNode
  protectedTags : List Nat
  segments : List RangeSegment

/-- Looks up `tag`'s `TbLocationState` inside a segment's `nodeStates`. -/
@[expose] def lookupLocState (tag : Nat) (states : List (Nat × TbLocationState))
    :
    Option TbLocationState :=
  states.foldr
    (fun entry acc => if Nat.beq entry.1 tag then some entry.2 else acc)
    none

/-- Checks that every tag in `topo` has an entry in `states`. -/
@[expose] def segCoversTopology (topo : List TbTopoNode)
    (states : List (Nat × TbLocationState)) : Bool :=
  topo.foldr
    (fun nd acc =>
      match lookupLocState nd.tag states with
      | some _ => acc
      | none => false)
    true

/-- Outcome of applying an access across one `RangeSegment`. -/
inductive SegmentAccessOutcome where
  | ok (seg : RangeSegment)
  | missingState (seg : RangeSegment)
  | accessErr (seg : RangeSegment) (nodeTag : Nat) (err : TbTransitionError)
  | invErr (seg : RangeSegment) (nodeTag : Nat)

/-- Accumulator status during left-to-right node-state folding on a segment. -/
inductive SegFoldStatus where
  | ok
  | missingState
  | accessErr (nodeTag : Nat) (err : TbTransitionError)
  | invErr (nodeTag : Nat)

/-- Updates every entry matching `tag` in `states` to `st'`. -/
@[expose] def updateLocState (tag : Nat) (st' : TbLocationState)
    (states : List (Nat × TbLocationState)) : List (Nat × TbLocationState) :=
  states.foldr
    (fun entry acc =>
      if Nat.beq entry.1 tag then (entry.1, st') :: acc else entry :: acc)
    []

/-- Bounded ancestor-chain walk from `curTag` to a `parentTag = none` root,
returning `none` on missing topology nodes or exhausted `fuel`. -/
@[expose] def ancestorChain? (topo : List TbTopoNode) (fuel curTag : Nat) :
    Option (List Nat) :=
  (natFold
    (fun _ => none)
    (fun _ ih t =>
      match findTopoNode t topo with
      | none => none
      | some nd =>
        match nd.parentTag with
        | none => some [t]
        | some p =>
          match ih p with
          | none => none
          | some rest => some (t :: rest))
    fuel) curTag

/-- Short-circuiting single-node transition step inside `performSegmentAccess`.
-/
@[expose] def stepSegNode (protectedTags : List Nat) (kind : TbAccessKind)
    (rel : TbAccessRelatedness)
    (acc : List (Nat × TbLocationState) × SegFoldStatus) (ndTag : Nat) :
    List (Nat × TbLocationState) × SegFoldStatus :=
  match acc.2 with
  | .ok =>
    match lookupLocState ndTag acc.1 with
    | none => (acc.1, .missingState)
    | some st =>
      let isProt : Bool := natListMem ndTag protectedTags
      match st.performAccess kind rel isProt with
      | .Success st' => (updateLocState ndTag st' acc.1, .ok)
      | .Error st' err => (updateLocState ndTag st' acc.1, .accessErr ndTag err)
      | .InvariantFailure st' =>
        (updateLocState ndTag st' acc.1, .invErr ndTag)
  | .missingState => acc
  | .accessErr _ _ => acc
  | .invErr _ => acc

/-- Applies `actorTag`'s `kind` access across `seg` in local-first
short-circuiting order (`actorTag` and its ancestors before foreign nodes),
failing closed with `.missingState` if `actorTag` is absent from `topo` or any
topology or ancestor-chain tag lacks an entry in `seg.nodeStates`, and leaving
unvisited nodes untouched after the first error. -/
@[expose] def performSegmentAccess (topo : List TbTopoNode) (protectedTags :
    List Nat)
    (seg : RangeSegment) (actorTag : Nat) (kind : TbAccessKind)
    (mode : TbChildrenVisitMode) : SegmentAccessOutcome :=
  match findTopoNode actorTag topo with
  | none => .missingState seg
  | some _ =>
    if !segCoversTopology topo seg.nodeStates then
      .missingState seg
    else
      match ancestorChain? topo topo.length actorTag with
      | none => .missingState seg
      | some localTags =>
        let afterLocal :=
          localTags.foldl
            (stepSegNode protectedTags kind .LocalAccess)
            (seg.nodeStates, .ok)
        let afterAll :=
          match afterLocal.2 with
          | .ok =>
            seg.nodeStates.foldl
              (fun (acc : List (Nat × TbLocationState) × SegFoldStatus)
                   (entry : Nat × TbLocationState) =>
                let ndTag := entry.1
                if natListMem ndTag localTags then
                  acc
                else
                  let isStrictChild : Bool :=
                    !Nat.beq ndTag actorTag &&
                      tbIsAncestorOrSelf topo topo.length actorTag ndTag
                  let skip : Bool :=
                    match mode with
                    | .SkipChildrenOfAccessed => isStrictChild
                    | .VisitChildrenOfAccessed => false
                  if skip then
                    acc
                  else
                    stepSegNode protectedTags kind .ForeignAccess acc ndTag)
              afterLocal
          | .missingState => afterLocal
          | .accessErr _ _ => afterLocal
          | .invErr _ => afterLocal
        let seg' : RangeSegment := ⟨seg.offset, seg.length, afterAll.1⟩
        match afterAll.2 with
        | .ok => .ok seg'
        | .missingState => .missingState seg'
        | .accessErr t e => .accessErr seg' t e
        | .invErr t => .invErr seg' t

/-- Splits any segment straddling `cut` into `[offset, cut)` and
`[cut, offset + length)`. -/
@[expose] def splitSegmentsAt (cut : Nat) (segs : List RangeSegment) :
    List RangeSegment :=
  segs.foldr
    (fun seg acc =>
      if Nat.blt seg.offset cut && Nat.blt cut (seg.offset + seg.length) then
        let leftSeg : RangeSegment :=
          ⟨seg.offset, cut - seg.offset, seg.nodeStates⟩
        let rightSeg : RangeSegment :=
          ⟨cut, (seg.offset + seg.length) - cut, seg.nodeStates⟩
        leftSeg :: rightSeg :: acc
      else
        seg :: acc)
    []

/-- Status of a ranged Tree Borrows access across `RangedBorrowTree`. -/
inductive RangedAccessStatus where
  | Completed
  | UncoveredOrMissingTag
  | TransitionError (offset length nodeTag : Nat) (err : TbTransitionError)
  | InvariantFailure (offset length nodeTag : Nat)

/-- Result `(tree, status)` of `performRangedAccess`. -/
structure RangedAccessResult where
  tree : RangedBorrowTree
  status : RangedAccessStatus

/-- Steps one positive-length `RangeSegment` during `performRangedAccess`,
leaving disjoint segments (`Anneal.ByteSubLens.rangesDisjoint`) untouched,
enforcing contiguous non-overlapping tiling (`seg.offset = off + covered`),
and tracking covered byte length. -/
@[expose] def stepRangedSegment (topo : List TbTopoNode) (protTags : List Nat)
    (off len actorTag : Nat) (kind : TbAccessKind) (mode : TbChildrenVisitMode)
    (acc : List RangeSegment × Nat × RangedAccessStatus) (seg : RangeSegment) :
    List RangeSegment × Nat × RangedAccessStatus :=
  match acc.2.2 with
  | .Completed =>
    if rangesDisjoint off len seg.offset seg.length then
      (acc.1 ++ [seg], acc.2.1, .Completed)
    else
      match Nat.beq seg.offset (off + acc.2.1) with
      | false => (acc.1 ++ [seg], acc.2.1, .UncoveredOrMissingTag)
      | true =>
        match performSegmentAccess topo protTags seg actorTag kind mode with
        | .ok seg' => (acc.1 ++ [seg'], acc.2.1 + seg.length, .Completed)
        | .missingState seg' =>
          (acc.1 ++ [seg'], acc.2.1, .UncoveredOrMissingTag)
        | .accessErr seg' t e =>
          (acc.1 ++ [seg'], acc.2.1,
           .TransitionError seg.offset seg.length t e)
        | .invErr seg' t =>
          (acc.1 ++ [seg'], acc.2.1,
           .InvariantFailure seg.offset seg.length t)
  | .UncoveredOrMissingTag => (acc.1 ++ [seg], acc.2.1, .UncoveredOrMissingTag)
  | .TransitionError o l t e =>
    (acc.1 ++ [seg], acc.2.1, .TransitionError o l t e)
  | .InvariantFailure o l t =>
    (acc.1 ++ [seg], acc.2.1, .InvariantFailure o l t)

/-- Executes a ranged Tree Borrows access over `[off, off + len)`. Positive
lengths require `tree.segments` to contiguously tile `[off, off + len)` without
gaps or overlap and every topology/local-chain tag to appear in each touched
segment; otherwise this returns `.UncoveredOrMissingTag`. Zero-length accesses
on a known tag return `.Completed`. (`.SkipChildrenOfAccessed` is intended only
for protector-exit accesses.) -/
@[expose] def performRangedAccess (tree : RangedBorrowTree) (off len actorTag :
    Nat)
    (kind : TbAccessKind) (mode : TbChildrenVisitMode) : RangedAccessResult :=
  match findTopoNode actorTag tree.topology with
  | none => ⟨tree, .UncoveredOrMissingTag⟩
  | some _ =>
    if Nat.beq len 0 then
      ⟨tree, .Completed⟩
    else
      let split1 := splitSegmentsAt off tree.segments
      let split2 := splitSegmentsAt (off + len) split1
      let stepOut :=
        split2.foldl
          (stepRangedSegment tree.topology tree.protectedTags off len actorTag
            kind mode)
          ([], 0, .Completed)
      let finalStatus :=
        match stepOut.2.2 with
        | .Completed =>
          match Nat.beq stepOut.2.1 len with
          | true => .Completed
          | false => .UncoveredOrMissingTag
        | .UncoveredOrMissingTag => .UncoveredOrMissingTag
        | .TransitionError o l t e => .TransitionError o l t e
        | .InvariantFailure o l t => .InvariantFailure o l t
      ⟨{ tree with segments := stepOut.1 }, finalStatus⟩

/-- Status of protector release at call-frame exit. -/
inductive ProtectorReleaseStatus where
  | Released
  | MissingTag (tag : Nat)
  | AccessFailure (offset length nodeTag : Nat) (err : TbTransitionError)
  | InvariantFailure (offset length nodeTag : Nat)

/-- Result `(tree, status)` of protector release. -/
structure ProtectorReleaseResult where
  tree : RangedBorrowTree
  status : ProtectorReleaseStatus

/-- Emits implicit protector-release accesses (`TbPermission.associatedAccess`)
for `calleeTag` across all `accessed = true` segments while keeping all
co-frame tags in `tree.protectedTags`. Fails closed with `.MissingTag` when
`tree.segments` is empty or any segment omits a topology tag. -/
@[expose] def releaseProtectorKeepProtected (tree : RangedBorrowTree) (calleeTag
    : Nat) :
    ProtectorReleaseResult :=
  match findTopoNode calleeTag tree.topology with
  | none => ⟨tree, .MissingTag calleeTag⟩
  | some _ =>
    match tree.segments with
    | [] => ⟨tree, .MissingTag calleeTag⟩
    | _ :: _ =>
      let stepOut :=
        tree.segments.foldl
          (fun (acc : List RangeSegment × ProtectorReleaseStatus) seg =>
            match acc.2 with
            | .Released =>
              if !segCoversTopology tree.topology seg.nodeStates then
                (acc.1 ++ [seg], .MissingTag calleeTag)
              else
                match lookupLocState calleeTag seg.nodeStates with
                | none => (acc.1 ++ [seg], .MissingTag calleeTag)
                | some st =>
                  match st.permission.associatedAccess with
                  | none => (acc.1 ++ [seg], .Released)
                  | some kind =>
                    if st.accessed then
                      match performSegmentAccess tree.topology
                          tree.protectedTags seg calleeTag kind
                          .SkipChildrenOfAccessed with
                      | .ok seg' => (acc.1 ++ [seg'], .Released)
                      | .missingState seg' =>
                        (acc.1 ++ [seg'], .MissingTag calleeTag)
                      | .accessErr seg' t e =>
                        (acc.1 ++ [seg'],
                         .AccessFailure seg.offset seg.length t e)
                      | .invErr seg' t =>
                        (acc.1 ++ [seg'],
                         .InvariantFailure seg.offset seg.length t)
                    else
                      (acc.1 ++ [seg], .Released)
            | .MissingTag t => (acc.1 ++ [seg], .MissingTag t)
            | .AccessFailure o l t e =>
              (acc.1 ++ [seg], .AccessFailure o l t e)
            | .InvariantFailure o l t =>
              (acc.1 ++ [seg], .InvariantFailure o l t))
          ([], .Released)
      ⟨{ tree with segments := stepOut.1 }, stepOut.2⟩

/-- Removes `frameTags` from `tree.protectedTags` after implicit exit accesses
succeed. -/
@[expose] def endCallRemoveProtectors (tree : RangedBorrowTree) (frameTags :
    List Nat) :
    RangedBorrowTree :=
  { tree with
    protectedTags :=
      tree.protectedTags.filter (fun t => !natListMem t frameTags) }

/-- Full Miri-ordered frame exit: verifies every entry of `frameTags` is in
`tree.protectedTags` (failing closed with `.MissingTag`), runs
`releaseProtectorKeepProtected` across `frameTags` while all `frameTags` remain
protected, then strips `frameTags` via `endCallRemoveProtectors`. -/
@[expose] def exitFrameWithProtectors (tree : RangedBorrowTree) (frameTags :
    List Nat) :
    ProtectorReleaseResult :=
  let relOut :=
    frameTags.foldl
      (fun (acc : ProtectorReleaseResult) tag =>
        match acc.status with
        | .Released =>
          if !natListMem tag acc.tree.protectedTags then
            ⟨acc.tree, .MissingTag tag⟩
          else
            releaseProtectorKeepProtected acc.tree tag
        | .MissingTag _ | .AccessFailure _ _ _ _ | .InvariantFailure _ _ _ =>
          acc)
      ⟨tree, .Released⟩
  match relOut.status with
  | .Released => ⟨endCallRemoveProtectors relOut.tree frameTags, .Released⟩
  | .MissingTag _ | .AccessFailure _ _ _ _ | .InvariantFailure _ _ _ => relOut

/-- Parametric shared 3-node `topo3` `RangedBorrowTree` on `[0..16)` (`[0..8)`
for `src` tag `1` and `[8..16)` for `dst` tag `2`), with `dst` unaccessed
(`(Disabled, false)`) on `[0..8)` and `src` unaccessed (`(Disabled, false)`) on
`[8..16)`. -/
@[expose] def mkSharedTopo3Tree16 (pSrc : TbPermission) (accSrc : Bool)
    (pDst : TbPermission) (accDst : Bool) (protTags : List Nat) :
    RangedBorrowTree :=
  { topology := topo3
    protectedTags := protTags
    segments :=
      [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, accSrc⟩),
               (2, ⟨.Disabled, false⟩)]⟩,
       ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
               (2, ⟨pDst, accDst⟩)]⟩] }

/-- Decidable predicate for permissions supporting a local `.Read`. -/
@[expose] def permCanLocalRead (p : TbPermission) : Bool :=
  match p with
  | .Disabled => false
  | .Cell | .ReservedFrz _ | .ReservedIM | .Unique | .Frozen => true

/-- Decidable predicate for permissions supporting a protected local `.Write`.
-/
@[expose] def permCanProtectedLocalWrite (p : TbPermission) : Bool :=
  match p with
  | .Cell | .ReservedFrz false | .ReservedIM | .Unique => true
  | .ReservedFrz true | .Frozen | .Disabled => false

private def nextPermAfterProtectedWrite (p : TbPermission) : TbPermission :=
  match p with
  | .Cell => .Cell
  | .ReservedFrz _ | .ReservedIM | .Unique | .Frozen | .Disabled => .Unique

private theorem seg08_read_src_ok (pSrc : TbPermission) (accSrc protBoth : Bool)
    (hRead : permCanLocalRead pSrc = true) :
    performSegmentAccess topo3 (if protBoth then [1, 2] else [2])
      ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, accSrc⟩),
              (2, ⟨.Disabled, false⟩)]⟩
      1 .Read .VisitChildrenOfAccessed =
    .ok ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, true⟩),
                (2, ⟨.Disabled, false⟩)]⟩ := by
  cases pSrc with
  | Disabled => exact False.elim (boolFalseNeTrue hRead)
  | Cell => cases accSrc <;> cases protBoth <;> rfl
  | ReservedFrz cSrc => cases cSrc <;> cases accSrc <;> cases protBoth <;> rfl
  | ReservedIM => cases accSrc <;> cases protBoth <;> rfl
  | Unique => cases accSrc <;> cases protBoth <;> rfl
  | Frozen => cases accSrc <;> cases protBoth <;> rfl

private theorem seg816_write_dst_ok (pDst : TbPermission)
    (accDst protBoth : Bool) (hWrite : permCanProtectedLocalWrite pDst = true) :
    performSegmentAccess topo3 (if protBoth then [1, 2] else [2])
      ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
              (2, ⟨pDst, accDst⟩)]⟩
      2 .Write .VisitChildrenOfAccessed =
    .ok ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
      (2, ⟨nextPermAfterProtectedWrite pDst, true⟩)]⟩ := by
  cases pDst with
  | Frozen | Disabled => exact False.elim (boolFalseNeTrue hWrite)
  | ReservedFrz cDst =>
    cases cDst with
    | true => exact False.elim (boolFalseNeTrue hWrite)
    | false => cases accDst <;> cases protBoth <;> rfl
  | Cell => cases accDst <;> cases protBoth <;> rfl
  | ReservedIM => cases accDst <;> cases protBoth <;> rfl
  | Unique => cases accDst <;> cases protBoth <;> rfl

/-- Universal symbolic commutation on shared 3-node `mkSharedTopo3Tree16` (`[]`
zero axioms): reading `src` (`1`) at `[0..8)` and writing protected `dst` (`2`)
at `[8..16)` under `.VisitChildrenOfAccessed` commute to the identical
`RangedBorrowTree` across all readable `pSrc` and protected-writable `pDst`.
-/
theorem shared_topo3_ranged_commutation_universal
    (pSrc pDst : TbPermission) (accSrc accDst protBoth : Bool)
    (hRead : permCanLocalRead pSrc = true)
    (hWrite : permCanProtectedLocalWrite pDst = true) :
    let protTags := if protBoth then [1, 2] else [2]
    let tree0 := mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags
    let s1 := performRangedAccess tree0 0 8 1 .Read .VisitChildrenOfAccessed
    let s12 := performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
    let s2 := performRangedAccess tree0 8 8 2 .Write .VisitChildrenOfAccessed
    let s21 := performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
    s1.status = .Completed ∧
    s2.status = .Completed ∧
    s12.status = .Completed ∧
    s21.status = .Completed ∧
    s12.tree = s21.tree := by
  have hS08 := seg08_read_src_ok pSrc accSrc protBoth hRead
  have hS816 := seg816_write_dst_ok pDst accDst protBoth hWrite
  let protTags := if protBoth then [1, 2] else [2]
  let seg08Init : RangeSegment :=
    ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, accSrc⟩),
            (2, ⟨.Disabled, false⟩)]⟩
  let seg08After : RangeSegment :=
    ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, true⟩),
            (2, ⟨.Disabled, false⟩)]⟩
  let seg816Init : RangeSegment :=
    ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
            (2, ⟨pDst, accDst⟩)]⟩
  let seg816After : RangeSegment :=
    ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
      (2, ⟨nextPermAfterProtectedWrite pDst, true⟩)]⟩
  have hStep1 :
      performRangedAccess (mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags)
        0 8 1 .Read .VisitChildrenOfAccessed =
      ⟨{ topology := topo3, protectedTags := protTags,
         segments := [seg08After, seg816Init] }, .Completed⟩ := by
    unfold mkSharedTopo3Tree16 performRangedAccess
    change
      (let stepOut :=
        [seg08Init, seg816Init].foldl
          (stepRangedSegment topo3 protTags 0 8 1 .Read
            .VisitChildrenOfAccessed)
          ([], 0, .Completed)
       let finalStatus :=
         match stepOut.2.2 with
         | .Completed =>
           match Nat.beq stepOut.2.1 8 with
           | true => .Completed
           | false => .UncoveredOrMissingTag
         | .UncoveredOrMissingTag => .UncoveredOrMissingTag
         | .TransitionError o l t e => .TransitionError o l t e
         | .InvariantFailure o l t => .InvariantFailure o l t
       RangedAccessResult.mk
         { topology := topo3, protectedTags := protTags,
           segments := stepOut.1 } finalStatus) = _
    dsimp only [List.foldl, stepRangedSegment, seg08Init, seg816Init]
    rw [ite_bool_false (rfl : rangesDisjoint 0 8 0 8 = false), hS08]
    dsimp only
    rw [ite_bool_true (rfl : rangesDisjoint 0 8 8 8 = true)]
    rfl
  have hStep2 :
      performRangedAccess (mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags)
        8 8 2 .Write .VisitChildrenOfAccessed =
      ⟨{ topology := topo3, protectedTags := protTags,
         segments := [seg08Init, seg816After] }, .Completed⟩ := by
    unfold mkSharedTopo3Tree16 performRangedAccess
    change
      (let stepOut :=
        [seg08Init, seg816Init].foldl
          (stepRangedSegment topo3 protTags 8 8 2 .Write
            .VisitChildrenOfAccessed)
          ([], 0, .Completed)
       let finalStatus :=
         match stepOut.2.2 with
         | .Completed =>
           match Nat.beq stepOut.2.1 8 with
           | true => .Completed
           | false => .UncoveredOrMissingTag
         | .UncoveredOrMissingTag => .UncoveredOrMissingTag
         | .TransitionError o l t e => .TransitionError o l t e
         | .InvariantFailure o l t => .InvariantFailure o l t
       RangedAccessResult.mk
         { topology := topo3, protectedTags := protTags,
           segments := stepOut.1 } finalStatus) = _
    dsimp only [List.foldl, stepRangedSegment, seg08Init, seg816Init]
    rw [ite_bool_true (rfl : rangesDisjoint 8 8 0 8 = true)]
    dsimp only
    rw [ite_bool_false (rfl : rangesDisjoint 8 8 8 8 = false), hS816]
    rfl
  have hStep12 :
      performRangedAccess
        { topology := topo3, protectedTags := protTags,
          segments := [seg08After, seg816Init] }
        8 8 2 .Write .VisitChildrenOfAccessed =
      ⟨{ topology := topo3, protectedTags := protTags,
         segments := [seg08After, seg816After] }, .Completed⟩ := by
    unfold performRangedAccess
    change
      (let stepOut :=
        [seg08After, seg816Init].foldl
          (stepRangedSegment topo3 protTags 8 8 2 .Write
            .VisitChildrenOfAccessed)
          ([], 0, .Completed)
       let finalStatus :=
         match stepOut.2.2 with
         | .Completed =>
           match Nat.beq stepOut.2.1 8 with
           | true => .Completed
           | false => .UncoveredOrMissingTag
         | .UncoveredOrMissingTag => .UncoveredOrMissingTag
         | .TransitionError o l t e => .TransitionError o l t e
         | .InvariantFailure o l t => .InvariantFailure o l t
       RangedAccessResult.mk
         { topology := topo3, protectedTags := protTags,
           segments := stepOut.1 } finalStatus) = _
    dsimp only [List.foldl, stepRangedSegment, seg08After, seg816Init]
    rw [ite_bool_true (rfl : rangesDisjoint 8 8 0 8 = true)]
    dsimp only
    rw [ite_bool_false (rfl : rangesDisjoint 8 8 8 8 = false), hS816]
    rfl
  have hStep21 :
      performRangedAccess
        { topology := topo3, protectedTags := protTags,
          segments := [seg08Init, seg816After] }
        0 8 1 .Read .VisitChildrenOfAccessed =
      ⟨{ topology := topo3, protectedTags := protTags,
         segments := [seg08After, seg816After] }, .Completed⟩ := by
    unfold performRangedAccess
    change
      (let stepOut :=
        [seg08Init, seg816After].foldl
          (stepRangedSegment topo3 protTags 0 8 1 .Read
            .VisitChildrenOfAccessed)
          ([], 0, .Completed)
       let finalStatus :=
         match stepOut.2.2 with
         | .Completed =>
           match Nat.beq stepOut.2.1 8 with
           | true => .Completed
           | false => .UncoveredOrMissingTag
         | .UncoveredOrMissingTag => .UncoveredOrMissingTag
         | .TransitionError o l t e => .TransitionError o l t e
         | .InvariantFailure o l t => .InvariantFailure o l t
       RangedAccessResult.mk
         { topology := topo3, protectedTags := protTags,
           segments := stepOut.1 } finalStatus) = _
    dsimp only [List.foldl, stepRangedSegment, seg08Init, seg816After]
    rw [ite_bool_false (rfl : rangesDisjoint 0 8 0 8 = false), hS08]
    dsimp only
    rw [ite_bool_true (rfl : rangesDisjoint 0 8 8 8 = true)]
    rfl
  dsimp only
  change
    (let s1 := performRangedAccess
       (mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags)
       0 8 1 .Read .VisitChildrenOfAccessed
     let s12 := performRangedAccess s1.tree 8 8 2 .Write
       .VisitChildrenOfAccessed
     let s2 := performRangedAccess
       (mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags)
       8 8 2 .Write .VisitChildrenOfAccessed
     let s21 := performRangedAccess s2.tree 0 8 1 .Read
       .VisitChildrenOfAccessed
     s1.status = .Completed ∧ s2.status = .Completed ∧
       s12.status = .Completed ∧ s21.status = .Completed ∧
       s12.tree = s21.tree)
  rw [hStep1, hStep2]
  dsimp only
  rw [hStep12, hStep21]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.RefFrame

end
