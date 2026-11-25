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
public import Anneal.MiriTreeBorrows.Model
public import Anneal.MiriTreeBorrows.Retag

public section

/-!
# Miri Tree Borrows Verification Canaries (`Anneal.MiriTreeBorrows.Canaries`)

Concrete, zero-axiom (`[]`) Miri-faithful verification canaries exercising
`Anneal.MiriTreeBorrows`:

1. `canary_readOnly_aliased_reservedFrz_and_frozen_exits_cleanly`: parent
   `associatedAccess` at the second `FnEntry` retag transitions `ReservedFrz`
   from `false` to `true` (`conflicted = true`) on overlapping bytes, and both
   tags exit cleanly.
2. `canary_unique_reborrow_traps_at_second_fnEntry_retag`: reborrowing an
   overlapping `&` or `&mut` against an already-protected `Unique` traps
   immediately during `RetagPipeline.accessTreeForReborrow` with
   `.protectedDisabled 1 .unique`, paired with a disjoint `Unique` + `Frozen`
   write/exit witness.
3. `canary_outside_range_unaccessed_lazily_disables_vs_inside_traps`: pins
   `LocationState.lean:144` (`nextState.accessed`): foreign write lazily
   disables an unaccessed outside-range protected `ReservedFrz false` without
   UB, while trapping on the accessed inside-range bytes.
4. `canary_sifa_skippedForeignNodes_and_skipChildren_sound`: verifies SIFA
   subtree pruning spares a protected grandchild beneath a `.disabled` foreign
   node, end-to-end `miriExitCallFrame` `.skipChildrenOfAccessed` spares an
   active child of a released parent, ancestor `miriWeakenSegmentAncestors`
   using `min(insideLoc.sifa, outsideLoc.sifa)` prevents unsound foreign-write
   skipping outside the reborrow range, and ancestor `localAccess` events
   execute before `foreignAccess` events.
5. `canary_reservedIM_and_cell_protector_semantics`: verifies unprotected
   `.reservedIM` survives foreign write, protected `.reservedIM` fails closed,
   and accessed `.cell` overlapping protected `.unique` on `[0, 8)` emits
   `miriAssociatedAccess .cell = none` at both retag and protector exit.
6. `canary_forward_vs_reverse_release_order_separates_conflict_state`: on an
   explicit synthetic conflict state (not claimed reachable via `FnEntry`
   retagging), forward vs reverse release fails on distinct tags/permissions.
7. `canary_miriTreeBorrows_negative_fail_closed_tests`: single-cause
   fail-closed negative suite covering missing trees, unknown actor tags
   (nonzero and zero-size), dangling parents, uncovered/overlapping segments,
   out-of-bounds `.cell` reborrows, unknown frames on retag and exit, duplicate
   `newTag`, non-initial permissions, dead/missing allocations, missing tags or
   segment entries on protector release, write-to-readonly reborrows, lazy
   `.unique`, dead-allocation skip vs. missing-allocation rejection on exit,
   pre-error SIFA reset, and empty-interval non-overlap / zero-size segment
   preservation.
8. `canary_frame_protector_and_multi_root_fail_closed`: duplicate frame IDs
   fail closed, failed protected reborrows keep the registered protector, and
   accesses on multi-root trees fail closed with `.multipleRoots`.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and compile with zero axioms (`[]`).
-/

namespace Anneal.MiriTreeBorrows

open Trusted.MirAst Trusted.MirSemantics

/-- Live 16-byte mutable memory fixture (`allocId = 1`). -/
@[expose] def miriMem16Live : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1
         alignLog2 := 2
         mutability := .mut
         bytes := List.replicate 16 (AllocByte.init 0x11 none)
         live := true }] }

/-- Live 16-byte read-only (`.shared`) memory fixture (`allocId = 1`). -/
@[expose] def miriMem16Shared : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1
         alignLog2 := 2
         mutability := .shared
         bytes := List.replicate 16 (AllocByte.init 0x11 none)
         live := true }] }

/-- Dead 16-byte memory fixture (`allocId = 1`, `live = false`). -/
@[expose] def miriMem16Dead : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1
         alignLog2 := 2
         mutability := .mut
         bytes := List.replicate 16 (AllocByte.init 0x11 none)
         live := false }] }

/-- Initial single-root Tree Borrows state on `allocId = 1` (`[0, 16)`). -/
@[expose] def miriTbRoot16 : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree := [{ tag := 0, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 16
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Extracts the `MiriTbState` payload from a `MiriTbResult`. -/
@[expose] def unwrapTb (r : MiriTbResult MiriTbState) : MiriTbState :=
  match r with
  | .ok st => st
  | .err st _ => st

/-- `miriTbRoot16` with an empty protector frame `1`. -/
@[expose] def miriTbFrame1 : MiriTbState :=
  unwrapTb (miriBeginFrame miriTbRoot16 1)

/-- Computable 0-based list lookup returning `none` out of bounds. -/
@[expose] def listNth? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  (xs.foldl
    (fun (acc : Nat × Option α) x =>
      (acc.1 + 1, if Nat.beq acc.1 idx then some x else acc.2))
    (0, none)).2

/-- Looks up `(perm, accessed)` for `tag` in segment `segIdx` of `allocId`. -/
@[expose] def lookupPermInSeg? (st : MiriTbState) (allocId : AllocId)
    (segIdx tag : Nat) : Option (MiriPerm × Bool) :=
  match miriFindAllocTree? allocId st.allocTrees with
  | none => none
  | some atree =>
    match listNth? atree.segments segIdx with
    | none => none
    | some seg =>
      match miriFindTagEntry? tag seg.entries with
      | none => none
      | some e => some (e.loc.perm, e.loc.accessed)

/-- Computable structural Boolean equality on `MiriPerm`. -/
@[expose] def permEq (p1 p2 : MiriPerm) : Bool :=
  match p1, p2 with
  | .cell, .cell => true
  | .reservedFrz c1, .reservedFrz c2 =>
    match c1 with
    | false => match c2 with | false => true | true => false
    | true => match c2 with | false => false | true => true
  | .reservedIM, .reservedIM => true
  | .unique, .unique => true
  | .frozen, .frozen => true
  | .disabled, .disabled => true
  | .cell, .reservedFrz _ => false
  | .cell, .reservedIM => false
  | .cell, .unique => false
  | .cell, .frozen => false
  | .cell, .disabled => false
  | .reservedFrz _, .cell => false
  | .reservedFrz _, .reservedIM => false
  | .reservedFrz _, .unique => false
  | .reservedFrz _, .frozen => false
  | .reservedFrz _, .disabled => false
  | .reservedIM, .cell => false
  | .reservedIM, .reservedFrz _ => false
  | .reservedIM, .unique => false
  | .reservedIM, .frozen => false
  | .reservedIM, .disabled => false
  | .unique, .cell => false
  | .unique, .reservedFrz _ => false
  | .unique, .reservedIM => false
  | .unique, .frozen => false
  | .unique, .disabled => false
  | .frozen, .cell => false
  | .frozen, .reservedFrz _ => false
  | .frozen, .reservedIM => false
  | .frozen, .unique => false
  | .frozen, .disabled => false
  | .disabled, .cell => false
  | .disabled, .reservedFrz _ => false
  | .disabled, .reservedIM => false
  | .disabled, .unique => false
  | .disabled, .frozen => false

/-- Checks whether `r` failed with `.childAccessForbidden t p`. -/
@[expose] def isChildForbiddenErr {α : Type} (t : Nat) (p : MiriPerm)
    (r : MiriTbResult α) : Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .childAccessForbidden et ep => Nat.beq et t && permEq ep p
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.protectedDisabled t p`. -/
@[expose] def isProtectedDisabledErr (t : Nat) (p : MiriPerm)
    (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .protectedDisabled et ep => Nat.beq et t && permEq ep p
    | .childAccessForbidden _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.uncoveredRange aid`. -/
@[expose] def isUncoveredErr (aid : AllocId) (r : MiriTbResult MiriTbState) :
    Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .uncoveredRange a => Nat.beq a aid
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false

/-- Checks whether `r` failed with `.missingTag t`. -/
@[expose] def isMissingTagErr {α : Type} (t : Nat) (r : MiriTbResult α) :
    Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .missingTag et => Nat.beq et t
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.writeToReadOnly aid`. -/
@[expose] def isWriteToReadOnlyErr (aid : AllocId)
    (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .writeToReadOnly a => Nat.beq a aid
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.impossibleProtectedReservedIM t`. -/
@[expose] def isImpossibleProtResIMErr (t : Nat)
    (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .impossibleProtectedReservedIM et => Nat.beq et t
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.duplicateTag t`. -/
@[expose] def isDuplicateTagErr (t : Nat) (r : MiriTbResult MiriTbState) :
    Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .duplicateTag et => Nat.beq et t
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.missingFrame fid`. -/
@[expose] def isMissingFrameErr (fid : Nat) (r : MiriTbResult MiriTbState) :
    Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .missingFrame ef => Nat.beq ef fid
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.deadOrMissingAlloc aid`. -/
@[expose] def isDeadOrMissingAllocErr (aid : AllocId)
    (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame _ => false
    | .multipleRoots _ => false
    | .deadOrMissingAlloc ea => Nat.beq ea aid
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Two overlapping `FnEntry` arguments (`tag 1`: `&mut [0, 8)`, `tag 2`:
`& [4, 12)`) registered with `RetagPipeline.accessTreeForReborrow` parent
access. -/
@[expose] def miriReadOnlyAliasedEntry : MiriTbState :=
  let st0 := miriTbFrame1
  let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
    .mutable true false 0 8)
  unwrapTb (miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0
    .shared true false 4 8)

/-- Canary 1 (`[]`): registering `tag 2` (`& [4, 12)`) emits a parent `Read`
through `tag 0` that immediately marks protected `tag 1` (`ReservedFrz false`)
as `ReservedFrz true` (`conflicted = true`) on `[4, 8)` while leaving `[0, 4)`
unconflicted and `[8, 12)` unaccessed; an explicit read through `tag 2` and
forward frame exit both succeed cleanly. -/
theorem canary_readOnly_aliased_reservedFrz_and_frozen_exits_cleanly :
    lookupPermInSeg? miriReadOnlyAliasedEntry 1 0 1 =
      some (.reservedFrz false, true) ∧
    lookupPermInSeg? miriReadOnlyAliasedEntry 1 1 1 =
      some (.reservedFrz true, true) ∧
    lookupPermInSeg? miriReadOnlyAliasedEntry 1 2 1 =
      some (.reservedFrz true, false) ∧
    (match miriPerformRangedAccess miriReadOnlyAliasedEntry 1 2 4 8 .read
        .visitChildrenOfAccessed with
     | .err _ _ => false
     | .ok stAfterRead =>
       match miriExitCallFrame miriMem16Live stAfterRead 1 with
       | .ok stEnd => stEnd.frames.isEmpty
       | .err _ _ => false) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Canary 2 (`[]`): with `implicitWrites = true`, `tag 1` (`Unique [0, 8)`)
is protected in frame 1; attempting to register an overlapping `tag 2` as
either `& [4, 12)` or `&mut [4, 12)` traps immediately during the parent
`associatedAccess` traversal with `.protectedDisabled 1 .unique`. By contrast,
disjoint `tag 1` (`Unique [0, 8)`) + `tag 2` (`& [8, 16)`) succeeds through
both retags, write via `tag 1`, and clean frame exit. -/
theorem canary_unique_reborrow_traps_at_second_fnEntry_retag :
    (let st0 := miriTbFrame1
     let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
       .mutable true true 0 8)
     let rShared := miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0
       .shared true false 4 8
     let rMut := miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0
       .mutable true false 4 8
     isProtectedDisabledErr 1 .unique rShared &&
       isProtectedDisabledErr 1 .unique rMut) = true ∧
    (let st0 := miriTbFrame1
     let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
       .mutable true true 0 8)
     match miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0
         .shared true false 8 8 with
     | .err _ _ => false
     | .ok st2 =>
       match miriPerformRangedAccess st2 1 1 0 8 .write
           .visitChildrenOfAccessed with
       | .err _ _ => false
       | .ok stW =>
         match miriExitCallFrame miriMem16Live stW 1 with
         | .ok stEnd => stEnd.frames.isEmpty
         | .err _ _ => false) = true :=
  ⟨rfl, rfl⟩

/-- Canary 3 (`[]`): pins `nextState.accessed` in `LocationState.lean:144`:
registering protected `tag 1` (`&mut [0, 8)`, `implicitWrites = false`) leaves
`[0, 8)` `accessed = true` and outside-range `[8, 16)` `accessed = false`.
A foreign write through `tag 0` on `[8, 16)` lazily transitions `tag 1` to
`.disabled` without UB, whereas the same foreign write on `[0, 8)` traps with
`.protectedDisabled 1 (.reservedFrz false)`. -/
theorem canary_outside_range_unaccessed_lazily_disables_vs_inside_traps :
    (let st0 := miriTbFrame1
     let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
       .mutable true false 0 8)
     match miriPerformRangedAccess st1 1 0 8 8 .write
         .visitChildrenOfAccessed with
     | .err _ _ => false
     | .ok stOut =>
       match lookupPermInSeg? stOut 1 1 1 with
       | some (p, acc) => miriPermIsDisabled p && !acc
       | none => false) = true ∧
    (let st0 := miriTbFrame1
     let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
       .mutable true false 0 8)
     isProtectedDisabledErr 1 (.reservedFrz false)
       (miriPerformRangedAccess st1 1 0 0 8 .write
         .visitChildrenOfAccessed)) = true :=
  ⟨rfl, rfl⟩

/-- Three-node chain `0 -> 1 -> 2` fixture for SIFA subtree pruning. -/
@[expose] def sifaGrandchildTree : List MiriTopoNode :=
  [{ tag := 0, parent := none, children := [1] },
   { tag := 1, parent := some 0, children := [2] },
   { tag := 2, parent := some 1, children := [] }]

/-- Segment fixture with `.reservedIM` (`sifa = .write`) node `1`, isolating
the SIFA-rank disjunct of `miriSkipIfKnownNoop`. -/
@[expose] def sifaGrandchildSeg : MiriSegment :=
  { offset := 0
    size := 8
    entries :=
      [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
       { tag := 1, loc := ⟨.reservedIM, false, .write⟩ },
       { tag := 2, loc := ⟨.frozen, true, .read⟩ }] }

/-- Four-node tree fixture testing local-before-foreign event order. -/
@[expose] def localBeforeForeignTree : List MiriTopoNode :=
  [{ tag := 0, parent := none, children := [1, 3] },
   { tag := 1, parent := some 0, children := [2] },
   { tag := 2, parent := some 1, children := [] },
   { tag := 3, parent := some 0, children := [] }]

/-- Segment fixture pairing `.frozen` parent `1` with `.unique` cousin `3`. -/
@[expose] def localBeforeForeignSeg : MiriSegment :=
  { offset := 0
    size := 8
    entries :=
      [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
       { tag := 1, loc := ⟨.frozen, true, .read⟩ },
       { tag := 2, loc := ⟨.unique, true, .none⟩ },
       { tag := 3, loc := ⟨.unique, true, .none⟩ }] }

/-- Canary 4 (`[]`):
1. All three `miriSkipIfKnownNoop` pruning disjuncts (`sifa = .write` rank,
   `.disabled` with `sifa = .none` under `.write`, and `.frozen` with
   `sifa = .none` under `.read`) independently prune node `1` and spare its
   protected grandchild `2`.
2. `.skipChildrenOfAccessed` during `miriExitCallFrame` spares an unprotected
   `.unique` child `tag 2` reborrowed from protected parent `tag 1`, so writing
   through `tag 2` after frame 1 exits still succeeds.
3. Reborrowing `tag 2` (`insidePerm = .cell` with `sifa = .write`,
   `outsidePerm = .frozen` with `sifa = .read`) from `tag 1` (`.reservedIM`,
   `sifa = .write`) weakens `tag 1`'s SIFA to `min(.write, .read) = .read` on
   `[8, 16)`, ensuring a foreign write through root `0` on `[8, 16)` disables
   `tag 2` (`.childAccessForbidden 2 .disabled` on read).
4. Ancestor `localAccess` events execute before cousin `foreignAccess` events,
   so a write through `tag 2` under `.frozen` parent `tag 1` and protected
   `.unique` cousin `tag 3` halts with `.childAccessForbidden 1 .frozen` rather
   than `.protectedDisabled 3 .unique`. -/
theorem canary_sifa_skippedForeignNodes_and_skipChildren_sound :
    miriSkippedForeignNodes sifaGrandchildSeg .write = [1] ∧
    (miriTraverseSegmentEvents sifaGrandchildTree sifaGrandchildSeg 0 .write
      .visitChildrenOfAccessed) = [{ tag := 0, rel := .localAccess }] ∧
    (match miriPerformSegmentAccess sifaGrandchildTree [2] 0 .write
        .visitChildrenOfAccessed sifaGrandchildSeg with
     | .ok _ => true
     | .err _ _ => false) = true ∧
    (match miriPerformSegmentAccess sifaGrandchildTree [2] 0 .write
        .visitChildrenOfAccessed
        { offset := 0
          size := 8
          entries :=
            [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
             { tag := 1, loc := ⟨.disabled, false, .none⟩ },
             { tag := 2, loc := ⟨.frozen, true, .none⟩ }] } with
     | .ok _ => true
     | .err _ _ => false) = true ∧
    (match miriPerformSegmentAccess sifaGrandchildTree [2] 0 .read
        .visitChildrenOfAccessed
        { offset := 0
          size := 8
          entries :=
            [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
             { tag := 1, loc := ⟨.frozen, true, .none⟩ },
             { tag := 2, loc := ⟨.unique, true, .none⟩ }] } with
     | .ok _ => true
     | .err _ _ => false) = true ∧
    (let st0 := miriTbFrame1
     let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
       .mutable true true 0 8)
     match miriReborrowTag miriMem16Live st1 none 1 2 1 .unique .reservedIM
         0 8 with
     | .err _ _ => false
     | .ok st2 =>
       match miriExitCallFrame miriMem16Live st2 1 with
       | .err _ _ => false
       | .ok st3 =>
         match miriPerformRangedAccess st3 1 2 0 8 .write
             .visitChildrenOfAccessed with
         | .ok _ => true
         | .err _ _ => false) = true ∧
    (match miriReborrowTag miriMem16Live miriTbRoot16 none 1 1 0 .reservedIM
         .reservedIM 0 16 with
     | .err _ _ => false
     | .ok st1 =>
       match miriReborrowTag miriMem16Live st1 none 1 2 1 .cell .frozen
           0 8 with
       | .err _ _ => false
       | .ok st2 =>
         match miriPerformRangedAccess st2 1 0 8 8 .write
             .visitChildrenOfAccessed with
         | .err _ _ => false
         | .ok st3 =>
           isChildForbiddenErr 2 .disabled
             (miriPerformRangedAccess st3 1 2 8 8 .read
               .visitChildrenOfAccessed)) = true ∧
    isChildForbiddenErr 1 .frozen
      (miriPerformSegmentAccess localBeforeForeignTree [3] 2 .write
        .visitChildrenOfAccessed localBeforeForeignSeg) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 5 (`[]`): unprotected `.reservedIM` survives foreign writes without
disabling, protected `.reservedIM` is rejected at retag, and an accessed
protected `.cell` (`tag 1`) overlapping a protected `.unique` (`tag 2`) on the
same `[0, 8)` range emits `miriAssociatedAccess .cell = none` at both retag and
protector exit without disturbing `tag 2`. -/
theorem canary_reservedIM_and_cell_protector_semantics :
    (match miriReborrowTag miriMem16Live miriTbRoot16 none 1 1 0
        .reservedIM .reservedIM 0 8 with
     | .err _ _ => false
     | .ok st1 =>
       match miriPerformRangedAccess st1 1 0 0 8 .write
           .visitChildrenOfAccessed with
       | .err _ _ => false
       | .ok stW =>
         match lookupPermInSeg? stW 1 0 1 with
         | some (p, acc) => permEq p .reservedIM && acc
         | none => false) = true ∧
    isImpossibleProtResIMErr 1
      (miriReborrowTag miriMem16Live miriTbFrame1
        (some 1) 1 1 0 .reservedIM .reservedIM 0 8) = true ∧
    (let st0 := miriTbFrame1
     let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0
       .shared false false 0 8)
     match miriPerformRangedAccess st1 1 1 0 8 .write
         .visitChildrenOfAccessed with
     | .err _ _ => false
     | .ok stCellAcc =>
       match miriRegisterFnEntryArg miriMem16Live stCellAcc 1 1 2 0
           .mutable true true 0 8 with
       | .err _ _ => false
       | .ok stBoth =>
         match lookupPermInSeg? stBoth 1 0 1 with
         | none => false
         | some (p1, a1) =>
           match lookupPermInSeg? stBoth 1 0 2 with
           | none => false
           | some (p2, a2) =>
             permEq p1 .cell && a1 && permEq p2 .unique && a2 &&
               match miriExitCallFrame miriMem16Live stBoth 1 with
               | .ok stEnd => stEnd.frames.isEmpty
               | .err _ _ => false) = true :=
  ⟨rfl, rfl, rfl⟩

/-- Synthetic conflict fixture separating forward vs. reverse release. -/
@[expose] def syntheticConflictState : MiriTbState :=
  { frames := [{ frameId := 1, protectedTags := [(1, 1), (1, 2)] }]
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [1, 2] },
            { tag := 1, parent := some 0, children := [] },
            { tag := 2, parent := some 0, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 1, loc := ⟨.unique, true, .none⟩ },
                 { tag := 2, loc := ⟨.frozen, true, .read⟩ }] }] }] }

/-- Canary 6 (`[]`): on an explicit synthetic state containing both protected
`tag 1` (`.unique`) and protected `tag 2` (`.frozen`) on `[0, 8)` (not claimed
reachable through `miriRegisterFnEntryArg`, which rejects the second retag per
Canary 2), forward release `[(1, 1), (1, 2)]` traps on `tag 2` (`.frozen`)
whereas reversed release traps on `tag 1` (`.unique`). -/
theorem canary_forward_vs_reverse_release_order_separates_conflict_state :
    isProtectedDisabledErr 2 .frozen
      (miriReleaseTagListForward miriMem16Live syntheticConflictState
        [(1, 1), (1, 2)]) = true ∧
    isProtectedDisabledErr 1 .unique
      (miriReleaseTagListReverse miriMem16Live syntheticConflictState
        [(1, 1), (1, 2)]) = true :=
  ⟨rfl, rfl⟩

/-- Negative fixture with mid-tree dangling `parent = some 99`. -/
@[expose] def danglingParentState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [1] },
            { tag := 1, parent := some 99, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 1, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Negative fixture exhausting `tree.length` fuel on dangling root parent. -/
@[expose] def fullLenDanglingState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := some 99, children := [1] },
            { tag := 1, parent := some 0, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 1, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Negative fixture covering only `[0, 4)` of an `[0, 8)` access. -/
@[expose] def gappedSegState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree := [{ tag := 0, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 4
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Negative fixture with duplicate overlapping `[0, 4)` segments. -/
@[expose] def overlappingSegState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree := [{ tag := 0, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 4
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] },
            { offset := 0
              size := 4
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Negative fixture missing `tag 1` in its covered `[0, 8)` segment. -/
@[expose] def missingSegEntryState : MiriTbState :=
  { frames := [{ frameId := 1, protectedTags := [(1, 1)] }]
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [1] },
            { tag := 1, parent := some 0, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Single-cause fail-closed negative regression suite (`[]`):
1. missing allocation tree on `miriPerformRangedAccess` -> `.uncoveredRange 99`;
2. unknown actor tag in `miriPerformSegmentAccess` -> `.missingTag 99`;
3. unknown actor tag on zero-size `miriPerformRangedAccess` -> `.missingTag 99`;
4. dangling parent tag `99` in `miriPerformRangedAccess` (mid-tree and
   full-length `tree.length` chains) -> `.missingTag 99`;
5. uncovered range gap `[0, 8)` over `[0, 4)` -> `.uncoveredRange 1`;
6. overlapping duplicate segments `[0, 4) + [0, 4)` -> `.uncoveredRange 1`;
7. out-of-bounds `.cell` reborrow `[100, 108)` -> `.uncoveredRange 1`;
8. unknown frame on `miriRegisterFnEntryArg` and `miriExitCallFrame` ->
   `.missingFrame 99`;
9. duplicate `newTag` in `miriReborrowTag` -> `.duplicateTag 0`;
10. non-initial permissions in `miriInitialInsideLoc` / `miriInitialOutsideLoc`
    -> `.nonInitialPerm`;
11. dead or missing allocation in `miriReborrowTag` -> `.deadOrMissingAlloc`;
12. missing tree, missing topology tag, or missing segment entry in
    `miriReleaseOneProtector` -> `.uncoveredRange` / `.missingTag`;
13. `.unique` reborrow on `.shared` allocation -> `.writeToReadOnly 1`;
14. lazy non-accessed `.unique` -> `.error (.invalidLazyState 5)`;
15. dead allocation in `miriExitCallFrame` skips release without UB, while a
    missing allocation fails closed with `.deadOrMissingAlloc 1`;
16. forbidden child write on protected `ReservedFrz true` fails with
    `.childAccessForbidden` AND commits `.none` SIFA (`NormalTree.lean:77-93`);
17. empty byte ranges (`size = 0` or `seg.size = 0`) never overlap in
    `miriSegmentOverlaps`, and zero-size `miriPerformRangedAccess` at an
    interior offset preserves `segments.length = 1`.
-/
theorem canary_miriTreeBorrows_negative_fail_closed_tests :
    isUncoveredErr 99
      (miriPerformRangedAccess miriTbRoot16 99 0 0 4 .read
        .visitChildrenOfAccessed) = true ∧
    isMissingTagErr 99
      (miriPerformSegmentAccess sifaGrandchildTree [] 99 .write
        .visitChildrenOfAccessed sifaGrandchildSeg) = true ∧
    isMissingTagErr 99
      (miriPerformRangedAccess miriTbRoot16 1 99 0 0 .read
        .visitChildrenOfAccessed) = true ∧
    isMissingTagErr 99
      (miriPerformRangedAccess danglingParentState 1 1 0 8 .read
        .visitChildrenOfAccessed) = true ∧
    isMissingTagErr 99
      (miriPerformRangedAccess fullLenDanglingState 1 1 0 8 .read
        .visitChildrenOfAccessed) = true ∧
    isUncoveredErr 1
      (miriPerformRangedAccess gappedSegState 1 0 0 8 .read
        .visitChildrenOfAccessed) = true ∧
    isUncoveredErr 1
      (miriPerformRangedAccess overlappingSegState 1 0 0 8 .read
        .visitChildrenOfAccessed) = true ∧
    isUncoveredErr 1
      (miriReborrowTag miriMem16Live miriTbRoot16 none 1 1 0 .cell .cell
        100 8) = true ∧
    isMissingFrameErr 99
      (miriRegisterFnEntryArg miriMem16Live miriTbRoot16 99 1 1 0 .mutable
        true true 0 8) = true ∧
    isMissingFrameErr 99
      (miriExitCallFrame miriMem16Live miriTbRoot16 99) = true ∧
    isDuplicateTagErr 0
      (miriReborrowTag miriMem16Live miriTbRoot16 none 1 0 0 .frozen .frozen
        0 8) = true ∧
    miriInitialInsideLoc 5 .disabled true =
      .error (.nonInitialPerm 5 .disabled) ∧
    miriInitialInsideLoc 5 (.reservedFrz true) false =
      .error (.nonInitialPerm 5 (.reservedFrz true)) ∧
    miriInitialOutsideLoc 5 .disabled false =
      .error (.nonInitialPerm 5 .disabled) ∧
    isDeadOrMissingAllocErr 1
      (miriReborrowTag miriMem16Dead miriTbRoot16 none 1 1 0 .frozen .frozen
        0 8) = true ∧
    isDeadOrMissingAllocErr 99
      (miriReborrowTag miriMem16Live miriTbRoot16 none 99 1 0 .frozen .frozen
        0 8) = true ∧
    isUncoveredErr 99
      (miriReleaseOneProtector miriTbRoot16 99 0) = true ∧
    isMissingTagErr 99
      (miriReleaseOneProtector miriTbRoot16 1 99) = true ∧
    isMissingTagErr 1
      (miriReleaseOneProtector missingSegEntryState 1 1) = true ∧
    isWriteToReadOnlyErr 1
      (miriRegisterFnEntryArg miriMem16Shared
        miriTbFrame1 1 1 1 0 .mutable true true 0 8) =
        true ∧
    miriNewNonAccessed 5 .unique .none = .error (.invalidLazyState 5) ∧
    (match miriExitCallFrame miriMem16Dead syntheticConflictState 1 with
     | .ok stEnd => stEnd.frames.isEmpty
     | .err _ _ => false) = true ∧
    isDeadOrMissingAllocErr 1
      (miriExitCallFrame ⟨0, []⟩ syntheticConflictState 1) = true ∧
    miriPerformLocAccess 7 ⟨.reservedFrz true, true, .read⟩ .write
      .localAccess true =
      .err ⟨.reservedFrz true, true, .none⟩
        (.childAccessForbidden 7 (.reservedFrz true)) ∧
    miriSegmentOverlaps 4 0 { offset := 0, size := 8, entries := [] } =
      false ∧
    miriSegmentOverlaps 0 8 { offset := 4, size := 0, entries := [] } =
      false ∧
    (match miriPerformRangedAccess miriTbRoot16 1 0 4 0 .read
         .visitChildrenOfAccessed with
     | .ok stZst =>
       match miriFindAllocTree? 1 stZst.allocTrees with
       | some t => Nat.beq t.segments.length 1
       | none => false
     | .err _ _ => false) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two-root fixture (roots `0` and `5`) sharing segment `[0, 8)`. -/
@[expose] def twoRootState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [] },
            { tag := 5, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 5, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Checks whether `r` failed with `.duplicateFrame fid`. -/
@[expose] def isDuplicateFrameErr (fid : Nat) (r : MiriTbResult MiriTbState) :
    Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .duplicateFrame ef => Nat.beq ef fid
    | .multipleRoots _ => false
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Checks whether `r` failed with `.multipleRoots t`. -/
@[expose] def isMultipleRootsErr {α : Type} (t : Nat) (r : MiriTbResult α) :
    Bool :=
  match r with
  | .ok _ => false
  | .err _ e =>
    match e with
    | .multipleRoots et => Nat.beq et t
    | .duplicateFrame _ => false
    | .childAccessForbidden _ _ => false
    | .protectedDisabled _ _ => false
    | .impossibleProtectedReservedIM _ => false
    | .invalidLazyState _ => false
    | .nonInitialPerm _ _ => false
    | .duplicateTag _ => false
    | .missingFrame _ => false
    | .deadOrMissingAlloc _ => false
    | .writeToReadOnly _ => false
    | .missingTag _ => false
    | .uncoveredRange _ => false

/-- Canary 8 (`[]`):
1. `miriBeginFrame` rejects a duplicate frame ID with `.duplicateFrame 1`
   while a fresh ID `2` succeeds.
2. A protected reborrow on a dead allocation, and a protected reborrow whose
   parent access traps (Canary 2), both return an error state that already
   lists the new tag as protected (`RetagPipeline.lean:290-319`).
3. A concrete access on the two-root `twoRootState` fails closed with
   `.multipleRoots 0`, while single-root fixtures are unaffected. -/
theorem canary_frame_protector_and_multi_root_fail_closed :
    isDuplicateFrameErr 1 (miriBeginFrame miriTbFrame1 1) = true ∧
    (match miriBeginFrame miriTbFrame1 2 with
     | .ok st => Nat.beq st.frames.length 2
     | .err _ _ => false) = true ∧
    isDeadOrMissingAllocErr 1
      (miriReborrowTag miriMem16Dead miriTbFrame1 (some 1) 1 1 0 .frozen
        .frozen 0 8) = true ∧
    miriProtectedTagsOnAlloc 1
      (unwrapTb (miriReborrowTag miriMem16Dead miriTbFrame1 (some 1) 1 1 0
        .frozen .frozen 0 8)).frames = [1] ∧
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true true 0 8)
     isProtectedDisabledErr 1 .unique
       (miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0 .shared true false
         4 8)) = true ∧
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true true 0 8)
     miriProtectedTagsOnAlloc 1
       (unwrapTb (miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0 .shared
         true false 4 8)).frames) = [1, 2] ∧
    miriTreeHasMultipleRoots [{ tag := 0, parent := none, children := [] }] =
      false ∧
    isMultipleRootsErr 0
      (miriPerformRangedAccess twoRootState 1 0 0 8 .write
        .visitChildrenOfAccessed) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.MiriTreeBorrows

end
