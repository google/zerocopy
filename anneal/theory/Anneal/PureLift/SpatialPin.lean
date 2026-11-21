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
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph

public section

namespace Anneal.PureLift

/-!
# Hybrid Functional-Spatial Memory Pinning (`SpatialPin`)

Bridges pure functional loan-graph evaluation and localized spatial memory
reasoning for `unsafe` pointer/slice operations (`MaybeUninit` initialization,
`zerocopy` byte casts, and raw-pointer splitting):

- `freezeToSpatialInState` exports an active, unborrowed mutable loan into a
  disjoint `SpatialBlock Val` using a lawful `SpatialCodec Val`, transitioning
  the loan's phase to `LoanPhase.spatialPinned bid codec` while preserving its
  `BackTarget Val`.
- `mutateSpatialInState` mutates only the target `SpatialBlock Val` (checking
  provenance and write permission), leaving all unpinned pure loans in
  `st.loans` untouched without requiring spatial frame proofs for pure locals.
- `reabsorbFromSpatialInState` rejects any block containing `.uninit` cells
  (`hasUninitCell`), decodes the spatial block's cells back into a pure value
  using the original `pinnedCodec` stored in `LoanPhase.spatialPinned`, restores
  the loan's phase to `.activeMut`, and removes the spatial block from
  `st.spatial`.
- `SpatialTriple` and `spatial_frame_law` provide constructive separation-logic
  framing over the spatial heaplet `List (SpatialBlock Val)`.
- `Anneal.PureLift.SpatialMem` connects this discipline to
  `Trusted.MirSemantics.MemoryState`, `SpatialTargetSpec`-checked
  `LocalSlot.indirect` promotion, uninitialized aggregate padding masks
  (`TypedSpatialMemCodec`), per-byte `AllocByte` pointer provenance, and
  post-reabsorption byte and immediate-slot synchronization
  (`freezePaddedToMem`, `mutatePaddedInMem`, `reabsorbPaddedFromMem`,
  `writePaddedSymPlace`, `endPaddedLoan`, `evalPaddedMirOperand`,
  `deallocatePromotedLocal`).
-/

/-- Canonical single-cell value codec mapping `v` to `[.init v]` and rejecting
`.uninit` or multi-cell slices upon reabsorption. -/
@[expose] def valueCellCodec {Val : Type} : SpatialCodec Val where
  codecId := 0
  encode v := [.init v]
  decode cells :=
    match cells with
    | [.init v] => some v
    | _ => none
  decode_encode _ := rfl

/-- Round-trip law for a `SpatialCodec` (guaranteed for every `c : SpatialCodec
Val` by `c.decode_encode`). -/
@[expose] def LawfulCodec {Val : Type} (c : SpatialCodec Val) : Prop :=
  ∀ v : Val, c.decode (c.encode v) = some v

theorem valueCellCodec_lawful {Val : Type} :
    LawfulCodec (@valueCellCodec Val) :=
  (@valueCellCodec Val).decode_encode

/-- Constructive separation-logic assertion over a spatial heaplet. -/
@[expose] def SpatialProp (Val : Type) : Type :=
  List (SpatialBlock Val) → Prop

@[expose] def spatialEmp {Val : Type} : SpatialProp Val :=
  fun blocks => blocks = []

@[expose] def spatialPointsTo {Val : Type} (bid : BlockId) (perm : SpatialPerm)
    (cells : List (CellVal Val)) : SpatialProp Val :=
  fun blocks =>
    match blocks with
    | [b] =>
      b.blockId = bid ∧ b.perm = perm ∧
      b.activeSubSplits = 0 ∧ b.cells = cells
    | _ => False

/-- Heaplets `h1` and `h2` are disjoint when no block of one shares a
`blockId` or an `originLoan` with a block of the other: two blocks pinned from
the same loan are two representations of one allocation (see
`countBlocksForLoan`), so they must never be framed apart. -/
@[expose] def blocksDisjoint {Val : Type} (h1 h2 : List (SpatialBlock Val)) : Prop :=
  ∀ b1 b2, b1 ∈ h1 → b2 ∈ h2 →
    b1.blockId ≠ b2.blockId ∧ b1.originLoan ≠ b2.originLoan

@[expose] def spatialSepConj {Val : Type} (P Q : SpatialProp Val) : SpatialProp Val :=
  fun blocks =>
    Exists fun h1 => Exists fun h2 =>
      blocks = h1 ++ h2 ∧ blocksDisjoint h1 h2 ∧ P h1 ∧ Q h2

/-- Local Hoare triple over the spatial heaplet `List (SpatialBlock Val)`. -/
@[expose] def SpatialTriple {Val : Type} (Pre : SpatialProp Val)
    (cmd : List (SpatialBlock Val) → Option (List (SpatialBlock Val)))
    (Post : SpatialProp Val) : Prop :=
  ∀ h hFrame,
    blocksDisjoint h hFrame →
    Pre h →
    Exists fun h' =>
      cmd (h ++ hFrame) = some (h' ++ hFrame) ∧
      blocksDisjoint h' hFrame ∧ Post h'

/-- Constructive separation-logic frame theorem for spatial commands. -/
theorem spatial_frame_law {Val : Type} (Pre Post Frame : SpatialProp Val)
    (cmd : List (SpatialBlock Val) → Option (List (SpatialBlock Val)))
    (hTriple : SpatialTriple Pre cmd Post) :
    ∀ h, spatialSepConj Pre Frame h →
      Exists fun hOut =>
        cmd h = some hOut ∧ spatialSepConj Post Frame hOut := by
  intro h hSep
  cases hSep with
  | intro h1 hRest =>
    cases hRest with
    | intro h2 hConj =>
      have hEq : h = h1 ++ h2 := hConj.1
      have hDisj : blocksDisjoint h1 h2 := hConj.2.1
      have hPre : Pre h1 := hConj.2.2.1
      have hFr : Frame h2 := hConj.2.2.2
      have hStep := hTriple h1 h2 hDisj hPre
      cases hStep with
      | intro h1' hPost =>
        refine ⟨h1' ++ h2, ?_⟩
        rw [hEq]
        exact ⟨hPost.1,
          ⟨h1', ⟨h2, ⟨rfl, ⟨hPost.2.1, ⟨hPost.2.2, hFr⟩⟩⟩⟩⟩⟩

/-- Count occurrences of spatial block ID `bid` in `blocks`. -/
@[expose] def countSpatialBlockId {Val : Type} (bid : BlockId)
    (blocks : List (SpatialBlock Val)) : Nat :=
  blocks.foldr (fun b ih => if b.blockId == bid then ih + 1 else ih) 0

/-- True iff `blocks` already contains a `SpatialBlock` with `blockId == bid`.
-/
@[expose] def hasSpatialBlockId {Val : Type} (bid : BlockId)
    (blocks : List (SpatialBlock Val)) : Bool :=
  countSpatialBlockId bid blocks != 0

/-- Count spatial blocks in `blocks` whose `originLoan` is `lid`. A loan may
own at most one spatial block, otherwise reabsorbing one block would leave a
second mutable representation of the same allocation. -/
@[expose] def countBlocksForLoan {Val : Type} (lid : LoanId)
    (blocks : List (SpatialBlock Val)) : Nat :=
  blocks.foldr (fun b n => if b.originLoan == lid then n + 1 else n) 0

/-- Extract the pure `Val` payloads from all `.init` cells in `cells`,
ignoring `.uninit` and `.rawByte` cells (which hold no `Val`). -/
@[expose] def initCellVals {Val : Type} (cells : List (CellVal Val)) : List Val :=
  cells.foldr
    (fun c acc =>
      match c with
      | .init v => v :: acc
      | .uninit => acc
      | .rawByte _ => acc)
    []

/-- Concatenate `f v` across all `.init` cell payloads in `cells` (returning
`some []` definitionally for blocks of `.rawByte` / `.uninit` cells), or
`none` if `f` returns `none` for any `.init` value. -/
@[expose] def collectInitCells {Val α : Type} (f : Val → Option (List α))
    (cells : List (CellVal Val)) : Option (List α) :=
  (initCellVals cells).foldr
    (fun v acc =>
      match f v, acc with
      | some rs, some rest => some (rs ++ rest)
      | _, _ => none)
    (some [])

/-- True iff every `.init` cell in `cells` is accounted for by the handles
already held in `srcVal` (`replaceableVals`). Blocks without `.init` cells
(such as `[.rawByte ...]`) carry no handles and return `true` definitionally
(`rfl`) without inspecting `srcVal`. -/
@[expose] def cellsAccountedByVal {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (srcVal : Val)
    (cells : List (CellVal Val)) : Bool :=
  match initCellVals cells with
  | [] => true
  | cellVals => replaceableVals alg loans [srcVal] cellVals

/-- Extract spatial block `bid` and the remaining blocks in a single pass,
requiring `bid` to occur uniquely in `blocks`. -/
@[expose] def findSpatialBlock {Val : Type} (blocks : List (SpatialBlock Val))
    (bid : BlockId) : Option (SpatialBlock Val × List (SpatialBlock Val)) :=
  match
    blocks.foldr
      (fun b
           (acc :
             Bool × Option (SpatialBlock Val) × List (SpatialBlock Val)) =>
        match acc with
        | (dup, foundOpt, rest) =>
          if b.blockId == bid then
            match foundOpt with
            | some _ => (true, foundOpt, rest)
            | none => (dup, some b, rest)
          else
            (dup, foundOpt, b :: rest))
      (false, none, [])
  with
  | (false, some found, updated) => some (found, updated)
  | _ => none

/-- Update spatial block `bid` in place within `blocks` (preserving heaplet
block ordering), checking uniqueness of `bid`, provenance tag `tag`,
`.readWrite` permission, zero active sub-splits (`b.activeSubSplits == 0`), and
size preservation (`newCells.length == b.cells.length`). -/
@[expose] def mutateSpatialBlockAt {Val : Type} (bid : BlockId) (tag : Nat)
    (newCells : List (CellVal Val)) (blocks : List (SpatialBlock Val)) :
    Option (List (SpatialBlock Val)) :=
  match
    blocks.foldr
      (fun b (acc : Bool × Bool × List (SpatialBlock Val)) =>
        match acc with
        | (dup, found, rest) =>
          if b.blockId == bid then
            if found then
              (true, true, rest)
            else
              let writable : Bool :=
                match b.perm with
                | .readWrite => true
                | .readOnly => false
              if b.provenanceTag == tag && writable &&
                 b.activeSubSplits == 0 &&
                 newCells.length == b.cells.length then
                let b' : SpatialBlock Val :=
                  ⟨b.blockId, b.originLoan, b.perm, b.provenanceTag,
                   b.activeSubSplits, newCells⟩
                (dup, true, b' :: rest)
              else
                (true, true, rest)
          else
            (dup, found, b :: rest))
      (false, false, [])
  with
  | (false, true, updated) => some updated
  | _ => none

/-- Export active mutable loan `lid` into a fresh `SpatialBlock` using `codec`,
transitioning `lid`'s phase to `.spatialPinned bid codec` while preserving
`lid`'s backward target. Rejects any encoding that produces `.uninit` cells,
introduces handles into `.init` cells beyond `e.cell.val`
(`cellsAccountedByVal`), or collides with `st.nextSpatialTag`. -/
@[expose] def freezeToSpatialInState {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (codec : SpatialCodec Val) (st : SymState Val) :
    EvalOutcome (SymState Val) :=
  if !hasUniqueLoanId lid st.loans then .fail
  else
    match findLoan lid st.loans with
    | none => .fail
    | some e =>
      if !e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
         !noActiveChildLoanEdgesIn alg lid st.loans ||
         !noActiveChildRegionEdges lid st.regionGroups then
        .fail
      else
        let cells := codec.encode e.cell.val
        if hasUninitCell cells ||
           !cellsAccountedByVal alg st.loans e.cell.val cells then
          .fail
        else
          match st with
          | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
            if hasSpatialBlockId tag sp || countBlocksForLoan lid sp != 0 then
              .fail
            else
              let bid := tag
              let loans' := updateLoan lid
                (fun x =>
                  ⟨x.id, .spatialPinned bid codec, x.cell, x.target⟩)
                loans
              let blk : SpatialBlock Val :=
                ⟨bid, lid, .readWrite, bid, 0, cells⟩
              .ok ⟨locals, loans', rgs, deps, sp ++ [blk], tag + 1⟩

/-- Mutate the cells of spatial block `bid` in place after checking provenance
tag, write permission, and cell-count preservation (`newCells.length ==
blk.cells.length`). Leaves all pure loans in `st.loans` and the ordering of
`st.spatial` unchanged. -/
@[expose] def mutateSpatialInState {Val : Type} (bid : BlockId) (tag : Nat)
    (newCells : List (CellVal Val)) (st : SymState Val) :
    EvalOutcome (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, nextTag⟩ =>
    match mutateSpatialBlockAt bid tag newCells sp with
    | some sp' => .ok ⟨locals, loans, rgs, deps, sp', nextTag⟩
    | none => .fail

/-- Reabsorb spatially pinned loan `lid` back into the pure loan graph using
the original `pinnedCodec` bound in `LoanPhase.spatialPinned`. Rejects any
block containing `.uninit` cells (`hasUninitCell`), un-accounted `.init` cell
handles (`cellsAccountedByVal`), fabricated decoded handles (`replaceableVal`),
duplicate loan IDs, mismatched codec IDs, `.readOnly` spatial blocks, or
unmerged spatial sub-splits. -/
@[expose] def reabsorbFromSpatialInState {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (codec : SpatialCodec Val) (st : SymState Val) :
    EvalOutcome (SymState Val) :=
  if !hasUniqueLoanId lid st.loans then .fail
  else
    match findLoan lid st.loans with
  | none => .fail
  | some e =>
    match e.phase with
    | .spatialPinned bid pinnedCodec =>
      if pinnedCodec.codecId != codec.codecId then .fail
      else
        match findSpatialBlock st.spatial bid with
        | none => .fail
        | some (blk, restSpatial) =>
          let writable : Bool :=
            match blk.perm with
            | .readWrite => true
            | .readOnly => false
          if blk.originLoan == lid && blk.provenanceTag == bid && writable &&
             countBlocksForLoan lid restSpatial == 0 &&
             blk.activeSubSplits == 0 &&
             !hasUninitCell blk.cells &&
             cellsAccountedByVal alg st.loans e.cell.val blk.cells then
            match pinnedCodec.decode blk.cells with
            | none => .fail
            | some v' =>
              -- The cells are written by `mutateSpatialInState` callers, so
              -- the decoded value must not introduce borrow handles the
              -- pinned value did not hold.
              if !replaceableVal alg st.loans e.cell.val v' then .fail
              else
              match st with
              | ⟨locals, loans, rgs, deps, _, nextTag⟩ =>
                let loans' := updateLoan lid
                  (fun x => ⟨x.id, .activeMut, ⟨v', x.cell.perm⟩, x.target⟩)
                  loans
                .ok ⟨locals, loans', rgs, deps, restSpatial, nextTag⟩
          else
            .fail
    | _ => .fail

/-!
## Kernel-Checked Tests for `SpatialPin`
-/

/-- Codec that satisfies `decode_encode` on initialized values, used to test
that `reabsorbFromSpatialInState` still rejects `.uninit` cells even if a
codec's `decode` function would accept `.uninit`. -/
@[expose] def permissiveUninitCodec : SpatialCodec LensTestVal where
  codecId := 1
  encode v := [.init v]
  decode cells :=
    match cells with
    | [.init v] => some v
    | [.uninit] => some (.atom 999)
    | _ => none
  decode_encode _ := rfl

/-- Second codec sharing `codecId = 0` with `valueCellCodec` (encoding `v` as
a 2-cell header `[.rawByte 1, .init v]` while decoding `[.init v]` to `.atom
777`), used to verify that `reabsorbFromSpatialInState` decodes using the
original `pinnedCodec` bound in `LoanPhase.spatialPinned` rather than a forged
codec with the same `codecId`. -/
@[expose] def collidingIdCodec : SpatialCodec LensTestVal where
  codecId := 0
  encode v := [.rawByte 1, .init v]
  decode cells :=
    match cells with
    | [.rawByte 1, .init v] => some v
    | [.init _] => some (.atom 777)
    | _ => none
  decode_encode _ := rfl

/-- Freezing and immediately reabsorbing an untouched loan preserves its value
and binds decoding to the original `pinnedCodec`, ignoring any colliding codec
passed at reabsorption. -/
theorem spatial_roundtrip_and_codec_binding_test :
    let v : LensTestVal := .node (.atom 3) (.ref 9 [])
    let st0 : SymState LensTestVal :=
      { locals := [⟨v, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩
          , ⟨9, .activeMut, ⟨.atom 0, .unborrowed⟩, .rootParam 9⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    match freezeToSpatialInState lensTestValAlg 0 valueCellCodec st0 with
    | .ok stPinned =>
      match reabsorbFromSpatialInState lensTestValAlg 0
          collidingIdCodec stPinned with
      | .ok stReabsorbed =>
        match findLoan 0 stReabsorbed.loans with
        | some e =>
          e.cell.val = v ∧
          e.phase.isActiveMut = true ∧
          stReabsorbed.spatial.isEmpty = true
        | none => False
      | .fail => False
    | .fail => False :=
  ⟨rfl, rfl, rfl⟩

/-- `reabsorbFromSpatialInState` rejects `.uninit` cells even when the pinned
codec's `decode` function returns `some` on `[.uninit]`. -/
theorem spatial_rejects_uninit_even_with_permissive_codec :
    let st0 : SymState LensTestVal :=
      { locals := [⟨.atom 42, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 42, .unborrowed⟩,
                    .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    match freezeToSpatialInState lensTestValAlg 0 permissiveUninitCodec st0 with
    | .ok stPinned =>
      match mutateSpatialInState 0 0 [.uninit] stPinned with
      | .ok stUninit =>
        reabsorbFromSpatialInState lensTestValAlg 0
            permissiveUninitCodec stUninit = .fail
      | .fail => False
    | .fail => False := rfl

/-- `mutateSpatialInState` rejects wrong provenance tags and `.readOnly` blocks,
and `reabsorbFromSpatialInState` rejects mismatched `codecId` and non-zero
`activeSubSplits`. -/
theorem spatial_negative_guards_tests :
    let st0 : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩,
                    .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stShared : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩]
        loans := [⟨0, .activeShared, ⟨.atom 10, .unborrowed⟩,
                    .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stWithChild : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .mutLocked 1⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 10, .unborrowed⟩,
              .direct (.parentLoan 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stWithChildEdgeOnly : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 10, .unborrowed⟩,
              .direct (.parentLoan 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let uninitEncodingCodec : SpatialCodec LensTestVal :=
      { codecId := 30
        encode := fun v => [.uninit, .init v]
        decode := fun cs =>
          match cs with
          | [.uninit, .init v] => some v
          | _ => none
        decode_encode := fun _ => rfl }
    -- 1. Freezing nonexistent loan, `.activeShared` loan, loan with active
    -- child (in `PermTree` or child loan edge), or codec that emits `.uninit`
    -- all fail:
    freezeToSpatialInState lensTestValAlg 99 valueCellCodec st0 = .fail ∧
    freezeToSpatialInState lensTestValAlg 0 valueCellCodec stShared = .fail ∧
    freezeToSpatialInState lensTestValAlg 0 valueCellCodec stWithChild = .fail ∧
    freezeToSpatialInState lensTestValAlg 0
        valueCellCodec stWithChildEdgeOnly = .fail ∧
    freezeToSpatialInState lensTestValAlg 0 uninitEncodingCodec st0 = .fail ∧
    reabsorbFromSpatialInState lensTestValAlg 0 valueCellCodec st0 = .fail ∧
    -- 2. Mutable pinned block rejects double-freeze, wrong block ID, wrong tag,
    -- `.readOnly` permission, non-zero `activeSubSplits`, decode failure on
    -- multi-cell slice, and mismatched `codecId`:
    (match freezeToSpatialInState lensTestValAlg 0 valueCellCodec st0 with
     | .ok stPinned =>
       let stReadOnly : SymState LensTestVal :=
         { stPinned with
           spatial :=
             stPinned.spatial.map (fun b => { b with perm := .readOnly }) }
       let stSubSplit : SymState LensTestVal :=
         { stPinned with
           spatial :=
             stPinned.spatial.map (fun b => { b with activeSubSplits := 1 }) }
       let stForgedTag : SymState LensTestVal :=
         { stPinned with
           spatial :=
             stPinned.spatial.map (fun b => { b with provenanceTag := 99 }) }
       freezeToSpatialInState lensTestValAlg 0 valueCellCodec stPinned = .fail ∧
       mutateSpatialInState 99 0 [.init (.atom 20)] stPinned = .fail ∧
       mutateSpatialInState 0 99 [.init (.atom 20)] stPinned = .fail ∧
       mutateSpatialInState 0 0 [.init (.atom 20)] stReadOnly = .fail ∧
       mutateSpatialInState 0 0 [.init (.atom 20)] stSubSplit = .fail ∧
       mutateSpatialInState 0 0
         [.init (.atom 20), .init (.atom 30)] stPinned = .fail ∧
       reabsorbFromSpatialInState lensTestValAlg 0
           valueCellCodec stReadOnly = .fail ∧
       reabsorbFromSpatialInState lensTestValAlg 0
           valueCellCodec stSubSplit = .fail ∧
       reabsorbFromSpatialInState lensTestValAlg 0
           valueCellCodec stForgedTag = .fail ∧
       reabsorbFromSpatialInState lensTestValAlg 0
           permissiveUninitCodec stPinned = .fail ∧
       (match mutateSpatialInState 0 0 [.rawByte 5] stPinned with
        | .ok stRawByte =>
          reabsorbFromSpatialInState lensTestValAlg 0
              valueCellCodec stRawByte = .fail
        | .fail => False)
     | .fail => False) ∧
    -- 3. `freezeToSpatialInState` rejects a duplicate `nextSpatialTag`, and
    -- `mutateSpatialInState` updates the target block in place without
    -- reordering `st.spatial`:
    let stTwoLoans : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 20, .unborrowed⟩,
              .direct (.localReg 1) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match freezeToSpatialInState lensTestValAlg 0
        valueCellCodec stTwoLoans with
     | .ok stPin1 =>
       let stCollidingTag : SymState LensTestVal :=
         { stPin1 with nextSpatialTag := 0 }
       freezeToSpatialInState lensTestValAlg 1
           valueCellCodec stCollidingTag = .fail ∧
       (match freezeToSpatialInState lensTestValAlg 1 valueCellCodec stPin1 with
        | .ok stPin2 =>
          let stDupBlocks : SymState LensTestVal :=
            { stPin2 with
              spatial :=
                stPin2.spatial.map (fun b => { b with blockId := 0 }) }
          let stDupLoans : SymState LensTestVal :=
            { stPin2 with
              loans :=
                stPin2.loans.map (fun e => { e with id := 0 }) }
          mutateSpatialInState 0 0 [.init (.atom 99)] stDupBlocks = .fail ∧
          reabsorbFromSpatialInState lensTestValAlg 0
              valueCellCodec stDupBlocks = .fail ∧
          freezeToSpatialInState lensTestValAlg 0
              valueCellCodec stDupLoans = .fail ∧
          reabsorbFromSpatialInState lensTestValAlg 0
              valueCellCodec stDupLoans = .fail ∧
          match mutateSpatialInState 1 1 [.init (.atom 99)] stPin2 with
          | .ok stMut2 =>
            stMut2.spatial.map (fun b => b.blockId) = [0, 1]
          | .fail => False
        | .fail => False)
     | .fail => False) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩

/-- A loan owns at most one spatial block. Freezing a loan that already owns a
block fails, and reabsorbing fails when another block with the same
`originLoan` remains. -/
theorem spatial_single_block_per_loan_tests :
    let st0 : SymState LensTestVal :=
      { locals := []
        loans :=
          [⟨0, .activeMut, ⟨.atom 5, .unborrowed⟩, .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let extra : SpatialBlock LensTestVal :=
      ⟨7, 0, .readWrite, 7, 0, [.init (.atom 6)]⟩
    (match freezeToSpatialInState lensTestValAlg 0 valueCellCodec st0 with
     | .ok stPinned =>
       reabsorbFromSpatialInState lensTestValAlg 0 valueCellCodec
         { stPinned with spatial := stPinned.spatial ++ [extra] } = .fail ∧
       (match reabsorbFromSpatialInState lensTestValAlg 0
           valueCellCodec stPinned with
        | .ok _ => True
        | .fail => False)
     | .fail => False) ∧
    freezeToSpatialInState lensTestValAlg 0 valueCellCodec
      { st0 with spatial := [extra], nextSpatialTag := 8 } = .fail :=
  ⟨⟨rfl, trivial⟩, rfl⟩

/-- Blocks pinned from the same loan are aliases, so `blocksDisjoint` (and hence
`spatialSepConj`) refuses to separate them even when their block IDs differ. -/
theorem blocksDisjoint_same_origin_loan_tests :
    let b1 : SpatialBlock LensTestVal := ⟨1, 0, .readWrite, 1, 0, []⟩
    let b2 : SpatialBlock LensTestVal := ⟨2, 0, .readWrite, 2, 0, []⟩
    ¬ blocksDisjoint [b1] [b2] :=
  fun h => (h _ _ (List.Mem.head _) (List.Mem.head _)).2 rfl

/-- `reabsorbFromSpatialInState` rejects a spatial cell that decodes to a value
holding a handle to an active mutable loan that the pinned value did not
hold, and reabsorbs a handle-free value. -/
theorem reabsorb_rejects_fabricated_handle_tests :
    let st (v : LensTestVal) : SymState LensTestVal :=
      { locals := [⟨.atom 9, .mutLocked 1⟩]
        loans :=
          [⟨1, .spatialPinned 0 valueCellCodec, ⟨.atom 5, .unborrowed⟩,
            .direct (.localReg 0) []⟩,
           ⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩, .rootParam 3⟩]
        regionGroups := []
        regionDeposits := []
        spatial := [⟨0, 1, .readWrite, 0, 0, [.init v]⟩]
        nextSpatialTag := 1 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    isOk (reabsorbFromSpatialInState lensTestValAlg 1 valueCellCodec
      (st (.ref 3 []))) = false ∧
    isOk (reabsorbFromSpatialInState lensTestValAlg 1 valueCellCodec
      (st (.atom 6))) = true :=
  ⟨rfl, rfl⟩

/-- Freezing and reabsorbing check the loan graph:
1. freezing a loan fails while an active region group borrows from it,
2. freezing fails when the loan ID names two loans, and
3. reabsorbing fails when the block was pinned from a different loan, even
   if its provenance tag matches.
Each case has a succeeding twin. -/
theorem spatial_loan_graph_guard_tests :
    let x0 : OwnerRef := .localReg 0
    let mk (loans : List (LoanEntry LensTestVal))
        (rgs : List (RegionGroupEntry LensTestVal)) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans := loans
        regionGroups := rgs
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let loan0 (v : Nat) : LoanEntry LensTestVal :=
      ⟨0, .activeMut, ⟨.atom v, .unborrowed⟩, .direct x0 []⟩
    let rg (act : Bool) : RegionGroupEntry LensTestVal :=
      ⟨0, act, 9, [(.parentLoan 0, [])], [], [],
       fun _ _ => some ([.atom 7], [])⟩
    let stPinned (origin : LoanId) : SymState LensTestVal :=
      { locals := [⟨.atom 9, .mutLocked 1⟩]
        loans :=
          [⟨1, .spatialPinned 0 valueCellCodec, ⟨.atom 5, .unborrowed⟩,
            .direct x0 []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := [⟨0, origin, .readWrite, 0, 0, [.init (.atom 6)]⟩]
        nextSpatialTag := 1 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    -- 1. Region-group borrow:
    isOk (freezeToSpatialInState lensTestValAlg 0 valueCellCodec
      (mk [loan0 5] [rg true])) = false ∧
    isOk (freezeToSpatialInState lensTestValAlg 0 valueCellCodec
      (mk [loan0 5] [rg false])) = true ∧
    -- 2. Duplicate loan ID:
    isOk (freezeToSpatialInState lensTestValAlg 0 valueCellCodec
      (mk [loan0 5, loan0 6] [])) = false ∧
    isOk (freezeToSpatialInState lensTestValAlg 0 valueCellCodec
      (mk [loan0 5] [])) = true ∧
    -- 3. Block origin:
    isOk (reabsorbFromSpatialInState lensTestValAlg 1 valueCellCodec
      (stPinned 7)) = false ∧
    isOk (reabsorbFromSpatialInState lensTestValAlg 1 valueCellCodec
      (stPinned 1)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Spatial cell handle accounting checks all `.init` cells (even those ignored
by `decode`), while leaving `.rawByte` cells definitionally handle-free:
1. freezing fails when `encode` places a fabricated mutable handle into an
   ignored second `.init` cell,
2. mutating an ignored second `.init` cell after freezing to inject an active
   mutable handle fails reabsorption,
3. valid multi-cell handle-preserving and handle-dropping layouts succeed
   reabsorption, and
4. `.rawByte`-only blocks reduce definitionally to `[]` handles and `true`
   accounting under `rfl`. -/
theorem spatial_cell_handle_accounting_tests :
    let x0 : OwnerRef := .localReg 0
    let loans (v0 : LensTestVal) : List (LoanEntry LensTestVal) :=
      [ ⟨0, .activeMut, ⟨v0, .unborrowed⟩, .direct x0 []⟩
      , ⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩, .rootParam 3⟩
      , ⟨4, .activeMut, ⟨.atom 40, .unborrowed⟩, .rootParam 4⟩ ]
    let stWith (v0 : LensTestVal) : SymState LensTestVal :=
      { locals := [⟨v0, .mutLocked 0⟩]
        loans := loans v0
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let fabricatingExtraCodec : SpatialCodec LensTestVal :=
      { codecId := 40
        encode := fun v => [.init v, .init (.ref 3 [])]
        decode := fun cells =>
          match cells with
          | .init v :: _ => some v
          | _ => none
        decode_encode := fun _ => rfl }
    let ignoredExtraCodec : SpatialCodec LensTestVal :=
      { codecId := 41
        encode := fun v => [.init v, .init (.atom 0)]
        decode := fun cells =>
          match cells with
          | .init v :: _ => some v
          | _ => none
        decode_encode := fun _ => rfl }
    let pairCellCodec : SpatialCodec LensTestVal :=
      { codecId := 42
        encode := fun v =>
          match v with
          | ⟨_, .branch fl fr l r⟩ => [.init ⟨fl, l⟩, .init ⟨fr, r⟩]
          | other => [.init other]
        decode := fun cells =>
          match cells with
          | [.init a, .init b] => some (.node a b)
          | [.init single] => some single
          | _ => none
        decode_encode := fun v => by
          cases v with
          | mk fuel tree => cases tree <;> rfl }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    -- 1. Fabricating extra-cell codec fails at freeze:
    freezeToSpatialInState lensTestValAlg 0
        fabricatingExtraCodec (stWith (.atom 5)) = .fail ∧
    -- 2. Smuggling an active handle in an ignored `.init` cell fails reabsorb:
    (match freezeToSpatialInState lensTestValAlg 0
        ignoredExtraCodec (stWith (.atom 5)) with
     | .ok stPinned =>
       match mutateSpatialInState 0 0
           [.init (.atom 6), .init (.ref 3 [])] stPinned with
       | .ok stMut =>
         reabsorbFromSpatialInState lensTestValAlg 0
             ignoredExtraCodec stMut = .fail
       | .fail => False
     | .fail => False) ∧
    -- 3. Valid multi-cell codecs preserving or dropping handles succeed:
    (match freezeToSpatialInState lensTestValAlg 0
        ignoredExtraCodec (stWith (.ref 3 [])) with
     | .ok stPinned =>
       isOk (reabsorbFromSpatialInState lensTestValAlg 0
         ignoredExtraCodec stPinned) = true
     | .fail => False) ∧
    (match freezeToSpatialInState lensTestValAlg 0
        pairCellCodec (stWith (.node (.ref 3 []) (.ref 4 []))) with
     | .ok stPinned =>
       isOk (reabsorbFromSpatialInState lensTestValAlg 0
         pairCellCodec stPinned) = true ∧
       match mutateSpatialInState 0 0
           [.init (.ref 3 []), .init (.atom 9)] stPinned with
       | .ok stDropped =>
         isOk (reabsorbFromSpatialInState lensTestValAlg 0
           pairCellCodec stDropped) = true
       | .fail => False
     | .fail => False) ∧
    -- 4. `.rawByte`-only blocks reduce definitionally under `rfl`:
    (∀ (b0 b1 : UInt8) (srcVal : LensTestVal),
      collectInitCells (collectHandleRefs lensTestValAlg)
          [.rawByte b0, .rawByte b1] = some [] ∧
      cellsAccountedByVal lensTestValAlg [] srcVal
        [.rawByte b0, .rawByte b1] = true) :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩

end Anneal.PureLift

end
