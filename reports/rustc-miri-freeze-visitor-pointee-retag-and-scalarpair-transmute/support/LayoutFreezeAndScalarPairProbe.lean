-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization Probe: `FreezeVisitor`, `PointeeInfo`/`RetagPolicy`, and `ScalarPair`

Self-contained Lean 4 formalization and equivalence proofs for:
1. **`FreezeVisitor` and Static `TyAndLayout` Freeze Interval Extraction**: Operational model of
   `rust-lang/miri`'s `visit_freeze_sensitive` / `UnsafeCellVisitor` (`src/helpers.rs:469-613`) and
   `proofs-rs/lean-miri`'s `Miri.TreeBorrows.FreezeVisitor`
   (`Miri/TreeBorrows/FreezeVisitor.lean:49-136`), plus a purely static interval-extraction
   algorithm over `TyAndLayout` and proofs of exact agreement across structs with padding,
   multi-variant vs. single-inhabited-variant enums, unions, and zero-sized `UnsafeCell<()>`
   (`in-bounds` vs. `outsidePermission` divergence).
2. **`PointeeInfo` and `RetagPolicy`**: Formal model of `TyAndLayout::pointee_info_at`
   (`compiler/rustc_middle/src/ty/layout.rs:1049-1226`) and Tree Borrows `NewPermission::new` /
   `RetagPolicy.create` (`src/borrow_tracker/tree_borrows/mod.rs:126-221`,
   `Miri/TreeBorrows/RetagPolicy.lean:52-92`), proving how `Unpin ∧ UnsafeUnpin`, `Freeze`,
   `Box<T>`, `Pin<&mut T>`, and `RetagMode` (`Default` vs. `FnEntry`) interact.
3. **`BackendRepr::ScalarPair` `bOffset` and `Transmute`**: Formal model of
   `bOffset = alignTo a.size b.align`, inter-element alignment padding `[a.size .. bOffset)`,
   `read_immediate_from_mplace_raw`, `write_immediate_to_mplace_no_validate`, and
   `copy_op_allow_transmute` (`Rvalue::Cast::Transmute`), proving padding stripping in both
   directions.
-/

namespace FreezeRetagScalarPairProbe

-- ============================================================================
-- Part 1: FreezeVisitor and Static TyAndLayout Freeze Interval Extraction
-- ============================================================================

/-- A contiguous byte interval `[start, start + size)` tagged with `frozen : Bool`
(`true` = `Frozen`, `false` = `UnsafeCell` / interior mutable). -/
structure FreezeInterval where
  start : Nat
  size : Nat
  frozen : Bool
  deriving DecidableEq, Repr

/-- Simplified representation of `rustc_abi::Variants` sufficient for `UnsafeCellVisitor`
and static layout extraction. Note that `rustc_abi` uses `Variants::Single` both for structs/unions
and for enums with a single inhabited variant when `!repr.inhibit_enum_layout_opt()` holds. -/
inductive VariantsShape where
  | Empty
  | Single (index : Nat)
  | Multiple
  deriving DecidableEq, Repr

/-- Simplified representation of `rustc_abi::FieldsShape` together with child field layouts.
For `Arbitrary`, `fieldsInMemoryOrder` lists `(fieldOffset, fieldLayout)` sorted by increasing
byte offset, matching `FieldsShape::Arbitrary::in_memory_order` in
`compiler/rustc_const_eval/src/interpret/visitor.rs:148-153`. -/
inductive FieldsShape (α : Type) where
  | Primitive
  | Union (fields : List α)
  | Array (stride : Nat) (count : Nat) (elem : α)
  | Arbitrary (fieldsInMemoryOrder : List (Nat × α))
  deriving Repr

/-- Static layout tree node corresponding to `rustc_middle::ty::layout::TyAndLayout`. -/
inductive TyLayoutNode where
  | mk
      (size : Nat)
      (isFreeze : Bool)
      (isUnsafeCell : Bool)
      (variants : VariantsShape)
      (fields : FieldsShape TyLayoutNode)
  deriving Repr

namespace TyLayoutNode

def size : TyLayoutNode → Nat
  | .mk s _ _ _ _ => s

def isFreeze : TyLayoutNode → Bool
  | .mk _ f _ _ _ => f

def isUnsafeCell : TyLayoutNode → Bool
  | .mk _ _ u _ _ => u

def variants : TyLayoutNode → VariantsShape
  | .mk _ _ _ v _ => v

def fields : TyLayoutNode → FieldsShape TyLayoutNode
  | .mk _ _ _ _ fs => fs

end TyLayoutNode

/-- Cursor state of `visit_freeze_sensitive` (`src/helpers.rs:487-511`, `FreezeVisitor.lean:49-62`). -/
structure CursorState where
  startAddr : Nat
  curAddr : Nat
  intervals : List FreezeInterval
  deriving DecidableEq, Repr

/-- Exact port of `unsafe_cell_action` (`src/helpers.rs:490-511`, `FreezeVisitor.lean:49-62`). -/
def unsafeCellAction (unsafeCellAddr unsafeCellSize : Nat) (st : CursorState) : CursorState :=
  let frozenSize := unsafeCellAddr - st.curAddr
  let st1 :=
    if frozenSize != 0 then
      { st with
        curAddr := st.curAddr + frozenSize
        intervals := st.intervals ++ [⟨st.curAddr - st.startAddr, frozenSize, true⟩] }
    else
      st
  if unsafeCellSize != 0 then
    { st1 with
      curAddr := st1.curAddr + unsafeCellSize
      intervals := st1.intervals ++ [⟨st1.curAddr - st1.startAddr, unsafeCellSize, false⟩] }
  else
    st1

/-- Closure passed to `UnsafeCellVisitor` (`src/helpers.rs:516-530`, `FreezeVisitor.lean:64-69`):
Notice the guard `if unsafeCellSize != 0`! A zero-sized `UnsafeCell<()>` does NOT invoke
`unsafeCellAction`. -/
def visitorUnsafeCellHook (placeAddr placeSize : Nat) (st : CursorState) : CursorState :=
  if placeSize != 0 then
    unsafeCellAction placeAddr placeSize st
  else
    st

/-- Operational model of `UnsafeCellVisitor::visit_value` and `ValueVisitor::walk_value`
(`src/helpers.rs:562-603`, `visitor.rs:81-188`, `FreezeVisitor.lean:77-118`). -/
def visitFreezeNode (fuel : Nat) (baseAddr : Nat) (node : TyLayoutNode) (st : CursorState) : CursorState :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
    if node.isUnsafeCell then
      visitorUnsafeCellHook baseAddr node.size st
    else if node.isFreeze then
      st
    else match node.fields with
      | .Union _ =>
        visitorUnsafeCellHook baseAddr node.size st
      | _ =>
        match node.variants with
        | .Multiple =>
          visitorUnsafeCellHook baseAddr node.size st
        | .Empty => st
        | .Single _ =>
          match node.fields with
          | .Primitive => st
          | .Union _ => visitorUnsafeCellHook baseAddr node.size st
          | .Array stride count elem =>
            (List.range count).foldl
              (fun acc idx => visitFreezeNode fuel' (baseAddr + idx * stride) elem acc)
              st
          | .Arbitrary fieldsInMemoryOrder =>
            fieldsInMemoryOrder.foldl
              (fun acc (offset, fieldNode) => visitFreezeNode fuel' (baseAddr + offset) fieldNode acc)
              st

/-- Operational model of `visit_freeze_sensitive` (`src/helpers.rs:475-539`, `FreezeVisitor.lean:120-135`). -/
def visitFreezeSensitive (fuel : Nat) (startAddr : Nat) (root : TyLayoutNode) : List FreezeInterval :=
  let init : CursorState := ⟨startAddr, startAddr, []⟩
  let afterWalk := visitFreezeNode fuel startAddr root init
  let finalState := unsafeCellAction (startAddr + root.size) 0 afterWalk
  finalState.intervals

-- ----------------------------------------------------------------------------
-- Purely Static Extraction Algorithm over `TyAndLayout`
-- ----------------------------------------------------------------------------

/-- Step 1 of the static algorithm: collect all non-empty `(offset, size)` byte ranges of
interior-mutable leaves (`UnsafeCell`, `!Freeze` union, or `!Freeze` multi-variant enum/coroutine)
in increasing memory-offset order. -/
def collectUnfrozenRanges (fuel : Nat) (baseOffset : Nat) (node : TyLayoutNode) : List (Nat × Nat) :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if node.isUnsafeCell then
      if node.size != 0 then [(baseOffset, node.size)] else []
    else if node.isFreeze then
      []
    else match node.fields with
      | .Union _ =>
        if node.size != 0 then [(baseOffset, node.size)] else []
      | _ =>
        match node.variants with
        | .Multiple =>
          if node.size != 0 then [(baseOffset, node.size)] else []
        | .Empty => []
        | .Single _ =>
          match node.fields with
          | .Primitive => []
          | .Union _ => if node.size != 0 then [(baseOffset, node.size)] else []
          | .Array stride count elem =>
            (List.range count).flatMap (fun idx =>
              collectUnfrozenRanges fuel' (baseOffset + idx * stride) elem)
          | .Arbitrary fieldsInMemoryOrder =>
            fieldsInMemoryOrder.flatMap (fun (offset, fieldNode) =>
              collectUnfrozenRanges fuel' (baseOffset + offset) fieldNode)

/-- Step 2 of the static algorithm: convert the sorted non-empty unfrozen ranges into the exact
sequence of `FreezeInterval`s emitted by `visit_freeze_sensitive`, sweeping all gaps and padding
into `frozen = true` intervals. -/
def rangesToFreezeIntervalsAux (cursor : Nat) (totalSize : Nat) : List (Nat × Nat) → List FreezeInterval
  | [] =>
    let tailSize := totalSize - cursor
    if tailSize != 0 then [⟨cursor, tailSize, true⟩] else []
  | (ufStart, ufSize) :: rest =>
    let gap := ufStart - cursor
    let pre := if gap != 0 then [⟨cursor, gap, true⟩] else []
    let curr := if ufSize != 0 then [⟨ufStart, ufSize, false⟩] else []
    pre ++ curr ++ rangesToFreezeIntervalsAux (ufStart + ufSize) totalSize rest

def extractStaticFreezeIntervals (fuel : Nat) (root : TyLayoutNode) : List FreezeInterval :=
  rangesToFreezeIntervalsAux 0 root.size (collectUnfrozenRanges fuel 0 root)

-- ----------------------------------------------------------------------------
-- Concrete Test Layouts for Structs, Enums, Unions, and Zero-Sized UnsafeCell
-- ----------------------------------------------------------------------------

/-- Primitive `Freeze` scalar of `sz` bytes (e.g. `u8`, `u32`, `u64`). -/
def primFreezeLayout (sz : Nat) : TyLayoutNode :=
  .mk sz true false (.Single 0) .Primitive

/-- `UnsafeCell<T>` of `sz` bytes (`isFreeze = false`, `isUnsafeCell = true`). -/
def unsafeCellLayout (sz : Nat) : TyLayoutNode :=
  .mk sz false true (.Single 0) .Primitive

/-- `#[repr(C)] struct MixedStruct { a: u8, b: UnsafeCell<u32> }`
(`size = 8`, `a` at `0..1`, padding at `1..4`, `b` at `4..8`). -/
def mixedStructLayout : TyLayoutNode :=
  .mk 8 false false (.Single 0)
    (.Arbitrary [(0, primFreezeLayout 1), (4, unsafeCellLayout 4)])

/-- `#[repr(C)] struct TrailingPadStruct { cell: UnsafeCell<u32>, flag: u8 }`
(`size = 8`, `cell` at `0..4`, `flag` at `4..5`, trailing padding at `5..8`). -/
def trailingPadStructLayout : TyLayoutNode :=
  .mk 8 false false (.Single 0)
    (.Arbitrary [(0, unsafeCellLayout 4), (4, primFreezeLayout 1)])

/-- `#[repr(C, u64)] enum MultiEnum { Frozen(u64), SharedMut(UnsafeCell<u64>) }`
(`size = 16`, tag at `0..8`, payload at `8..16`, `VariantsShape.Multiple`, `isFreeze = false`). -/
def multiEnumLayout : TyLayoutNode :=
  .mk 16 false false .Multiple
    (.Arbitrary [(0, primFreezeLayout 8)])

/-- `enum SingleInhabitedEnum { Active(u32, UnsafeCell<u32>), Dead(Void) }`
Because `Dead(Void)` is uninhabited and `!repr.inhibit_enum_layout_opt()`, `rustc_abi` gives
`SingleInhabitedEnum` `VariantsShape.Single 0`. -/
def singleInhabitedEnumLayout : TyLayoutNode :=
  .mk 8 false false (.Single 0)
    (.Arbitrary [(0, primFreezeLayout 4), (4, unsafeCellLayout 4)])

/-- `#[repr(C)] union UnionWithSmallCell { a: u64, b: ManuallyDrop<UnsafeCell<u32>> }`
(`size = 8`, `isFreeze = false`, `FieldsShape.Union`). -/
def unionWithSmallCellLayout : TyLayoutNode :=
  .mk 8 false false (.Single 0)
    (.Union [primFreezeLayout 8, unsafeCellLayout 4])

/-- `#[repr(C)] union UnionAllFreeze { a: u64, b: u32 }`
(`size = 8`, `isFreeze = true`, `FieldsShape.Union`). -/
def unionAllFreezeLayout : TyLayoutNode :=
  .mk 8 true false (.Single 0)
    (.Union [primFreezeLayout 8, primFreezeLayout 4])

/-- `#[repr(C)] struct WithZstCell(u32, UnsafeCell<()>)`
(`size = 4`, `isFreeze = false`, field 0 is `u32` at `0..4`, field 1 is `UnsafeCell<()>` of size `0` at `4..4`). -/
def withZstCellLayout : TyLayoutNode :=
  .mk 4 false false (.Single 0)
    (.Arbitrary [(0, primFreezeLayout 4), (4, unsafeCellLayout 0)])

/-- Theorem: Inter-field padding `[1..4)` in `MixedStruct` is merged into `[0..4)` with
`frozen = true`, and trailing padding `[5..8)` in `TrailingPadStruct` is merged into `[4..8)` with
`frozen = true`. Static extraction and operational `visitFreezeSensitive` agree identically. -/
theorem thm_mixed_struct_and_trailing_padding :
    visitFreezeSensitive 4 100 mixedStructLayout = [⟨0, 4, true⟩, ⟨4, 4, false⟩] ∧
    extractStaticFreezeIntervals 4 mixedStructLayout = [⟨0, 4, true⟩, ⟨4, 4, false⟩] ∧
    visitFreezeSensitive 4 100 trailingPadStructLayout = [⟨0, 4, false⟩, ⟨4, 4, true⟩] ∧
    extractStaticFreezeIntervals 4 trailingPadStructLayout = [⟨0, 4, false⟩, ⟨4, 4, true⟩] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem: A non-`Freeze` `Variants::Multiple` enum (`MultiEnum`) marks its entire `[0..16)`
extent (including discriminant tag `[0..8)` and `Frozen(u64)` variant payload `[8..16)`) as
`frozen = false`, whereas a single-inhabited-variant enum (`Variants::Single`) recurses into its
inhabited variant and freezes the `u32` field `[0..4)`. -/
theorem thm_multi_variant_vs_single_inhabited_enum :
    visitFreezeSensitive 4 200 multiEnumLayout = [⟨0, 16, false⟩] ∧
    extractStaticFreezeIntervals 4 multiEnumLayout = [⟨0, 16, false⟩] ∧
    visitFreezeSensitive 4 200 singleInhabitedEnumLayout = [⟨0, 4, true⟩, ⟨4, 4, false⟩] ∧
    extractStaticFreezeIntervals 4 singleInhabitedEnumLayout = [⟨0, 4, true⟩, ⟨4, 4, false⟩] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem: A union containing an `UnsafeCell` variant marks its entire `[0..8)` size as
`frozen = false` (even when the `UnsafeCell` variant is smaller than the union), whereas an
all-`Freeze` union marks `[0..8)` as `frozen = true`. -/
theorem thm_union_unsafecell_vs_all_freeze :
    visitFreezeSensitive 4 300 unionWithSmallCellLayout = [⟨0, 8, false⟩] ∧
    extractStaticFreezeIntervals 4 unionWithSmallCellLayout = [⟨0, 8, false⟩] ∧
    visitFreezeSensitive 4 300 unionAllFreezeLayout = [⟨0, 8, true⟩] ∧
    extractStaticFreezeIntervals 4 unionAllFreezeLayout = [⟨0, 8, true⟩] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem: For `(u32, UnsafeCell<()>)`, `isFreeze` is `false`, yet `visitFreezeSensitive`
and `extractStaticFreezeIntervals` both produce `[⟨0, 4, true⟩]` — i.e., all in-bounds bytes `[0..4)`
are marked `frozen = true`! -/
theorem thm_zst_unsafecell_inbounds_frozen :
    withZstCellLayout.isFreeze = false ∧
    visitFreezeSensitive 4 400 withZstCellLayout = [⟨0, 4, true⟩] ∧
    extractStaticFreezeIntervals 4 withZstCellLayout = [⟨0, 4, true⟩] := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Part 2: PointeeInfo, Unpin vs. UnsafeUnpin, and RetagPolicy
-- ============================================================================

inductive Permission where
  | ReservedIM
  | ReservedFrz (conflicted : Bool)
  | Unique
  | Frozen
  | Cell
  | Disabled
  deriving DecidableEq, Repr

inductive ProtectorKind where
  | WeakProtector
  | StrongProtector
  deriving DecidableEq, Repr

inductive RetagMode where
  | None
  | Default
  | FnEntry
  | TwoPhase
  | Raw
  deriving DecidableEq, Repr

inductive ReferenceKind where
  | Shared
  | Mutable
  | Box
  deriving DecidableEq, Repr

structure PointeeFlags where
  isUnpin : Bool
  isUnsafeUnpin : Bool
  isFreeze : Bool
  deriving DecidableEq, Repr

structure FnEntryFlags where
  implicitWrites : Bool
  rustcNoWritable : Bool
  deriving DecidableEq, Repr

structure NewPermission where
  unfreezePermission : Permission
  freezePermission : Permission
  outsidePermission : Permission
  protector : Option ProtectorKind
  deriving DecidableEq, Repr

inductive InitialPermissionPlace where
  | InsideFrozen
  | InsideUnsafeCell
  | Outside
  deriving DecidableEq, Repr

/-- Exact port of `NewPermission::new` (`rust-lang/miri/src/borrow_tracker/tree_borrows/mod.rs:126-221`)
and `Miri.TreeBorrows.RetagPolicy.create` (`Miri/TreeBorrows/RetagPolicy.lean:52-92`). -/
def createNewPermission (pointee : PointeeFlags) (kind : ReferenceKind)
    (mode : RetagMode) (fnEntry : FnEntryFlags := ⟨false, false⟩) : Option NewPermission :=
  if mode == .None then
    none
  else
    let tyIsUnpin := pointee.isUnpin && pointee.isUnsafeUnpin
    let tyIsFreeze := pointee.isFreeze
    if (kind == .Mutable || kind == .Box) && !tyIsUnpin then
      none
    else
      let isProtected := mode == .FnEntry
      let protector :=
        if isProtected then
          some (if kind == .Box then .WeakProtector else .StrongProtector)
        else
          none
      let implicitWritesEnabled :=
        isProtected && fnEntry.implicitWrites && !fnEntry.rustcNoWritable
      let permAt (place : InitialPermissionPlace) : Permission :=
        let frozen :=
          match place with
          | .InsideFrozen => true
          | .InsideUnsafeCell => false
          | .Outside => tyIsFreeze
        match kind, mode with
        | .Mutable, .TwoPhase => .ReservedIM
        | .Mutable, _ | .Box, _ =>
          if implicitWritesEnabled && (place == .InsideFrozen || place == .InsideUnsafeCell) then
            .Unique
          else if isProtected || frozen then
            .ReservedFrz false
          else
            .ReservedIM
        | .Shared, _ =>
          if frozen then .Frozen else .Cell
      some
        { unfreezePermission := permAt .InsideUnsafeCell
          freezePermission := permAt .InsideFrozen
          outsidePermission := permAt .Outside
          protector := protector }

/-- Combine `createNewPermission` with `extractStaticFreezeIntervals` to compute the exact
`(inBoundsIntervals, outsidePermission)` pair for a retagged pointer to `root`. -/
def computeRetagPermissions (fuel : Nat) (root : TyLayoutNode) (pointee : PointeeFlags)
    (kind : ReferenceKind) (mode : RetagMode) (fnEntry : FnEntryFlags := ⟨false, false⟩) :
    Option (List (Nat × Nat × Permission) × Permission × Option ProtectorKind) :=
  match createNewPermission pointee kind mode fnEntry with
  | none => none
  | some policy =>
    let intervals := (extractStaticFreezeIntervals fuel root).map fun iv =>
      let perm := if iv.frozen then policy.freezePermission else policy.unfreezePermission
      (iv.start, iv.size, perm)
    some (intervals, policy.outsidePermission, policy.protector)

/-- Theorem: For `(u32, UnsafeCell<()>)`, retagging a shared reference
`&(u32, UnsafeCell<()>)` gives `Permission.Frozen` on in-bounds bytes `[0..4)` (because
`UnsafeCell<()>` has size 0), but `Permission.Cell` on `outsidePermission` (because
`ty.isFreeze == false`)! And retagging an unprotected `&mut (u32, UnsafeCell<()>)` gives
`Permission.ReservedFrz false` on in-bounds `[0..4)` and `Permission.ReservedIM` on
`outsidePermission`! -/
theorem thm_inbounds_vs_outside_permission_divergence :
    computeRetagPermissions 4 withZstCellLayout ⟨true, true, false⟩ .Shared .Default =
      some ([(0, 4, .Frozen)], .Cell, none) ∧
    computeRetagPermissions 4 withZstCellLayout ⟨true, true, false⟩ .Mutable .Default =
      some ([(0, 4, .ReservedFrz false)], .ReservedIM, none) := by
  exact ⟨rfl, rfl⟩

/-- Theorem: Whenever `!(isUnpin && isUnsafeUnpin)` holds (e.g. `PhantomPinned` or `!UnsafeUnpin`),
neither `Mutable` (`&mut T`, `Pin<&mut T>`) nor `Box` (`Box<T>`, `Pin<Box<T>>`) is retagged in ANY
`RetagMode`, whereas `Shared` (`&T`) IS retagged regardless of `isUnpin`/`isUnsafeUnpin`. -/
theorem thm_not_unpin_skips_mutable_and_box_retag
    (pointee : PointeeFlags) (mode : RetagMode) (fnEntry : FnEntryFlags)
    (hNotUnpin : (pointee.isUnpin && pointee.isUnsafeUnpin) = false) :
    createNewPermission pointee .Mutable mode fnEntry = none ∧
    createNewPermission pointee .Box mode fnEntry = none := by
  cases mode <;> simp [createNewPermission, hNotUnpin]

/-- Theorem: On `FnEntry` with `isUnpin && isUnsafeUnpin = true`:
- `Box<T>` gets `some .WeakProtector`, while `&T` and `&mut T` get `some .StrongProtector`.
- With default Miri settings (`implicitWrites = false`), even when `isFreeze = false`
  (e.g., `Box<UnsafeCell<u32>>` or `&mut UnsafeCell<u32>`), BOTH `unfreezePermission` and
  `outsidePermission` are `.ReservedFrz false` (never `.ReservedIM`), whereas under `Default` mode
  both are `.ReservedIM`! -/
theorem thm_box_and_mut_unsafecell_default_vs_fn_entry :
    createNewPermission ⟨true, true, false⟩ .Box .Default =
      some ⟨.ReservedIM, .ReservedFrz false, .ReservedIM, none⟩ ∧
    createNewPermission ⟨true, true, false⟩ .Box .FnEntry ⟨false, false⟩ =
      some ⟨.ReservedFrz false, .ReservedFrz false, .ReservedFrz false, some .WeakProtector⟩ ∧
    createNewPermission ⟨true, true, false⟩ .Mutable .FnEntry ⟨false, false⟩ =
      some ⟨.ReservedFrz false, .ReservedFrz false, .ReservedFrz false, some .StrongProtector⟩ := by
  exact ⟨rfl, rfl, rfl⟩

/-- Model of `rustc_abi::PointerKind` and `rustc_abi::PointeeInfo`
(`compiler/rustc_abi/src/lib.rs:2359-2391`). -/
inductive PointerKind where
  | SharedRef (frozen : Bool)
  | MutableRef (unpin : Bool)
  | Box (unpin : Bool) (global : Bool)
  deriving DecidableEq, Repr

structure PointeeInfo where
  safe : Option PointerKind
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

/-- Model of `TyAndLayout::ty_and_layout_pointee_info_at` at offset 0
(`compiler/rustc_middle/src/ty/layout.rs:1049-1226`). -/
inductive PointerCarrierTy where
  | RawPtr
  | FnPtr
  | SharedRef (pointeeSize pointeeAlign : Nat) (isFreeze : Bool)
  | MutableRef (pointeeSize pointeeAlign : Nat) (isUnpin isUnsafeUnpin : Bool)
  | BoxAdt (pointeeSize pointeeAlign : Nat) (isUnpin isUnsafeUnpin isGlobal : Bool)
  | SingleVariantWrapperAtZero (inner : PointerCarrierTy) -- e.g. `Pin<P>`, `NonNull<T>`, `Unique<T>`
  | MaybeDanglingWrapper (inner : PointerCarrierTy)
  deriving DecidableEq, Repr

def pointeeInfoAtZero (optimize : Bool) : PointerCarrierTy → Option PointeeInfo
  | .RawPtr | .FnPtr =>
    some ⟨none, 0, 1⟩
  | .SharedRef sz align isFreeze =>
    let frozen := optimize && isFreeze
    some ⟨some (.SharedRef frozen), if frozen then sz else 0, align⟩
  | .MutableRef sz align isUnpin isUnsafeUnpin =>
    let unpin := optimize && isUnpin && isUnsafeUnpin
    some ⟨some (.MutableRef unpin), if unpin then sz else 0, align⟩
  | .BoxAdt sz align isUnpin isUnsafeUnpin isGlobal =>
    let unpin := optimize && isUnpin && isUnsafeUnpin
    some ⟨some (.Box unpin isGlobal), if unpin then sz else 0, align⟩
  | .SingleVariantWrapperAtZero inner =>
    pointeeInfoAtZero optimize inner
  | .MaybeDanglingWrapper inner =>
    match pointeeInfoAtZero optimize inner with
    | none => none
    | some info => some ⟨none, 0, info.align⟩

/-- Theorem: `Pin<&mut T>` (`SingleVariantWrapperAtZero (.MutableRef ...)`) and
`Pin<Box<T>>` (`SingleVariantWrapperAtZero (.BoxAdt ...)`) have the exact same `PointeeInfo` as
`&mut T` and `Box<T>`, whereas `Unique<T>` (`SingleVariantWrapperAtZero (.SingleVariantWrapperAtZero .RawPtr)`)
has `safe = none, size = 0, align = 1`. -/
theorem thm_pointee_info_pin_and_unique (opt : Bool) (sz align : Nat) (u uu g : Bool) :
    pointeeInfoAtZero opt (.SingleVariantWrapperAtZero (.MutableRef sz align u uu)) =
      pointeeInfoAtZero opt (.MutableRef sz align u uu) ∧
    pointeeInfoAtZero opt (.SingleVariantWrapperAtZero (.BoxAdt sz align u uu g)) =
      pointeeInfoAtZero opt (.BoxAdt sz align u uu g) ∧
    pointeeInfoAtZero opt (.SingleVariantWrapperAtZero (.SingleVariantWrapperAtZero .RawPtr)) =
      some ⟨none, 0, 1⟩ := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Part 3: BackendRepr::ScalarPair bOffset, Padding, and Transmute
-- ============================================================================

/-- Round `size` up to the next multiple of `align` (`align > 0`). -/
def alignTo (size align : Nat) : Nat :=
  if align == 0 then size
  else ((size + align - 1) / align) * align

structure ScalarDesc where
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

structure ScalarPairLayout where
  a : ScalarDesc
  b : ScalarDesc
  bOffset : Nat
  totalAlign : Nat
  totalSize : Nat
  deriving DecidableEq, Repr

/-- Exact port of `LayoutData::scalar_pair` (`compiler/rustc_abi/src/layout/simple.rs:94-126`). -/
def mkScalarPairLayout (a b : ScalarDesc) (aggregateAlign : Nat := 1) : ScalarPairLayout :=
  let bAlign := b.align
  let totalAlign := max (max a.align bAlign) aggregateAlign
  let bOffset := alignTo a.size bAlign
  let totalSize := alignTo (bOffset + b.size) totalAlign
  ⟨a, b, bOffset, totalAlign, totalSize⟩

/-- Whether a `ScalarPair` layout has inter-element or trailing padding
(`compiler/rustc_const_eval/src/interpret/place.rs:815, 984`). -/
def scalarPairHasPadding (sp : ScalarPairLayout) : Bool :=
  sp.a.size + sp.b.size != sp.totalSize

/-- Abstract byte in memory. -/
inductive AbsByte where
  | uninit
  | init (val : UInt8)
  deriving DecidableEq, Repr

/-- An immediate `ScalarPair` value holds only the bytes of `a` (`a.size` bytes) and `b` (`b.size` bytes);
it has no representation for `[a.size .. bOffset)` or `[bOffset + b.size .. totalSize)`. -/
structure ScalarPairImm where
  aBytes : List AbsByte
  bBytes : List AbsByte
  deriving DecidableEq, Repr

/-- Read a `ScalarPair` immediate from an in-memory buffer (`read_immediate_from_mplace_raw`,
`compiler/rustc_const_eval/src/interpret/operand.rs:597-631`). -/
def readScalarPairFromMemory (sp : ScalarPairLayout) (mem : List AbsByte) : ScalarPairImm :=
  let aBytes := (mem.drop 0).take sp.a.size
  let bBytes := (mem.drop sp.bOffset).take sp.b.size
  ⟨aBytes, bBytes⟩

/-- Write a `ScalarPair` immediate to an in-memory buffer and reset non-data padding ranges when
`resetPadding` is true (`write_immediate_to_mplace_no_validate` + `reset_padding`,
`compiler/rustc_const_eval/src/interpret/place.rs:795-821`, `validity.rs:1113-1161`). -/
def writeScalarPairToMemory (sp : ScalarPairLayout) (imm : ScalarPairImm) (mem : List AbsByte) : List AbsByte :=
  (List.range sp.totalSize).map fun idx =>
    if idx < sp.a.size then
      imm.aBytes.getD idx .uninit
    else if sp.bOffset ≤ idx && idx < sp.bOffset + sp.b.size then
      imm.bBytes.getD (idx - sp.bOffset) .uninit
    else if scalarPairHasPadding sp then
      .uninit
    else
      mem.getD idx .uninit

/-- Reset padding bytes of a `ScalarPairLayout` in an in-memory buffer (`ValidityVisitor::reset_padding`,
`compiler/rustc_const_eval/src/interpret/validity.rs:1113-1161`). -/
def resetScalarPairPaddingInMemory (sp : ScalarPairLayout) (mem : List AbsByte) : List AbsByte :=
  (List.range sp.totalSize).map fun idx =>
    if idx < sp.a.size || (sp.bOffset ≤ idx && idx < sp.bOffset + sp.b.size) then
      mem.getD idx .uninit
    else
      .uninit

/-- Model of `copy_op_allow_transmute` (`Rvalue::Cast::Transmute`,
`compiler/rustc_const_eval/src/interpret/place.rs:912-1051`):
Even when `mem_copy` copies all bytes of `src` to `dest` (because `src_has_padding` is `true` when
`src` is in memory, or when `src` is `[u8; N]`), `copy_op_inner` runs `validate_place` with
`reset_provenance_and_padding = true` at `src.layout` (if `src.ty != dest.ty`) AND at `dest.layout`! -/
def transmuteMemoryWithScalarPairPaddingReset (sp : ScalarPairLayout) (srcMem : List AbsByte) : List AbsByte :=
  resetScalarPairPaddingInMemory sp srcMem

/-- Concrete layouts:
1. `#[repr(C)] struct PairU8U32(u8, u32)`: `a = (1, 1)`, `b = (4, 4)` -> `bOffset = 4`, `totalSize = 8`.
2. `#[repr(C)] struct PairU8U64(u8, u64)` / `Result<u8, u64>`: `a = (1, 1)`, `b = (8, 8)` -> `bOffset = 8`, `totalSize = 16`.
3. `(u32, u32)`: `a = (4, 4)`, `b = (4, 4)` -> `bOffset = 4`, `totalSize = 8`, `hasPadding = false`. -/
def pairU8U32Layout : ScalarPairLayout := mkScalarPairLayout ⟨1, 1⟩ ⟨4, 4⟩
def pairU8U64Layout : ScalarPairLayout := mkScalarPairLayout ⟨1, 1⟩ ⟨8, 8⟩
def pairU32U32Layout : ScalarPairLayout := mkScalarPairLayout ⟨4, 4⟩ ⟨4, 4⟩

/-- Theorem: `bOffset`, `totalSize`, and `scalarPairHasPadding` for `(u8, u32)`, `(u8, u64)`,
and `(u32, u32)`. -/
theorem thm_scalar_pair_offsets_and_padding :
    pairU8U32Layout = ⟨⟨1, 1⟩, ⟨4, 4⟩, 4, 4, 8⟩ ∧
    scalarPairHasPadding pairU8U32Layout = true ∧
    pairU8U64Layout = ⟨⟨1, 1⟩, ⟨8, 8⟩, 8, 8, 16⟩ ∧
    scalarPairHasPadding pairU8U64Layout = true ∧
    pairU32U32Layout = ⟨⟨4, 4⟩, ⟨4, 4⟩, 4, 4, 8⟩ ∧
    scalarPairHasPadding pairU32U32Layout = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem: For `PairU8U32`, starting from a fully initialized 8-byte memory buffer
`[.init 1, .init 2, .init 3, .init 4, .init 5, .init 6, .init 7, .init 8]`:
1. Reading as a `ScalarPair` immediate and writing back to memory strips bytes `[1..4)` to `.uninit`
   while preserving byte `0` and bytes `[4..8)`.
2. Transmuting (`transmuteMemoryWithScalarPairPaddingReset`) in EITHER direction (`[u8; 8] -> PairU8U32`
   or `PairU8U32 -> [MaybeUninit<u8>; 8]`) strips bytes `[1..4)` to `.uninit`! -/
def fullInit8 : List AbsByte :=
  [.init 1, .init 2, .init 3, .init 4, .init 5, .init 6, .init 7, .init 8]

def expectedAfterStrip8 : List AbsByte :=
  [.init 1, .uninit, .uninit, .uninit, .init 5, .init 6, .init 7, .init 8]

theorem thm_pair_u8_u32_padding_stripped_to_uninit :
    writeScalarPairToMemory pairU8U32Layout (readScalarPairFromMemory pairU8U32Layout fullInit8) fullInit8 =
      expectedAfterStrip8 ∧
    transmuteMemoryWithScalarPairPaddingReset pairU8U32Layout fullInit8 =
      expectedAfterStrip8 := by
  exact ⟨rfl, rfl⟩

end FreezeRetagScalarPairProbe

#print axioms FreezeRetagScalarPairProbe.thm_mixed_struct_and_trailing_padding
#print axioms FreezeRetagScalarPairProbe.thm_multi_variant_vs_single_inhabited_enum
#print axioms FreezeRetagScalarPairProbe.thm_union_unsafecell_vs_all_freeze
#print axioms FreezeRetagScalarPairProbe.thm_zst_unsafecell_inbounds_frozen
#print axioms FreezeRetagScalarPairProbe.thm_inbounds_vs_outside_permission_divergence
#print axioms FreezeRetagScalarPairProbe.thm_not_unpin_skips_mutable_and_box_retag
#print axioms FreezeRetagScalarPairProbe.thm_box_and_mut_unsafecell_default_vs_fn_entry
#print axioms FreezeRetagScalarPairProbe.thm_pointee_info_pin_and_unique
#print axioms FreezeRetagScalarPairProbe.thm_scalar_pair_offsets_and_padding
#print axioms FreezeRetagScalarPairProbe.thm_pair_u8_u32_padding_stripped_to_uninit
