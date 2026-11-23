-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Init.Data.Nat.Div.Basic
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Layout

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Byte-Level Memory (`Trusted.MirSemantics.Memory`)

The memory of $M_{\text{anneal}}$ (`MemoryState`): a list of allocations, each
holding its own bytes, alignment, mutability, and liveness, together with a
monotonic allocation-id counter. Stack allocation (`allocateStack`),
deallocation (`deallocateStack`), and checked byte reads and writes
(`readBytes`, `writeBytes`, `writeUninit`) follow
`rustc_const_eval::interpret::Memory`
(`compiler/rustc_const_eval/src/interpret/memory.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`).

Allocation ids are never reused, so an id names at most one allocation for
the whole execution. A deallocated allocation stays in `allocations` with
`live = false`, so later accesses through a stale place fault with
`.undefined` instead of reaching a newer allocation.
-/

/-- Memory of $M_{\text{anneal}}$: every stack allocation made so far
(including deallocated ones, with `live = false`) and the next unused
allocation id. -/
structure MemoryState where
  nextAllocId : AllocId
  allocations : List Allocation

/-- Memory with no allocations. Allocation ids start at `1`, matching
`rustc`'s `AllocId(NonZero<u64>)` and `Miri.Memory.MemoryState.empty`. -/
noncomputable def MemoryState.empty : MemoryState :=
  { nextAllocId := 1, allocations := [] }

/-- Reserve the next allocation id, matching `TyCtxt::reserve_alloc_id`
(called from `insert_allocation` in
`compiler/rustc_const_eval/src/interpret/memory.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let id = self.tcx.reserve_alloc_id();" -/
noncomputable def MemoryState.reserveAllocId (m : MemoryState) :
    MemoryState × AllocId :=
  ({ m with nextAllocId := m.nextAllocId + 1 }, m.nextAllocId)

/-- Memory at entry to the program's entry function: no allocations, with
allocation id `1` reserved for the caller-owned return place. `rustc` and
`lean-miri` (`Miri.Interpreter.callMain`) allocate the return place before
pushing the entry frame. $M_{\text{anneal}}$ returns `_0`'s value directly
(`TerminalOut.returned`) and so does not model the return place's bytes, but
it reserves the id so that the ids of later stack allocations agree with
`lean-miri`'s. -/
noncomputable def entryMemory : MemoryState :=
  MemoryState.empty.reserveAllocId.1

/-- Find the allocation with id `id` (live or deallocated). -/
noncomputable def findAllocation (id : AllocId) :
    List Allocation → Option Allocation
  | [] => none
  | a :: rest => if Nat.beq a.allocId id then some a else findAllocation id rest

/-- Replace the allocation whose id is `a'.allocId` by `a'`. -/
noncomputable def replaceAllocation (a' : Allocation) :
    List Allocation → List Allocation
  | [] => []
  | a :: rest =>
    if Nat.beq a.allocId a'.allocId then a' :: rest
    else a :: replaceAllocation a' rest

/-- Allocate a fresh, mutable, uninitialized stack allocation of
`layout.size` bytes and alignment `layout.alignLog2`, returning the place of
its first byte. Matches `allocate` and `allocate_dyn` in
`compiler/rustc_const_eval/src/interpret/place.rs` and `allocate_ptr` in
`compiler/rustc_const_eval/src/interpret/memory.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn allocate(
>     &mut self,
>     layout: TyAndLayout<'tcx>,
>     kind: MemoryKind<M::MemoryKind>,
> ) -> InterpResult<'tcx, MPlaceTy<'tcx, M::Provenance>> {
>     assert!(layout.is_sized());
>     self.allocate_dyn(layout, kind, MemPlaceMeta::None)
> }"
> (`compiler/rustc_const_eval/src/interpret/place.rs`)
>
> "let ptr = self.allocate_ptr(size, align, kind, AllocInit::Uninit)?;"
> (`allocate_dyn`, `compiler/rustc_const_eval/src/interpret/place.rs`) -/
noncomputable def allocateStack (m : MemoryState) (layout : LayoutData) :
    MemoryState × MemPlace :=
  let (m1, id) := m.reserveAllocId
  let alloc : Allocation := {
    allocId := id
    alignLog2 := layout.alignLog2
    mutability := .mut
    bytes := List.replicate layout.size .uninit
    live := true
  }
  ({ m1 with allocations := m1.allocations ++ [alloc] }, ⟨id, 0⟩)

/-- Deallocate the stack allocation that starts at `place`, matching
`deallocate_ptr` in `compiler/rustc_const_eval/src/interpret/memory.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "if offset.bytes() != 0 {
>     throw_ub_format!(
>         \"deallocating {ptr} which does not point to the beginning of an
>         object\"
>     );
> }
>
> let Some((alloc_kind, mut alloc)) = self.memory.alloc_map.remove(&alloc_id)
>     else {
>     ...
>     None => err_ub!(PointerUseAfterFree(alloc_id,
>         CheckInAllocMsg::MemoryAccess)),
>     ...
> };
>
> if alloc.mutability.is_not() {
>     throw_ub_format!(\"deallocating immutable allocation {alloc_id}\");
> }"

Every allocation in `MemoryState` is a mutable stack allocation, so the
`rustc` memory-kind check always passes. A missing, already deallocated, or
immutable allocation, or a place that does not point at offset `0`, faults
with `.undefined`. -/
noncomputable def deallocateStack (m : MemoryState) (place : MemPlace) :
    Except FaultKind MemoryState :=
  if !Nat.beq place.offset 0 then
    .error .undefined
  else
    match findAllocation place.allocId m.allocations with
    | none => .error .undefined
    | some a =>
      if !a.live then
        .error .undefined
      else
        match a.mutability with
        | .shared => .error .undefined
        | .mut =>
          .ok { m with
            allocations :=
              replaceAllocation { a with live := false } m.allocations }

/-- Whether the `size` bytes starting at `offset` lie inside allocation `a`,
matching the bounds check in `check_and_deref_ptr`
(`compiler/rustc_const_eval/src/interpret/memory.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "// Ensure both are within bounds.
> let in_bounds = begin.is_some() && end.is_some_and(|e| e <=
>     alloc_size.bytes());" -/
noncomputable def isInBounds (a : Allocation) (offset size : Nat) : Bool :=
  Nat.ble (offset + size) a.bytes.length

/-- Whether an access at `offset` with alignment `alignLog2` is aligned in
allocation `a`, matching `is_ptr_misaligned` in
`compiler/rustc_const_eval/src/interpret/memory.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) for provenance whose offset is
not an absolute address:

> "// Check allocation alignment and offset alignment.
> if alloc_info.align.bytes() < align.bytes() {
>     Some(Misalignment { has: alloc_info.align, required: align })
> } else {
>     is_offset_misaligned(offset.bytes(), align)
> }" -/
noncomputable def isAligned (a : Allocation) (offset alignLog2 : Nat) : Bool :=
  Nat.ble alignLog2 a.alignLog2 &&
    Nat.beq (Nat.mod offset (Nat.pow 2 alignLog2)) 0

/-- Read the `size` bytes at `place` for an access with alignment
`alignLog2`. Matches `get_ptr_alloc` and `check_and_deref_ptr` in
`compiler/rustc_const_eval/src/interpret/memory.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "// Everything is okay with size 0.
> if size == 0 {
>     return interp_ok(None);
> }"

A non-empty read from a missing or deallocated allocation
(`PointerUseAfterFree`), outside the allocation (`PointerOutOfBounds`), or at
a misaligned place (`AlignmentCheckFailed`) faults with `.undefined`. -/
noncomputable def readBytes (m : MemoryState) (place : MemPlace)
    (size alignLog2 : Nat) : Except FaultKind (List AllocByte) :=
  if Nat.beq size 0 then
    .ok []
  else
    match findAllocation place.allocId m.allocations with
    | none => .error .undefined
    | some a =>
      if !a.live || !isInBounds a place.offset size ||
          !isAligned a place.offset alignLog2 then
        .error .undefined
      else
        .ok ((a.bytes.drop place.offset).take size)

/-- Overwrite the bytes at `place` with `bytes` for an access with alignment
`alignLog2`. Performs the checks of `readBytes` and additionally requires a
mutable allocation, matching `get_ptr_alloc_mut` in
`compiler/rustc_const_eval/src/interpret/memory.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "if alloc.mutability.is_not() {
>     throw_ub!(WriteToReadOnly(id))
> }" -/
noncomputable def writeBytes (m : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bytes : List AllocByte) :
    Except FaultKind MemoryState :=
  if Nat.beq bytes.length 0 then
    .ok m
  else
    match findAllocation place.allocId m.allocations with
    | none => .error .undefined
    | some a =>
      if !a.live || !isInBounds a place.offset bytes.length ||
          !isAligned a place.offset alignLog2 then
        .error .undefined
      else
        match a.mutability with
        | .shared => .error .undefined
        | .mut =>
          let bytes' := a.bytes.take place.offset ++ bytes ++
            a.bytes.drop (place.offset + bytes.length)
          .ok { m with
            allocations :=
              replaceAllocation { a with bytes := bytes' } m.allocations }

/-- Mark the `size` bytes at `place` uninitialized, matching
`Allocation::write_uninit` in
`compiler/rustc_middle/src/mir/interpret/allocation.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn write_uninit(&mut self, cx: &impl HasDataLayout, range: AllocRange)
> {
>     self.mark_init(range, false);
>     self.provenance.clear(range, &self.bytes, cx);
> }" -/
noncomputable def writeUninit (m : MemoryState) (place : MemPlace)
    (size alignLog2 : Nat) : Except FaultKind MemoryState :=
  writeBytes m place alignLog2 (List.replicate size .uninit)

/-! ## Profile v2 Caller Memory and Pointer/Slice Checks -/

/-- Upper bound `isize::MAX + 1` on a 64-bit target (`2^63` bytes). -/
noncomputable def isizeMaxBytes : Nat :=
  Nat.pow 2 63

/-- Validate that all allocations in `cm` carry non-zero, pairwise-distinct
`allocId`s, fit within 64-bit `isize::MAX`, and stay within Rust's maximum
alignment (`2^29`). -/
noncomputable def allocIdsValid (seen : List AllocId) : List Allocation → Bool
  | [] => true
  | a :: rest =>
    !Nat.beq a.allocId 0 &&
      natNotElem a.allocId seen &&
      Nat.blt a.bytes.length isizeMaxBytes &&
      Nat.ble a.alignLog2 29 &&
      allocIdsValid (a.allocId :: seen) rest

/-- Structural validity of caller-provided memory for Profile v2. -/
noncomputable def validCallerMemory (cm : CallerMemory) : Bool :=
  allocIdsValid [] cm.allocations

/-- Compute the largest `allocId` appearing in `allocs` (or `0` when empty). -/
noncomputable def maxAllocId : List Allocation → AllocId
  | [] => 0
  | a :: rest => Nat.max a.allocId (maxAllocId rest)

/-- Build the Profile v2 entry `MemoryState` containing `cm.allocations`,
advancing `nextAllocId` past every caller allocation id (and past `entryMemory`'s
reserved id `1`) so callee stack allocations can never alias `cm`. -/
noncomputable def entryMemoryWithCaller (cm : CallerMemory) : MemoryState :=
  { nextAllocId := Nat.max entryMemory.nextAllocId (maxAllocId cm.allocations + 1)
    allocations := cm.allocations }

/-- Extract the post-execution caller-visible allocations from `m` in the
original order of `orig.allocations` so caller-memory mutations are observable
on return without exposing callee stack allocations. -/
noncomputable def extractCallerAllocations (m : MemoryState) :
    List Allocation → List Allocation
  | [] => []
  | a :: rest =>
    let updated := (findAllocation a.allocId m.allocations).getD a
    updated :: extractCallerAllocations m rest

/-- Snapshot caller-visible allocations from `m` on return. -/
noncomputable def extractCallerMemory (orig : CallerMemory) (m : MemoryState) :
    CallerMemory :=
  ⟨extractCallerAllocations m orig.allocations⟩

/-- Check that every byte in `bs` is initialized (`.init _ _`). -/
noncomputable def isSliceAllInit : List AllocByte → Bool
  | [] => true
  | .init _ _ :: rest => isSliceAllInit rest
  | .uninit :: _ => false

/-- Checked Rust `pointer::add` in `m`: requires byte delta `count * elemSize`
strictly below `isize::MAX + 1`, and for provenance-bearing pointers requires a
live allocation whose bounds cover `[offset, offset + count * elemSize]`.
Without provenance, only a zero delta is valid (matching `pointer::add(0)`). -/
noncomputable def ptrAddInMem (m : MemoryState) (elemSize : Nat) (p : PtrVal)
    (count : Nat) : Except FaultKind PtrVal :=
  let delta := count * elemSize
  if !Nat.blt delta isizeMaxBytes then
    .error .undefined
  else
    match p.allocId with
    | none =>
      if Nat.beq delta 0 then
        .ok p
      else
        .error .undefined
    | some aid =>
      match findAllocation aid m.allocations with
      | none => .error .undefined
      | some a =>
        if !a.live || !Nat.ble (p.offsetBytes.toNat + delta) a.bytes.length then
          .error .undefined
        else
          .ok { p with offsetBytes := UInt64.ofNat (p.offsetBytes.toNat + delta) }

/-- Validate `&[u8]` / `&mut [u8]` slice preconditions in `m`
(`core::slice::from_raw_parts` and `from_raw_parts_mut` / `Ref` validity):
- `len * elemSize < 2^63` (`isize::MAX` bound);
- non-null & aligned even when `len == 0` (`withoutProvenance 0` always faults);
- for non-zero length (or any provenance-bearing slice pointer): live allocation,
  in-bounds `[offset, offset + totalBytes]`, `isAligned a offset elemAlignLog2`,
  mutable allocation when `isMut = true`, and initialized element bytes. -/
noncomputable def sliceFromRawPartsCheck (m : MemoryState) (isMut : Bool)
    (elemSize elemAlignLog2 : Nat) (p : PtrVal) (len : UInt64) :
    Except FaultKind Val :=
  let totalBytes := len.toNat * elemSize
  if !Nat.blt totalBytes isizeMaxBytes then
    .error .undefined
  else
    match p.allocId with
    | none =>
      if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 totalBytes then
        .error .undefined
      else if !Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 elemAlignLog2)) 0 then
        .error .undefined
      else
        .ok (.slicePtr p len)
    | some aid =>
      match findAllocation aid m.allocations with
      | none => .error .undefined
      | some a =>
        if !a.live || !isInBounds a p.offsetBytes.toNat totalBytes ||
            !isAligned a p.offsetBytes.toNat elemAlignLog2 then
          .error .undefined
        else if isMut && !Mutability.beq a.mutability .mut then
          .error .undefined
        else if !isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take totalBytes) then
          .error .undefined
        else
          .ok (.slicePtr p len)

/-- Checked `slice::get_unchecked` subslice on `[u8]` (`[startOff..endOff]` of
slice `(p, len)`): requires `startOff <= endOff <= len`, advancing `p` by
`startOff` via `ptrAddInMem`. -/
noncomputable def sliceGetUncheckedCheck (m : MemoryState) (p : PtrVal)
    (len startOff endOff : Nat) : Except FaultKind Val :=
  if !Nat.ble startOff endOff || !Nat.ble endOff len then
    .error .undefined
  else
    match ptrAddInMem m 1 p startOff with
    | .error k => .error k
    | .ok p' => .ok (.slicePtr p' (UInt64.ofNat (endOff - startOff)))

end Trusted.MirSemantics

end
