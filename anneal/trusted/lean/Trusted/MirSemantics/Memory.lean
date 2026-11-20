-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.Nat.Div.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Layout

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

end Trusted.MirSemantics
