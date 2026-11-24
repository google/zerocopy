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

/-- Allocate an immutable (`.shared`) `.rodata` memory block in `m` preserving
per-byte initialization (including `.uninit` holes), returning the updated
memory and fresh `AllocId`. -/
noncomputable def allocRodataMemory (m : MemoryState) (bytes : List AllocByte)
    (alignLog2 : Nat) : MemoryState × AllocId :=
  let (m', id) := m.reserveAllocId
  let alloc : Allocation := {
    allocId := id
    bytes := bytes
    alignLog2 := alignLog2
    mutability := .shared
    live := true
  }
  ({ m' with allocations := alloc :: m'.allocations }, id)

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
`alignLog2`. Matches `check_and_deref_ptr`
(`compiler/rustc_const_eval/src/interpret/memory.rs:519-566`) composed with
`get_place_alloc` (`compiler/rustc_const_eval/src/interpret/place.rs:485-498`,
both at `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "// Everything is okay with size 0.
> if size == 0 {
>     return interp_ok(None);
> }"
(`check_and_deref_ptr`, skipping liveness and bounds at `size == 0`)

> "let a = self.get_ptr_alloc(mplace.ptr(), size)?;
> self.check_misalign(mplace.mplace.misaligned, CheckAlignMsg::BasedOn)?;"
(`get_place_alloc`, checking alignment even at `size == 0`)

The place's `misaligned` flag comes from `is_ptr_misaligned`, which reads
allocation alignment metadata even for dead allocations. When `size == 0`,
`readBytes` resolves the allocation record (faulting with `.undefined` if
unknown) and checks `isAligned a place.offset alignLog2` without checking
`a.live` or `isInBounds`. When `size > 0`, a missing or deallocated allocation
(`PointerUseAfterFree`), out-of-bounds span (`PointerOutOfBounds`), or
misaligned place (`AlignmentCheckFailed`) faults with `.undefined`. -/
noncomputable def readBytes (m : MemoryState) (place : MemPlace)
    (size alignLog2 : Nat) : Except FaultKind (List AllocByte) :=
  match findAllocation place.allocId m.allocations with
  | none => .error .undefined
  | some a =>
    if Nat.beq size 0 then
      if !isAligned a place.offset alignLog2 then
        .error .undefined
      else
        .ok []
    else if !a.live || !isInBounds a place.offset size ||
        !isAligned a place.offset alignLog2 then
      .error .undefined
    else
      .ok ((a.bytes.drop place.offset).take size)

/-- Overwrite the bytes at `place` with `bytes` for an access with alignment
`alignLog2`. Matches `get_place_alloc_mut`
(`compiler/rustc_const_eval/src/interpret/place.rs:501-516`) calling
`get_alloc_raw_mut`
(`compiler/rustc_const_eval/src/interpret/memory.rs:813-840`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) via
`get_ptr_alloc_mut` (`memory.rs:852-893`), where `:836` checks mutability:

> "if alloc.mutability.is_not() {
>     throw_ub!(WriteToReadOnly(id))
> }"

`get_place_alloc_mut` checks alignment whatever the size:

> "let misalign_res = self.check_misalign(mplace.mplace.misaligned,
> CheckAlignMsg::BasedOn);"

When `bytes.length == 0`, `writeBytes` resolves the allocation record and checks
`isAligned a place.offset alignLog2` (even when `a.live == false`) without
checking `a.live`, `isInBounds`, or `a.mutability` (`WriteToReadOnly` runs only
for non-empty writes). When `bytes.length > 0`, it performs all checks of
`readBytes` and additionally requires `a.mutability == .mut`. -/
noncomputable def writeBytes (m : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bytes : List AllocByte) :
    Except FaultKind MemoryState :=
  match findAllocation place.allocId m.allocations with
  | none => .error .undefined
  | some a =>
    if Nat.beq bytes.length 0 then
      if !isAligned a place.offset alignLog2 then
        .error .undefined
      else
        .ok m
    else if !a.live || !isInBounds a place.offset bytes.length ||
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
alignment (`2^29`).

The size bound is the Reference's allocation limit
(`src/behavior-considered-undefined.md:149-152`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`):

> "In particular, the dynamic size of a Rust value (as determined by
> `size_of_val`) must never exceed `isize::MAX`, since it is impossible for a
> single allocation to be larger than `isize::MAX`."

The alignment bound is `Align::MAX` (`compiler/rustc_abi/src/lib.rs:1057-1058`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), which
`Align::max_for_target` also yields on 64-bit targets:

> "// LLVM has a maximal supported alignment of 2^29, we inherit that.
> pub const MAX: Align = Align { pow2: 29 };" -/
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

/-- Compute the largest provenance `allocId` carried by initialized bytes in
`bs` (or `0` when no byte carries provenance). -/
noncomputable def maxByteProvAllocId : List AllocByte → AllocId
  | [] => 0
  | .uninit :: rest => maxByteProvAllocId rest
  | .init _ none :: rest => maxByteProvAllocId rest
  | .init _ (some aid) :: rest => Nat.max aid (maxByteProvAllocId rest)

/-- Compute the largest byte-provenance `allocId` across `allocs` (or `0` when
none). -/
noncomputable def maxAllocBytesProvId : List Allocation → AllocId
  | [] => 0
  | a :: rest => Nat.max (maxByteProvAllocId a.bytes) (maxAllocBytesProvId rest)

/-- Compute the largest allocation id or byte-provenance id across `allocs`. -/
noncomputable def maxAllocAndProvId (allocs : List Allocation) : AllocId :=
  Nat.max (maxAllocId allocs) (maxAllocBytesProvId allocs)

mutual
  /-- Return `true` when `ty` is a raw pointer or an option, range, tuple,
  fixed-size array, `Vec`, or `Box` containing one. Kept exhaustive over
  `MirTy` so adding new aggregate/container constructors forces updating
  raw-pointer freshness tracking. -/
  noncomputable def tyHasRawPtrV2 : MirTy → Bool
    | .rawPtr _ _ => true
    | .array elem _ => tyHasRawPtrV2 elem
    | .option e | .rangeTo e | .rangeFrom e | .range e => tyHasRawPtrV2 e
    | .tuple fs => tyListHasRawPtrV2 fs
    | .vec elem => tyHasRawPtrV2 elem
    | .box pointee => tyHasRawPtrV2 pointee
    | .bool | .int _ _ | .unit | .never | .char | .str | .ordering | .enum _
    | .ref _ _ | .slice _ | .unsupported => false

  noncomputable def tyListHasRawPtrV2 : List MirTy → Bool
    | [] => false
    | t :: ts => tyHasRawPtrV2 t || tyListHasRawPtrV2 ts
end

mutual
  /-- Compute the largest provenance `allocId` occurring inside pointer or slice
  leaves of `v` (or `0` when `v` carries no provenance-bearing pointer). Kept
  exhaustive over `Val` so adding new value constructors forces updating
  raw-pointer `AllocId` freshness tracking. -/
  noncomputable def maxValPtrAllocId : Val → AllocId
    | .ptr p => p.allocId.getD 0
    | .slicePtr p _ => p.allocId.getD 0
    | .vec p _ _ => p.allocId.getD 0
    | .boxPtr p _ => p.allocId.getD 0
    | .tuple vs => maxValPtrAllocIdList vs
    | .array vs => maxValPtrAllocIdList vs
    | .bytes bs => maxByteProvAllocId bs
    | .optionVal (some v) => maxValPtrAllocId v
    | .optionVal none => 0
    | .scalar _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .bool _ | .char _
    | .ordering _ | .unit | .enumVal _ _ => 0

  noncomputable def maxValPtrAllocIdList : List Val → AllocId
    | [] => 0
    | v :: vs => Nat.max (maxValPtrAllocId v) (maxValPtrAllocIdList vs)
end

/-- Build the Profile v2 entry `MemoryState` containing `cm.allocations`,
advancing `nextAllocId` past every caller allocation id, every provenance id
stored inside `cm.allocations` bytes, and `entryMemory`'s reserved id `1` so
callee stack and `.rodata` allocations can never reuse an existing caller or
provenance `AllocId`. -/
noncomputable def entryMemoryWithCaller (cm : CallerMemory) : MemoryState :=
  { nextAllocId := Nat.max entryMemory.nextAllocId (maxAllocAndProvId cm.allocations + 1)
    allocations := cm.allocations }

/-- Build the Profile v2 entry `MemoryState` for a body with parameter types
`paramTys` and argument values `args`, additionally advancing `nextAllocId`
past any provenance `AllocId` carried in raw-pointer parameters (including
dangling provenance ids absent from `cm.allocations`). When `paramTys` contains
no raw pointers, this reduces definitionally to `entryMemoryWithCaller cm`. -/
noncomputable def entryMemoryForArgsV2 (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val) : MemoryState :=
  let base := entryMemoryWithCaller cm
  if !tyListHasRawPtrV2 paramTys then
    base
  else
    { base with
      nextAllocId := Nat.max base.nextAllocId (maxValPtrAllocIdList args + 1) }

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
Without provenance, only a zero delta is valid (matching `pointer::add(0)`).

This is the safety contract of `<*const T>::add` and `<*mut T>::add`
(`library/core/src/ptr/docs/add.md:12-20`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "If any of the following conditions are violated, the result is Undefined
> Behavior:
>
> * The offset in bytes, `count * size_of::<T>()`, computed on mathematical
>   integers (without "wrapping around"), must fit in an `isize`.
>
> * If the computed offset is non-zero, then `self` must be [derived
>   from][crate::ptr#provenance] a pointer to some [allocation], and the
>   entire memory range between `self` and the result must be in bounds of
>   that allocation. In particular, this range must not "wrap around" the edge
>   of the address space."

Both methods are `unsafe { intrinsics::offset(self, count) }`
(`library/core/src/ptr/const_ptr.rs:863`, `mut_ptr.rs:961`), the
`BinOp::Offset` primitive. Its interpreter implementation (see
`evalPtrOffsetV2`) also requires the allocation to be live. Conservative
divergence: a zero offset from a provenance pointer into a dead or
out-of-bounds allocation is `.undefined` here, although
`check_and_deref_ptr` accepts every size-0 range. -/
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

/-- Validate the raw pointer, bounds, alignment, `isize::MAX` byte-size limit,
and mutability invariants for `&[T]` / `&mut [T]` in `m`, without requiring
every byte in `[offset, offset + len * elemSize)` to be initialized (so
non-integer slice elements with padding or inactive enum payloads such as
`Option<u64>::None` can validate initialization per active field via
`validateSliceElemsV2`). -/
noncomputable def sliceRefRawCheck (m : MemoryState) (isMut : Bool)
    (elemSize elemAlignLog2 : Nat) (p : PtrVal) (len : UInt64) :
    Except FaultKind (Option Allocation) :=
  let totalBytes := len.toNat * elemSize
  if !Nat.blt totalBytes isizeMaxBytes then
    .error .undefined
  else
    match p.allocId with
    | none =>
      if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 totalBytes then
        .error .undefined
      else if !Nat.beq
          (Nat.mod p.offsetBytes.toNat (Nat.pow 2 elemAlignLog2)) 0 then
        .error .undefined
      else
        .ok none
    | some aid =>
      match findAllocation aid m.allocations with
      | none => .error .undefined
      | some a =>
        if !a.live || !isInBounds a p.offsetBytes.toNat totalBytes ||
            !isAligned a p.offsetBytes.toNat elemAlignLog2 then
          .error .undefined
        else if isMut && !Mutability.beq a.mutability .mut then
          .error .undefined
        else
          .ok (some a)

/-- Validate the slice-reference invariants for `&[uN]` / `&mut [uN]` in `m`.
`refValidInMem` uses this for integer slice elements, while non-integer slice
elements use `sliceRefRawCheck` plus `validateSliceElemsV2`:
- `len * elemSize < 2^63` (`isize::MAX` bound);
- non-null and aligned even when `len == 0`. A pointer with no provenance is
  accepted only when `len * elemSize == 0`;
- for a provenance-bearing pointer: live allocation, in-bounds
  `[offset, offset + totalBytes]`, `isAligned a offset elemAlignLog2`, a
  mutable allocation when `isMut = true`, and initialized element bytes.

These are the `core::slice::from_raw_parts` safety bullets that do not concern
aliasing (`library/core/src/slice/raw.rs:14-26,31-32`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). Every initialized bit pattern is
a valid integer, so for `[uN]` "properly initialized" reduces to
`isSliceAllInit`:

> "* `data` must be non-null, [valid] for reads for `len * size_of::<T>()`
>   many bytes, and it must be properly aligned. This means in particular:
>
>     * The entire memory range of this slice must be contained within a
>       single allocation! Slices can never span across multiple allocations.
>       See [below](#incorrect-usage) for an example incorrectly not taking
>       this into account.
>     * `data` must be non-null and aligned even for zero-length slices or
>       slices of ZSTs. One reason for this is that enum layout optimizations
>       may rely on references (including slices of any length) being aligned
>       and non-null to distinguish them from other data. You can obtain a
>       pointer that is usable as `data` for zero-length slices using
>       [`NonNull::dangling()`].
>
> * `data` must point to `len` consecutive properly initialized values of type
>   `T`.
> ...
> * The total size `len * size_of::<T>()` of the slice must be no larger than
>   `isize::MAX`, and adding that size to `data` must not "wrap around" the
>   address space."

The remaining bullets, "must not be mutated" for `&[T]` and "must not be
accessed through any other pointer" for `&mut [T]`, belong to the aliasing
model. This check does not enforce them; see `BodyVerifiedV2`. Conservative
divergence: a provenance pointer with `totalBytes == 0` still requires a live,
in-bounds allocation, although zero-size ranges never dangle. -/
noncomputable def sliceFromRawPartsCheck (m : MemoryState) (isMut : Bool)
    (elemSize elemAlignLog2 : Nat) (p : PtrVal) (len : UInt64) :
    Except FaultKind Val :=
  let totalBytes := len.toNat * elemSize
  match sliceRefRawCheck m isMut elemSize elemAlignLog2 p len with
  | .error k => .error k
  | .ok none => .ok (.slicePtr p len)
  | .ok (some a) =>
    if !isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take totalBytes) then
      .error .undefined
    else
      .ok (.slicePtr p len)

/-- Checked `slice::get_unchecked` subslice (`[startOff..endOff]` of slice
`(p, len)` with element byte size `elemSize`, defaulting to `1` for `[u8]`):
requires `startOff <= endOff <= len`, advancing `p` by `startOff` elements of
size `elemSize` via `ptrAddInMem`.

`<[T]>::get_unchecked` with `RangeTo<usize>` or `RangeFrom<usize>` delegates
to `(0..self.end)` or `(self.start..slice.len())`. The `Range<usize>` impl
checks the library-UB precondition and then offsets the data pointer by
`start` (`library/core/src/slice/index.rs:392-411`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
>     assert_unsafe_precondition!(
>         check_library_ub,
>         "slice::get_unchecked requires that the range is within the slice",
>         (
>             start: usize = self.start,
>             end: usize = self.end,
>             len: usize = slice.len()
>         ) => end >= start && end <= len
>     );
> ...
>         let new_len = crate::intrinsics::unchecked_sub(self.end, self.start);
>         get_offset_len_noubcheck(slice, self.start, new_len)"

The documented contract (`library/core/src/slice/mod.rs:613-614`) is:

> "Calling this method with an out-of-bounds index is *[undefined behavior]*
> even if the resulting reference is not used." -/
noncomputable def sliceGetUncheckedCheck (m : MemoryState) (p : PtrVal)
    (len startOff endOff : Nat) (elemSize : Nat := 1) : Except FaultKind Val :=
  if !Nat.ble startOff endOff || !Nat.ble endOff len then
    .error .undefined
  else
    match ptrAddInMem m elemSize p startOff with
    | .error k => .error k
    | .ok p' => .ok (.slicePtr p' (UInt64.ofNat (endOff - startOff)))

end Trusted.MirSemantics

end
