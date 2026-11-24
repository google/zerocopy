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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Nat.Div.Basic
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Heap Allocation Contracts (`Trusted.MirSemantics.AllocContracts`)

Operational contract layer for `alloc::vec::Vec<T>` and
`alloc::boxed::Box<P>` (with the `Global` allocator) in Profile v2. The
contracts model the standard library of the pinned nightly toolchain,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`; every `library/`
citation below is at that commit.

Contracts track real `AllocId` provenance (`allocId ≠ 0` when backed by a
non-empty heap buffer), capacity/length bounds (`len ≤ cap`,
`cap * size ≤ isize::MAX`), buffer alignment and initialization, and fresh
disjoint allocation ids on `with_capacity`, buffer growth, `Box::clone`, and
`Box::new`. Zero-sized element/pointee types use dangling aligned pointers
without allocating heap bytes. The upstream `RawVec` documents these
obligations (`library/alloc/src/raw_vec/mod.rs:55-61`):

> "/// * Produces `Unique::dangling()` on zero-sized types.
> /// * Produces `Unique::dangling()` on zero-length allocations.
> /// * Avoids freeing `Unique::dangling()`.
> /// * Catches all overflows in capacity computations (promotes them to
> \"capacity overflow\" panics).
> ...
> /// * Calls `handle_alloc_error` for fallible allocations."

(The fourth quoted line is wrapped here; upstream it is one line.)

A capacity overflow is a panic, which Profile v2 does not model, so it faults
with `.unsupported`, like a failed bounds-check `Assert`. Undefined behavior
faults with `.undefined`.

**Assumption: allocation never fails.** `allocHeapBuffer` always succeeds:
the model assumes an unbounded heap and does not model the out-of-memory path,
where the allocator returns an error and the standard library calls
`handle_alloc_error` (`library/alloc/src/alloc.rs:513-532`):

> "/// This function is guaranteed to diverge (not return normally with a
> value), but depending on
> /// global configuration, it may either panic (resulting in unwinding or
> aborting as per
> /// configuration for all panics), or abort the process (with no
> unwinding)."

(Wrapped here.) A program that the model shows to return normally may
therefore instead diverge on a real machine that runs out of memory. Receipts
for Profile v2 record this assumption.
-/

/-! ## Logical Models and Well-Formedness Predicates -/

/-- Logical view of an `alloc::vec::Vec<T>` handle. -/
structure VecModel where
  elem : MirTy
  ptr : PtrVal
  cap : UInt64
  len : UInt64

/-- Logical view of an `alloc::boxed::Box<P>` handle (`len = some n` for
`Box<[T]>`, `len = none` for sized `Box<T>`). -/
structure BoxModel where
  pointee : MirTy
  ptr : PtrVal
  len : Option UInt64

/-- Encode a `VecModel` as a `Val.vec`. -/
noncomputable def VecModel.toVal (v : VecModel) : Val :=
  .vec v.ptr v.cap v.len

/-- Decidable check that `v : VecModel` satisfies `Vec` invariants in `m`. -/
noncomputable def vecValidInMem (m : MemoryState) (isMut : Bool)
    (v : VecModel) : Except FaultKind Unit :=
  if !isSupportedPointeeTy v.elem then
    .error .unsupported
  else
    ownedHeapBufValidInMem m isMut v.elem v.ptr v.cap v.len

/-- Decidable check that `b : BoxModel` satisfies `Box` invariants in `m`. -/
noncomputable def boxValidInMem (m : MemoryState) (isMut : Bool)
    (b : BoxModel) : Except FaultKind Unit :=
  match b.pointee with
  | .slice elem =>
    if !isSupportedPointeeTy elem then
      .error .unsupported
    else
      boxPointeeValidInMem m isMut b.pointee b.ptr b.len
  | pt =>
    if !isSupportedPointeeTy pt then
      .error .unsupported
    else
      boxPointeeValidInMem m isMut pt b.ptr b.len

/-- Dangling non-null aligned pointer for empty/ZST buffers, with address
equal to the alignment and no provenance
(`library/core/src/ptr/non_null.rs:126-129`):

> "pub const fn dangling() -> Self {
>     let align = crate::mem::Alignment::of::<T>();
>     NonNull::without_provenance(align.as_nonzero_usize())
> }" -/
noncomputable def danglingAligned (alignLog2 : Nat) : PtrVal :=
  ⟨none, UInt64.ofNat (Nat.pow 2 alignLog2), .isize⟩

/-- Allocate a fresh, mutable, uninitialized heap allocation of `byteSize`
bytes and alignment `alignLog2`, returning its base pointer and updated
memory. This always succeeds: allocation failure (`handle_alloc_error`) is not
modeled (see the module documentation). -/
noncomputable def allocHeapBuffer (m : MemoryState)
    (byteSize alignLog2 : Nat) : MemoryState × PtrVal :=
  let (m1, aid) := m.reserveAllocId
  let alloc : Allocation := {
    allocId := aid
    alignLog2 := alignLog2
    mutability := .mut
    bytes := List.replicate byteSize .uninit
    live := true
  }
  ({ m1 with allocations := m1.allocations ++ [alloc] },
    ⟨some aid, 0, .isize⟩)

/-- Mark an existing backing heap allocation dead (`live := false`) when
reallocated. Requires offset `0`, liveness, and mutability. -/
noncomputable def retireHeapBuffer (m : MemoryState) (p : PtrVal) :
    Except FaultKind MemoryState :=
  match p.allocId with
  | none => .ok m
  | some aid => deallocateStack m ⟨aid, p.offsetBytes.toNat⟩

/-- Capacity after growing a buffer of `curCap` elements of size `elemSize` to
hold at least `minCap` elements, matching `RawVecInner::grow_amortized`
(`library/alloc/src/raw_vec/mod.rs:502-532`):

> "if elem_layout.size() == 0 {
> ...
>     return Err(CapacityOverflow.into());
> }
> ...
> let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
> ...
> let cap = cmp::max(self.cap.as_inner() * 2, required_cap);
> let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);"

followed by `finish_grow`, whose first line is
`let new_layout = layout_array(cap, elem_layout)?;` (`:548`), which fails with
`CapacityOverflow` when `cap * size` exceeds `isize::MAX`. A
`CapacityOverflow` is a panic (`handle_error`, `:882-892`), so `none` here
means the operation panics. `min_non_zero_cap` is 8 for 1-byte elements, 4
for elements of at most 1024 bytes, and 1 otherwise (`:153-166`).

For zero-sized elements the model returns `minCap` instead of panicking. The
upstream `capacity()` of a ZST buffer is `usize::MAX` (`:617-620`), so
`grow_amortized` is reached only when `minCap` exceeds `usize::MAX`, which the
first check below rejects; the model's `cap` field for a ZST buffer is
bookkeeping that no program can observe. -/
noncomputable def vecGrowCap (elemSize curCap minCap : Nat) : Option Nat :=
  let u64Bound := Nat.pow 2 64
  if !Nat.blt minCap u64Bound then
    none
  else if Nat.beq elemSize 0 then
    some minCap
  else if !Nat.blt (minCap * elemSize) isizeMaxBytes then
    none
  else
    let minNonZero :=
      if Nat.beq elemSize 1 then 8
      else if Nat.ble elemSize 1024 then 4
      else 1
    let doubled := Nat.max (curCap * 2) (Nat.max minCap minNonZero)
    if Nat.blt (doubled * elemSize) isizeMaxBytes &&
        Nat.blt doubled u64Bound then
      some doubled
    else
      none

/-- Repeat byte block `bs` `n` times. -/
noncomputable def repeatBytes (n : Nat) (bs : List AllocByte) :
    List AllocByte :=
  match n with
  | 0 => []
  | k + 1 => bs ++ repeatBytes k bs

/-- Ensure `v` has capacity at least `minCap`, growing to a fresh heap
allocation and retiring any old non-empty allocation when needed. Growth faults
with `.unsupported` (a capacity-overflow panic) when `vecGrowCap` fails.
Following Miri, a reallocation is a fresh allocation plus a copy, so pointers
into the old buffer lose their provenance. -/
noncomputable def ensureVecCapacity (m : MemoryState) (lay : LayoutData)
    (v : VecModel) (minCap : Nat) :
    Except FaultKind (MemoryState × VecModel) :=
  if !Nat.ble v.len.toNat minCap then
    .error .undefined
  else if Nat.ble minCap v.cap.toNat then
    .ok (m, v)
  else
    match vecGrowCap lay.size v.cap.toNat minCap with
    | none => .error .unsupported
    | some newCap =>
      if Nat.beq lay.size 0 then
        .ok (m, { v with cap := UInt64.ofNat newCap })
      else
        let copyByteCount := v.len.toNat * lay.size
        let copiedRes : Except FaultKind (List AllocByte) :=
          if Nat.beq copyByteCount 0 then
            .ok []
          else
            match v.ptr.allocId with
            | none => .error .undefined
            | some oldAid =>
              readBytes m ⟨oldAid, v.ptr.offsetBytes.toNat⟩
                copyByteCount lay.alignLog2
        match copiedRes with
        | .error k => .error k
        | .ok oldBytes =>
          let retiredRes : Except FaultKind MemoryState :=
            if Nat.beq v.cap.toNat 0 then
              .ok m
            else
              retireHeapBuffer m v.ptr
          match retiredRes with
          | .error k => .error k
          | .ok m1 =>
            let (m2, newPtr) := allocHeapBuffer m1 (newCap * lay.size)
              lay.alignLog2
            let writeRes : Except FaultKind MemoryState :=
              if Nat.beq copyByteCount 0 then
                .ok m2
              else
                match newPtr.allocId with
                | none => .error .undefined
                | some newAid =>
                  writeBytes m2 ⟨newAid, 0⟩ lay.alignLog2 oldBytes
            match writeRes with
            | .error k => .error k
            | .ok m3 =>
              .ok (m3, { v with
                ptr := newPtr
                cap := UInt64.ofNat newCap })

/-- Advance pointer `p` by `elemCount` elements of size `elemSize`, checking
that the resulting byte offset fits within the live allocation (when
`p.allocId = some _`). -/
noncomputable def ptrAdvanceElem (m : MemoryState) (elemSize : Nat)
    (p : PtrVal) (elemCount : Nat) : Except FaultKind PtrVal :=
  if Nat.beq elemSize 0 then
    .ok p
  else
    ptrAddInMem m elemSize p elemCount

/-- Convert `Nat` to canonical `usize` `ScalarVal`. -/
noncomputable def usizeScalarVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 n)⟩

/-! ## Reference Read/Write Helpers for `Vec` and `Box` -/

/-- Validate and decode a `Vec<elem>` accessed through `selfPtr : &Vec<elem>`
or `&mut Vec<elem>`. -/
noncomputable def readVecFromRef (m : MemoryState) (reqMut : Bool)
    (elem : MirTy) (selfPtr : PtrVal) : Except FaultKind VecModel :=
  if !isSupportedPointeeTy elem then
    .error .unsupported
  else
    let refMut := if reqMut then Mutability.mut else Mutability.shared
    match refValidInMem m refMut (.vec elem) (.ptr selfPtr) with
    | .error k => .error k
    | .ok () =>
      match selfPtr.allocId with
      | none => .error .undefined
      | some aid =>
        match loadIndirectV2 m (.vec elem) ⟨aid, selfPtr.offsetBytes.toNat⟩ with
        | .ok (some (.vec bufPtr cap len)) =>
          let model : VecModel := ⟨elem, bufPtr, cap, len⟩
          match vecValidInMem m reqMut model with
          | .error k => .error k
          | .ok () => .ok model
        | .ok _ => .error .undefined
        | .error k => .error k

/-- Write updated `VecModel` back through `selfPtr : &mut Vec<elem>`. -/
noncomputable def writeVecToRef (m : MemoryState) (selfPtr : PtrVal)
    (v : VecModel) : Except FaultKind MemoryState :=
  match selfPtr.allocId with
  | none => .error .undefined
  | some aid =>
    storeIndirectV2 m (.vec v.elem) ⟨aid, selfPtr.offsetBytes.toNat⟩ v.toVal

/-- Validate and decode a `Box<pointee>` accessed through `selfPtr`. -/
noncomputable def readBoxFromRef (m : MemoryState) (reqMut : Bool)
    (pointee : MirTy) (selfPtr : PtrVal) : Except FaultKind BoxModel :=
  let refMut := if reqMut then Mutability.mut else Mutability.shared
  match refValidInMem m refMut (.box pointee) (.ptr selfPtr) with
  | .error k => .error k
  | .ok () =>
    match selfPtr.allocId with
    | none => .error .undefined
    | some aid =>
      match loadIndirectV2 m (.box pointee)
          ⟨aid, selfPtr.offsetBytes.toNat⟩ with
      | .ok (some (.boxPtr boxP optLen)) =>
        let model : BoxModel := ⟨pointee, boxP, optLen⟩
        match boxValidInMem m reqMut model with
        | .error k => .error k
        | .ok () => .ok model
      | .ok _ => .error .undefined
      | .error k => .error k

/-! ## `Vec<T>` Contract Operations -/

/-- `alloc::vec::Vec::<T>::new()` (`library/alloc/src/vec/mod.rs:463-465`
and `library/alloc/src/raw_vec/mod.rs:571-575`):

> "pub const fn new() -> Self {
>     Vec { buf: RawVec::new(), len: 0 }
> }"

> "// `cap: 0` means \"unallocated\". zero-sized types are ignored."

`RawVec::new_in` sets the pointer to `NonNull::without_provenance` of the
alignment, which is `danglingAligned`. -/
noncomputable def evalVecNew (elem : MirTy) : Except FaultKind Val :=
  if !isSupportedPointeeTy elem then
    .error .unsupported
  else
    match layoutOfTyV2 elem with
    | none => .error .unsupported
    | some lay => .ok (.vec (danglingAligned lay.alignLog2) 0 0)

/-- `alloc::vec::Vec::<T>::with_capacity(capacity: usize)`, which reaches
`RawVecInner::try_allocate_in` (`library/alloc/src/raw_vec/mod.rs:446-481`):

> "let layout = match layout_array(capacity, elem_layout) {
>     Ok(layout) => layout,
>     Err(_) => return Err(CapacityOverflow.into()),
> };
>
> // Don't allocate here because `Drop` will not deallocate when `capacity`
> is 0.
> if layout.size() == 0 {
>     return Ok(Self::new_in(alloc, elem_layout.alignment()));
> }"

(The comment line is wrapped here.) The model allocates exactly `capacity`
elements, as `try_allocate_in` does (it sets `cap` to `capacity`), and faults
with `.unsupported` (a capacity-overflow panic) when
`capacity * size > isize::MAX`. -/
noncomputable def evalVecWithCapacity (m : MemoryState) (elem : MirTy)
    (cap : UInt64) : Except FaultKind (Val × MemoryState) :=
  if !isSupportedPointeeTy elem then
    .error .unsupported
  else
    match layoutOfTyV2 elem with
    | none => .error .unsupported
    | some lay =>
      let totalBytes := cap.toNat * lay.size
      if !Nat.blt totalBytes isizeMaxBytes then
        .error .unsupported
      else if Nat.beq totalBytes 0 then
        .ok (.vec (danglingAligned lay.alignLog2) cap 0, m)
      else
        let (m1, p) := allocHeapBuffer m totalBytes lay.alignLog2
        .ok (.vec p cap 0, m1)

/-- `alloc::vec::Vec::<T>::len(&self) -> usize`, a read of the `len` field
(`library/alloc/src/vec/mod.rs:3060-3068`). -/
noncomputable def evalVecLen (m : MemoryState) (elem : MirTy)
    (selfPtr : PtrVal) : Except FaultKind Val :=
  match readVecFromRef m false elem selfPtr with
  | .error k => .error k
  | .ok v => .ok (usizeScalarVal v.len.toNat)

/-- `alloc::vec::Vec::<T>::push(&mut self, value: T)`, which calls `push_mut`
(`library/alloc/src/vec/mod.rs:1035-1049`):

> "let len = self.len;
> ...
> if len == self.buf.capacity() {
>     self.buf.grow_one();
> }
> unsafe {
>     let end = self.as_mut_ptr().add(len);
>     ptr::write(end, value);
>     self.len = len + 1;"

`grow_one` is `grow_amortized(cap, 1)` (`raw_vec/mod.rs:490-494`), modeled by
`ensureVecCapacity` with `minCap = len + 1`. -/
noncomputable def evalVecPush (m : MemoryState) (elem : MirTy)
    (selfPtr : PtrVal) (value : Val) : Except FaultKind MemoryState :=
  if !checkValV2 value elem then
    .error .unsupported
  else
    match readVecFromRef m true elem selfPtr, layoutOfTyV2 elem,
        encodeValV2 profileV2TargetEndian elem value with
    | .error k, _, _ => .error k
    | _, none, _ => .error .unsupported
    | _, _, .error k => .error k
    | .ok v, some lay, .ok valBytes =>
      let newLen := v.len.toNat + 1
      match ensureVecCapacity m lay v newLen with
      | .error k => .error k
      | .ok (m1, v1) =>
        let writeRes : Except FaultKind MemoryState :=
          if Nat.beq lay.size 0 then
            .ok m1
          else
            match v1.ptr.allocId with
            | none => .error .undefined
            | some aid =>
              let off := v1.ptr.offsetBytes.toNat + v1.len.toNat * lay.size
              writeBytes m1 ⟨aid, off⟩ lay.alignLog2 valBytes
        match writeRes with
        | .error k => .error k
        | .ok m2 =>
          writeVecToRef m2 selfPtr { v1 with len := UInt64.ofNat newLen }

/-- `alloc::vec::Vec::<T>::reserve(&mut self, additional: usize)`
(`library/alloc/src/vec/mod.rs:1470-1472` and
`library/alloc/src/raw_vec/mod.rs:766-768`):

> "pub fn reserve(&mut self, additional: usize) {
>     self.buf.reserve(self.len, additional);
> }"

> "additional > self.capacity(elem_layout.size()).wrapping_sub(len)"

The model grows exactly when `len + additional > cap`; an overflowing
`len + additional` is a capacity-overflow panic (`.unsupported`). -/
noncomputable def evalVecReserve (m : MemoryState) (elem : MirTy)
    (selfPtr : PtrVal) (additional : UInt64) :
    Except FaultKind MemoryState :=
  match readVecFromRef m true elem selfPtr, layoutOfTyV2 elem with
  | .error k, _ => .error k
  | _, none => .error .unsupported
  | .ok v, some lay =>
    let minCap := v.len.toNat + additional.toNat
    if !Nat.blt minCap (Nat.pow 2 64) then
      .error .unsupported
    else
      match ensureVecCapacity m lay v minCap with
      | .error k => .error k
      | .ok (m1, v1) => writeVecToRef m1 selfPtr v1

/-- `alloc::vec::Vec::<T>::resize(&mut self, new_len: usize, value: T)`
(`library/alloc/src/vec/mod.rs:3529-3537`):

> "if new_len > len {
>     self.extend_with(new_len - len, value)
> } else {
>     self.truncate(new_len);
> }"

`extend_with` calls `self.reserve(n)` and then writes `n` copies of `value`;
`truncate` sets `len` and runs `ptr::drop_in_place` on the tail, which is a
no-op for the modeled scalar and unit element types, so the tail bytes keep
their values, and it never deallocates. -/
noncomputable def evalVecResize (m : MemoryState) (elem : MirTy)
    (selfPtr : PtrVal) (newLen : UInt64) (value : Val) :
    Except FaultKind MemoryState :=
  if !checkValV2 value elem then
    .error .unsupported
  else
    match readVecFromRef m true elem selfPtr, layoutOfTyV2 elem,
        encodeValV2 profileV2TargetEndian elem value with
    | .error k, _, _ => .error k
    | _, none, _ => .error .unsupported
    | _, _, .error k => .error k
    | .ok v, some lay, .ok valBytes =>
      if Nat.ble newLen.toNat v.len.toNat then
        writeVecToRef m selfPtr { v with len := newLen }
      else
        match ensureVecCapacity m lay v newLen.toNat with
        | .error k => .error k
        | .ok (m1, v1) =>
          let addCount := newLen.toNat - v1.len.toNat
          let fillRes : Except FaultKind MemoryState :=
            if Nat.beq lay.size 0 then
              .ok m1
            else
              match v1.ptr.allocId with
              | none => .error .undefined
              | some aid =>
                let off := v1.ptr.offsetBytes.toNat + v1.len.toNat * lay.size
                writeBytes m1 ⟨aid, off⟩ lay.alignLog2
                  (repeatBytes addCount valBytes)
          match fillRes with
          | .error k => .error k
          | .ok m2 => writeVecToRef m2 selfPtr { v1 with len := newLen }

/-- `alloc::vec::Vec::<T>::extend_from_slice(&mut self, other: &[T])`, which
for the modeled scalar element types reaches `append_elements`
(`library/alloc/src/vec/mod.rs:2937-2946`):

> "let count = other.len();
> self.reserve(count);
> let len = self.len();
> if count > 0 {
>     ...
> }
> self.len += count;"

where the elided lines copy `count` elements from `other` to index `len`.
As upstream does, the model reserves before it reads the source: when growth
retires a buffer that `other` points into, reading the source from the
post-reserve memory faults with `.undefined` rather than copying stale
bytes. The elided copy is `ptr::copy_nonoverlapping`, so a source that
overlaps the destination range also faults with `.undefined`. -/
noncomputable def evalVecExtendFromSlice (m : MemoryState) (elem : MirTy)
    (selfPtr srcPtr : PtrVal) (srcLen : UInt64) :
    Except FaultKind MemoryState :=
  match readVecFromRef m true elem selfPtr,
      heapBufValidInMem m false elem srcPtr srcLen srcLen,
      layoutOfTyV2 elem with
  | .error k, _, _ => .error k
  | _, .error k, _ => .error k
  | _, _, none => .error .unsupported
  | .ok v, .ok (), some lay =>
    let newLen := v.len.toNat + srcLen.toNat
    if !Nat.blt newLen (Nat.pow 2 64) then
      .error .unsupported
    else
      match ensureVecCapacity m lay v newLen with
      | .error k => .error k
      | .ok (m1, v1) =>
        let srcByteCount := srcLen.toNat * lay.size
        let srcBytesRes : Except FaultKind (List AllocByte) :=
          if Nat.beq srcByteCount 0 then
            .ok []
          else
            match srcPtr.allocId with
            | none => .error .undefined
            | some srcAid =>
              readBytes m1 ⟨srcAid, srcPtr.offsetBytes.toNat⟩ srcByteCount
                lay.alignLog2
        match srcBytesRes with
        | .error k => .error k
        | .ok srcBytes =>
          let writeRes : Except FaultKind MemoryState :=
            if Nat.beq srcByteCount 0 then
              .ok m1
            else
              match v1.ptr.allocId with
              | none => .error .undefined
              | some dstAid =>
                let off := v1.ptr.offsetBytes.toNat + v1.len.toNat * lay.size
                let srcOff := srcPtr.offsetBytes.toNat
                let sameAlloc : Bool :=
                  match srcPtr.allocId with
                  | none => false
                  | some srcAid => Nat.beq srcAid dstAid
                -- `ptr::copy_nonoverlapping` is UB on overlapping ranges.
                if sameAlloc && Nat.blt srcOff (off + srcByteCount) &&
                    Nat.blt off (srcOff + srcByteCount) then
                  .error .undefined
                else
                  writeBytes m1 ⟨dstAid, off⟩ lay.alignLog2 srcBytes
          match writeRes with
          | .error k => .error k
          | .ok m2 =>
            writeVecToRef m2 selfPtr { v1 with len := UInt64.ofNat newLen }

/-- `<alloc::vec::Vec<T> as Index<usize>>::index` and `IndexMut::index_mut`
(`library/alloc/src/vec/mod.rs:3866-3881`):

> "fn index(&self, index: I) -> &Self::Output {
>     Index::index(&**self, index)
> }"

which indexes the `len`-element slice; for `I = usize` that is the built-in
place `&(*slice)[self]` (`library/core/src/slice/index.rs:269-279`), guarded
by a bounds-check `Assert`. An index `idx >= len` therefore panics, which
faults with `.unsupported`. -/
noncomputable def evalVecIndex (m : MemoryState) (reqMut : Mutability)
    (elem : MirTy) (selfPtr : PtrVal) (idx : UInt64) :
    Except FaultKind Val :=
  let isMut := Mutability.beq reqMut .mut
  match readVecFromRef m isMut elem selfPtr, layoutOfTyV2 elem with
  | .error k, _ => .error k
  | _, none => .error .unsupported
  | .ok v, some lay =>
    if !Nat.blt idx.toNat v.len.toNat then
      .error .unsupported
    else
      match ptrAdvanceElem m lay.size v.ptr idx.toNat with
      | .error k => .error k
      | .ok elemPtr =>
        match refValidInMem m reqMut elem (.ptr elemPtr) with
        | .error k => .error k
        | .ok () => .ok (.ptr elemPtr)

/-- `<alloc::vec::Vec<T> as Deref>::deref` and `DerefMut::deref_mut`
(`library/alloc/src/vec/mod.rs:3789-3805`), which return
`self.as_slice()` / `self.as_mut_slice()`: the slice of the first `len`
elements of the buffer. -/
noncomputable def evalVecDeref (m : MemoryState) (reqMut : Mutability)
    (elem : MirTy) (selfPtr : PtrVal) : Except FaultKind Val :=
  let isMut := Mutability.beq reqMut .mut
  match readVecFromRef m isMut elem selfPtr with
  | .error k => .error k
  | .ok v =>
    match refValidInMem m reqMut (.slice elem) (.slicePtr v.ptr v.len) with
    | .error k => .error k
    | .ok () => .ok (.slicePtr v.ptr v.len)

/-! ## `Box<[T]>` and `Box<T>` Contract Operations -/

/-- `<alloc::boxed::Box<[T]> as From<alloc::vec::Vec<T>>>::from(v)`
(`library/alloc/src/vec/mod.rs:4463-4486`), which is
`v.into_boxed_slice()` (`:1733-1740`):

> "self.shrink_to_fit();
> let me = ManuallyDrop::new(self);
> let buf = ptr::read(&me.buf);
> let len = me.len();
> buf.into_box(len).assume_init()"

`Vec::shrink_to_fit` (`:1604-1611`) calls `self.buf.shrink_to_fit(self.len)`
only `if self.capacity() > self.len`, and `RawVecInner::shrink_unchecked`
(`library/alloc/src/raw_vec/mod.rs:835-860`) returns early for an unallocated
or zero-sized buffer, deallocates when shrinking to `0`, and otherwise calls
`Allocator::shrink`:

> "// If shrinking to 0, deallocate the buffer. We don't reach this point
> // for the T::IS_ZST case since current_memory() will have returned
> // None.
> if cap == 0 {
>     unsafe { self.alloc.deallocate(ptr, layout) };"

Following Miri, a reallocation is a fresh allocation plus a copy of the `len`
initialized elements, so the old `AllocId` is retired and any pointer into the
old buffer (including its excess capacity) loses its provenance. When
`cap = len`, or for zero-sized elements, the buffer is kept unchanged. -/
noncomputable def evalBoxFromVec (m : MemoryState) (elem : MirTy)
    (ptr : PtrVal) (cap len : UInt64) : Except FaultKind (Val × MemoryState) :=
  let v : VecModel := ⟨elem, ptr, cap, len⟩
  match vecValidInMem m true v, layoutOfTyV2 elem with
  | .error k, _ => .error k
  | _, none => .error .unsupported
  | .ok (), some lay =>
    if Nat.beq lay.size 0 || Nat.beq cap.toNat len.toNat then
      .ok (.boxPtr ptr (some len), m)
    else
      let byteCount := len.toNat * lay.size
      match ptr.allocId with
      | none => .error .undefined
      | some oldAid =>
        let copiedRes : Except FaultKind (List AllocByte) :=
          if Nat.beq byteCount 0 then
            .ok []
          else
            readBytes m ⟨oldAid, ptr.offsetBytes.toNat⟩ byteCount lay.alignLog2
        match copiedRes with
        | .error k => .error k
        | .ok bytes =>
          match retireHeapBuffer m ptr with
          | .error k => .error k
          | .ok m1 =>
            if Nat.beq byteCount 0 then
              .ok (.boxPtr (danglingAligned lay.alignLog2) (some len), m1)
            else
              let (m2, newPtr) := allocHeapBuffer m1 byteCount lay.alignLog2
              match newPtr.allocId with
              | none => .error .undefined
              | some newAid =>
                match writeBytes m2 ⟨newAid, 0⟩ lay.alignLog2 bytes with
                | .error k => .error k
                | .ok m3 => .ok (.boxPtr newPtr (some len), m3)

/-- `<alloc::boxed::Box<P> as Deref>::deref` and `DerefMut::deref_mut`
(`library/alloc/src/boxed.rs:2251-2264`), which are
`&**self` / `&mut **self`: a reference to the boxed value (or slice). -/
noncomputable def evalBoxDeref (m : MemoryState) (reqMut : Mutability)
    (pointee : MirTy) (selfPtr : PtrVal) : Except FaultKind Val :=
  let isMut := Mutability.beq reqMut .mut
  match readBoxFromRef m isMut pointee selfPtr with
  | .error k => .error k
  | .ok b =>
    match b.pointee, b.len with
    | .slice _, some len =>
      let res := Val.slicePtr b.ptr len
      match refValidInMem m reqMut b.pointee res with
      | .error k => .error k
      | .ok () => .ok res
    | pt, none =>
      if isUnsizedTy pt then
        .error .unsupported
      else
        let res := Val.ptr b.ptr
        match refValidInMem m reqMut pt res with
        | .error k => .error k
        | .ok () => .ok res
    | _, _ => .error .unsupported

/-- `<alloc::boxed::Box<P> as Clone>::clone(&self)`
(`library/alloc/src/boxed.rs:2043-2049` for sized `P`, `:2077-2081` for
`P = [T]`):

> "let mut boxed = Self::new_uninit_in(self.1.clone());"

> "self.to_vec_in(alloc).into_boxed_slice()"

Both allocate a fresh buffer of exactly the boxed size (the `into_boxed_slice`
shrink is a no-op because `to_vec_in` allocates `len` elements) and copy the
boxed bytes, so the clone never shares the original's allocation. -/
noncomputable def evalBoxClone (m : MemoryState) (pointee : MirTy)
    (selfPtr : PtrVal) : Except FaultKind (Val × MemoryState) :=
  match readBoxFromRef m false pointee selfPtr with
  | .error k => .error k
  | .ok b =>
    let elemAndCount : Except FaultKind (LayoutData × Nat) :=
      match b.pointee, b.len with
      | .slice elem, some len =>
        match layoutOfTyV2 elem with
        | none => .error .unsupported
        | some lay => .ok (lay, len.toNat)
      | pt, none =>
        if isUnsizedTy pt then
          .error .unsupported
        else
          match layoutOfTyV2 pt with
          | none => .error .unsupported
          | some lay => .ok (lay, 1)
      | _, _ => .error .unsupported
    match elemAndCount with
    | .error k => .error k
    | .ok (lay, count) =>
      let totalBytes := count * lay.size
      if Nat.beq totalBytes 0 then
        .ok (.boxPtr (danglingAligned lay.alignLog2) b.len, m)
      else
        match b.ptr.allocId with
        | none => .error .undefined
        | some srcAid =>
          match readBytes m ⟨srcAid, b.ptr.offsetBytes.toNat⟩ totalBytes
              lay.alignLog2 with
          | .error k => .error k
          | .ok copiedBytes =>
            let (m1, newPtr) := allocHeapBuffer m totalBytes lay.alignLog2
            match newPtr.allocId with
            | none => .error .undefined
            | some newAid =>
              match writeBytes m1 ⟨newAid, 0⟩ lay.alignLog2 copiedBytes with
              | .error k => .error k
              | .ok m2 => .ok (.boxPtr newPtr b.len, m2)

/-- `alloc::boxed::Box::<T>::new(x: T)` (`library/alloc/src/boxed.rs:284-291`):

> "let ptr = box_new_uninit(<T as SizedTypeProperties>::LAYOUT) as *mut T;
> ...
> unsafe { core::intrinsics::write_via_move(ptr, x) };"

`box_new_uninit` (`:247-252`) calls `Global.allocate(layout)`, which for a
zero-sized `T` returns a dangling pointer without allocating, and calls
`handle_alloc_error` on failure, which is not modeled. -/
noncomputable def evalBoxNew (m : MemoryState) (pointee : MirTy)
    (value : Val) : Except FaultKind (Val × MemoryState) :=
  if isUnsizedTy pointee || !isSupportedPointeeTy pointee ||
      !checkValV2 value pointee then
    .error .unsupported
  else
    match layoutOfTyV2 pointee,
        encodeValV2 profileV2TargetEndian pointee value with
    | none, _ => .error .unsupported
    | _, .error k => .error k
    | some lay, .ok valBytes =>
      if Nat.beq lay.size 0 then
        .ok (.boxPtr (danglingAligned lay.alignLog2) none, m)
      else
        let (m1, newPtr) := allocHeapBuffer m lay.size lay.alignLog2
        match newPtr.allocId with
        | none => .error .undefined
        | some newAid =>
          match writeBytes m1 ⟨newAid, 0⟩ lay.alignLog2 valBytes with
          | .error k => .error k
          | .ok m2 => .ok (.boxPtr newPtr none, m2)

/-! ## `CoreCallOp` Dispatch Entrypoint -/

/-- Execute an allocation `CoreCallOp` in `m`, returning `none` when `op` is
not an allocation contract operation (so `Step.lean` falls back to
`execCoreCallOp`). -/
noncomputable def execAllocCoreCall (m : MemoryState) (op : CoreCallOp)
    (args : List (MirTy × Val)) (dstTy : MirTy) :
    Option (Except FaultKind (Val × MemoryState)) :=
  match op, args with
  | .vecNew elem, [] =>
    if !MirTy.beq dstTy (.vec elem) then
      some (.error .unsupported)
    else
      some (match evalVecNew elem with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .vecNew _, _ => some (.error .unsupported)
  | .vecWithCapacity elem, [(.int .isize false, .scalar capSv)] =>
    if !MirTy.beq dstTy (.vec elem) then
      some (.error .unsupported)
    else
      some (evalVecWithCapacity m elem (UInt64.ofNat capSv.bits.toNat))
  | .vecWithCapacity _, _ => some (.error .unsupported)
  | .vecLen, [(.ref _ (.vec elem), .ptr selfPtr)] =>
    if !MirTy.beq dstTy (.int .isize false) then
      some (.error .unsupported)
    else
      some (match evalVecLen m elem selfPtr with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .vecLen, _ => some (.error .unsupported)
  | .vecPush, [(.ref .mut (.vec elem), .ptr selfPtr), (valTy, val)] =>
    if !MirTy.beq dstTy .unit || !MirTy.beq valTy elem then
      some (.error .unsupported)
    else
      some (match evalVecPush m elem selfPtr val with
        | .error k => .error k
        | .ok m1 => .ok (.unit, m1))
  | .vecPush, _ => some (.error .unsupported)
  | .vecResize,
      [(.ref .mut (.vec elem), .ptr selfPtr),
       (.int .isize false, .scalar lenSv),
       (valTy, val)] =>
    if !MirTy.beq dstTy .unit || !MirTy.beq valTy elem then
      some (.error .unsupported)
    else
      some (match evalVecResize m elem selfPtr
          (UInt64.ofNat lenSv.bits.toNat) val with
        | .error k => .error k
        | .ok m1 => .ok (.unit, m1))
  | .vecResize, _ => some (.error .unsupported)
  | .vecExtendFromSlice,
      [(.ref .mut (.vec elem), .ptr selfPtr),
       (.ref _ (.slice sliceElem), .slicePtr srcPtr srcLen)] =>
    if !MirTy.beq dstTy .unit || !MirTy.beq sliceElem elem then
      some (.error .unsupported)
    else
      some (match evalVecExtendFromSlice m elem selfPtr srcPtr srcLen with
        | .error k => .error k
        | .ok m1 => .ok (.unit, m1))
  | .vecExtendFromSlice, _ => some (.error .unsupported)
  | .vecIndex,
      [(.ref inMut (.vec elem), .ptr selfPtr),
       (.int .isize false, .scalar idxSv)] =>
    if !MirTy.beq dstTy (.ref .shared elem) then
      some (.error .unsupported)
    else
      let _ := inMut
      some (match evalVecIndex m .shared elem selfPtr
          (UInt64.ofNat idxSv.bits.toNat) with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .vecIndex, _ => some (.error .unsupported)
  | .vecIndexMut,
      [(.ref .mut (.vec elem), .ptr selfPtr),
       (.int .isize false, .scalar idxSv)] =>
    if !MirTy.beq dstTy (.ref .mut elem) then
      some (.error .unsupported)
    else
      some (match evalVecIndex m .mut elem selfPtr
          (UInt64.ofNat idxSv.bits.toNat) with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .vecIndexMut, _ => some (.error .unsupported)
  | .vecDeref, [(.ref _ (.vec elem), .ptr selfPtr)] =>
    if !MirTy.beq dstTy (.ref .shared (.slice elem)) then
      some (.error .unsupported)
    else
      some (match evalVecDeref m .shared elem selfPtr with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .vecDeref, _ => some (.error .unsupported)
  | .vecDerefMut, [(.ref .mut (.vec elem), .ptr selfPtr)] =>
    if !MirTy.beq dstTy (.ref .mut (.slice elem)) then
      some (.error .unsupported)
    else
      some (match evalVecDeref m .mut elem selfPtr with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .vecDerefMut, _ => some (.error .unsupported)
  | .vecReserve,
      [(.ref .mut (.vec elem), .ptr selfPtr),
       (.int .isize false, .scalar addSv)] =>
    if !MirTy.beq dstTy .unit then
      some (.error .unsupported)
    else
      some (match evalVecReserve m elem selfPtr
          (UInt64.ofNat addSv.bits.toNat) with
        | .error k => .error k
        | .ok m1 => .ok (.unit, m1))
  | .vecReserve, _ => some (.error .unsupported)
  | .boxFromVec, [(.vec elem, .vec ptr cap len)] =>
    if !MirTy.beq dstTy (.box (.slice elem)) then
      some (.error .unsupported)
    else
      some (evalBoxFromVec m elem ptr cap len)
  | .boxFromVec, _ => some (.error .unsupported)
  | .boxDeref, [(.ref _ (.box pointee), .ptr selfPtr)] =>
    if !MirTy.beq dstTy (.ref .shared pointee) then
      some (.error .unsupported)
    else
      some (match evalBoxDeref m .shared pointee selfPtr with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .boxDeref, _ => some (.error .unsupported)
  | .boxDerefMut, [(.ref .mut (.box pointee), .ptr selfPtr)] =>
    if !MirTy.beq dstTy (.ref .mut pointee) then
      some (.error .unsupported)
    else
      some (match evalBoxDeref m .mut pointee selfPtr with
        | .error k => .error k
        | .ok v => .ok (v, m))
  | .boxDerefMut, _ => some (.error .unsupported)
  | .boxClone, [(.ref _ (.box pointee), .ptr selfPtr)] =>
    if !MirTy.beq dstTy (.box pointee) then
      some (.error .unsupported)
    else
      some (evalBoxClone m pointee selfPtr)
  | .boxClone, _ => some (.error .unsupported)
  | .boxNew pointee, [(valTy, val)] =>
    if !MirTy.beq valTy pointee || !MirTy.beq dstTy (.box pointee) then
      some (.error .unsupported)
    else
      some (evalBoxNew m pointee val)
  | .boxNew _, _ => some (.error .unsupported)
  | _, _ => none

end Trusted.MirSemantics

end
