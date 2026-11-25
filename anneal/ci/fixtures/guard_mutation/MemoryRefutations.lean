-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Memory

/-!
# Negative Refutations for `Trusted.MirSemantics.Memory` UB Guards

Exercises every UB guard in `Trusted/MirSemantics/Memory.lean`:

- `deallocateStack`: non-zero offset, missing allocation, use-after-free,
  immutable allocation.
- `readBytes`: missing allocation, use-after-free, out-of-bounds, misaligned.
- `writeBytes`: missing allocation, use-after-free, out-of-bounds, misaligned,
  write to read-only allocation.
- `isAligned`: allocation alignment lower than access alignment, and access
  offset not divisible by access alignment.

Profile version 1 MIR instructions cannot yet construct arbitrary pointer
offsets or immutable allocations, so these refutations exercise the memory
operations directly. Importing only `Trusted.MirSemantics.Memory` also keeps
each `Memory.lean` mutant check under a quarter of a second.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Live mutable 4-byte, 4-byte-aligned (`alignLog2 = 2`) allocation with id
`1`. -/
noncomputable def liveMut4Alloc : Allocation := {
  allocId := 1
  alignLog2 := 2
  mutability := .mut
  bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
  live := true
}

/-- Live mutable 8-byte, 4-byte-aligned (`alignLog2 = 2`) allocation with id
`1`, used for offset-misalignment checks that stay in bounds. -/
noncomputable def liveMut8Alloc : Allocation := {
  allocId := 1
  alignLog2 := 2
  mutability := .mut
  bytes := List.replicate 8 (.init 0 none)
  live := true
}

/-- Live mutable 4-byte, 1-byte-aligned (`alignLog2 = 0`) allocation with id
`1`, used for allocation-alignment checks at offset `0`. -/
noncomputable def liveMut4Align1Alloc : Allocation := {
  allocId := 1
  alignLog2 := 0
  mutability := .mut
  bytes := List.replicate 4 (.init 0 none)
  live := true
}

/-- Already deallocated (`live = false`) 4-byte allocation with id `1`. -/
noncomputable def deadMut4Alloc : Allocation :=
  { liveMut4Alloc with live := false }

/-- Live immutable (`mutability = .shared`) 4-byte allocation with id `1`. -/
noncomputable def shared4Alloc : Allocation :=
  { liveMut4Alloc with mutability := .shared }

/-- Helper constructing a `MemoryState` containing a single allocation. -/
noncomputable def singleAllocMem (a : Allocation) : MemoryState :=
  { nextAllocId := 2, allocations := [a] }

/-- Four initialized bytes for `writeBytes` refutations. -/
noncomputable def fourBytes : List AllocByte :=
  [.init 9 none, .init 8 none, .init 7 none, .init 6 none]

/-- Guard `mem_dealloc_nonzero_offset`: deallocating at non-zero offset `1`
faults with `.undefined`. -/
theorem refute_mem_dealloc_nonzero_offset :
    deallocateStack (singleAllocMem liveMut4Alloc) ⟨1, 1⟩ =
      .error .undefined :=
  rfl

/-- Guard `mem_dealloc_missing_alloc`: deallocating a nonexistent allocation id
faults with `.undefined`. -/
theorem refute_mem_dealloc_missing_alloc :
    deallocateStack (singleAllocMem liveMut4Alloc) ⟨99, 0⟩ =
      .error .undefined :=
  rfl

/-- Guard `mem_dealloc_use_after_free`: double deallocation of an already dead
allocation faults with `.undefined`. -/
theorem refute_mem_dealloc_use_after_free :
    deallocateStack (singleAllocMem deadMut4Alloc) ⟨1, 0⟩ =
      .error .undefined :=
  rfl

/-- Guard `mem_dealloc_immutable`: deallocating a `.shared` allocation faults
with `.undefined`. -/
theorem refute_mem_dealloc_immutable :
    deallocateStack (singleAllocMem shared4Alloc) ⟨1, 0⟩ =
      .error .undefined :=
  rfl

/-- Guard `mem_read_missing_alloc`: reading from a nonexistent allocation id
faults with `.undefined`. -/
theorem refute_mem_read_missing_alloc :
    readBytes (singleAllocMem liveMut4Alloc) ⟨99, 0⟩ 4 2 =
      .error .undefined :=
  rfl

/-- Guard `mem_read_use_after_free`: reading from a deallocated allocation
faults with `.undefined`. -/
theorem refute_mem_read_use_after_free :
    readBytes (singleAllocMem deadMut4Alloc) ⟨1, 0⟩ 4 2 =
      .error .undefined :=
  rfl

/-- Guard `mem_read_out_of_bounds`: reading 4 bytes at offset 4 of a 4-byte
allocation (aligned, live, but out of bounds) faults with `.undefined`. -/
theorem refute_mem_read_out_of_bounds :
    readBytes (singleAllocMem liveMut4Alloc) ⟨1, 4⟩ 4 2 =
      .error .undefined :=
  rfl

/-- Guard `mem_read_misaligned`: reading 4 bytes with `alignLog2 = 2` at
offset `1` of a live 8-byte allocation faults with `.undefined`. -/
theorem refute_mem_read_misaligned :
    readBytes (singleAllocMem liveMut8Alloc) ⟨1, 1⟩ 4 2 =
      .error .undefined :=
  rfl

/-- Guard `mem_write_missing_alloc`: writing to a nonexistent allocation id
faults with `.undefined`. -/
theorem refute_mem_write_missing_alloc :
    writeBytes (singleAllocMem liveMut4Alloc) ⟨99, 0⟩ 2 fourBytes =
      .error .undefined :=
  rfl

/-- Guard `mem_write_use_after_free`: writing to a deallocated allocation
faults with `.undefined`. -/
theorem refute_mem_write_use_after_free :
    writeBytes (singleAllocMem deadMut4Alloc) ⟨1, 0⟩ 2 fourBytes =
      .error .undefined :=
  rfl

/-- Guard `mem_write_out_of_bounds`: writing 4 bytes at offset 4 of a 4-byte
allocation (aligned, live, mutable, but out of bounds) faults with
`.undefined`. -/
theorem refute_mem_write_out_of_bounds :
    writeBytes (singleAllocMem liveMut4Alloc) ⟨1, 4⟩ 2 fourBytes =
      .error .undefined :=
  rfl

/-- Guard `mem_write_misaligned`: writing 4 bytes with `alignLog2 = 2` at
offset `1` of a live mutable 8-byte allocation faults with `.undefined`. -/
theorem refute_mem_write_misaligned :
    writeBytes (singleAllocMem liveMut8Alloc) ⟨1, 1⟩ 2 fourBytes =
      .error .undefined :=
  rfl

/-- Guard `mem_write_readonly`: writing to a live, in-bounds, aligned `.shared`
allocation faults with `.undefined`. -/
theorem refute_mem_write_readonly :
    writeBytes (singleAllocMem shared4Alloc) ⟨1, 0⟩ 2 fourBytes =
      .error .undefined :=
  rfl

/-- Guard `mem_align_alloc_align_check`: reading with `alignLog2 = 2` at
offset `0` from an allocation whose own alignment is `alignLog2 = 0` faults
with `.undefined`. -/
theorem refute_mem_align_alloc_align_check :
    readBytes (singleAllocMem liveMut4Align1Alloc) ⟨1, 0⟩ 4 2 =
      .error .undefined :=
  rfl

/-- Guard `mem_align_offset_mod_check`: reading with `alignLog2 = 2` at
offset `1` from an `alignLog2 = 2` allocation faults with `.undefined`. -/
theorem refute_mem_align_offset_mod_check :
    readBytes (singleAllocMem liveMut8Alloc) ⟨1, 1⟩ 4 2 =
      .error .undefined :=
  rfl

/-- Live mutable 4-byte allocation whose bytes are all `.uninit`. -/
noncomputable def uninitMut4Alloc : Allocation := {
  allocId := 1
  alignLog2 := 0
  mutability := .mut
  bytes := List.replicate 4 .uninit
  live := true
}

/-- Guard `mem_v2_ptr_add_null_nonzero`: offsetting a provenance-free (null)
pointer by a nonzero byte delta faults with `.undefined`. -/
theorem refute_mem_v2_ptr_add_null_nonzero :
    ptrAddInMem MemoryState.empty 1 ⟨none, 0, .isize⟩ 1 = .error .undefined :=
  rfl

/-- Guard `mem_v2_ptr_add_oob`: offsetting a live pointer past the end of its
allocation faults with `.undefined`. -/
theorem refute_mem_v2_ptr_add_oob :
    ptrAddInMem (singleAllocMem liveMut4Alloc) 1 ⟨some 1, 2, .isize⟩ 3 =
      .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_null`: constructing even a zero-length slice from a
null (`⟨none, 0, .isize⟩`) pointer faults with `.undefined`. -/
theorem refute_mem_v2_slice_null :
    sliceFromRawPartsCheck MemoryState.empty false 1 0 ⟨none, 0, .isize⟩ 0 =
      .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_readonly`: constructing a mutable slice (`&mut [u8]`)
over a `.shared` allocation faults with `.undefined`. -/
theorem refute_mem_v2_slice_readonly :
    sliceFromRawPartsCheck (singleAllocMem shared4Alloc) true 1 0 ⟨some 1, 0, .isize⟩ 4 =
      .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_uninit`: constructing a byte slice over uninitialized
bytes faults with `.undefined`. -/
theorem refute_mem_v2_slice_uninit :
    sliceFromRawPartsCheck (singleAllocMem uninitMut4Alloc) false 1 0
      ⟨some 1, 0, .isize⟩ 4 = .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_get_unchecked_oob`: subslicing with `endOff > len`
faults with `.undefined` even when the underlying allocation has extra bytes. -/
theorem refute_mem_v2_slice_get_unchecked_oob :
    sliceGetUncheckedCheck (singleAllocMem liveMut8Alloc) ⟨some 1, 0, .isize⟩ 4 1 6 =
      .error .undefined :=
  rfl

/-- Guard `mem_read_zst_misaligned`: zero-size `readBytes` at a misaligned
offset (`alignLog2 = 2`, `offset = 1`) faults with `.undefined`. -/
theorem refute_mem_read_zst_misaligned :
    readBytes (singleAllocMem liveMut8Alloc) ⟨1, 1⟩ 0 2 =
      .error .undefined :=
  rfl

/-- Guard `mem_write_zst_misaligned`: zero-size `writeBytes` at a misaligned
offset (`alignLog2 = 2`, `offset = 1`) faults with `.undefined`. -/
theorem refute_mem_write_zst_misaligned :
    writeBytes (singleAllocMem liveMut8Alloc) ⟨1, 1⟩ 2 [] =
      .error .undefined :=
  rfl

/-- Zero-size `readBytes` at offset `0` from an allocation whose own alignment
(`alignLog2 = 0`) is below the requested `alignLog2 = 2` faults with
`.undefined`. -/
theorem refute_mem_read_zst_alloc_align :
    readBytes (singleAllocMem liveMut4Align1Alloc) ⟨1, 0⟩ 0 2 =
      .error .undefined :=
  rfl

/-- Zero-size `readBytes` on a deallocated (`live = false`) allocation still
checks alignment and faults with `.undefined` when misaligned. -/
theorem refute_mem_read_zst_dead_misaligned :
    readBytes (singleAllocMem deadMut4Alloc) ⟨1, 1⟩ 0 2 =
      .error .undefined :=
  rfl

/-- Zero-size `writeUninit` at a misaligned offset faults with `.undefined`. -/
theorem refute_mem_uninit_zst_misaligned :
    writeUninit (singleAllocMem liveMut8Alloc) ⟨1, 1⟩ 0 2 =
      .error .undefined :=
  rfl

/-- Zero-size `readBytes` / `writeBytes` against a nonexistent allocation id
faults with `.undefined`. -/
theorem refute_mem_zst_missing_alloc :
    readBytes (singleAllocMem liveMut4Alloc) ⟨99, 0⟩ 0 0 =
      .error .undefined ∧
    writeBytes (singleAllocMem liveMut4Alloc) ⟨99, 0⟩ 0 [] =
      .error .undefined :=
  ⟨rfl, rfl⟩

/-- Anti-overreach positive canaries matching `rustc` `get_place_alloc` /
`get_place_alloc_mut` and `lean-miri` (`checkAndDerefPtr` size-0 skip +
alignment-only check): aligned `size == 0` accesses succeed even when the
allocation is deallocated (`live = false`), read-only (`.shared`), or the
offset is out of bounds. -/
theorem positive_zst_alignment_only_canaries :
    readBytes (singleAllocMem deadMut4Alloc) ⟨1, 0⟩ 0 2 = .ok [] ∧
    writeBytes (singleAllocMem shared4Alloc) ⟨1, 0⟩ 2 [] =
      .ok (singleAllocMem shared4Alloc) ∧
    readBytes (singleAllocMem liveMut4Alloc) ⟨1, 8⟩ 0 2 = .ok [] ∧
    writeBytes (singleAllocMem liveMut4Alloc) ⟨1, 8⟩ 2 [] =
      .ok (singleAllocMem liveMut4Alloc) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Guard `mem_alloc_starts_uninit`: `allocateStack` initializes every byte
of a fresh allocation to `.uninit` rather than zero-initialized bytes. -/
theorem refute_mem_alloc_starts_uninit :
    (let (m1, p) := allocateStack MemoryState.empty ⟨4, 2⟩
     readBytes m1 p 4 2 = .ok (List.replicate 4 .uninit)) :=
  rfl

/-- Guard `mem_dealloc_clears_live`: `deallocateStack` marks the freed
allocation `live := false` so subsequent reads fault `.undefined`. -/
theorem refute_mem_dealloc_clears_live :
    (match deallocateStack (singleAllocMem liveMut4Alloc) ⟨1, 0⟩ with
     | .ok m1 => readBytes m1 ⟨1, 0⟩ 4 2 = .error .undefined
     | .error _ => False) :=
  rfl

/-- Guard `mem_alloc_id_fresh`: successive `allocateStack` calls produce
distinct `AllocId`s so freeing the first cannot invalidate the second. -/
theorem refute_mem_alloc_id_fresh :
    (let (m1, p1) := allocateStack MemoryState.empty ⟨4, 2⟩
     let (m2, p2) := allocateStack m1 ⟨4, 2⟩
     match deallocateStack m2 p1 with
     | .ok m3 =>
       match readBytes m3 p2 4 2 with
       | .ok _ => True
       | .error _ => False
     | .error _ => False) :=
  trivial

end GuardMutation
