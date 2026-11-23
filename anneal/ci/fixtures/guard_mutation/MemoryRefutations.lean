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

end GuardMutation
