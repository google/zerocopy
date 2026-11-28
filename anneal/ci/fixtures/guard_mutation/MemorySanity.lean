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
# Positive Memory Sanity Check for Guard-Mutation CI

Confirms that ordinary in-bounds, aligned, live, mutable stack allocation,
write, read, and deallocation continue to succeed on every single-guard mutant
of `Trusted/MirSemantics/Memory.lean`.
It also holds every `Memory` anti-overreach positive canary, including the
Profile v2 ones, plus the helpers those canaries share with
`MemoryRefutations.lean` and `ProfileV2MemoryRefutations.lean`, which import
this module. Keeping positive canaries out of the refutation modules matters:
a refutation module is expected to fail to compile on its mutant, so a
positive canary inside it could break unnoticed.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

theorem positive_sanity_memory_roundtrip :
    (let (m1, p) := allocateStack MemoryState.empty ⟨4, 2⟩
     let bs : List AllocByte :=
       [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
     match writeBytes m1 p 2 bs with
     | .error _ => False
     | .ok m2 =>
       match readBytes m2 p 4 2 with
       | .error _ => False
       | .ok got =>
         match writeBytes m2 p 2 [] with
         | .error _ => False
         | .ok m3 =>
           match readBytes m3 p 0 2 with
           | .error _ => False
           | .ok emptyBs =>
             match deallocateStack m3 p with
             | .error _ => False
             | .ok _ => got = bs ∧ emptyBs = [] ∧ m3 = m2) :=
  ⟨rfl, rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- Profile v2 helpers and canaries (shared with
-- `ProfileV2MemoryRefutations.lean`)
-- ---------------------------------------------------------------------------

/-- Live mutable 4-byte, 4-byte-aligned allocation with id `1`. -/
noncomputable def v2LiveMut4Alloc : Allocation := {
  allocId := 1
  alignLog2 := 2
  mutability := .mut
  bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
  live := true
}

/-- Single-allocation `MemoryState` helper. -/
noncomputable def v2SingleAllocMem (a : Allocation) : MemoryState :=
  { nextAllocId := 2, allocations := [a] }

/-- Anti-overreach Profile v2 memory canaries: an in-range
`sliceGetUncheckedCheck`, an in-bounds `ptrAddInMem` on a live allocation, and
two valid `sliceFromRawPartsCheck` calls (a provenance-bearing in-bounds slice
and a provenance-free, aligned, zero-length `&[u32]`) succeed. -/
theorem positive_sanity_v2_memory :
    sliceGetUncheckedCheck (v2SingleAllocMem v2LiveMut4Alloc)
      ⟨some 1, 0, .isize⟩ 4 1 3 = .ok (.slicePtr ⟨some 1, 1, .isize⟩ 2) ∧
    ptrAddInMem (v2SingleAllocMem v2LiveMut4Alloc) 1
      ⟨some 1, 1, .isize⟩ 2 = .ok ⟨some 1, 3, .isize⟩ ∧
    sliceFromRawPartsCheck (v2SingleAllocMem v2LiveMut4Alloc) true 1 0
      ⟨some 1, 0, .isize⟩ 4 = .ok (.slicePtr ⟨some 1, 0, .isize⟩ 4) ∧
    sliceFromRawPartsCheck MemoryState.empty false 4 2
      ⟨none, 4, .isize⟩ 0 = .ok (.slicePtr ⟨none, 4, .isize⟩ 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Live mutable 4-byte, 4-byte-aligned (`alignLog2 = 2`) allocation with id
`1`. -/
noncomputable def liveMut4Alloc : Allocation := {
  allocId := 1
  alignLog2 := 2
  mutability := .mut
  bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
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

/-- Anti-overreach canary for `mem_v2_entry_raw_ptr_arg_fresh`: when no
parameter has a raw-pointer type, `entryMemoryForArgsV2` reduces to
`entryMemoryWithCaller` without advancing `nextAllocId`. -/
theorem positive_mem_v2_entry_non_raw_ptr_arg_unchanged :
    let emptyCm : CallerMemory := { allocations := [] }
    (entryMemoryForArgsV2 emptyCm [.int .i32 false]
      [.scalar ⟨.i32, false, 0⟩]).nextAllocId = 2 :=
  rfl

/-- Anti-overreach canary for `mem_v2_slice_get_unchecked_elem_size`: an
in-bounds zero-length `sliceGetUncheckedCheck` with `elemSize = 4` and
`startOff = 1` on a 4-byte allocation succeeds. -/
theorem positive_mem_v2_slice_get_unchecked_elem_size_in_bounds :
    (match sliceGetUncheckedCheck (singleAllocMem liveMut4Alloc)
        ⟨some 1, 0, .isize⟩ 1 1 1 4 with
     | .ok _ => True
     | .error _ => False) :=
  trivial

/-- Anti-overreach canary for `mem_v2_entry_option_raw_ptr_val`: `None`
contributes `0` to `maxValPtrAllocId`. -/
theorem positive_mem_v2_entry_option_none_zero :
    maxValPtrAllocId (.optionVal none) = 0 :=
  rfl

end GuardMutation
