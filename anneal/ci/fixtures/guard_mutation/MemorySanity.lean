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
It also holds the Profile v2 memory anti-overreach canaries (and the helpers
`ProfileV2MemoryRefutations.lean` imports), so every `Memory` mutant must keep
those valid operations working too.
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

end GuardMutation
