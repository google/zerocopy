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
import Trusted.MirSemantics.Step

/-!
# Positive Heap-Allocation Sanity Check for Guard-Mutation CI

Holds the shared helpers that `AllocRefutations.lean` imports and the
anti-overreach positive canaries for the `Vec`/`Box` guards in
`Trusted/MirSemantics/{AllocContracts,Bytes,Step}.lean`. The runner compiles
this module on every mutant of those guards and requires it to pass, so a
mutation that rejects valid heap buffers (rather than weakening a single
guard) is reported as an error, never as a kill.

Imports only `Trusted.*` modules, so mutants of `AllocContracts`, `Bytes`, and
`Step` rebuild it without rebuilding the shared `GuardRefuteBase` helper.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- `u8`. -/
noncomputable def acU8Ty : MirTy := .int .i8 false

/-- `u32`. -/
noncomputable def acU32Ty : MirTy := .int .i32 false

/-- Overflow pair `(u8, bool)`: it has a layout, but `isSupportedPointeeTy`
refuses it behind a pointer or inside a `Vec`, `Box`, or slice. -/
noncomputable def acPairTy : MirTy := .tuple [.int .i8 false, .bool]

/-- Live mutable byte-aligned heap buffer with id `2` holding `bs`. -/
noncomputable def acBuf (bs : List AllocByte) : Allocation :=
  { allocId := 2, alignLog2 := 0, mutability := .mut, bytes := bs,
    live := true }

/-- Memory holding `allocs`, with next allocation id `3`. -/
noncomputable def acMem (allocs : List Allocation) : MemoryState :=
  { nextAllocId := 3, allocations := allocs }

/-- Pointer to offset `0` of heap buffer `2`. -/
noncomputable def acBufPtr : PtrVal := ⟨some 2, 0, .isize⟩

/-- Provenance-free non-null pointer `8`, aligned for every modeled type. -/
noncomputable def acDangling : PtrVal := ⟨none, 8, .isize⟩

/-- Initialized byte `b` without provenance. -/
noncomputable def acB (b : UInt8) : AllocByte := .init b none

/-- `Vec<u8>` handle in mutable allocation `1`: pointer to `acBufPtr`, then
`cap`, then `len` (little-endian `usize` words). -/
noncomputable def acVecHandle (cap len : UInt8) : Allocation :=
  { allocId := 1, alignLog2 := 3, mutability := .mut,
    bytes := List.replicate 8 (.init 0 (some 2)) ++
      (acB cap :: List.replicate 7 (acB 0)) ++
      (acB len :: List.replicate 7 (acB 0)),
    live := true }

/-- Pointer to the `Vec` handle in allocation `1`. -/
noncomputable def acVecPtr : PtrVal := ⟨some 1, 0, .isize⟩

/-- `Vec<u8>` buffer with `cap = 8` and `len = 2`: exactly 8 bytes, the first
two initialized. -/
noncomputable def acStaleMem : MemoryState :=
  acMem [acBuf ([acB 3, acB 5] ++ List.replicate 6 .uninit)]

theorem alloc_sanity_vec_box_valid :
    vecValidInMem (acMem [acBuf [acB 7, acB 9]]) true
        ⟨acU8Ty, acBufPtr, 2, 2⟩ = .ok () ∧
    vecValidInMem MemoryState.empty false ⟨acU8Ty, acDangling, 0, 0⟩ =
      .ok () ∧
    boxValidInMem (acMem [acBuf [acB 7, acB 9]]) true
        ⟨.slice acU8Ty, acBufPtr, some 2⟩ = .ok () ∧
    boxValidInMem (acMem [acBuf [acB 7]]) true
        ⟨acU8Ty, acBufPtr, none⟩ = .ok () :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem alloc_sanity_heap_buf_valid :
    zeroCapPtrValidInMem MemoryState.empty false 0 ⟨none, 1, .isize⟩ =
      .ok () ∧
    heapBufValidInMem (acMem [acBuf [acB 7, .uninit, .uninit, .uninit]])
        true acU8Ty acBufPtr 4 1 = .ok () ∧
    ownedHeapBufValidInMem (acMem [acBuf [acB 7, .uninit]]) true acU8Ty
        acBufPtr 2 1 = .ok () ∧
    boxPointeeValidInMem (acMem [acBuf [acB 7]]) false (.slice acU8Ty)
        acBufPtr (some 1) = .ok () :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem alloc_sanity_capacity :
    vecGrowCap 1 0 1 = some 8 ∧
    vecGrowCap 0 0 5 = some 5 ∧
    vecGrowCap 1 (Nat.pow 2 61) (Nat.pow 2 62 + 2) =
      some (Nat.pow 2 62 + 2) ∧
    (match evalVecWithCapacity MemoryState.empty acU8Ty 4 with
     | .ok (.vec _ 4 0, _) => true
     | _ => false) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem alloc_sanity_index_and_realloc :
    evalVecIndex (acMem [acVecHandle 2 1, acBuf [acB 7, acB 9]]) .shared
        acU8Ty acVecPtr 0 = .ok (.ptr acBufPtr) ∧
    (match evalBoxFromVec acStaleMem acU8Ty acBufPtr 8 2 with
     | .ok (.boxPtr ⟨some 3, 0, .isize⟩ (some 2), m') =>
       match readBytes m' ⟨3, 0⟩ 2 0 with
       | .ok [.init 3 none, .init 5 none] => true
       | _ => false
     | _ => false) = true :=
  ⟨rfl, rfl⟩

theorem alloc_sanity_box_as_ref :
    evalCastKindV2 (acMem [acBuf [acB 7]]) (.ref .shared acU8Ty)
        (.box acU8Ty) (.boxPtr acBufPtr none) (.ref .shared acU8Ty) =
      .ok (.ptr acBufPtr) :=
  rfl

end GuardMutation
