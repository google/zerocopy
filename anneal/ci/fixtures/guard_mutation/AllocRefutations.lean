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
import AllocSanity

/-!
# Profile v2 Heap-Allocation Refutations

Negative refutations for the `Vec`/`Box` guards of Profile v2:
- `Trusted/MirSemantics/AllocContracts.lean`: the `isSupportedPointeeTy` gate
  of `vecValidInMem` and `boxValidInMem`, the capacity-overflow panics of
  `vecGrowCap` and `evalVecWithCapacity`, the `evalVecIndex` bounds-check
  panic, and `retireHeapBuffer`, which kills the provenance of a reallocated
  buffer.
- `Trusted/MirSemantics/Bytes.lean`: the heap-buffer validity checks
  `zeroCapPtrValidInMem`, `heapBufValidInMem`, `ownedHeapBufValidInMem`, and
  `boxPointeeValidInMem`.
- `Trusted/MirSemantics/Step.lean`: `evalCastKindV2 .boxAsRef`.

Each theorem evaluates the guarded function on a concrete input by `rfl`, in
the style of `theory/Anneal/Core/AllocContractCanaries.lean`. The shared
helpers and the anti-overreach positive canaries live in `AllocSanity.lean`,
which the runner compiles and requires to pass on every mutant before this
module.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-! ## `AllocContracts.lean` -/

/-- Guard `alloc_vec_valid_unsupported_elem`: `vecValidInMem` refuses a
`Vec<(u8, bool)>` with `.unsupported`, even though its empty dangling buffer
would otherwise pass the heap-buffer checks. -/
theorem refute_alloc_vec_valid_unsupported_elem :
    vecValidInMem MemoryState.empty false ⟨acPairTy, acDangling, 0, 0⟩ =
      .error .unsupported :=
  rfl

/-- Guard `alloc_box_valid_unsupported_slice_elem`: `boxValidInMem` refuses
an empty `Box<[(u8, bool)]>` with `.unsupported`. -/
theorem refute_alloc_box_valid_unsupported_slice_elem :
    boxValidInMem MemoryState.empty false
        ⟨.slice acPairTy, acDangling, some 0⟩ = .error .unsupported :=
  rfl

/-- Guard `alloc_vec_grow_cap_u64_bound`: growing a zero-sized-element buffer
to `minCap = 2^64` overflows `usize`, so `vecGrowCap` fails (a
capacity-overflow panic) instead of granting `minCap`. -/
theorem refute_alloc_vec_grow_cap_u64_bound :
    vecGrowCap 0 0 (Nat.pow 2 64) = none :=
  rfl

/-- Guard `alloc_vec_grow_cap_doubled_overflow`: from capacity `2^62 + 1`,
the doubled capacity `2^63 + 2` of a `Vec<u8>` exceeds `isize::MAX` bytes,
so `vecGrowCap` fails even though `minCap = 2^62 + 2` itself fits. -/
theorem refute_alloc_vec_grow_cap_doubled_overflow :
    vecGrowCap 1 (Nat.pow 2 62 + 1) (Nat.pow 2 62 + 2) = none :=
  rfl

/-- Guard `alloc_vec_with_capacity_overflow`:
`Vec::<u64>::with_capacity(2^62)` needs `2^65` bytes, more than `isize::MAX`,
so it faults with `.unsupported` (a capacity-overflow panic) instead of
allocating. -/
theorem refute_alloc_vec_with_capacity_overflow :
    (match evalVecWithCapacity MemoryState.empty (.int .i64 false)
        (UInt64.ofNat (Nat.pow 2 62)) with
     | .error .unsupported => true
     | _ => false) = true :=
  rfl

/-- Guard `alloc_vec_index_oob`: indexing a `Vec<u8>` with `len = 1` at index
`1` panics (`.unsupported`), even though capacity slot `1` holds an
initialized byte. -/
theorem refute_alloc_vec_index_oob :
    evalVecIndex (acMem [acVecHandle 2 1, acBuf [acB 7, acB 9]]) .shared
        acU8Ty acVecPtr 1 = .error .unsupported :=
  rfl

/-- Guard `alloc_retire_heap_buffer`: `Box<[u8]>::from` on a `Vec<u8>` with
`cap = 8` and `len = 2` reallocates the buffer and retires the old
allocation, so a read through the old pointer faults with `.undefined`. -/
theorem refute_alloc_retire_heap_buffer :
    (match evalBoxFromVec acStaleMem acU8Ty acBufPtr 8 2 with
     | .ok (_, m') => readBytes m' ⟨2, 0⟩ 2 0
     | .error _ => .ok []) = .error .undefined :=
  rfl

/-! ## `Bytes.lean` -/

/-- Guard `bytes_zero_cap_ptr_null`: `zeroCapPtrValidInMem` rejects the null
pointer for an empty buffer, even with alignment `1`. -/
theorem refute_bytes_zero_cap_ptr_null :
    zeroCapPtrValidInMem MemoryState.empty false 0 ⟨none, 0, .isize⟩ =
      .error .undefined :=
  rfl

/-- Guard `bytes_heap_buf_len_gt_cap`: `heapBufValidInMem` rejects
`len = 2 > cap = 1`, even when two initialized bytes follow the pointer. -/
theorem refute_bytes_heap_buf_len_gt_cap :
    heapBufValidInMem (acMem [acBuf [acB 7, acB 9]]) false acU8Ty acBufPtr
        1 2 = .error .undefined :=
  rfl

/-- Guard `bytes_heap_buf_dead_alloc`: `heapBufValidInMem` rejects a buffer
in a deallocated (`live = false`) allocation. -/
theorem refute_bytes_heap_buf_dead_alloc :
    heapBufValidInMem (acMem [{ acBuf [acB 7] with live := false }]) false
        acU8Ty acBufPtr 1 1 = .error .undefined :=
  rfl

/-- Guard `bytes_heap_buf_cap_oob`: `heapBufValidInMem` rejects `cap = 4`
over a 2-byte allocation, even though the `len = 1` initialized prefix is in
bounds. -/
theorem refute_bytes_heap_buf_cap_oob :
    heapBufValidInMem (acMem [acBuf [acB 7, acB 9]]) false acU8Ty acBufPtr
        4 1 = .error .undefined :=
  rfl

/-- Guard `bytes_heap_buf_uninit`: `heapBufValidInMem` rejects an
uninitialized byte inside the `len = 1` prefix of a `u8` buffer. -/
theorem refute_bytes_heap_buf_uninit :
    heapBufValidInMem (acMem [acBuf [.uninit]]) false acU8Ty acBufPtr 1 1 =
      .error .undefined :=
  rfl

/-- Guard `bytes_owned_heap_buf_size`: `ownedHeapBufValidInMem` rejects a
`cap = 2` buffer in a 4-byte allocation, whose layout the buffer could not
have been allocated with. -/
theorem refute_bytes_owned_heap_buf_size :
    ownedHeapBufValidInMem (acMem [acBuf [acB 7, acB 9, acB 1, acB 2]])
        false acU8Ty acBufPtr 2 1 = .error .undefined :=
  rfl

/-- Guard `bytes_box_pointee_slice_owned`: `boxPointeeValidInMem` requires a
`Box<[u8]>` of length `1` to own its whole allocation, so it rejects one
pointing into a 2-byte allocation. -/
theorem refute_bytes_box_pointee_slice_owned :
    boxPointeeValidInMem (acMem [acBuf [acB 7, acB 9]]) false (.slice acU8Ty)
        acBufPtr (some 1) = .error .undefined :=
  rfl

/-! ## `Step.lean` -/

/-- Guard `step_box_as_ref_validity`: `&*b` for a `Box<u8>` whose pointer has
dangling provenance faults with `.undefined`. -/
theorem refute_step_box_as_ref_validity :
    evalCastKindV2 MemoryState.empty (.ref .shared acU8Ty) (.box acU8Ty)
        (.boxPtr ⟨some 5, 0, .isize⟩ none) (.ref .shared acU8Ty) =
      .error .undefined :=
  rfl

/-- Guard `step_box_as_ref_pointee_mismatch`: casting a valid `Box<u8>` to
`&u32` is refused with `.unsupported`. -/
theorem refute_step_box_as_ref_pointee_mismatch :
    evalCastKindV2 (acMem [acBuf [acB 7]]) (.ref .shared acU32Ty)
        (.box acU8Ty) (.boxPtr acBufPtr none) (.ref .shared acU32Ty) =
      .error .unsupported :=
  rfl

end GuardMutation
