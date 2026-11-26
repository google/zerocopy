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
import MemorySanity

/-!
# Additional Profile v2 Refutations for `Trusted.MirSemantics.Memory`

Closes high-consequence Profile v2 UB guard blind spots in `Memory.lean`:
- `sliceGetUncheckedCheck` inverted range `startOff > endOff` (where Lean `Nat`
  subtraction `endOff - startOff` would otherwise silently saturate to `0`),
- `ptrAddInMem` dead-allocation (`!a.live`) check, and
- `sliceFromRawPartsCheck` provenance-free non-empty / misaligned checks plus
  dead-allocation, out-of-bounds (`List.take` truncation trap), and alignment
  checks.

Imports only `Trusted.MirSemantics.Memory` and `MemorySanity` so each mutant
compiles without rebuilding downstream semantics modules. The shared
allocation helpers and the anti-overreach positive canaries for these guards
live in `MemorySanity.lean`, which the runner compiles and requires to pass on
every mutant before this module.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Deallocated (`live = false`) 4-byte allocation with id `1`. -/
noncomputable def v2DeadMut4Alloc : Allocation :=
  { v2LiveMut4Alloc with live := false }

/-- Guard `mem_v2_slice_get_unchecked_inverted`: subslicing with
`startOff > endOff` (`3 > 1`) within `len = 4` faults with `.undefined` rather
than silently saturating `endOff - startOff = 0`. -/
theorem refute_mem_v2_slice_get_unchecked_inverted :
    sliceGetUncheckedCheck (v2SingleAllocMem v2LiveMut4Alloc)
      ⟨some 1, 0, .isize⟩ 4 3 1 = .error .undefined :=
  rfl

/-- Guard `mem_v2_ptr_add_dead_alloc`: `ptrAddInMem` rejects an in-bounds
offset on a deallocated (`live = false`) allocation as `.undefined`. -/
theorem refute_mem_v2_ptr_add_dead_alloc :
    ptrAddInMem (v2SingleAllocMem v2DeadMut4Alloc) 1
      ⟨some 1, 0, .isize⟩ 1 = .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_no_prov_nonempty`: `sliceFromRawPartsCheck` rejects a
non-empty slice backed by a provenance-free non-null aligned pointer. -/
theorem refute_mem_v2_slice_no_prov_nonempty :
    sliceFromRawPartsCheck MemoryState.empty false 1 0
      ⟨none, 8, .isize⟩ 1 = .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_no_prov_misaligned`: `sliceFromRawPartsCheck` rejects
even a zero-length `&[u32]` backed by a misaligned provenance-free pointer
(`offset = 2`, `align = 4`). -/
theorem refute_mem_v2_slice_no_prov_misaligned :
    sliceFromRawPartsCheck MemoryState.empty false 4 2
      ⟨none, 2, .isize⟩ 0 = .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_dead_alloc`: `sliceFromRawPartsCheck` rejects an
in-bounds slice into a deallocated (`live = false`) allocation. -/
theorem refute_mem_v2_slice_dead_alloc :
    sliceFromRawPartsCheck (v2SingleAllocMem v2DeadMut4Alloc) false 1 0
      ⟨some 1, 0, .isize⟩ 2 = .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_oob`: `sliceFromRawPartsCheck` rejects a slice whose
end exceeds `a.bytes.length` (`offset = 2`, `len = 4` on a 4-byte allocation)
rather than allowing `List.take` to silently truncate to the remaining
initialized bytes. -/
theorem refute_mem_v2_slice_oob :
    sliceFromRawPartsCheck (v2SingleAllocMem v2LiveMut4Alloc) false 1 0
      ⟨some 1, 2, .isize⟩ 4 = .error .undefined :=
  rfl

/-- Guard `mem_v2_slice_misaligned`: `sliceFromRawPartsCheck` rejects an
in-bounds `&[u32]` at misaligned offset `2` inside a 4-byte-aligned live
allocation. -/
theorem refute_mem_v2_slice_misaligned :
    sliceFromRawPartsCheck (v2SingleAllocMem v2LiveMut4Alloc) false 4 2
      ⟨some 1, 2, .isize⟩ 0 = .error .undefined :=
  rfl

end GuardMutation
