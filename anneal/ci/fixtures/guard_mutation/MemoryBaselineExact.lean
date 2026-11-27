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
# Baseline-Only Exact Value Checks for `Trusted.MirSemantics.Memory`

Compiled against the unmodified baseline `Trusted.MirSemantics.Memory` during
`check_guard_mutation.py`, never against mutants. Holds exact return-value
assertions whose expected value intentionally changes under a guard mutant
(such as `mem_v2_slice_get_unchecked_elem_size`, which replaces `elemSize`
with `1` in `sliceGetUncheckedCheck` and therefore requires `MemorySanity`
to assert only mutant-compatible success `.ok _`).
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Exact byte-offset assertion paired with
`positive_mem_v2_slice_get_unchecked_elem_size_in_bounds`: with `elemSize = 4`
and `startOff = 1` on a 4-byte allocation, `sliceGetUncheckedCheck` scales
the returned pointer offset to `4`. -/
theorem baseline_mem_v2_slice_get_unchecked_elem_size_exact :
    sliceGetUncheckedCheck (singleAllocMem liveMut4Alloc)
        ⟨some 1, 0, .isize⟩ 1 1 1 4 =
      .ok (.slicePtr ⟨some 1, 4, .isize⟩ 0) :=
  rfl

end GuardMutation
