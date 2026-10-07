/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Obligations
open Zerocopy.Proofs
set_option linter.unusedVariables false

/- This arbitrary-outcome expectation requires every harness assertion to
terminate throughout the automatic decoder domain. It includes no size-fit,
metadata-fit, witness-match, phase-range, or size-equality premise: the harness
itself guards the independent witnesses and derives metadata representability.
-/
def cast_composition_check_spec_contract
    (src dst : layout.DstLayout) (src_align : NonZeroUsize) (src_phase : Usize)
    (dst_align : NonZeroUsize) (dst_phase src_meta : Usize) (run : Result Unit) : Prop :=
  0 < src.align.val.val → 0 < dst.align.val.val →
  canonicalLayout src → canonicalLayout dst →
  0 < src_align.val.val → 0 < dst_align.val.val → run ⦃ _ => True ⦄

def cast_composition_check_spec : Prop :=
  ∀ src dst src_align src_phase dst_align dst_phase src_meta,
    cast_composition_check_spec_contract src dst src_align src_phase dst_align dst_phase src_meta
      (layout.cast_from.checks.assert_cast_preserves_size
        src dst src_align src_phase dst_align dst_phase src_meta)

end Zerocopy.Obligations
