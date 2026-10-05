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

def cast_unsized_layouts_match_spec_contract (src dst : layout.DstLayout)
    (run : Result Bool) : Prop :=
  layoutValid src → layoutValid dst → run ⦃ accepted =>
    match src.size_info, dst.size_info with
    | .Sized src_size, .Sized dst_size =>
      accepted = decide (src_size.val = dst_size.val)
    | .SliceDst src_tail, .SliceDst dst_tail => accepted = true →
      src.align.val.val = dst.align.val.val ∧ src_tail.offset.val = dst_tail.offset.val ∧
      ∀ count : Nat,
        completeLayoutSize src count = completeLayoutSize dst count ∧
        (completeLayoutSize src count ≤ Usize.max ↔ completeLayoutSize dst count ≤ Usize.max)
    | _, _ => accepted = false ⦄
def cast_unsized_layouts_match_spec : Prop := ∀ src dst,
  cast_unsized_layouts_match_spec_contract src dst
    (pointer.cast.cast_unsized_layouts_match src dst)

def cast_unsized_check_spec_contract (src dst : layout.DstLayout)
    (src_align : NonZeroUsize) (src_phase : Usize) (dst_align : NonZeroUsize)
    (dst_phase metadata : Usize) (run : Result Unit) : Prop :=
  layoutValid src → layoutValid dst →
    0 < src_align.val.val → 0 < dst_align.val.val → run ⦃ _ => True ⦄
def cast_unsized_check_spec : Prop := ∀ src dst src_align src_phase dst_align dst_phase metadata,
  cast_unsized_check_spec_contract src dst src_align src_phase dst_align dst_phase metadata
    (pointer.cast.checks.assert_cast_unsized src dst src_align src_phase dst_align dst_phase metadata)

end Zerocopy.Obligations
