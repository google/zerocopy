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

/- These arbitrary-run contracts retain the full decoded machine-word domain.
Their total True conclusions discharge the numerical assertions visible in
Rust; the original natural-number method obligations remain independent.
-/
def tail_transformations_check_spec_contract
    (tail : layout.TrailingSliceLayout Usize) (align : NonZeroUsize)
    (phase bytes replacement_stride elems : Usize) (run : Result Unit) : Prop :=
  0 < tail.size_rounding_align_and_phase._0.val.val → 0 < align.val.val →
    run ⦃ _ => True ⦄

def tail_transformations_check_spec : Prop :=
  ∀ tail align phase bytes replacement_stride elems,
    tail_transformations_check_spec_contract tail align phase bytes replacement_stride elems
      (layout.tail_transform_checks.tail_transformations_check
        tail align phase bytes replacement_stride elems)

def tail_size_sequence_check_spec_contract
    (left right : layout.TrailingSliceLayout Usize)
    (left_align : NonZeroUsize) (left_phase : Usize)
    (right_align : NonZeroUsize) (right_phase elems : Usize) (run : Result Unit) : Prop :=
  0 < left.size_rounding_align_and_phase._0.val.val →
    0 < right.size_rounding_align_and_phase._0.val.val →
    0 < left_align.val.val → 0 < right_align.val.val → run ⦃ _ => True ⦄

def tail_size_sequence_check_spec : Prop :=
  ∀ left right left_align left_phase right_align right_phase elems,
    tail_size_sequence_check_spec_contract left right left_align left_phase right_align right_phase elems
      (layout.tail_transform_checks.tail_size_sequence_check
        left right left_align left_phase right_align right_phase elems)

def tail_dynamic_padding_check_spec_contract
    (runtime_layout : layout.DstLayout) (align : NonZeroUsize) (phase : Usize)
    (run : Result Unit) : Prop :=
  layoutValid runtime_layout → 0 < align.val.val → run ⦃ _ => True ⦄

def tail_dynamic_padding_check_spec : Prop :=
  ∀ runtime_layout align phase,
    tail_dynamic_padding_check_spec_contract runtime_layout align phase
      (layout.tail_transform_checks.tail_dynamic_padding_check runtime_layout align phase)

end Zerocopy.Obligations
