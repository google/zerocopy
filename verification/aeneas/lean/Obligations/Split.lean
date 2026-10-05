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

-- Expected domains and observations are independent of inline specs. The
-- successful count subtraction has exactly the source's valid-index domain.
def split_right_len_spec_contract (total left : Usize) (run : Result Usize) : Prop :=
  left.val ≤ total.val → run ⦃ right =>
    right.val = total.val - left.val ∧ right.val + left.val = total.val ∧
    right.val ≤ total.val ⦄

def split_right_len_spec : Prop := ∀ total left,
  split_right_len_spec_contract total left (split_at.split_right_len total left)

-- Every machine padding value is admitted. Acceptance retains its exact gate.
def split_zero_padding_spec_contract (padding : Usize) (run : Result Bool) : Prop :=
  run ⦃ accepted => (accepted = true ↔ padding.val = 0) ⦄

def split_zero_padding_spec : Prop := ∀ padding,
  split_zero_padding_spec_contract padding (split_at.split_zero_padding padding)

-- Every positive stored layout word and positive witness alignment is admitted,
-- with arbitrary other fields and indices. The source guards reject mismatched
-- witnesses and nonrealizable/overflowing geometry before assertion sites.
def split_geometry_check_spec_contract (tail : layout.TrailingSliceLayout Usize)
    (align : NonZeroUsize) (phase total left : Usize) (run : Result Unit) : Prop :=
  0 < tail.size_rounding_align_and_phase._0.val.val → 0 < align.val.val →
    run ⦃ _ => True ⦄

def split_geometry_check_spec : Prop := ∀ tail align phase total left,
  split_geometry_check_spec_contract tail align phase total left
    (split_at.numerical_checks.check_split_geometry tail align phase total left)

end Zerocopy.Obligations
