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

/- These roots promise that every assertion terminates on the full admitted
Rust domain. Their observations are the executable assertions in tail_checks;
the original method obligations retain their separate mathematical promises.
-/
def trailing_arithmetic_check_spec_contract
    (tail : layout.TrailingSliceLayout Usize) (align : NonZeroUsize)
    (phase elems budget : Usize) (run : Result Unit) : Prop :=
  0 < tail.size_rounding_align_and_phase._0.val.val → 0 < align.val.val →
    run ⦃ _ => True ⦄

def trailing_arithmetic_check_spec : Prop :=
  ∀ tail align phase elems budget,
    trailing_arithmetic_check_spec_contract tail align phase elems budget
      (layout.tail_checks.trailing_arithmetic_check tail align phase elems budget)

def layout_observations_check_spec_contract
    (runtime_layout : layout.DstLayout) (align : NonZeroUsize)
    (phase size addr length : Usize) (side : layout.CastType)
    (run : Result Unit) : Prop :=
  layoutValid runtime_layout → 0 < align.val.val → run ⦃ _ => True ⦄

def layout_observations_check_spec : Prop :=
  ∀ runtime_layout align phase size addr length side,
    layout_observations_check_spec_contract runtime_layout align phase size addr length side
      (layout.tail_checks.layout_observations_check runtime_layout align phase size addr length side)

end Zerocopy.Obligations
