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

/- This expectation independently classifies all optional machine sizes. The
numerical preparation does not allocate or change the supplied metadata size.
-/
def allocation_prepare_spec_contract (size : Option Usize) (align : NonZeroUsize)
    (run : Result (Option (Usize × NonZeroUsize))) : Prop :=
  0 < align.val.val → run ⦃ result =>
    result.map (fun pair => (pair.1.val, pair.2.val.val)) =
      size.map (fun size => (size.val, align.val.val)) ⦄

def allocation_prepare_spec : Prop :=
  ∀ size align, allocation_prepare_spec_contract size align
    (util.allocation.prepare size align)

def allocation_preparation_check_spec_contract (_size : Option Usize) (align : NonZeroUsize)
    (run : Result Unit) : Prop := 0 < align.val.val → run ⦃ _ => True ⦄

def allocation_preparation_check_spec : Prop :=
  ∀ size align, allocation_preparation_check_spec_contract size align
    (util.allocation.assert_preparation size align)

def allocation_size_check_spec_contract (runtime_layout : layout.DstLayout)
    (rounding_align : NonZeroUsize) (_phase _metadata : Usize) (run : Result Unit) : Prop :=
  0 < runtime_layout.align.val.val → canonicalLayout runtime_layout →
  0 < rounding_align.val.val → run ⦃ _ => True ⦄

def allocation_size_check_spec : Prop :=
  ∀ runtime_layout rounding_align phase metadata,
    allocation_size_check_spec_contract runtime_layout rounding_align phase metadata
      (util.allocation.assert_allocation_size runtime_layout rounding_align phase metadata)

end Zerocopy.Obligations
