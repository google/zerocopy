/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutMath
@[expose] public section

/-!
Pure arithmetic for composing a selected cast plan with its metadata map.
All metadata and sizes are unbounded natural numbers. These lemmas concern
complete numerical sizes, not physical slice offsets, pointer validity, or
provenance. Bounds on the two metadata operations are derived separately
from equality of complete sizes.
-/
namespace Zerocopy.LayoutMath

/- Byte advancement implements the affine element-count map exactly when the
source stride is a multiple of the destination stride. Positivity is needed
only for the later bounds, not for this identity.
-/
theorem advance_affine_size (src dst : Formula) (offset multiple n : Nat)
    (he : src.elem = multiple * dst.elem) :
    (dst.advance (offset * dst.elem) src.elem).size n =
      dst.size (offset + n * multiple) := by
  rw [advance_size]
  simp only [Formula.size, Formula.bytes, he, Nat.add_mul, Nat.mul_assoc,
    Nat.add_assoc]

/- A size-sequence certificate for the shifted formula can therefore be
applied to every source metadata value, including values whose sizes exceed
any particular machine bound.
-/
theorem affine_size_of_advance (src dst : Formula) (offset multiple : Nat)
    (he : src.elem = multiple * dst.elem)
    (hseq : ∀ n, src.size n = (dst.advance (offset * dst.elem) src.elem).size n)
    (n : Nat) : src.size n = dst.size (offset + n * multiple) := by
  rw [hseq n, advance_affine_size src dst offset multiple n he]

end Zerocopy.LayoutMath
