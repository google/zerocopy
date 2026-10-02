/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import LayoutMath
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

abbrev NonZeroUsize := core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner

def byteFormula {E : Type} (self : layout.TrailingSliceLayout E) : LayoutMath.Formula :=
  let code := self.size_rounding_align_and_phase.val.val
  let align := 2 ^ Nat.log2 code
  ⟨self.size_base.val, code - align, align, 0, self.offset.val⟩

def trailingFormula (self : layout.TrailingSliceLayout Usize) : LayoutMath.Formula :=
  { byteFormula self with elem := self.elem_size.val }

def packingValue (packed : Option NonZeroUsize) : Nat :=
  (packed.map (fun a => a.val.val)).getD (2 ^ (System.Platform.numBits - 1))

def fieldAlignment (field : layout.DstLayout) (packed : Option NonZeroUsize) : Nat :=
  min field.align.val.val (packingValue packed)

def placement (size : Usize) (field : layout.DstLayout) (packed : Option NonZeroUsize) :=
  LayoutMath.roundUp size.val (fieldAlignment field packed)

def layoutValue (self : layout.DstLayout) : LayoutMath.LayoutValue :=
  { align := self.align.val.val,
    payload := match self.size_info with
      | .Sized size => .fixed size.val
      | .SliceDst tail => .trailing (trailingFormula tail),
    unpadded := self.statically_shallow_unpadded }

def canonicalLayout (self : layout.DstLayout) : Prop :=
  match self.size_info with
  | .Sized _ => True
  | .SliceDst t => 0 < t.size_rounding_align_and_phase.val.val

def alignmentDomain (a : Nat) : Prop := a.isPowerOfTwo ∧ a ≤ 2 ^ 29

end Zerocopy.Proofs
