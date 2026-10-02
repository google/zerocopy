/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import MathViews
public import LayoutMath
@[expose] public section

/-!
Extracted records contain machine words and compressed rounding encodings.
This module gives those records ordinary mathematical observations: a size
formula, a physical slice offset, and field placement. The definitions do not
call an extracted operation or assume that it is correct.

Proofs uses the raw observations to state implementation lemmas and
independent expectations. ModelViews exposes corresponding observations of
recursively decoded mathematical records for inline clauses.
ModelProjectionLaws proves the connection when decoding succeeds. Keeping
physical offset separate from normalized base and phase is essential: inner
padding can make them differ.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

/- Read the raw trailing record as a complete-size formula over byte counts. The
compressed word determines alignment and phase; physical offset is retained.
-/
def byteFormula {E : Type} (self : layout.TrailingSliceLayout E) : LayoutMath.Formula :=
  let code := self.size_rounding_align_and_phase._0.val.val
  let align := 2 ^ Nat.log2 code
  ⟨self.size_base.val, code - align, align, 0, self.offset.val⟩

/- Specialize the byte formula to the raw element stride used by usize metadata.
-/
def trailingFormula (self : layout.TrailingSliceLayout Usize) : LayoutMath.Formula :=
  { byteFormula self with elem := self.elem_size.val }

/- An absent packing bound acts as the largest representable power of two. The
alignment domain bounds ensure that taking the minimum leaves an admitted
field alignment unchanged in that case.
-/
def packingValue (packed : Option NonZeroUsize) : Nat :=
  (packed.map (fun a => a.val.val)).getD (2 ^ (System.Platform.numBits - 1))

def fieldAlignment (field : layout.DstLayout) (packed : Option NonZeroUsize) : Nat :=
  min field.align.val.val (packingValue packed)

/- Round the current fixed size to the field's effective placement alignment.
-/
def placement (size : Usize) (field : layout.DstLayout) (packed : Option NonZeroUsize) :=
  LayoutMath.roundUp size.val (fieldAlignment field packed)

/- Project the raw record to the fragment vocabulary used by layout operations.
This preserves alignment, payload, physical offset, stride, and unpadded
flag.
-/
def layoutValue (self : layout.DstLayout) : LayoutMath.LayoutValue :=
  { align := self.align.val.val,
    payload := match self.size_info with
      | .Sized size => .fixed size.val
      | .SliceDst tail => .trailing (trailingFormula tail),
    unpadded := self.statically_shallow_unpadded }

/- Require the nonzero compressed rounding word in a trailing payload. Sized
fragments have no rounding encoding to validate.
-/
def canonicalLayout (self : layout.DstLayout) : Prop :=
  match self.size_info with
  | .Sized _ => True
  | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val

/- The selected Rust layout premise bounds power-of-two alignments at 2^29. This
is an explicit operation domain, not a consequence of NonZeroUsize alone.
-/
def alignmentDomain (a : Nat) : Prop := a.isPowerOfTwo ∧ a ≤ 2 ^ 29

end Zerocopy.Proofs

-- Mathematical projections consume the one recursively decoded record. The
-- raw projections above remain for independently stated representation claims.
namespace Zerocopy.ModelViews
open AeneasSpecs

/- Read the decoded mathematical trailing record as a complete-size formula over
byte counts. Alignment and phase have already been decoded; physical offset
remains a separate observation.
-/
def byteFormula {EModel : Type}
    (self : layout.TrailingSliceLayout.Fields EModel) : LayoutMath.Formula :=
  let rounding := self.size_rounding_align_and_phase
  ⟨self.size_base.value, rounding.phase, rounding.align, 0, self.offset.value⟩

/- Specialize the byte formula to the decoded bounded element stride used by
usize metadata.
-/
def trailingFormula (self : layout.TrailingSliceLayout.Fields (UnsignedWord .Usize)) : LayoutMath.Formula :=
  { byteFormula self with elem := self.elem_size.value }

/- An absent packing bound acts as the largest representable power of two. The
alignment domain bounds ensure that taking the minimum leaves an admitted
field alignment unchanged in that case.
-/
def packingValue (packed : Option NonZeroUsizeValue) : Nat :=
  (packed.map (fun a => a.value)).getD (2 ^ (System.Platform.numBits - 1))

def fieldAlignment (field : layout.DstLayout.Fields) (packed : Option NonZeroUsizeValue) : Nat :=
  min field.align.value (packingValue packed)

/- Round the current fixed size to the field's effective placement alignment.
-/
def placement (size : UnsignedWord .Usize) (field : layout.DstLayout.Fields)
    (packed : Option NonZeroUsizeValue) : Nat :=
  LayoutMath.roundUp size.value (fieldAlignment field packed)

/- Project the decoded record to the fragment vocabulary used by layout
operations, preserving alignment, payload, physical offset, stride and flag.
-/
def layoutValue (self : layout.DstLayout.Fields) : LayoutMath.LayoutValue :=
  { align := self.align.value,
    payload := match self.size_info with
      | .Sized size => .fixed size.value
      | .SliceDst tail => .trailing (trailingFormula tail),
    unpadded := self.statically_shallow_unpadded }

end Zerocopy.ModelViews
