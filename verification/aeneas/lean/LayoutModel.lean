/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import LayoutMath
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

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

def castSide (cast : layout.CastType) (length : Nat) : Nat :=
  match cast with | .Prefix => 0 | .Suffix => length

def castSplit (cast : layout.CastType) (length size : Nat) : Nat :=
  match cast with | .Prefix => size | .Suffix => length - size

def castSpec (self : layout.DstLayout) (addr length : Nat) (cast : layout.CastType)
    (result : core.result.Result (Usize × Usize) layout.MetadataCastError) : Prop :=
  let anchor := addr + castSide cast length
  match result with
  | .Err .Alignment => anchor % self.align.val.val ≠ 0
  | .Err .Size => anchor % self.align.val.val = 0 ∧
    match self.size_info with
    | .Sized size => length < size.val
    | .SliceDst tail => ∀ n : Nat, length < (trailingFormula tail).size n
  | .Ok (elems, split) => anchor % self.align.val.val = 0 ∧
    match self.size_info with
    | .Sized size => elems.val = 0 ∧ size.val ≤ length ∧
      split.val = castSplit cast length size.val
    | .SliceDst tail => (trailingFormula tail).size elems.val ≤ length ∧
      (∀ n : Nat, (trailingFormula tail).size n ≤ length ↔ n ≤ elems.val) ∧
      split.val = castSplit cast length ((trailingFormula tail).size elems.val)

def metadataSpec (self : layout.DstLayout) (size : Nat) (r : Option Usize) : Prop :=
  match self.size_info with
  | .Sized _ => r = none
  | .SliceDst tail =>
    if tail.elem_size.val = 0 then r = none else
    match r with
    | none => ∀ n : Nat, (trailingFormula tail).size n ≠ size
    | some elems => (trailingFormula tail).size elems.val = size ∧
      (∀ n : Nat, (trailingFormula tail).size n ≤ size ↔ n ≤ elems.val)

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
