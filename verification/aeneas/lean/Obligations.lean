/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Obligations
open Zerocopy.Proofs
abbrev NonZeroUsize :=
  core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner

def max_spec : Prop :=
  ∀ (a b : NonZeroUsize), 0 < a.val.val → 0 < b.val.val → ∃ r, util.max a b = .ok r ∧ 0 < r.val.val ∧
    r.val.val = Nat.max a.val.val b.val.val ∧ (r = a ∨ r = b) ∧
      a.val.val ≤ r.val.val ∧ b.val.val ≤ r.val.val

def min_spec : Prop :=
  ∀ (a b : NonZeroUsize), 0 < a.val.val → 0 < b.val.val → ∃ r, util.min a b = .ok r ∧ 0 < r.val.val ∧
    r.val.val = Nat.min a.val.val b.val.val ∧ (r = a ∨ r = b) ∧
      r.val.val ≤ a.val.val ∧ r.val.val ≤ b.val.val

def padding_lt_alignment : Prop :=
  ∀ (len : Usize) (align : NonZeroUsize) (_valid : 0 < align.val.val) (_h : align.val.val.isPowerOfTwo),
    util.padding_needed_for len align ⦃ p => p.val < align.val.val ∧
      p.val = (align.val.val - len.val % align.val.val) % align.val.val ∧
      (len.val + p.val) % align.val.val = 0 ∧
      (∀ q : Nat, (len.val + q) % align.val.val = 0 → p.val ≤ q) ∧
      (p.val = 0 ↔ len.val % align.val.val = 0) ⦄

def round_down_spec : Prop :=
  ∀ (n : Usize) (align : NonZeroUsize)
    (_valid : 0 < align.val.val) (_h : align.val.val.isPowerOfTwo),
    util.round_down_to_next_multiple_of_alignment n align ⦃ m =>
      m.val ≤ n.val ∧ m.val = n.val - n.val % align.val.val ∧
      m.val % align.val.val = 0 ∧ n.val < m.val + align.val.val ∧
      (∀ q : Nat, q ≤ n.val → q % align.val.val = 0 → q ≤ m.val) ⦄

def encoding_new_spec : Prop :=
  ∀ (a : NonZeroUsize) (p : Usize), 0 < a.val.val → a.val.val.isPowerOfTwo → p.val < a.val.val →
    ∃ code, layout.RoundingAlignAndPhase.new a p = .ok code ∧ encodingValid code ∧ code._0.val.val = a.val.val + p.val

def encoding_components_spec : Prop :=
  ∀ (code : layout.RoundingAlignAndPhase), 0 < code._0.val.val →
    layout.RoundingAlignAndPhase.components code ⦃ (a, p) =>
      0 < a.val.val ∧ a.val.val.isPowerOfTwo ∧ p.val < a.val.val ∧ a.val.val + p.val = code._0.val.val ∧
      a.val.val = 2 ^ code._0.val.val.log2 ∧ p.val = code._0.val.val - 2 ^ code._0.val.val.log2 ⦄

def encoding_align_spec : Prop :=
  ∀ (code : layout.RoundingAlignAndPhase), 0 < code._0.val.val →
    ∃ a, layout.RoundingAlignAndPhase.align code = .ok a ∧ 0 < a.val.val ∧ a.val.val = 2 ^ code._0.val.val.log2

def size_offset_spec : Prop :=
  ∀ (E : Type) (t : layout.TrailingSliceLayout E) [IsValid E], trailingValid t →
    ∃ offset, layout.TrailingSliceLayout.size_offset t = .ok offset ∧
      offset.val = t.size_base.val - t.size_base.val % (byteFormula t).align + (byteFormula t).phase

def max_trailing_bytes_spec : Prop :=
  ∀ (E : Type) (t : layout.TrailingSliceLayout E) (budget : Usize) [IsValid E],
    trailingValid t →
    ∃ cap, layout.TrailingSliceLayout.max_trailing_bytes t budget = .ok cap ∧
      cap.map UScalar.val = (byteFormula t).capacity budget.val

def padding_for_elems_spec : Prop :=
  ∀ (t : layout.TrailingSliceLayout Usize) (n : Usize), 0 < t.size_rounding_align_and_phase._0.val.val →
    ∃ p, layout.TrailingSliceLayoutUsize.padding_for_elems t n = .ok p ∧
      (p.val + t.offset.val + n.val * t.elem_size.val) % UScalar.size .Usize =
        (trailingFormula t).size n.val % UScalar.size .Usize

def size_for_elems_spec : Prop :=
  ∀ (t : layout.TrailingSliceLayout Usize) (n : Usize), 0 < t.size_rounding_align_and_phase._0.val.val →
    ∃ size, layout.TrailingSliceLayoutUsize.size_for_elems t n = .ok size ∧
      size.map UScalar.val = (trailingFormula t).checkedSize Usize.max n.val

def try_nonzero_spec : Prop :=
  ∀ (si : layout.SizeInfo Usize), sizeInfoValid si → layout.SizeInfoUsize.try_to_nonzero_elem_size si ⦃ r => (∀ next ∈ r, sizeInfoValid next) ∧
    match si with
    | .Sized bytes => r = some (.Sized bytes)
    | .SliceDst t => if t.elem_size = 0#usize then r = none else
      ∃ next, r = some (.SliceDst next) ∧ next.offset = t.offset ∧ next.size_base = t.size_base ∧
        next.size_rounding_align_and_phase = t.size_rounding_align_and_phase ∧
        next.elem_size.val = t.elem_size ⦄

def max_elems_for_bytes_spec : Prop :=
  ∀ (budget : Usize) (stride : NonZeroUsize), 0 < stride.val.val →
    layout.max_elems_for_bytes budget stride ⦃ (n, bytes) =>
      n.val = budget.val / stride.val.val ∧ bytes.val = n.val * stride.val.val ∧
      bytes.val ≤ budget.val ∧ budget.val < (n.val + 1) * stride.val.val ∧
      (∀ k : Nat, k * stride.val.val ≤ budget.val ↔ k ≤ n.val) ⦄

def assume_shallow_unpadded_spec : Prop :=
  ∀ (self : layout.DstLayout), layoutValid self → ∃ r, layout.DstLayout.assume_shallow_unpadded self = .ok r ∧ layoutValid r ∧
    r.align = self.align ∧ r.size_info = self.size_info ∧ r.statically_shallow_unpadded = true

def new_zst_spec : Prop :=
  ∀ (a : Option NonZeroUsize), (∀ x ∈ a, 0 < x.val.val) → (∀ x ∈ a, x.val.val.isPowerOfTwo) →
    ∃ r, layout.DstLayout.new_zst a = .ok r ∧ layoutValid r ∧ r.align = a.getD ⟨1#usize⟩ ∧
      r.size_info = .Sized 0#usize ∧ r.statically_shallow_unpadded = true

def for_type_spec : Prop :=
  ∀ (T : Type) [IsValid T] (size align : Usize), core.mem.size_of T = .ok size →
    core.mem.align_of T = .ok align → 0 < align.val →
    ∃ r, layout.DstLayout.for_type T = .ok r ∧ layoutValid r ∧ r.align.val = align ∧
      r.size_info = .Sized size ∧ r.statically_shallow_unpadded = false

def for_unpadded_type_spec : Prop :=
  ∀ (T : Type) [IsValid T] (size align : Usize), core.mem.size_of T = .ok size →
    core.mem.align_of T = .ok align → 0 < align.val →
    ∃ r, layout.DstLayout.for_unpadded_type T = .ok r ∧ layoutValid r ∧ r.align.val = align ∧
      r.size_info = .Sized size ∧ r.statically_shallow_unpadded = true

def for_slice_spec : Prop :=
  ∀ (T : Type) [IsValid T] (size align : Usize), core.mem.size_of T = .ok size →
    core.mem.align_of T = .ok align → align.val.isPowerOfTwo →
    ∃ r, layout.DstLayout.for_slice T = .ok r ∧ layoutValid r ∧ r.align.val = align ∧
      r.statically_shallow_unpadded = true ∧ ∃ t, r.size_info = .SliceDst t ∧
      t.offset = 0#usize ∧ t.elem_size = size ∧ t.size_base = 0#usize ∧
      t.size_rounding_align_and_phase._0.val.val = align.val

def extend_spec : Prop :=
  ∀ (self field : layout.DstLayout) (packing : Option NonZeroUsize) (size : Usize),
    layoutValid self → layoutValid field → (∀ a ∈ packing, 0 < a.val.val) →
    self.size_info = .Sized size →
    (self.align.val.val.isPowerOfTwo ∧ self.align.val.val ≤ 2 ^ 29) →
    (field.align.val.val.isPowerOfTwo ∧ field.align.val.val ≤ 2 ^ 29) →
    (∀ a ∈ packing, a.val.val.isPowerOfTwo ∧ a.val.val ≤ 2 ^ 29) →
    (match field.size_info with
      | .Sized s => placement size field packing + s.val ≤ Usize.max
      | .SliceDst t => placement size field packing + t.offset.val ≤ Usize.max ∧
        placement size field packing + t.size_base.val ≤ Usize.max) →
    layout.DstLayout.extend self field packing ⦃ r => layoutValid r ∧
      r.align.val.val = Nat.max self.align.val.val (fieldAlignment field packing) ∧
      r.statically_shallow_unpadded = (self.statically_shallow_unpadded &&
        field.statically_shallow_unpadded && decide (size.val % fieldAlignment field packing = 0)) ∧
      match field.size_info with
      | .Sized s => ∃ bytes, r.size_info = .Sized bytes ∧ bytes.val = placement size field packing + s.val
      | .SliceDst t => ∃ next, r.size_info = .SliceDst next ∧
        next.offset.val = placement size field packing + t.offset.val ∧
        next.size_base.val = placement size field packing + t.size_base.val ∧
        next.elem_size = t.elem_size ∧ next.size_rounding_align_and_phase = t.size_rounding_align_and_phase ⦄

def pad_to_align_spec : Prop :=
  ∀ (self : layout.DstLayout), layoutValid self → self.align.val.val.isPowerOfTwo →
    (match self.size_info with
      | .Sized bytes => LayoutMath.roundUp bytes.val self.align.val.val ≤ Usize.max
      | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val ∧
        (if (trailingFormula t).align < self.align.val.val then
          LayoutMath.roundUp t.size_base.val (trailingFormula t).align + (trailingFormula t).phase ≤ Usize.max
         else LayoutMath.roundUp t.size_base.val self.align.val.val ≤ Usize.max)) →
    layout.DstLayout.pad_to_align self ⦃ r => layoutValid r ∧ r.align = self.align ∧
      match self.size_info with
      | .Sized bytes => ∃ padded, r.size_info = .Sized padded ∧
        padded.val = LayoutMath.roundUp bytes.val self.align.val.val ∧
        r.statically_shallow_unpadded =
          (self.statically_shallow_unpadded && decide (bytes.val % self.align.val.val = 0))
      | .SliceDst t => ∃ next, r.size_info = .SliceDst next ∧
        trailingFormula next = (trailingFormula t).pad self.align.val.val ∧
        r.statically_shallow_unpadded = self.statically_shallow_unpadded ⦄

def requires_static_padding_spec : Prop :=
  ∀ (self : layout.DstLayout), layoutValid self → ∃ r, layout.DstLayout.requires_static_padding self = .ok r ∧
    r = !self.statically_shallow_unpadded

end Zerocopy.Obligations
