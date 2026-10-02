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

-- Written independently of the specification expansions, using mathematical
-- values. Each family describes an arbitrary outcome; its transparent alias
-- applies the family to the extracted operation.
def max_spec_contract (a b : NonZeroUsize)
    (run : Result NonZeroUsize) : Prop :=
  0 < a.val.val → 0 < b.val.val → ∃ r, run = .ok r ∧ 0 < r.val.val ∧
    r.val.val = Nat.max a.val.val b.val.val ∧ (r = a ∨ r = b) ∧
      a.val.val ≤ r.val.val ∧ b.val.val ≤ r.val.val

def max_spec : Prop :=
  ∀ (a b : NonZeroUsize),
    max_spec_contract a b (util.max a b)

def min_spec_contract (a b : NonZeroUsize)
    (run : Result NonZeroUsize) : Prop :=
  0 < a.val.val → 0 < b.val.val → ∃ r, run = .ok r ∧ 0 < r.val.val ∧
    r.val.val = Nat.min a.val.val b.val.val ∧ (r = a ∨ r = b) ∧
      r.val.val ≤ a.val.val ∧ r.val.val ≤ b.val.val

def min_spec : Prop :=
  ∀ (a b : NonZeroUsize),
    min_spec_contract a b (util.min a b)

def padding_lt_alignment_contract (len : Usize) (align : NonZeroUsize)
    (run : Result Usize) : Prop :=
  ∀ (_valid : 0 < align.val.val) (_h : align.val.val.isPowerOfTwo),
    run ⦃ p => p.val < align.val.val ∧
      p.val = (align.val.val - len.val % align.val.val) % align.val.val ∧
      (len.val + p.val) % align.val.val = 0 ∧
      (∀ q : Nat, (len.val + q) % align.val.val = 0 → p.val ≤ q) ∧
      (p.val = 0 ↔ len.val % align.val.val = 0) ⦄

def padding_lt_alignment : Prop :=
  ∀ (len : Usize) (align : NonZeroUsize),
    padding_lt_alignment_contract len align (util.padding_needed_for len align)

def round_down_spec_contract (n : Usize) (align : NonZeroUsize)
    (run : Result Usize) : Prop :=
  ∀ (_valid : 0 < align.val.val) (_h : align.val.val.isPowerOfTwo),
    run ⦃ m =>
      m.val ≤ n.val ∧ m.val = n.val - n.val % align.val.val ∧
      m.val % align.val.val = 0 ∧ n.val < m.val + align.val.val ∧
      (∀ q : Nat, q ≤ n.val → q % align.val.val = 0 → q ≤ m.val) ⦄

def round_down_spec : Prop :=
  ∀ (n : Usize) (align : NonZeroUsize),
    round_down_spec_contract n align (util.round_down_to_next_multiple_of_alignment n align)

-- These propositions are maintained separately from the specification macro and
-- native proof modules. They fix successful termination and mathematical results.
def encoding_new_spec_contract (a : NonZeroUsize) (p : Usize)
    (run : Result layout.RoundingAlignAndPhase) : Prop :=
  0 < a.val.val → a.val.val.isPowerOfTwo → p.val < a.val.val →
    ∃ code, run = .ok code ∧ encodingValid code ∧ code._0.val.val = a.val.val + p.val

def encoding_new_spec : Prop :=
  ∀ (a : NonZeroUsize) (p : Usize),
    encoding_new_spec_contract a p (layout.RoundingAlignAndPhase.new a p)

def encoding_components_spec_contract (code : layout.RoundingAlignAndPhase)
    (run : Result (NonZeroUsize × Usize)) : Prop :=
  0 < code._0.val.val →
    run ⦃ (a, p) =>
      0 < a.val.val ∧ a.val.val.isPowerOfTwo ∧ p.val < a.val.val ∧ a.val.val + p.val = code._0.val.val ∧
      a.val.val = 2 ^ code._0.val.val.log2 ∧ p.val = code._0.val.val - 2 ^ code._0.val.val.log2 ⦄

def encoding_components_spec : Prop :=
  ∀ (code : layout.RoundingAlignAndPhase),
    encoding_components_spec_contract code (layout.RoundingAlignAndPhase.components code)

def encoding_align_spec_contract (code : layout.RoundingAlignAndPhase)
    (run : Result NonZeroUsize) : Prop :=
  0 < code._0.val.val →
    ∃ a, run = .ok a ∧ 0 < a.val.val ∧ a.val.val = 2 ^ code._0.val.val.log2

def encoding_align_spec : Prop :=
  ∀ (code : layout.RoundingAlignAndPhase),
    encoding_align_spec_contract code (layout.RoundingAlignAndPhase.align code)

def size_offset_spec_contract (E : Type) (t : layout.TrailingSliceLayout E)
    (run : Result Usize) : Prop :=
  ∀ [RustModel E], trailingValid t →
    ∃ offset, run = .ok offset ∧
      offset.val = t.size_base.val - t.size_base.val % (byteFormula t).align + (byteFormula t).phase

def size_offset_spec : Prop :=
  ∀ (E : Type) (t : layout.TrailingSliceLayout E),
    size_offset_spec_contract E t (layout.TrailingSliceLayout.size_offset t)

def max_trailing_bytes_spec_contract
    (E : Type) (t : layout.TrailingSliceLayout E) (budget : Usize)
    (run : Result (Option Usize)) : Prop :=
  ∀ [RustModel E],
    trailingValid t →
    ∃ cap, run = .ok cap ∧
      cap.map UScalar.val = (byteFormula t).capacity budget.val

def max_trailing_bytes_spec : Prop :=
  ∀ (E : Type) (t : layout.TrailingSliceLayout E) (budget : Usize),
    max_trailing_bytes_spec_contract E t budget
      (layout.TrailingSliceLayout.max_trailing_bytes t budget)

def padding_for_elems_spec_contract (t : layout.TrailingSliceLayout Usize) (n : Usize)
    (run : Result Usize) : Prop :=
  0 < t.size_rounding_align_and_phase._0.val.val →
    ∃ p, run = .ok p ∧
      (p.val + t.offset.val + n.val * t.elem_size.val) % UScalar.size .Usize =
        (trailingFormula t).size n.val % UScalar.size .Usize

def padding_for_elems_spec : Prop :=
  ∀ (t : layout.TrailingSliceLayout Usize) (n : Usize),
    padding_for_elems_spec_contract t n (layout.TrailingSliceLayoutUsize.padding_for_elems t n)

def size_for_elems_spec_contract (t : layout.TrailingSliceLayout Usize) (n : Usize)
    (run : Result (Option Usize)) : Prop :=
  0 < t.size_rounding_align_and_phase._0.val.val →
    ∃ size, run = .ok size ∧
      size.map UScalar.val = (trailingFormula t).checkedSize Usize.max n.val

def size_for_elems_spec : Prop :=
  ∀ (t : layout.TrailingSliceLayout Usize) (n : Usize),
    size_for_elems_spec_contract t n (layout.TrailingSliceLayoutUsize.size_for_elems t n)

def same_size_sequence_spec_contract (a b : layout.TrailingSliceLayout Usize)
    (run : Result Bool) : Prop :=
  0 < a.size_rounding_align_and_phase._0.val.val → 0 < b.size_rounding_align_and_phase._0.val.val →
    ∃ same, run = .ok same ∧
      (same = true → ∀ n : Nat, (trailingFormula a).size n = (trailingFormula b).size n)

def same_size_sequence_spec : Prop :=
  ∀ (a b : layout.TrailingSliceLayout Usize),
    same_size_sequence_spec_contract a b
      (layout.TrailingSliceLayoutUsize.has_same_size_sequence a b)

def advance_spec_contract (t : layout.TrailingSliceLayout Usize) (bytes stride : Usize)
    (run : Result (Option (layout.TrailingSliceLayout Usize))) : Prop :=
  0 < t.size_rounding_align_and_phase._0.val.val →
    run ⦃ r => (∀ next ∈ r, encodingValid next.size_rounding_align_and_phase) ∧
      match r with
      | none => Usize.max < ((trailingFormula t).advance bytes.val stride.val).base
      | some next => trailingFormula next = (trailingFormula t).advance bytes.val stride.val ∧
        ((trailingFormula t).advance bytes.val stride.val).base ≤ Usize.max ⦄

def advance_spec : Prop :=
  ∀ (t : layout.TrailingSliceLayout Usize) (bytes stride : Usize),
    advance_spec_contract t bytes stride
      (layout.TrailingSliceLayoutUsize.advance t bytes stride)

def try_nonzero_spec_contract (si : layout.SizeInfo Usize)
    (run : Result (Option (layout.SizeInfo NonZeroUsize))) : Prop :=
  sizeInfoValid si → run ⦃ r => (∀ next ∈ r, sizeInfoValid next) ∧
    match si with
    | .Sized bytes => r = some (.Sized bytes)
    | .SliceDst t => if t.elem_size = 0#usize then r = none else
      ∃ next, r = some (.SliceDst next) ∧ next.offset = t.offset ∧ next.size_base = t.size_base ∧
        next.size_rounding_align_and_phase = t.size_rounding_align_and_phase ∧
        next.elem_size.val = t.elem_size ⦄

def try_nonzero_spec : Prop :=
  ∀ (si : layout.SizeInfo Usize),
    try_nonzero_spec_contract si (layout.SizeInfoUsize.try_to_nonzero_elem_size si)

def max_elems_for_bytes_spec_contract (budget : Usize) (stride : NonZeroUsize)
    (run : Result (Usize × Usize)) : Prop :=
  0 < stride.val.val →
    run ⦃ (n, bytes) =>
      n.val = budget.val / stride.val.val ∧ bytes.val = n.val * stride.val.val ∧
      bytes.val ≤ budget.val ∧ budget.val < (n.val + 1) * stride.val.val ∧
      (∀ k : Nat, k * stride.val.val ≤ budget.val ↔ k ≤ n.val) ⦄

def max_elems_for_bytes_spec : Prop :=
  ∀ (budget : Usize) (stride : NonZeroUsize),
    max_elems_for_bytes_spec_contract budget stride (layout.max_elems_for_bytes budget stride)

def assume_shallow_unpadded_spec_contract (self : layout.DstLayout)
    (run : Result layout.DstLayout) : Prop :=
  layoutValid self → ∃ r, run = .ok r ∧ layoutValid r ∧
    r.align = self.align ∧ r.size_info = self.size_info ∧ r.statically_shallow_unpadded = true

def assume_shallow_unpadded_spec : Prop :=
  ∀ (self : layout.DstLayout),
    assume_shallow_unpadded_spec_contract self (layout.DstLayout.assume_shallow_unpadded self)

def new_zst_spec_contract (a : Option NonZeroUsize)
    (run : Result layout.DstLayout) : Prop :=
  (∀ x ∈ a, 0 < x.val.val) → (∀ x ∈ a, x.val.val.isPowerOfTwo) →
    ∃ r, run = .ok r ∧ layoutValid r ∧ r.align = a.getD ⟨1#usize⟩ ∧
      r.size_info = .Sized 0#usize ∧ r.statically_shallow_unpadded = true

def new_zst_spec : Prop :=
  ∀ (a : Option NonZeroUsize),
    new_zst_spec_contract a (layout.DstLayout.new_zst a)

def for_type_spec_contract (T : Type)
    (run : Result layout.DstLayout) : Prop :=
  ∀ [RustModel T] (size align : Usize), core.mem.size_of T = .ok size →
    core.mem.align_of T = .ok align → 0 < align.val →
    ∃ r, run = .ok r ∧ layoutValid r ∧ r.align.val = align ∧
      r.size_info = .Sized size ∧ r.statically_shallow_unpadded = false

def for_type_spec : Prop :=
  ∀ (T : Type),
    for_type_spec_contract T (layout.DstLayout.for_type T)

def for_unpadded_type_spec_contract (T : Type)
    (run : Result layout.DstLayout) : Prop :=
  ∀ [RustModel T] (size align : Usize), core.mem.size_of T = .ok size →
    core.mem.align_of T = .ok align → 0 < align.val →
    ∃ r, run = .ok r ∧ layoutValid r ∧ r.align.val = align ∧
      r.size_info = .Sized size ∧ r.statically_shallow_unpadded = true

def for_unpadded_type_spec : Prop :=
  ∀ (T : Type),
    for_unpadded_type_spec_contract T (layout.DstLayout.for_unpadded_type T)

def for_slice_spec_contract (T : Type)
    (run : Result layout.DstLayout) : Prop :=
  ∀ [RustModel T] (size align : Usize), core.mem.size_of T = .ok size →
    core.mem.align_of T = .ok align → align.val.isPowerOfTwo →
    ∃ r, run = .ok r ∧ layoutValid r ∧ r.align.val = align ∧
      r.statically_shallow_unpadded = true ∧ ∃ t, r.size_info = .SliceDst t ∧
      t.offset = 0#usize ∧ t.elem_size = size ∧ t.size_base = 0#usize ∧
      t.size_rounding_align_and_phase._0.val.val = align.val

def for_slice_spec : Prop :=
  ∀ (T : Type),
    for_slice_spec_contract T (layout.DstLayout.for_slice T)

def extend_spec_contract (self field : layout.DstLayout) (packing : Option NonZeroUsize)
    (run : Result layout.DstLayout) : Prop :=
  ∀ (size : Usize),
    layoutValid self → layoutValid field → (∀ a ∈ packing, 0 < a.val.val) →
    self.size_info = .Sized size →
    (self.align.val.val.isPowerOfTwo ∧ self.align.val.val ≤ 2 ^ 29) →
    (field.align.val.val.isPowerOfTwo ∧ field.align.val.val ≤ 2 ^ 29) →
    (∀ a ∈ packing, a.val.val.isPowerOfTwo ∧ a.val.val ≤ 2 ^ 29) →
    (match field.size_info with
      | .Sized s => placement size field packing + s.val ≤ Usize.max
      | .SliceDst t => placement size field packing + t.offset.val ≤ Usize.max ∧
        placement size field packing + t.size_base.val ≤ Usize.max) →
    run ⦃ r => layoutValid r ∧
      r.align.val.val = Nat.max self.align.val.val (fieldAlignment field packing) ∧
      r.statically_shallow_unpadded = (self.statically_shallow_unpadded &&
        field.statically_shallow_unpadded && decide (size.val % fieldAlignment field packing = 0)) ∧
      match field.size_info with
      | .Sized s => ∃ bytes, r.size_info = .Sized bytes ∧ bytes.val = placement size field packing + s.val
      | .SliceDst t => ∃ next, r.size_info = .SliceDst next ∧
        next.offset.val = placement size field packing + t.offset.val ∧
        next.size_base.val = placement size field packing + t.size_base.val ∧
        next.elem_size = t.elem_size ∧ next.size_rounding_align_and_phase = t.size_rounding_align_and_phase ⦄

def extend_spec : Prop :=
  ∀ (self field : layout.DstLayout) (packing : Option NonZeroUsize),
    extend_spec_contract self field packing (layout.DstLayout.extend self field packing)

def pad_to_align_spec_contract (self : layout.DstLayout)
    (run : Result layout.DstLayout) : Prop :=
  layoutValid self → self.align.val.val.isPowerOfTwo →
    (match self.size_info with
      | .Sized bytes => LayoutMath.roundUp bytes.val self.align.val.val ≤ Usize.max
      | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val ∧
        (if (trailingFormula t).align < self.align.val.val then
          LayoutMath.roundUp t.size_base.val (trailingFormula t).align + (trailingFormula t).phase ≤ Usize.max
         else LayoutMath.roundUp t.size_base.val self.align.val.val ≤ Usize.max)) →
    run ⦃ r => layoutValid r ∧ r.align = self.align ∧
      match self.size_info with
      | .Sized bytes => ∃ padded, r.size_info = .Sized padded ∧
        padded.val = LayoutMath.roundUp bytes.val self.align.val.val ∧
        r.statically_shallow_unpadded =
          (self.statically_shallow_unpadded && decide (bytes.val % self.align.val.val = 0))
      | .SliceDst t => ∃ next, r.size_info = .SliceDst next ∧
        trailingFormula next = (trailingFormula t).pad self.align.val.val ∧
        r.statically_shallow_unpadded = self.statically_shallow_unpadded ⦄

def pad_to_align_spec : Prop :=
  ∀ (self : layout.DstLayout),
    pad_to_align_spec_contract self (layout.DstLayout.pad_to_align self)

def requires_static_padding_spec_contract (self : layout.DstLayout)
    (run : Result Bool) : Prop :=
  layoutValid self → ∃ r, run = .ok r ∧
    r = !self.statically_shallow_unpadded

def requires_static_padding_spec : Prop :=
  ∀ (self : layout.DstLayout),
    requires_static_padding_spec_contract self (layout.DstLayout.requires_static_padding self)

def requires_dynamic_padding_spec_contract (self : layout.DstLayout)
    (run : Result Bool) : Prop :=
  layoutValid self →
    ∃ r, run = .ok r ∧
      (r = false ↔ match self.size_info with
        | .Sized _ => True
        | .SliceDst t => (trailingFormula t).size 0 = t.offset.val ∧
          t.elem_size.val % (trailingFormula t).align = 0)

def requires_dynamic_padding_spec : Prop :=
  ∀ (self : layout.DstLayout),
    requires_dynamic_padding_spec_contract self
      (layout.DstLayout.requires_dynamic_padding self)

def validate_cast_spec_contract
    (self : layout.DstLayout) (addr length : Usize) (side : layout.CastType)
    (run : Result (core.result.Result (Usize × Usize) layout.MetadataCastError)) : Prop :=
  layoutValid self →
    0 < self.align.val.val → addr.val + length.val ≤ Usize.max →
    (match self.size_info with
      | .Sized _ => True
      | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val ∧ 0 < t.elem_size.val) →
    ∃ r, run = .ok r ∧
      -- State the expected cases independently of the inline outcome helper.
      let anchor := addr.val + (match side with | .Prefix => 0 | .Suffix => length.val)
      match r with
      | .Err .Alignment => anchor % self.align.val.val ≠ 0
      | .Err .Size => anchor % self.align.val.val = 0 ∧
        match self.size_info with
        | .Sized bytes => length.val < bytes.val
        | .SliceDst tail => ∀ n : Nat, length.val < (trailingFormula tail).size n
      | .Ok (elems, split) => anchor % self.align.val.val = 0 ∧
        match self.size_info with
        | .Sized bytes => elems.val = 0 ∧ bytes.val ≤ length.val ∧
          split.val = (match side with
            | .Prefix => bytes.val
            | .Suffix => length.val - bytes.val)
        | .SliceDst tail => (trailingFormula tail).size elems.val ≤ length.val ∧
          (∀ n : Nat, (trailingFormula tail).size n ≤ length.val ↔ n ≤ elems.val) ∧
          split.val = (match side with
            | .Prefix => (trailingFormula tail).size elems.val
            | .Suffix => length.val - (trailingFormula tail).size elems.val)

def validate_cast_spec : Prop :=
  ∀ (self : layout.DstLayout) (addr length : Usize) (side : layout.CastType),
    validate_cast_spec_contract self addr length side
      (layout.DstLayout.validate_cast_and_convert_metadata self addr length side)

def metadata_exact_spec_contract (self : layout.DstLayout) (size : Usize)
    (run : Result (Option Usize)) : Prop :=
  layoutValid self → 0 < self.align.val.val →
    (match self.size_info with
      | .Sized _ => True
      | .SliceDst t => t.elem_size.val ≠ 0 → 0 < t.size_rounding_align_and_phase._0.val.val) →
    ∃ r, run = .ok r ∧
      -- Pin exact size and maximal metadata without sharing the inline predicate.
      match self.size_info with
      | .Sized _ => r = none
      | .SliceDst tail =>
        if tail.elem_size.val = 0 then r = none else
        match r with
        | none => ∀ n : Nat, (trailingFormula tail).size n ≠ size.val
        | some elems => (trailingFormula tail).size elems.val = size.val ∧
          (∀ n : Nat, (trailingFormula tail).size n ≤ size.val ↔ n ≤ elems.val)

def metadata_exact_spec : Prop :=
  ∀ (self : layout.DstLayout) (size : Usize),
    metadata_exact_spec_contract self size (layout.DstLayout.metadata_for_exact_size self size)

def for_repr_c_struct_spec_contract
    (a packed : Option NonZeroUsize) (fields : Slice layout.DstLayout)
    (run : Result layout.DstLayout) : Prop :=
  (∀ x ∈ a, 0 < x.val.val) → (∀ x ∈ packed, 0 < x.val.val) →
    (∀ field ∈ fields.val, layoutValid field) →
    (∀ x ∈ a, alignmentDomain x.val.val) → (∀ x ∈ packed, alignmentDomain x.val.val) →
    constructionDomain fields (LayoutMath.LayoutValue.initial (initialAlignment a)) packed →
    alignmentDomain (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment a))
      packed fields.val.length).align →
    (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment a))
      packed fields.val.length).padFits Usize.max →
    ∃ r, run = .ok r ∧ layoutValid r ∧ layoutValue r =
      (constructionPrefix fields (LayoutMath.LayoutValue.initial (initialAlignment a)) packed fields.val.length).pad

def for_repr_c_struct_spec : Prop :=
  ∀ (a packed : Option NonZeroUsize) (fields : Slice layout.DstLayout),
    for_repr_c_struct_spec_contract a packed fields
      (layout.DstLayout.for_repr_c_struct a packed fields)

end Zerocopy.Obligations
