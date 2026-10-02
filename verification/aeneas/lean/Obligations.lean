/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Obligations
abbrev NonZeroUsize :=
  core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner

-- Written independently of the specification expansions, using mathematical values.
def max_spec : Prop :=
  ∀ (a b : NonZeroUsize), ∃ r, util.max a b = .ok r ∧
    r.val.val = Nat.max a.val.val b.val.val ∧ (r = a ∨ r = b) ∧
      a.val.val ≤ r.val.val ∧ b.val.val ≤ r.val.val

def min_spec : Prop :=
  ∀ (a b : NonZeroUsize), ∃ r, util.min a b = .ok r ∧
    r.val.val = Nat.min a.val.val b.val.val ∧ (r = a ∨ r = b) ∧
      r.val.val ≤ a.val.val ∧ r.val.val ≤ b.val.val

def padding_lt_alignment : Prop :=
  ∀ (len : Usize) (align : NonZeroUsize) (_h : align.val.val.isPowerOfTwo),
    util.padding_needed_for len align ⦃ p => p.val < align.val.val ∧
      p.val = (align.val.val - len.val % align.val.val) % align.val.val ∧
      (len.val + p.val) % align.val.val = 0 ∧
      (∀ q : Nat, (len.val + q) % align.val.val = 0 → p.val ≤ q) ∧
      (p.val = 0 ↔ len.val % align.val.val = 0) ⦄

def round_down_spec : Prop :=
  ∀ (n : Usize) (align : NonZeroUsize)
    (_h : align.val.val.isPowerOfTwo),
    util.round_down_to_next_multiple_of_alignment n align ⦃ m =>
      m.val ≤ n.val ∧ m.val = n.val - n.val % align.val.val ∧
      m.val % align.val.val = 0 ∧ n.val < m.val + align.val.val ∧
      (∀ q : Nat, q ≤ n.val → q % align.val.val = 0 → q ≤ m.val) ⦄

def pad_to_align_spec : Prop :=
  ∀ (self : layout.DstLayout)
    (_h : match self.size_info with
      | layout.SizeInfo.Sized size =>
        self.align.val.val.isPowerOfTwo ∧
          size.val + (self.align.val.val - size.val % self.align.val.val)
            % self.align.val.val ≤ Usize.max
      | layout.SizeInfo.SliceDst _ => True),
    layout.DstLayout.pad_to_align self ⦃ r => r.align = self.align ∧
      match self.size_info with
      | layout.SizeInfo.Sized size => ∃ padded,
        r.size_info = layout.SizeInfo.Sized padded ∧
        padded.val = size.val + (self.align.val.val - size.val % self.align.val.val)
          % self.align.val.val ∧
        size.val ≤ padded.val ∧ padded.val < size.val + self.align.val.val ∧
        padded.val % self.align.val.val = 0 ∧
        (∀ q : Nat, size.val ≤ q → q % self.align.val.val = 0 → padded.val ≤ q) ∧
        r.statically_shallow_unpadded =
          (self.statically_shallow_unpadded && decide (size.val % self.align.val.val = 0))
      | layout.SizeInfo.SliceDst _ => r = self ⦄

end Zerocopy.Obligations
