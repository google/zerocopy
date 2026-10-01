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

def max_spec : Prop :=
  ∀ (a b : NonZeroUsize),
    ∃ r, util.max a b = .ok r ∧ r.val.val = Nat.max a.val.val b.val.val

def min_spec : Prop :=
  ∀ (a b : NonZeroUsize),
    ∃ r, util.min a b = .ok r ∧ r.val.val = Nat.min a.val.val b.val.val

def padding_lt_alignment : Prop :=
  ∀ (len : Usize) (align : NonZeroUsize)
    (_h : 0 < align.val.val),
    util.padding_needed_for len align ⦃ p => p.val < align.val.val ⦄

def round_down_spec : Prop :=
  ∀ (n : Usize) (align : NonZeroUsize)
    (_hpos : 0 < align.val.val) (_h : align.val.val.isPowerOfTwo),
    util.round_down_to_next_multiple_of_alignment n align
      ⦃ m => m.val ≤ n.val ∧ m.val % align.val.val = 0 ⦄

end Zerocopy.Obligations
