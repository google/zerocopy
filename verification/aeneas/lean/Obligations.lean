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
public import Arithmetic
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

end Zerocopy.Obligations
