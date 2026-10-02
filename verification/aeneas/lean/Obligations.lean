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

-- These propositions are maintained separately from the specification macro and
-- native proof modules. They fix successful termination and mathematical results.
def encoding_new_spec : Prop :=
  ∀ (a : NonZeroUsize) (p : Usize), a.val.val.isPowerOfTwo → p.val < a.val.val →
    ∃ code, layout.RoundingAlignAndPhase.new a p = .ok code ∧ code.val.val = a.val.val + p.val

def encoding_components_spec : Prop :=
  ∀ (code : layout.RoundingAlignAndPhase), 0 < code.val.val →
    layout.RoundingAlignAndPhase.components code ⦃ (a, p) =>
      a.val.val.isPowerOfTwo ∧ p.val < a.val.val ∧ a.val.val + p.val = code.val.val ∧
      a.val.val = 2 ^ code.val.val.log2 ∧ p.val = code.val.val - 2 ^ code.val.val.log2 ⦄

def encoding_align_spec : Prop :=
  ∀ (code : layout.RoundingAlignAndPhase), 0 < code.val.val →
    ∃ a, layout.RoundingAlignAndPhase.align code = .ok a ∧ a.val.val = 2 ^ code.val.val.log2


end Zerocopy.Obligations
