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


end Zerocopy.Obligations
