/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import Aeneas
import all Init.Data.Nat.Power2.Basic
@[expose] public section

/-!
A function contract is most useful when other proofs can consume it. These
corollaries compose the checked operation lemmas into arithmetic consequences
and layout equivalence results. In particular, the recursive-size and direct
record-placement results connect runtime normalization to independent layout
mathematics for every metadata value in their stated domains.

The bridge to an actual Rust type remains the explicit premise documented in
SEMANTICS.md. A proof about extracted numerical operations does not itself
prove pointer safety, nor does it prove that every Rust caller meets a
contract's requirements.
-/
open Aeneas Aeneas.Std Aeneas.Std.Result
namespace Zerocopy.Corollaries
open Proofs Proofs.Raw


theorem max_preserves (a b : NonZeroUsize) (P : NonZeroUsize → Prop)
    (ha : P a)
    (hb : P b) :
    util.max a b
      ⦃ r => P r ⦄ := by
  step with Proofs.Raw.max_spec a b as ⟨r, _, hchoice, _, _⟩
  rcases hchoice with h | h
  · simpa only [h] using ha
  · simpa only [h] using hb

theorem min_preserves (a b : NonZeroUsize) (P : NonZeroUsize → Prop)
    (ha : P a)
    (hb : P b) :
    util.min a b
      ⦃ r => P r ⦄ := by
  step with Proofs.Raw.min_spec a b as ⟨r, _, hchoice, _, _⟩
  rcases hchoice with h | h
  · simpa only [h] using ha
  · simpa only [h] using hb

theorem round_down_aligned (n : Usize) (align : NonZeroUsize)
    (hpow : (align.val : Nat).isPowerOfTwo)
    (haligned : (n : Nat) % (align.val : Nat) = 0) :
    util.round_down_to_next_multiple_of_alignment n align = .ok n := by
  obtain ⟨m, hm, _, hexact, _, _, _⟩ :=
    WP.spec_imp_exists (Proofs.Raw.round_down_spec n align hpow)
  have heq : m = n := UScalar.eq_of_val_eq (by
    simpa only [haligned, Nat.sub_zero] using hexact)
  simpa only [heq] using hm

theorem round_down_idempotent (n : Usize) (align : NonZeroUsize)
    (hpow : (align.val : Nat).isPowerOfTwo) :
    (do
      let m ← util.round_down_to_next_multiple_of_alignment n align
      let m' ← util.round_down_to_next_multiple_of_alignment m align
      ok (m, m'))
      ⦃ m m' => m' = m ⦄ := by
  step with Proofs.Raw.round_down_spec n align hpow as ⟨m, _, _, haligned, _, _⟩
  rw [round_down_aligned m align hpow haligned]
  simp only [bind_ok, WP.spec_ok, WP.uncurry'_pair]

theorem round_down_monotone (a b : Usize) (align : NonZeroUsize)
    (hab : a ≤ b)
    (hpow : (align.val : Nat).isPowerOfTwo) :
    (do
      let m ← util.round_down_to_next_multiple_of_alignment a align
      let m' ← util.round_down_to_next_multiple_of_alignment b align
      ok (m, m'))
      ⦃ m m' => m ≤ m' ⦄ := by
  step with Proofs.Raw.round_down_spec a align hpow as ⟨m, hbound, _, haligned, _, _⟩
  step with Proofs.Raw.round_down_spec b align hpow as ⟨m', _, _, _, _, hgreatest⟩
  apply (UScalar.le_equiv _ _).mpr
  exact hgreatest m.val ((UScalar.le_equiv _ _).mp (le_trans hbound hab)) haligned

theorem size_matches_recursive (tail : layout.TrailingSliceLayout Usize)
    (description : LayoutMath.Description) (n : Usize)
    (hn : 0 < tail.size_rounding_align_and_phase._0.val.val)
    (hd : description.valid)
    (hr : trailingFormula tail = description.compile) :
    layout.TrailingSliceLayoutUsize.size_for_elems tail n
      ⦃ r => r.map UScalar.val =
        if description.size n.val ≤ Usize.max then some (description.size n.val) else none ⦄ := by
  step with Proofs.Raw.size_for_elems_spec tail n hn as ⟨r, hsize⟩
  rw [hr, LayoutMath.Formula.checkedSize, LayoutMath.compile_size description hd] at hsize
  exact hsize

theorem padding_matches_recursive (tail : layout.TrailingSliceLayout Usize)
    (description : LayoutMath.Description) (n : Usize)
    (hn : 0 < tail.size_rounding_align_and_phase._0.val.val)
    (hd : description.valid)
    (hr : trailingFormula tail = description.compile)
    (hfit : description.size n.val ≤ Usize.max) :
    layout.TrailingSliceLayoutUsize.padding_for_elems tail n
      ⦃ p => p.val + description.offset + n.val * description.elem = description.size n.val ⦄ := by
  step with Proofs.Raw.padding_for_elems_spec tail n hn as ⟨p, hp⟩
  have ho : tail.offset.val = description.offset := by
    have h := congrArg LayoutMath.Formula.offset hr
    simpa only [trailingFormula, byteFormula, LayoutMath.compile_offset] using h
  have he : tail.elem_size.val = description.elem := by
    have h := congrArg LayoutMath.Formula.elem hr
    simpa only [trailingFormula, LayoutMath.compile_elem] using h
  rw [ho, he, hr, LayoutMath.compile_size description hd] at hp
  have hcontains := LayoutMath.description_contains_tail description n.val
  let physical := description.offset + n.val * description.elem
  let remaining := description.size n.val - physical
  have hsum : remaining + physical = description.size n.val := by
    dsimp only [remaining, physical]
    omega
  have hmod : Nat.ModEq (UScalar.size .Usize) (p.val + physical) (remaining + physical) := by
    change (p.val + physical) % UScalar.size .Usize =
      (remaining + physical) % UScalar.size .Usize
    rw [hsum]
    simpa only [physical, Nat.add_assoc, UScalar.size_UScalarTyUsize] using hp
  have hcancel := Nat.ModEq.add_right_cancel' physical hmod
  have hremaining : remaining ≤ Usize.max := by dsimp only [remaining]; omega
  change p.val % UScalar.size .Usize = remaining % UScalar.size .Usize at hcancel
  rw [Nat.mod_eq_of_lt (UScalar.hSize p), word_mod_of_le remaining hremaining] at hcancel
  dsimp only [remaining, physical] at hcancel
  omega

end Zerocopy.Corollaries
