/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.Result
namespace Zerocopy.Corollaries
open Proofs

/- Selecting either input preserves any predicate shared by both inputs. -/
contract max_preserves (a b : NonZeroUsize) (P : NonZeroUsize → Prop)
  for util.max a b
  requires ha : P a
  requires hb : P b
  ensures r => P r
  proof:
    step with max_spec a b as ⟨r, _, hchoice, _, _⟩
    rcases hchoice with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb

contract min_preserves (a b : NonZeroUsize) (P : NonZeroUsize → Prop)
  for util.min a b
  requires ha : P a
  requires hb : P b
  ensures r => P r
  proof:
    step with min_spec a b as ⟨r, _, hchoice, _, _⟩
    rcases hchoice with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb

/-- Aligned inputs are fixed points of round-down. -/
theorem round_down_aligned (n : Usize) (align : NonZeroUsize)
    (hpow : (align.val : Nat).isPowerOfTwo)
    (haligned : (n : Nat) % (align.val : Nat) = 0) :
    util.round_down_to_next_multiple_of_alignment n align = .ok n := by
  obtain ⟨m, hm, _, hexact, _, _, _⟩ :=
    WP.spec_imp_exists (round_down_spec n align hpow)
  have heq : m = n := UScalar.eq_of_val_eq (by
    simpa only [haligned, Nat.sub_zero] using hexact)
  simpa only [heq] using hm

contract round_down_idempotent (n : Usize) (align : NonZeroUsize)
  for (do
    let m ← util.round_down_to_next_multiple_of_alignment n align
    let m' ← util.round_down_to_next_multiple_of_alignment m align
    ok (m, m'))
  requires hpow : (align.val : Nat).isPowerOfTwo
  ensures m m' => m' = m
  proof:
    step with round_down_spec n align hpow as ⟨m, _, _, haligned, _, _⟩
    rw [round_down_aligned m align hpow haligned]
    simp only [bind_ok, WP.spec_ok, WP.uncurry'_pair]

contract round_down_monotone (a b : Usize) (align : NonZeroUsize)
  for (do
    let m ← util.round_down_to_next_multiple_of_alignment a align
    let m' ← util.round_down_to_next_multiple_of_alignment b align
    ok (m, m'))
  requires hab : a ≤ b
  requires hpow : (align.val : Nat).isPowerOfTwo
  ensures m m' => m ≤ m'
  proof:
    step with round_down_spec a align hpow as ⟨m, hbound, _, haligned, _, _⟩
    step with round_down_spec b align hpow as ⟨m', _, _, _, _, hgreatest⟩
    apply (UScalar.le_equiv _ _).mpr
    exact hgreatest m.val ((UScalar.le_equiv _ _).mp (le_trans hbound hab)) haligned

/-- The original headroom condition implies the exact fit requirement. -/
theorem pad_to_align_sized_headroom (self : layout.DstLayout) (size : Usize)
    (hs : self.size_info = layout.SizeInfo.Sized size)
    (hpow : (self.align.val : Nat).isPowerOfTwo)
    (hroom : (size : Nat) + (self.align.val : Nat) - 1 ≤ Usize.max) :
    ∃ r, layout.DstLayout.pad_to_align self = .ok r := by
  have hpos := Nat.pos_of_isPowerOfTwo hpow
  have hlt := Nat.mod_lt (self.align.val.val - size.val % self.align.val.val) hpos
  have hp := pad_to_align_spec self (by
    simp only [hs]
    exact ⟨hpow, by omega⟩)
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists hp
  exact ⟨r, hr⟩

/-- Padding an already aligned sized layout or any DST is the identity. -/
theorem pad_to_align_aligned (self : layout.DstLayout)
    (h : ∀ size, self.size_info = layout.SizeInfo.Sized size →
      (self.align.val : Nat).isPowerOfTwo ∧
        (size : Nat) % (self.align.val : Nat) = 0) :
    layout.DstLayout.pad_to_align self = .ok self := by
  cases hs : self.size_info with
  | SliceDst dst =>
    have hp := pad_to_align_spec self (by simp only [hs])
    obtain ⟨r, hr, _, heq⟩ := WP.spec_imp_exists hp
    simp only [hs] at heq
    simpa only [heq] using hr
  | Sized size =>
    obtain ⟨hpow, haligned⟩ := h size hs
    have hp := pad_to_align_spec self (by
      simp only [hs]
      refine ⟨hpow, ?_⟩
      simp only [haligned, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
      scalar_tac)
    obtain ⟨r, hr, halign, hpost⟩ := WP.spec_imp_exists hp
    simp only [hs] at hpost
    obtain ⟨padded, hinfo, hexact, _, _, _, _, hflag⟩ := hpost
    have heq : padded = size := UScalar.eq_of_val_eq (by
      simpa only [haligned, Nat.sub_zero, Nat.mod_self, Nat.add_zero] using hexact)
    have hflag' : r.statically_shallow_unpadded = self.statically_shallow_unpadded := by
      simpa only [haligned, decide_true, Bool.and_true] using hflag
    have hrself : r = self := by
      cases r
      cases self
      simp_all
    simpa only [hrself] using hr

/- Reapplying layout padding succeeds and leaves the first result unchanged. -/
contract pad_to_align_idempotent (self : layout.DstLayout)
  for (do
    let r ← layout.DstLayout.pad_to_align self
    let r' ← layout.DstLayout.pad_to_align r
    ok (r, r'))
  requires h : ∀ size, self.size_info = layout.SizeInfo.Sized size →
    let S : Nat := size
    let A : Nat := self.align.val
    A.isPowerOfTwo ∧ S + (A - S % A) % A ≤ Usize.max
  ensures r r' => r' = r
  proof:
    have hp := pad_to_align_spec self (by
      cases hs : self.size_info with
      | Sized size => exact h size hs
      | SliceDst dst => trivial)
    obtain ⟨r, hr, halign, hpost⟩ := WP.spec_imp_exists hp
    rw [hr, bind_ok]
    have hraligned : ∀ size, r.size_info = layout.SizeInfo.Sized size →
        (r.align.val : Nat).isPowerOfTwo ∧
          (size : Nat) % (r.align.val : Nat) = 0 := by
      cases hs : self.size_info with
      | SliceDst dst =>
        simp only [hs] at hpost
        intro size hsize
        rw [hpost, hs] at hsize
        contradiction
      | Sized size =>
        obtain ⟨hpow, _⟩ := h size hs
        simp only [hs] at hpost
        obtain ⟨padded, hinfo, _, _, _, haligned, _, _⟩ := hpost
        intro size' hsize
        rw [hinfo] at hsize
        cases hsize
        simpa only [halign] using And.intro hpow haligned
    rw [pad_to_align_aligned r hraligned]
    simp only [bind_ok, WP.spec_ok, WP.uncurry'_pair]

end Zerocopy.Corollaries
