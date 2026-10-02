/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Raw.Layout
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false
theorem packing_limit_spec (packed : Option NonZeroUsize)
    (hp : ∀ a ∈ packed, a.val.val.isPowerOfTwo) :
    (match packed with | none => layout.DstLayout.THEORETICAL_MAX_ALIGN | some a => Result.ok a)
      ⦃ a => a.val.val = packingValue packed ∧ a.val.val.isPowerOfTwo ⦄ := by
  cases packed with
  | none =>
    step with theoretical_max_align_spec as ⟨a, ha⟩
    exact ⟨ha, ⟨_, ha⟩⟩
  | some a =>
    simp only [WP.spec_ok, packingValue, Option.map_some, Option.getD_some]
    exact ⟨by trivial, hp a rfl⟩

-- Aeneas shares a generated matcher with the alignment encoder. The model
-- comparison checks that matcher; this proof deliberately names it.
set_option linter.auxLemma false in
/- Append a field at its effective packed alignment, retaining the field's
complete inner layout. The canonical theorem then proves the concise
mathematical extension equation and successful decoding of the returned
record.
-/
theorem extend_spec :
  ∀ (self field : layout.DstLayout) (repr_packed : Option NonZeroUsize) (size : Usize), ∀ (hs : (self.size_info = .Sized size : Prop)), ∀ (hself : (self.align.val.val.isPowerOfTwo ∧ self.align.val.val ≤ 2 ^ 29 : Prop)), ∀ (hfield : (field.align.val.val.isPowerOfTwo ∧ field.align.val.val ≤ 2 ^ 29 : Prop)), ∀ (hpacked : (∀ a ∈ repr_packed, a.val.val.isPowerOfTwo ∧ a.val.val ≤ 2 ^ 29 : Prop)), ∀ (hfit : (match field.size_info with
    | .Sized field_size => placement size field repr_packed + field_size.val ≤ Usize.max
    | .SliceDst t => placement size field repr_packed + t.offset.val ≤ Usize.max ∧
      placement size field repr_packed + t.size_base.val ≤ Usize.max : Prop)),
    @Zerocopy.layout.DstLayout.extend self field repr_packed ⦃ r => r.align.val.val = max self.align.val.val (fieldAlignment field repr_packed) ∧
    r.statically_shallow_unpadded = (self.statically_shallow_unpadded &&
      field.statically_shallow_unpadded && decide (size.val % fieldAlignment field repr_packed = 0)) ∧
    match field.size_info with
    | .Sized field_size => ∃ s, r.size_info = .Sized s ∧
      s.val = placement size field repr_packed + field_size.val
    | .SliceDst t => ∃ u, r.size_info = .SliceDst u ∧
      u.offset.val = placement size field repr_packed + t.offset.val ∧
      u.size_base.val = placement size field repr_packed + t.size_base.val ∧
      u.elem_size = t.elem_size ∧
      u.size_rounding_align_and_phase = t.size_rounding_align_and_phase ⦄ := by
  intro self field packed size hs hself hfield hpacked hfit
  unfold layout.DstLayout.extend
  step with packing_limit_spec packed (fun a h => (hpacked a h).1) as ⟨limit, hl, hlpow⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨b, hb⟩
  have hbt : b = true := by
    have hb' : (b = true) = True := by simpa only [hlpow] using hb
    exact Eq.mpr hb' trivial
  simp only [massert, hbt, if_true, bind_ok]
  step with current_max_align_spec as ⟨maximum, hmaximum⟩
  have hsa : self.align.val ≤ maximum.val := (UScalar.le_equiv _ _).mpr (by omega)
  have hfa : field.align.val ≤ maximum.val := (UScalar.le_equiv _ _).mpr (by omega)
  simp only [hsa, hfa, if_true, bind_ok]
  -- State the match directly. Aeneas may assign its shared matcher to a
  -- different declaration when extraction gains another caller.
  have hpackcheck : (match (generalizing := false) packed with
    | none => Result.ok none
    | some a => do
      if a.val ≤ maximum.val then Result.ok () else Result.fail .assertionFailure
      Result.ok packed) = Result.ok packed := by
    cases packed with
    | none => rfl
    | some a =>
      have ha : a.val ≤ maximum.val := (UScalar.le_equiv _ _).mpr (by
        have := (hpacked a rfl).2
        omega)
      simp only [ha, if_true, bind_ok]
  -- Convert the initial bind to the same ordinary match before rewriting.
  -- The continuation and postcondition are preserved by the placeholders.
  change (Aeneas.Std.bind
    (match (generalizing := false) packed with
    | none => Result.ok none
    | some a => do
      if a.val ≤ maximum.val then Result.ok () else Result.fail .assertionFailure
      Result.ok packed) _) ⦃ _ ⦄
  rw [hpackcheck]
  simp only [bind_ok]
  step with min_spec field.align limit as ⟨fa, hmin, hchoice, _, _⟩
  have hfp : fa.val.val.isPowerOfTwo := by
    rcases hchoice with h | h
    · simpa only [h] using hfield.1
    · simpa only [h] using hlpow
  have hfv : fa.val.val = fieldAlignment field packed := by
    rw [hmin, Arithmetic.coe_min, hl]
    rfl
  step with max_spec self.align fa as ⟨align, hmax, _, _, _⟩
  have halign : align.val.val = max self.align.val.val (fieldAlignment field packed) := by
    rw [hmax, Arithmetic.coe_max, hfv]
  rw [hs]
  step with Zerocopy.Proofs.Raw.padding_lt_alignment size fa hfp as ⟨pad, _, hpad, _, _, hzero⟩
  have ho : size.val + pad.val = placement size field packed := by
    rw [hpad, hfv]
    rfl
  have hzero' : (pad = 0#usize) = (size.val % fieldAlignment field packed = 0) := by
    apply propext
    simpa only [UScalar.eq_equiv, show (0#usize).val = 0 by simp, hfv] using hzero
  step as ⟨checked, hsum⟩
  cases checked with
  | none =>
    simp only [] at hsum
    cases hf : field.size_info <;> simp only [hf] at hfit <;> omega
  | some offset =>
    simp only [] at hsum
    have hoff : offset.val = placement size field packed := by omega
    cases hf : field.size_info with
    | Sized field_size =>
      simp only [hf] at hfit
      step as ⟨checked, hsized⟩
      cases checked with
      | none => simp only [] at hsized; omega
      | some total =>
        simp only [] at hsized
        simp only []
        cases self.statically_shallow_unpadded <;> cases field.statically_shallow_unpadded <;>
          simp only [Bool.false_eq_true, Bool.false_and, Bool.true_and,
            if_false, if_true, WP.spec_ok, hzero']
        all_goals
          exact ⟨halign, by trivial, total, by trivial, by omega⟩
    | SliceDst tail =>
      simp only [hf] at hfit
      step as ⟨checked, hoffset⟩
      cases checked with
      | none => simp only [] at hoffset; omega
      | some physical =>
        simp only [] at hoffset
        simp only []
        step as ⟨checked, hbase⟩
        cases checked with
        | none => simp only [] at hbase; omega
        | some base =>
          simp only [] at hbase
          simp only []
          cases self.statically_shallow_unpadded <;> cases field.statically_shallow_unpadded <;>
            simp only [Bool.false_eq_true, Bool.false_and, Bool.true_and,
              if_false, if_true, WP.spec_ok, hzero']
          all_goals
            exact ⟨halign, by trivial, { tail with offset := physical, size_base := base },
              by trivial, by dsimp only; omega, by dsimp only; omega, rfl, rfl⟩

end Zerocopy.Proofs.Raw
