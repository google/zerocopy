/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Raw.Trailing
public import Proofs.Raw.Layout
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false
theorem cast_offset_spec (cast : layout.CastType) (length : Usize) :
    (match cast with | .Prefix => Result.ok 0#usize | .Suffix => Result.ok length)
      ⦃ offset => offset.val = castSide cast length.val ∧ offset ≤ length ⦄ := by
  cases cast <;> simp [castSide, WP.spec_ok]

theorem cast_split_spec (cast : layout.CastType) (length size elems : Usize)
    (h : size.val ≤ length.val) :
    (match cast with
      | .Prefix => Result.ok (core.result.Result.Ok (elems, size))
      | .Suffix => do
        let split ← length - size
        Result.ok (core.result.Result.Ok (elems, split)) :
      Result (core.result.Result (Usize × Usize) layout.MetadataCastError))
      ⦃ r => ∃ split, r = .Ok (elems, split) ∧
        split.val = castSplit cast length.val size.val ⦄ := by
  cases cast with
  | Prefix => exact WP.spec.ret ⟨size, rfl, rfl⟩
  | Suffix =>
    step with Usize.sub_spec h as ⟨split, hs, _⟩
    exact ⟨split, rfl, hs⟩

/- Track alignment-error priority, complete-size capacity, and prefix/suffix
splitting through the actual branches. A zero trailing stride intentionally
panics and therefore lies outside this total contract's required domain.
-/
theorem validate_cast_spec :
  ∀ (self : layout.DstLayout) (addr bytes_len : Usize) (cast_type : layout.CastType), ∀ (ha : (0 < self.align.val.val : Prop)), ∀ (hroom : (addr.val + bytes_len.val ≤ Usize.max : Prop)), ∀ (ht : (match self.size_info with
    | .Sized _ => True
    | .SliceDst tail => 0 < tail.size_rounding_align_and_phase._0.val.val ∧ 0 < tail.elem_size.val : Prop)),
    @Zerocopy.layout.DstLayout.validate_cast_and_convert_metadata self addr bytes_len cast_type ⦃ r => castSpec self addr.val bytes_len.val cast_type r ⦄ := by
  intro self addr length cast ha hroom ht
  unfold layout.DstLayout.validate_cast_and_convert_metadata
  cases hs : self.size_info with
  | Sized size =>
    step with try_nonzero_spec (.Sized size) as ⟨converted, hconverted⟩
    rw [hconverted]
    step as ⟨checked, haddr⟩
    cases checked with
    | none => simp only [] at haddr; omega
    | some ending =>
      simp only [] at haddr
      simp only [Option.isSome_some, massert, if_true, bind_ok]
      step with cast_offset_spec cast length as ⟨offset, ho, hle⟩
      have hlen := (UScalar.le_equiv _ _).mp hle
      step with Usize.add_spec (x := addr) (y := offset) (by omega) as ⟨aligned, haligned⟩
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      step with Usize.rem_spec aligned (y := self.align.val) (by omega) as ⟨rem, hr⟩
      simp only [bne_iff_ne]
      split
      · rename_i hne
        apply WP.spec.ret
        unfold castSpec
        have hv : rem.val ≠ 0 := by
          intro h
          apply hne
          exact (UScalar.eq_equiv _ _).mpr h
        rw [hr, haligned, ho] at hv
        exact hv
      · rename_i heq
        have hzero : (addr.val + castSide cast length.val) % self.align.val.val = 0 := by
          have h : rem = 0#usize := not_ne_iff.mp heq
          have hv := congrArg UScalar.val h
          rw [hr, haligned, ho] at hv
          exact hv
        have htotal : (decide (size > length) || decide (size ≤ length)) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact lt_or_ge length size
        simp only [UScalar.lt_equiv, UScalar.le_equiv] at htotal ⊢
        simp only [htotal, if_true, bind_ok]
        split
        · rename_i hbig
          apply WP.spec.ret
          simp only [castSpec, hs]
          exact ⟨hzero, hbig⟩
        · rename_i hsmall
          step with cast_split_spec cast length size 0#usize (by omega) as ⟨r, split, hr, hv⟩
          rw [hr]
          simp only [castSpec, hs, show (0#usize).val = 0 by simp]
          exact ⟨hzero, trivial, by omega, hv⟩
  | SliceDst tail =>
    simp only [hs] at ht
    step with try_nonzero_spec (.SliceDst tail) as ⟨converted, hconverted⟩
    have hne : tail.elem_size ≠ 0#usize := by
      intro h
      have hv := congrArg UScalar.val h
      change tail.elem_size.val = 0 at hv
      omega
    simp only [hne, if_false] at hconverted
    obtain ⟨t, hconverted, hoffset, hbase, hcode, helem⟩ := hconverted
    rw [hconverted]
    step as ⟨checked, haddr⟩
    cases checked with
    | none => simp only [] at haddr; omega
    | some ending =>
      simp only [] at haddr
      simp only [Option.isSome_some, massert, if_true, bind_ok]
      step with cast_offset_spec cast length as ⟨offset, ho, hle⟩
      have hlen := (UScalar.le_equiv _ _).mp hle
      step with Usize.add_spec (x := addr) (y := offset) (by omega) as ⟨aligned, haligned⟩
      simp only [core.num.nonzero.NonZero.get, bind_ok]
      step with Usize.rem_spec aligned (y := self.align.val) (by omega) as ⟨rem, hr⟩
      simp only [bne_iff_ne]
      split
      · rename_i hne
        apply WP.spec.ret
        unfold castSpec
        have hv : rem.val ≠ 0 := by
          intro h
          apply hne
          exact (UScalar.eq_equiv _ _).mpr h
        rw [hr, haligned, ho] at hv
        exact hv
      · rename_i heq
        have hzero : (addr.val + castSide cast length.val) % self.align.val.val = 0 := by
          have h : rem = 0#usize := not_ne_iff.mp heq
          have hv := congrArg UScalar.val h
          rw [hr, haligned, ho] at hv
          exact hv
        have htn : 0 < t.size_rounding_align_and_phase._0.val.val := by rw [hcode]; exact ht.1
        have hte : 0 < t.elem_size.val.val := by rw [helem]; exact ht.2
        have hview : byteFormula t = byteFormula tail := by simp only [byteFormula, hbase, hcode, hoffset]
        step with max_trailing_bytes_spec t length htn as ⟨capacity, hc⟩
        rw [hview] at hc
        cases capacity with
        | none =>
          have hmiss := LayoutMath.capacity_spec (byteFormula tail) length.val (Nat.two_pow_pos _)
          rw [← hc] at hmiss
          apply WP.spec.ret
          refine ⟨hzero, ?_⟩
          simp only [hs]
          intro n
          exact hmiss (n * tail.elem_size.val)
        | some capacity =>
          dsimp only
          step with max_elems_for_bytes_spec capacity t.elem_size hte as ⟨elems, used, hen, _, _, _, _⟩
          step with encoding_align_spec t.size_rounding_align_and_phase htn as ⟨a, ha⟩
          have hav : a.val.val = (trailingFormula tail).align := by
            simpa only [trailingFormula, byteFormula, hcode] using ha
          step with Usize.rem_spec capacity (y := t.elem_size.val) (by omega) as ⟨unused, hu⟩
          have hap : a.val.val.isPowerOfTwo := ⟨_, by simpa only [hcode] using ha⟩
          step with round_down_spec unused a hap as ⟨unused_aligned, _, huf, _, _, _⟩
          have hcap : (trailingFormula tail).capacity length.val = some capacity.val := hc.symm
          have hmax := LayoutMath.maximal_metadata _ _ _ ht.2 hcap (trailing_align_pos tail)
          have hfit : (trailingFormula tail).size elems.val ≤ length.val := by
            apply (hmax elems.val).mpr
            rw [hen, helem]
            exact le_rfl
          have hmin := (LayoutMath.capacity_spec (trailingFormula tail) length.val (trailing_align_pos tail))
          rw [hcap] at hmin
          have hminfit := (hmin 0).mpr (by omega)
          have hbfit : t.size_base.val ≤ length.val := by
            rw [hbase]
            simp only [trailingFormula, byteFormula, LayoutMath.Formula.bytes] at hminfit
            omega
          step with Usize.sub_spec hbfit as ⟨available, hb, _⟩
          step with round_down_spec available a hap as ⟨budget, _, hbudget, _, _, _⟩
          have hused := LayoutMath.capacity_object_size (trailingFormula tail) length.val capacity.val
            (trailing_align_pos tail) hcap
          change (trailingFormula tail).size (capacity.val / tail.elem_size.val) =
            tail.size_base.val + (length.val - tail.size_base.val -
              (length.val - tail.size_base.val) % (trailingFormula tail).align) -
              (capacity.val % tail.elem_size.val -
                capacity.val % tail.elem_size.val % (trailingFormula tail).align) at hused
          rw [← hav, ← hbase] at hused
          have hunused : unused.val = capacity.val % tail.elem_size.val := by rw [hu, helem]
          have hbval : budget.val = length.val - t.size_base.val -
              (length.val - t.size_base.val) % a.val.val := by rw [hbudget, hb]
          have hus : unused_aligned.val ≤ budget.val := by
            have hmod := Nat.mod_le capacity.val tail.elem_size.val
            have hcapval : capacity.val = length.val - t.size_base.val -
                (length.val - t.size_base.val) % a.val.val - (trailingFormula tail).phase := by
              unfold LayoutMath.Formula.capacity at hcap
              simp only [hminfit, if_true, Option.some.injEq] at hcap
              have hav' : a.val.val = 2 ^ tail.size_rounding_align_and_phase._0.val.val.log2 := hav
              simpa only [trailingFormula, byteFormula, ← hav', ← hbase] using hcap.symm
            rw [huf, hbval, hunused]
            omega
          step with Usize.sub_spec hus as ⟨remaining, hremaining, _⟩
          have hsum : t.size_base.val + remaining.val ≤ Usize.max := by
            have hlenfit : length.val ≤ Usize.max := by scalar_tac
            rw [hremaining]
            have hbudget_bound : budget.val ≤ length.val - t.size_base.val := by rw [hbval]; omega
            omega
          step with Usize.add_spec (x := t.size_base) (y := remaining) hsum as ⟨size, hsize⟩
          have hexact : size.val = (trailingFormula tail).size elems.val := by
            rw [hen, helem]
            rw [hused]
            rw [hsize, hremaining, huf, hunused, hbval]
            rw [huf, hunused, hbval] at hus
            omega
          have hsizefit : size ≤ length := (UScalar.le_equiv _ _).mpr (by rw [hexact]; exact hfit)
          simp only [hsizefit, if_true, bind_ok]
          step with cast_split_spec cast length size elems (by rw [hexact]; exact hfit) as ⟨r, split, hr, hv⟩
          rw [hr]
          simp only [castSpec, hs]
          refine ⟨hzero, hfit, ?_, ?_⟩
          · intro n
            rw [hmax n, hen, helem]
            rfl
          · simpa only [hexact] using hv

/- Prove exact metadata inference, including rejection of unattainable sizes and
greatest-count selection when several counts share the same padded size.
-/
theorem metadata_exact_spec :
  ∀ (self : layout.DstLayout) (size : Usize), ∀ (ha : (0 < self.align.val.val : Prop)), ∀ (ht : (match self.size_info with
    | .Sized _ => True
    | .SliceDst tail => tail.elem_size.val ≠ 0 →
      0 < tail.size_rounding_align_and_phase._0.val.val : Prop)),
    @Zerocopy.layout.DstLayout.metadata_for_exact_size self size ⦃ r => metadataSpec self size.val r ⦄ := by
  intro self size ha ht
  unfold layout.DstLayout.metadata_for_exact_size
  cases hs : self.size_info with
  | Sized s => simp only [WP.spec_ok, metadataSpec, hs]
  | SliceDst tail =>
    simp only [hs] at ht ⊢
    cases hz : tail.elem_size.val with
    | zero =>
      simp only [WP.spec_ok, metadataSpec, hs, hz, if_true]
    | succ k =>
      simp only []
      have he : 0 < tail.elem_size.val := by omega
      have hn : tail.elem_size.val ≠ 0 := by omega
      step with validate_cast_spec self 0#usize size .Prefix ha (by scalar_tac)
        (by simp only [hs]; exact ⟨ht hn, he⟩) as ⟨cast, hc⟩
      cases cast with
      | Err err =>
        cases err with
        | Alignment =>
          simp only [castSpec, castSide, Nat.zero_add, Nat.zero_mod,
            ] at hc
          exact False.elim (hc rfl)
        | Size =>
          simp only [castSpec, castSide, hs,
            Nat.zero_add, Nat.zero_mod, true_and] at hc
          apply WP.spec.ret
          simp only [metadataSpec, hs, hn, if_false]
          intro n h
          have := hc n
          omega
      | Ok pair =>
        rcases pair with ⟨elems, bytes⟩
        change (if bytes = size then Result.ok (some elems) else Result.ok none)
          ⦃ r => metadataSpec self size.val r ⦄
        simp only [castSpec, castSide, castSplit, hs,
          Nat.zero_add, Nat.zero_mod, true_and] at hc
        split
        · rename_i hsame
          apply WP.spec.ret
          simp only [metadataSpec, hs, hn, if_false]
          have hbytes := congrArg UScalar.val hsame
          exact ⟨by omega, hc.2.1⟩
        · rename_i hdiff
          apply WP.spec.ret
          simp only [metadataSpec, hs, hn, if_false]
          intro n h
          have hle : n ≤ elems.val := (hc.2.1 n).mp (by omega)
          have hmono := LayoutMath.Formula.size_mono (trailingFormula tail)
            (trailing_align_pos tail) hle
          apply hdiff
          apply (UScalar.eq_equiv _ _).mpr
          omega

end Zerocopy.Proofs.Raw
