/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Raw.Trailing
public import Proofs.Raw.Layout
@[expose] public section

open Aeneas Aeneas.Std

namespace Zerocopy.Proofs
open AeneasSpecs

-- Unfold only representation domains. The model calls and authored outcome
-- predicates remain the independently verified raw contracts below.
macro "representation_simps" : tactic =>
  `(tactic|
    (simp only [WP.spec_equiv_exists]
     simp (config := { index := false }) only [contract_simps]
     simp only [← WP.spec_equiv_exists]))

/- Connect the constructor's power-of-two and phase checks to exact encoding.
The canonical form also proves decoding of the actual returned word.
-/
theorem encoding_new_spec : Zerocopy.Specs.encoding_new_spec := by
  intro align phase av ha pv hp hpow hphase
  have hav := (decodeNonZeroUScalar_iff align av).mp ha
  have hpv := (decodeUScalar_iff phase pv).mp hp
  apply WP.spec_mono (Raw.encoding_new_spec align phase
    (by simpa only [hav] using hpow) (by simpa only [hav, hpv] using hphase))
  intro encoded he
  have hfit : av.value + pv.value ≤ Usize.max := by
    rw [← hav, ← hpv, ← he]
    scalar_tac
  let value : layout.RoundingAlignAndPhase.RoundingValue :=
    ⟨av.value, pv.value, hpow, hphase, hfit⟩
  refine ⟨value, (rounding_decode_iff encoded value).mpr ?_, rfl, rfl⟩
  simpa only [roundingRepresents, value, hav, hpv] using he
register_spec_step encoding_new_spec

/- Prove the implementation's bit scan recovers the alignment and phase of every
positive stored word, not only words built by the constructor.
-/
theorem encoding_components_spec : Zerocopy.Specs.encoding_components_spec := by
  intro self value decoded
  have hn := (encoding_valid_iff self).mp ⟨value, decoded⟩
  have hvalue := rounding_decode_components self value decoded
  apply WP.spec_mono (Raw.encoding_components_spec self hn)
  rintro ⟨align, phase⟩ facts
  let av : NonZeroUsizeValue :=
    ⟨unsignedWord align.val, Nat.pos_of_isPowerOfTwo facts.1⟩
  have ha : modelNonZeroUsize.decode align = some av :=
    (decodeNonZeroUScalar_iff align av).mpr rfl
  refine ⟨(av, unsignedWord phase), ?_, ?_⟩
  · simp only [RustModel.decode,
      dif_pos (Nat.pos_of_isPowerOfTwo facts.1)]
    rfl
  · exact ⟨facts.2.2.2.1.trans hvalue.1.symm,
      facts.2.2.2.2.trans hvalue.2.symm⟩
register_spec_step encoding_components_spec

/- Reuse the components theorem for the getter that discards phase.
-/
theorem encoding_align_spec : Zerocopy.Specs.encoding_align_spec := by
  intro self value decoded
  have hn := (encoding_valid_iff self).mp ⟨value, decoded⟩
  have hvalue := rounding_decode_components self value decoded
  apply WP.spec_mono (Raw.encoding_align_spec self hn)
  intro align he
  have hp : 0 < align.val.val := by rw [he]; exact Nat.two_pow_pos _
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, hp⟩
  exact ⟨av, (decodeNonZeroUScalar_iff align av).mpr rfl, he.trans hvalue.1.symm⟩
register_spec_step encoding_align_spec

/- Reading physical offset must preserve the raw word even though the element
carrier can be generic. No size normalization is needed for this observation.
-/
theorem size_offset_spec : Zerocopy.Specs.size_offset_spec := by
  unfold Zerocopy.Specs.size_offset_spec
  representation_simps
  intro E self validity hv
  exact Raw.size_offset_spec self hv.2
register_spec_step size_offset_spec

/- Solve the rounded complete-size inequality for the greatest byte budget. The
proof must preserve rounding plateaus and the case where even zero bytes do
not fit; dividing by element stride belongs to a later operation.
-/
theorem max_trailing_bytes_spec : Zerocopy.Specs.max_trailing_bytes_spec := by
  unfold Zerocopy.Specs.max_trailing_bytes_spec
  representation_simps
  intro E self available validity hv
  apply WP.spec_mono (Raw.max_trailing_bytes_spec self available hv.2)
  intro result facts
  refine ⟨?_, facts⟩
  change isValid result
  simp
register_spec_step max_trailing_bytes_spec

/- Compute padding with wrapping machine arithmetic. The raw theorem records the
modular result; physical padding follows only when the complete size fits.
-/
theorem padding_for_elems_spec : Zerocopy.Specs.padding_for_elems_spec := by
  unfold Zerocopy.Specs.padding_for_elems_spec
  representation_simps
  intro self elems hv
  exact Raw.padding_for_elems_spec self elems hv
register_spec_step padding_for_elems_spec

/- Distinguish a successful checked size from overflow using the unbounded
complete-size formula. Rust None is a successful payload, not a panic.
-/
theorem size_for_elems_spec : Zerocopy.Specs.size_for_elems_spec := by
  intro self elems value hvalue count hcount
  have hv : 0 < self.size_rounding_align_and_phase._0.val.val :=
    by simpa only [trailingValid, encodingValid, scalar_valid_iff, true_and] using
      (trailing_decoder_admitted_iff self).mp ⟨value, hvalue⟩
  have hformula := trailingFormula_decode self value hvalue
  have hn := (decodeUScalar_iff elems count).mp hcount
  apply WP.spec_mono (Raw.size_for_elems_spec self elems hv)
  intro result facts
  obtain ⟨decoded, hd⟩ := (option_valid_iff result).mpr (by simp)
  refine ⟨decoded, hd, ?_⟩
  change decoded.map (fun size => (size : Nat)) = _
  rw [optionalSize_decode result decoded hd, hformula, ← hn]
  exact facts
register_spec_step size_for_elems_spec

theorem max_elems_for_bytes_spec : Zerocopy.Specs.max_elems_for_bytes_spec := by
  unfold Zerocopy.Specs.max_elems_for_bytes_spec
  representation_simps
  intro bytes elem hn
  apply WP.spec_mono (Raw.max_elems_for_bytes_spec bytes elem hn)
  intro result facts
  refine ⟨?_, facts⟩
  change isValid result
  simp
register_spec_step max_elems_for_bytes_spec

theorem assume_shallow_unpadded_spec : Zerocopy.Specs.assume_shallow_unpadded_spec := by
  unfold Zerocopy.Specs.assume_shallow_unpadded_spec
  representation_simps
  intro self hv
  apply WP.spec_mono (Raw.assume_shallow_unpadded_spec self)
  intro r facts
  refine ⟨?_, facts⟩
  simpa only [facts.1, facts.2.1] using hv
register_spec_step assume_shallow_unpadded_spec

/- Construct a fixed layout from explicit modeled size and alignment reads.
Those reads are data premises supplied by the external ABI bridge, not axioms
asserting that an arbitrary modeled size is the layout of a Rust type.
-/
theorem for_type_spec : Zerocopy.Specs.for_type_spec := by
  unfold Zerocopy.Specs.for_type_spec
  representation_simps
  intro T validity size align hs ha hn
  apply WP.spec_mono (Raw.for_type_spec T size align hs ha hn)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1, hn, and_self]
register_spec_step for_type_spec

/- Construct the same fixed layout with its asserted unpadded flag. The caller's
separate padding justification is outside this numerical contract.
-/
theorem for_unpadded_type_spec : Zerocopy.Specs.for_unpadded_type_spec := by
  unfold Zerocopy.Specs.for_unpadded_type_spec
  representation_simps
  intro T validity size align hs ha hn
  apply WP.spec_mono (Raw.for_unpadded_type_spec T size align hs ha hn)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1, hn, and_self]
register_spec_step for_unpadded_type_spec

/- Construct a trailing layout with element size as stride and the modeled ABI
alignment as its rounding alignment. The primitive read premises stay
explicit.
-/
theorem for_slice_spec : Zerocopy.Specs.for_slice_spec := by
  unfold Zerocopy.Specs.for_slice_spec
  representation_simps
  intro T validity size align hs ha hp
  apply WP.spec_mono (Raw.for_slice_spec T size align hs ha hp)
  intro r facts
  refine ⟨?_, facts⟩
  rcases facts with ⟨halign, _, tail, hsi, _, _, _, hcode⟩
  simp only [halign, hsi]
  have := Nat.pos_of_isPowerOfTwo hp
  simpa only [hcode, and_self] using this
register_spec_step for_slice_spec

theorem requires_static_padding_spec : Zerocopy.Specs.requires_static_padding_spec := by
  unfold Zerocopy.Specs.requires_static_padding_spec
  representation_simps
  intro self _
  exact Raw.requires_static_padding_spec self
register_spec_step requires_static_padding_spec

end Zerocopy.Proofs

namespace Zerocopy.Proofs
open AeneasSpecs

/- Explain both zero-stride rejection and successful conversion. The raw lemma
retains broad representation coverage; the canonical spec adds recursive
admission rather than silently changing that useful raw theorem.
-/
theorem try_nonzero_spec : Zerocopy.Specs.try_nonzero_spec := by
  unfold Zerocopy.Specs.try_nonzero_spec
  representation_simps
  intro self value decoded
  have hv := (size_info_valid_iff self).mp ⟨value, decoded⟩
  apply WP.spec_mono (Raw.try_nonzero_spec self)
  intro r facts
  constructor
  swap
  · cases self <;> simpa using facts
  change isValid r
  rw [option_valid_iff]
  cases self with
  | Sized size =>
    simp only [] at facts
    rw [facts]
    simp [sizeInfoValid]
  | SliceDst tail =>
    simp only [sizeInfoValid, trailingValid, scalar_valid_iff, true_and] at hv
    simp only [] at facts
    by_cases hz : tail.elem_size = 0#usize
    · simp only [hz, if_true] at facts
      rw [facts]
      simp
    · simp only [hz, if_false] at facts
      rcases facts with ⟨next, hr, _, _, hcode, helem⟩
      rw [hr]
      simp only [Option.mem_some_iff, forall_eq']
      rw [size_info_valid_iff]
      change trailingValid next
      simp only [trailingValid, nonzero_valid_iff, encodingValid, hcode]
      have hnz : tail.elem_size.val ≠ 0 := by
        intro h
        apply hz
        exact UScalar.eq_of_val_eq (by simpa using h)
      exact ⟨by simpa only [helem] using Nat.pos_of_ne_zero hnz, hv⟩
register_spec_step try_nonzero_spec

theorem new_zst_spec : Zerocopy.Specs.new_zst_spec := by
  unfold Zerocopy.Specs.new_zst_spec
  representation_simps
  intro repr_align hv hp
  apply WP.spec_mono (Raw.new_zst_spec repr_align hp)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1]
  cases repr_align with
  | none => simp
  | some a => simpa only [Option.getD_some, and_true] using Nat.pos_of_isPowerOfTwo (hp a rfl)
register_spec_step new_zst_spec

/-- An arbitrary proof of the compact mathematical clause implies the separately
maintained exact optional-size and overflow obligation. -/
@[contract_simps] theorem size_for_elems_spec_implies_required
    (self : layout.TrailingSliceLayout Usize) (elems : Usize) (run : Result (Option Usize))
    (provided : Zerocopy.Specs.size_for_elems_spec_contract self elems run) :
    Zerocopy.Obligations.size_for_elems_spec_contract self elems run := by
  intro positive
  have valid : trailingValid self := ⟨by simp, positive⟩
  obtain ⟨value, hvalue⟩ := (trailing_decoder_admitted_iff self).mpr valid
  have hformula := trailingFormula_decode self value hvalue
  have execution := provided value hvalue (unsignedWord elems) rfl
  simp only [WP.spec_equiv_exists] at execution
  obtain ⟨result, hexec, decoded, hd, hsize⟩ := execution
  refine ⟨result, hexec, ?_⟩
  change decoded.map (fun size => (size : Nat)) = _ at hsize
  rw [optionalSize_decode result decoded hd, hformula, unsignedWord_value] at hsize
  exact hsize

end Zerocopy.Proofs
