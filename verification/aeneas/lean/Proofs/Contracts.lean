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

end Zerocopy.Proofs
