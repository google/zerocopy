/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Raw.Encoding
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

end Zerocopy.Proofs

namespace Zerocopy.Proofs
open AeneasSpecs

end Zerocopy.Proofs
