/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import TraitLaws
@[expose] public section

/-!
Generic callers receive evidence about the exact extracted dictionary. An
implementation proof discharges that evidence separately. XOR cancellation
proves a total codec, and forwarding preserves only the supplied codec's law.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- These primitive byte interpretations follow Rust's validity and layout
-- rules. The array law below uses those interpretations, not the optional
-- library decoder's (possibly smaller) admission domain.
@[instance] theorem Bool.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized Bool Zerocopy.Bool.Insts.ZerocopyIntoBytes :=
  ⟨Rust.Storage.boolDecoder_initialized⟩

@[instance] theorem U8.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized U8 Zerocopy.U8.Insts.ZerocopyIntoBytes :=
  ⟨initializedUScalar .U8⟩

@[instance] theorem Tuple.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized Unit Zerocopy.Tuple.Insts.ZerocopyIntoBytes :=
  ⟨Rust.Storage.unitDecoder_initialized⟩

-- The original type, const length, and computational dictionary remain the
-- native implementation's prefix. Only the element's provider and law are
-- added. There is no assumption of the array's own law.
@[instance] theorem Array.Insts.ZerocopyIntoBytes_law
    {T : Type} (N : Usize) (dictionary : IntoBytes T)
    [meaning : RustModel T] [law : TraitLaws.into_bytes_initialized T dictionary] :
    TraitLaws.into_bytes_initialized (Aeneas.Std.Array T N)
      (Zerocopy.Array.Insts.ZerocopyIntoBytes N dictionary) :=
  ⟨RustModel.initialized_array T N (@TraitLaws.into_bytes_initialized.holds T dictionary meaning law)⟩

-- Calling the real Rust helper selects the existing unsafe impls in Charon.
-- The generic impl law proves all lengths; these concrete cases additionally
-- check that the actual extraction and canonical model bindings compose.
theorem array_into_bytes_spec : Specs.array_into_bytes_spec := by
  simp only [Specs.array_into_bytes_spec, Zerocopy.trait_checks.check_array_into_bytes,
    Zerocopy.trait_checks.require_into_bytes, bind_ok, WP.spec_ok]
  refine ⟨(), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (@TraitLaws.into_bytes_initialized.holds _
      (Zerocopy.Array.Insts.ZerocopyIntoBytes _ Zerocopy.Bool.Insts.ZerocopyIntoBytes)
      _ inferInstance)
  · exact (@TraitLaws.into_bytes_initialized.holds _
      (Zerocopy.Array.Insts.ZerocopyIntoBytes _ Zerocopy.U8.Insts.ZerocopyIntoBytes)
      _ inferInstance)
  · exact (@TraitLaws.into_bytes_initialized.holds _
      (Zerocopy.Array.Insts.ZerocopyIntoBytes _ Zerocopy.Tuple.Insts.ZerocopyIntoBytes)
      _ inferInstance)
  · exact (@TraitLaws.into_bytes_initialized.holds _
      (Zerocopy.Array.Insts.ZerocopyIntoBytes _ Zerocopy.Bool.Insts.ZerocopyIntoBytes)
      _ inferInstance)
  · exact (@TraitLaws.into_bytes_initialized.holds _
      (Zerocopy.Array.Insts.ZerocopyIntoBytes _
        (Zerocopy.Array.Insts.ZerocopyIntoBytes _ Zerocopy.Bool.Insts.ZerocopyIntoBytes))
      _ inferInstance)


@[instance] theorem trait_checks.XorCodec.Insts.ZerocopyTrait_checksByteCodec_law :
    TraitLaws.byte_roundtrip Zerocopy.trait_checks.XorCodec
      Zerocopy.trait_checks.XorCodec.Insts.ZerocopyTrait_checksByteCodec := by
  constructor
  intro byte
  simp only [Zerocopy.trait_checks.XorCodec.Insts.ZerocopyTrait_checksByteCodec.encode,
    Zerocopy.trait_checks.XorCodec.Insts.ZerocopyTrait_checksByteCodec.decode,
    bind_ok, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  simp [UScalar.val_xor]

@[instance] theorem trait_checks.Forward.Insts.ZerocopyTrait_checksByteCodec_law
    {C : Type} (dictionary : Zerocopy.trait_checks.ByteCodec C)
    [law : TraitLaws.byte_roundtrip C dictionary] :
    TraitLaws.byte_roundtrip (Zerocopy.trait_checks.Forward C)
      (Zerocopy.trait_checks.Forward.Insts.ZerocopyTrait_checksByteCodec dictionary) := by
  constructor
  simpa only [Zerocopy.trait_checks.Forward.Insts.ZerocopyTrait_checksByteCodec,
    Zerocopy.trait_checks.Forward.Insts.ZerocopyTrait_checksByteCodec.encode,
    Zerocopy.trait_checks.Forward.Insts.ZerocopyTrait_checksByteCodec.decode]
    using (@TraitLaws.byte_roundtrip.holds C dictionary law)

theorem byte_codec_roundtrip_spec : Specs.byte_codec_roundtrip_spec := by
  intro C dictionary byte _ law mathematical decoded
  apply WP.spec_mono (@TraitLaws.byte_roundtrip.holds C dictionary law byte)
  intro result same
  subst result
  exact ⟨mathematical, decoded, rfl⟩

theorem forwarded_byte_codec_spec : Specs.forwarded_byte_codec_spec := by
  intro byte mathematical decoded
  exact byte_codec_roundtrip_spec (Zerocopy.trait_checks.Forward Zerocopy.trait_checks.XorCodec)
    (Zerocopy.trait_checks.Forward.Insts.ZerocopyTrait_checksByteCodec
      Zerocopy.trait_checks.XorCodec.Insts.ZerocopyTrait_checksByteCodec)
    byte mathematical decoded

end Zerocopy.Proofs
