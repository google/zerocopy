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

@[instance] theorem U8.Insts.ZerocopyUnaligned_law :
    TraitLaws.unaligned Aeneas.Std.U8 Zerocopy.U8.Insts.ZerocopyUnaligned :=
  ⟨RustLayout.align_u8⟩

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

theorem unaligned_alignment_spec : Specs.unaligned_alignment_spec := by
  intro T dictionary _ law
  simp only [Zerocopy.trait_checks.unaligned_alignment, core.mem.align_of, WP.spec_ok]
  refine ⟨unsignedWord (RustLayout.align T), rfl, ?_⟩
  rw [@TraitLaws.unaligned.holds T dictionary law]
  simp [unsignedWord, UScalar.val]

theorem unaligned_check_spec : Specs.unaligned_check_spec := by
  intro T dictionary _ law
  unfold Zerocopy.trait_checks.check_unaligned
  step with unaligned_alignment_spec T dictionary as ⟨alignment, mathematical, decoded, one⟩
  have same : alignment = 1#usize := by
    apply UScalar.eq_of_val_eq
    have numeric := (decodeUScalar_iff alignment _).mp decoded
    change alignment.val = 1
    exact numeric.trans one
  simp only [same, massert, ↓reduceIte, WP.spec_ok]
  exact ⟨(), rfl⟩

theorem unused_unaligned_bound_spec : Specs.unused_unaligned_bound_spec := by
  intro T dictionary value _ law mathematical decoded
  simp only [Zerocopy.trait_checks.unused_unaligned_bound, WP.spec_ok]
  exact ⟨mathematical, decoded, rfl⟩

theorem concrete_unaligned_check_spec : Specs.concrete_unaligned_check_spec := by
  simpa only [Specs.concrete_unaligned_check_spec, Zerocopy.trait_checks.check_byte_unaligned]
    using (unaligned_check_spec Aeneas.Std.U8 Zerocopy.U8.Insts.ZerocopyUnaligned)

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
