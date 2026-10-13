/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy
public import TraitLaws
@[expose] public section

/-!
These expectations retain every original type, dictionary, and machine word.
They require a successful return, including for the assertion-only callers;
the codec and identity checks observe exact raw words. A generic bound supplies
only its dictionary's law, including when the function never uses the bound.
The contract families quantify an arbitrary outcome independently of any body.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Obligations

def unaligned_alignment_spec_contract (T : Type) (dictionary : Unaligned T)
    (run : Result Usize) : Prop :=
  TraitLaws.unaligned T dictionary → run ⦃ alignment => alignment = 1#usize ⦄

def unaligned_alignment_spec : Prop :=
  ∀ (T : Type) (dictionary : Unaligned T),
    unaligned_alignment_spec_contract T dictionary (trait_checks.unaligned_alignment dictionary)

def unaligned_check_spec_contract (T : Type) (dictionary : Unaligned T)
    (run : Result Unit) : Prop :=
  TraitLaws.unaligned T dictionary → run ⦃ _ => True ⦄

def unaligned_check_spec : Prop :=
  ∀ (T : Type) (dictionary : Unaligned T),
    unaligned_check_spec_contract T dictionary (trait_checks.check_unaligned dictionary)

def unused_unaligned_bound_spec_contract (T : Type) (dictionary : Unaligned T)
    (value : Usize) (run : Result Usize) : Prop :=
  TraitLaws.unaligned T dictionary → run ⦃ result => result = value ⦄

def unused_unaligned_bound_spec : Prop :=
  ∀ (T : Type) (dictionary : Unaligned T) (value : Usize),
    unused_unaligned_bound_spec_contract T dictionary value
      (trait_checks.unused_unaligned_bound dictionary value)

def concrete_unaligned_check_spec_contract (run : Result Unit) : Prop :=
  run ⦃ _ => True ⦄

def concrete_unaligned_check_spec : Prop :=
  concrete_unaligned_check_spec_contract trait_checks.check_byte_unaligned

def byte_codec_roundtrip_spec_contract (C : Type) (dictionary : trait_checks.ByteCodec C)
    (byte : U8) (run : Result U8) : Prop :=
  TraitLaws.byte_roundtrip C dictionary → run ⦃ result => result = byte ⦄

def byte_codec_roundtrip_spec : Prop :=
  ∀ (C : Type) (dictionary : trait_checks.ByteCodec C) (byte : U8),
    byte_codec_roundtrip_spec_contract C dictionary byte
      (trait_checks.byte_codec_roundtrip dictionary byte)

def forwarded_byte_codec_spec_contract (byte : U8) (run : Result U8) : Prop :=
  run ⦃ result => result = byte ⦄

def forwarded_byte_codec_spec : Prop :=
  ∀ (byte : U8), forwarded_byte_codec_spec_contract byte (trait_checks.forwarded_byte_codec byte)

end Zerocopy.Obligations
