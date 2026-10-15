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

-- State initialization directly on accepted byte lists. This expectation
-- independently fixes the physical decoder used by each concrete root case,
-- rather than referring to the generated RustModel representation selection.
def arrayBytesInitialized (element : Rust.Storage.BitDecoder Raw) (count : Usize) : Prop :=
  ∀ bytes values,
    ((Rust.Storage.arrayDecoder element count.val).map
      (fun values => Aeneas.Std.Array.from values.val values.property)).run bytes = some values →
      Rust.Storage.Initialized bytes

def array_into_bytes_spec_contract (run : Result Unit) : Prop :=
  run ⦃ _ =>
    arrayBytesInitialized Rust.Storage.boolDecoder (3#usize) ∧
    arrayBytesInitialized AeneasSpecs.u8BitDecoder (3#usize) ∧
    arrayBytesInitialized Rust.Storage.unitDecoder (4#usize) ∧
    arrayBytesInitialized Rust.Storage.boolDecoder (0#usize) ∧
    arrayBytesInitialized ((Rust.Storage.arrayDecoder Rust.Storage.boolDecoder 2).map
      (fun values => Aeneas.Std.Array.from (n := 2#usize) values.val values.property)) (3#usize) ⦄

def array_into_bytes_spec : Prop :=
  array_into_bytes_spec_contract trait_checks.check_array_into_bytes

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

def divide_by_unaligned_spec_contract (T : Type) (dictionary : Unaligned T)
    (x : Usize) (run : Result Usize) : Prop :=
  TraitLaws.unaligned T dictionary → run ⦃ result => result = x ⦄

def divide_by_unaligned_spec : Prop :=
  ∀ (T : Type) (dictionary : Unaligned T) (x : Usize),
    divide_by_unaligned_spec_contract T dictionary x
      (trait_checks.divide_by_unaligned dictionary x)

def divide_by_byte_alignment_spec_contract (x : Usize) (run : Result Usize) : Prop :=
  run ⦃ result => result = x ⦄

def divide_by_byte_alignment_spec : Prop :=
  ∀ (x : Usize), divide_by_byte_alignment_spec_contract x
    (trait_checks.divide_by_byte_alignment x)

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

/-- Explicit count-indexed expectation, independent of provider selection. -/
def sliceBytesInitialized (element : Rust.Storage.BitDecoder Raw) : Prop :=
  ∀ (count : Usize) bytes raw,
    (AeneasSpecs.RustModel.sliceStorageDecoder element).run count bytes = some raw →
      Rust.Storage.Initialized bytes

def slice_into_bytes_spec_contract (run : Result Unit) : Prop :=
  run ⦃ _ =>
    sliceBytesInitialized Rust.Storage.boolDecoder ∧
    (∀ raw : Aeneas.Std.Slice Bool, ∃ bytes,
      (AeneasSpecs.RustModel.sliceStorageDecoder Rust.Storage.boolDecoder).run raw.len bytes = some raw) ∧
    sliceBytesInitialized Rust.Storage.unitDecoder ∧
    (∀ (count : Usize) bytes raw,
      ((AeneasSpecs.RustModel.sliceStorageDecoder AeneasSpecs.u8BitDecoder).map
        core.mem.manually_drop.ManuallyDrop.mk
        (fun wrapped => wrapped.value.len) (fun _ => rfl)).run count bytes = some raw →
      Rust.Storage.Initialized bytes) ⦄

def slice_into_bytes_spec : Prop :=
  slice_into_bytes_spec_contract trait_checks.check_slice_into_bytes

end Zerocopy.Obligations
