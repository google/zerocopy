/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public import Rust.Storage
@[expose] public section

/-!
The shared integer decoder retains the complete bit pattern. Aeneas's unsigned
and signed scalar carriers store that same bit vector, so these adapters change
the carrier without testing or discarding any initialized pattern. Signed
interpretation is supplied by Aeneas's two's-complement scalar observation.

The byte order remains an argument. Connecting it and the machine-word width
to a Rust extraction is the consumer's target-specific responsibility; these
definitions do not establish a Rust ABI merely by constructing a Lean value.
-/

open Aeneas.Std
namespace Rust.Storage.AeneasAdapter

/-- Aeneas currently supports 32- and 64-bit machine words. Both have a whole
number of bytes, as do its fixed-width integer carriers. -/
theorem unsigned_byte_width (ty : UScalarTy) : 8 * (ty.numBits / 8) = ty.numBits := by
  cases ty <;> simp [UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp_all

theorem signed_byte_width (ty : IScalarTy) : 8 * (ty.numBits / 8) = ty.numBits := by
  cases ty <;> simp [IScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp_all

def unsignedDecoder (ty : UScalarTy) (endian : Rust.Bytes.Endian) : BitDecoder (UScalar ty) :=
  (integerDecoder (ty.numBits / 8) endian).map fun word =>
    ⟨word.cast (unsigned_byte_width ty)⟩

def signedDecoder (ty : IScalarTy) (endian : Rust.Bytes.Endian) : BitDecoder (IScalar ty) :=
  (integerDecoder (ty.numBits / 8) endian).map fun word =>
    ⟨word.cast (signed_byte_width ty)⟩

theorem unsignedDecoder_initialized (ty : UScalarTy) (endian : Rust.Bytes.Endian) :
    (unsignedDecoder ty endian).Initialized :=
  BitDecoder.map_initialized _ _ (integerDecoder_initialized _ _)

theorem signedDecoder_initialized (ty : IScalarTy) (endian : Rust.Bytes.Endian) :
    (signedDecoder ty endian).Initialized :=
  BitDecoder.map_initialized _ _ (integerDecoder_initialized _ _)

end Rust.Storage.AeneasAdapter
