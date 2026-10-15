/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
import all RustModel
import all ModelPrelude
@[expose] public section

/-!
A physical decoder describes which abstract bytes can produce a Rust value.
The library decoder may impose additional restrictions on that value, but those
restrictions must not weaken IntoBytes: every language-valid representation
must be initialized. These examples pin that separation and the forbidden
outcome of an invalid byte-to-value construction.

These are model tests, not executions of invalid Rust. In particular, they do
not construct an invalid boolean or read uninitialized memory in Rust.
-/
open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace PhysicalModelTests

example : RustModel.initializedRepresentation Bool := boolDecoder_initialized
example : RustModel.initializedRepresentation Unit := unitDecoder_initialized
example : RustModel.initializedRepresentation U8 :=
  initializedUScalar .U8

-- One proof covers every supported width and signedness. It does not assume
-- that an integer's alignment equals its byte size.
example (ty : UScalarTy) : RustModel.initializedRepresentation (UScalar ty) :=
  initializedUScalar ty
example (ty : IScalarTy) : RustModel.initializedRepresentation (IScalar ty) :=
  initializedIScalar ty

example : (modelUScalar .U16).decodeBitsResult [AMByte.init 0x34, AMByte.init 0x12] =
    .ok (0x1234#u16) := rfl
example : (modelIScalar .I16).decodeBitsResult [AMByte.init 255, AMByte.init 255] =
    .ok ((-1)#i16) := rfl
example : (modelChar).decodeBitsResult [AMByte.init 65, AMByte.init 0,
    AMByte.init 0, AMByte.init 0] = .ok 'A' := rfl
example : (modelChar).decodeBitsResult [AMByte.init 0, AMByte.init 0xd8,
    AMByte.init 0, AMByte.init 0] = .fail .undef := rfl

-- Zero is not a NonZero value, but it is the valid None representation of
-- Option<NonZero>. Failure to collect initialized bytes never becomes None.
example : (modelNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner).decodeBitsResult
    [AMByte.init 0] = .fail .undef := rfl
example : (modelOptionNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner).decodeBitsResult
    [AMByte.init 0] = .ok none := rfl
example : (modelOptionNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner).decodeBitsResult
    [AMByte.uninit] = .fail .undef := rfl
example : (modelOptionNonZeroIScalar .I8 core.num.niche_types.NonZeroI8Inner).decodeBitsResult
    [AMByte.init 255] = .ok (some ⟨(-1)#i8⟩) := rfl

-- Missing physical semantics cannot establish a trait law by vacuity.
example : ¬ RustModel.initializedRepresentation Nat := by
  simp [RustModel.initializedRepresentation, RustModel.storage]

-- This intentionally bad physical decoder accepts an uninitialized byte.
-- Rejecting all library values cannot turn it into an IntoBytes interpretation.
def acceptsUninit : BitDecoder Nat where
  byteSize := 1
  decode _ := some 0

@[reducible] def rejectsEverything : RustModel Nat where
  Model := Unit
  decode _ := none
  storage := some (.fixed acceptsUninit)

example : ¬ @RustModel.initializedRepresentation Nat rejectsEverything := by
  intro law
  have forbidden := law [AMByte.uninit] 0 rfl
  simp [Initialized] at forbidden

example : (modelBool).decodeBitsResult [AMByte.uninit] = .fail .undef := rfl
example : (modelBool).decodeBitsResult [AMByte.init 2] = .fail .undef := rfl
example : (modelBool).decodeBitsResult [] = .fail .undef := rfl
example : (modelBool).decodeBytesResult [AMByte.init 1] = .ok true := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.storage, PhysicalStorage.fixed?, RustModel.decode, BitDecoder.run, boolDecoder]
example : (modelUScalar .U8).decodeBytesResult [AMByte.init 255] =
    .ok (unsignedWord (255#u8)) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.storage, PhysicalStorage.fixed?, RustModel.decode,
    uScalarBitDecoder, Rust.Storage.AeneasAdapter.unsignedDecoder,
    BitDecoder.map, BitDecoder.run, integerDecoder, collectInitialized,
    Rust.Bytes.decode, Rust.Bytes.decodeLE, UScalar.ofNatCore]

-- Both correctness judgments reject forbidden construction, even when the
-- written postcondition makes no promise about the returned value.
example : ¬ WP.spec (modelBool.decodeBytesResult [AMByte.init 2]) (fun _ => True) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.storage, PhysicalStorage.fixed?, RustModel.decode, BitDecoder.run, boolDecoder]
example : ¬ WP.dspec (modelBool.decodeBytesResult [AMByte.uninit]) (fun _ => True) := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult,
    RustModel.decodeResult, RustModel.representation, RustModel.storage, PhysicalStorage.fixed?, RustModel.decode, BitDecoder.run, boolDecoder]

-- An element-count recursion, rather than division by byte width, handles
-- empty arrays, zero-sized elements, and nested arrays with the same rule.
example : RustModel.initializedRepresentation (Aeneas.Std.Array Bool (0#usize)) :=
  RustModel.initialized_array _ _ boolDecoder_initialized
example : RustModel.initializedRepresentation (Aeneas.Std.Array Unit (4#usize)) :=
  RustModel.initialized_array _ _ unitDecoder_initialized
example : RustModel.initializedRepresentation
    (Aeneas.Std.Array (Aeneas.Std.Array Bool (2#usize)) (3#usize)) :=
  RustModel.initialized_array _ _ (RustModel.initialized_array _ _ boolDecoder_initialized)

end PhysicalModelTests
