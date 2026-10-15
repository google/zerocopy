/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import TraitLawsSupport
public import ReferentValidity
public import LayoutModel
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.TraitLaws

trait_dictionary @Zerocopy.core.num.nonzero.ZeroablePrimitive
trait_dictionary @Zerocopy.byteorder.private.Sealed
trait_dictionary @Zerocopy.byteorder.ByteOrder
trait_dictionary @Zerocopy.pointer.invariant.sealed.Sealed
trait_dictionary @Zerocopy.pointer.invariant.Aliasing
trait_dictionary @Zerocopy.pointer.invariant.Read
trait_dictionary @Zerocopy.pointer.invariant.Reference
trait_dictionary @Zerocopy.pointer.invariant.Alignment
trait_dictionary @Zerocopy.TryFromBytes
trait_dictionary @Zerocopy.FromZeros
trait_dictionary @Zerocopy.FromBytes
trait_dictionary @Zerocopy.IntoBytes
trait_dictionary @Zerocopy.Unaligned
trait_dictionary @Zerocopy.pointer.invariant.Validity
trait_dictionary @Zerocopy.pointer.invariant.CastableFrom
trait_dictionary @Zerocopy.pointer.transmute.TransmuteFrom
trait_dictionary @Zerocopy.trait_checks.ByteCodec
trait_dictionary @Zerocopy.util.macro_util.transmute_copy.StaticAssert
trait_invariant from_zeros_valid for @Zerocopy.FromZeros with 1 type parameters where self =>
  AeneasSpecs.RustModel.zeroRepresentation Self

trait_invariant transmute_from for @Zerocopy.pointer.transmute.TransmuteFrom with 4 type parameters where self =>
  Referent.transmuteFrom Src Self SV DV

trait_invariant castable_from for @Zerocopy.pointer.invariant.CastableFrom with 4 type parameters where self =>
  Referent.typeIndependentPair SV DV

trait_invariant into_bytes_initialized for @Zerocopy.IntoBytes with 1 type parameters where self =>
  AeneasSpecs.RustModel.initializedRepresentation Self ∧
    AeneasSpecs.RustModel.realizableRepresentation Self

trait_invariant from_bytes_valid for @Zerocopy.FromBytes with 1 type parameters where self =>
  AeneasSpecs.RustModel.completeRepresentation Self

trait_invariant validity_kind for @Zerocopy.pointer.invariant.Validity with 1 type parameters where self =>
  Referent.kindMatches Self self.KIND

trait_invariant unaligned for @Zerocopy.Unaligned with 1 type parameters where self =>
  Zerocopy.RustLayout.align Self = 1#usize

trait_invariant byte_roundtrip for @Zerocopy.trait_checks.ByteCodec with 1 type parameters where self =>
  ∀ byte, (do let encoded ← self.encode byte; self.decode encoded)
      ⦃ result => result = byte ⦄

end Zerocopy.TraitLaws
