/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import TraitLawsSupport
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.TraitLaws

trait_dictionary @Zerocopy.core.num.nonzero.ZeroablePrimitive
trait_dictionary @Zerocopy.byteorder.private.Sealed
trait_dictionary @Zerocopy.byteorder.ByteOrder
trait_dictionary @Zerocopy.trait_checks.ByteCodec
trait_invariant byte_roundtrip for @Zerocopy.trait_checks.ByteCodec with 1 type parameters where self =>
  ∀ byte, (do let encoded ← self.encode byte; self.decode encoded)
      ⦃ result => result = byte ⦄

end Zerocopy.TraitLaws
