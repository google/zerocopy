/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelShapes
public import DeriveModels
public import ModelSupport
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs

derive_rust_model Zerocopy.byteorder.Order with 0 type parameters
check_model_binding Zerocopy.byteorder.Order with 0 type parameters

derive_rust_model Zerocopy.byteorder.BigEndian with 0 type parameters
check_model_binding Zerocopy.byteorder.BigEndian with 0 type parameters

derive_rust_model Zerocopy.byteorder.LittleEndian with 0 type parameters
check_model_binding Zerocopy.byteorder.LittleEndian with 0 type parameters

derive_rust_model Zerocopy.byteorder.U16 with 1 type parameters
check_model_binding Zerocopy.byteorder.U16 with 1 type parameters

derive_rust_model Zerocopy.byteorder.U32 with 1 type parameters
check_model_binding Zerocopy.byteorder.U32 with 1 type parameters

derive_rust_model Zerocopy.layout.RoundingAlignAndPhase with 0 type parameters decode self =>
  let word := self._0.value
  let align := 2 ^ Nat.log2 word
  { align := align, phase := word - align, .. }
check_model_binding Zerocopy.layout.RoundingAlignAndPhase with 0 type parameters

derive_rust_model Zerocopy.layout.nested_reference.NestedLayer with 0 type parameters
check_model_binding Zerocopy.layout.nested_reference.NestedLayer with 0 type parameters

