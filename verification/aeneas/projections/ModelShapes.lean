/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Types
public import ModelPrelude
public import DeriveModels
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs

derive_model_shape Zerocopy.byteorder.Order with 0 type parameters

derive_model_shape Zerocopy.byteorder.BigEndian with 0 type parameters

derive_model_shape Zerocopy.byteorder.LittleEndian with 0 type parameters

derive_model_shape Zerocopy.byteorder.U16 with 1 type parameters

derive_model_shape Zerocopy.byteorder.U32 with 1 type parameters

