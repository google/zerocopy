/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Lake
open Lake DSL

package rust_model

-- Normal consumers build the mathematical library. It needs only Lean's
-- standard library; frontend or Aeneas dependencies belong in the consumer.
@[default_target]
lean_lib Rust

-- Tests are explicit targets, so importing `Rust` does not run test commands.
-- Package validation builds the library and all four test targets below, then
-- reruns the `RustTests.lean` axiom audit when cached output might be reused.
lean_lib RustTests where
  roots := #[`RustTests]

lean_lib RustBytesTests where
  roots := #[`RustBytesTests]

lean_lib RustStorageTests where
  roots := #[`RustStorageTests]

lean_lib RustPointerTests where
  roots := #[`RustPointerTests]
