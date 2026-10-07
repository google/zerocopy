/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust.Layout
import Rust.Memory
import Rust.Bytes

/-!
The public entry point for the shared mathematical library. Consumers can import
`Rust` for layout, byte-order, and memory-geometry definitions, or import the
individual modules when they need fewer dependencies. These imports introduce
no assumptions about the Rust compiler, pointer validity, or a frontend's
translation. A consumer supplies those connections in its own verification.
-/
