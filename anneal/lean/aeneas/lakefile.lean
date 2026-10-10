/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Lake
open Lake DSL

require rust_model from ".."
require aeneas from ((get_config? aeneasPath).getD "../../aeneas/backends/lean")

package rust_model_aeneas

@[default_target]
lean_lib RustAeneas

lean_lib RustAeneasTests
