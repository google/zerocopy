<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal agent guide

Before working on the current Anneal redesign, read and preserve the project
principles in [`PRINCIPLES.md`](PRINCIPLES.md) and the shared design contract in
[`DESIGN.md`](DESIGN.md). The principles are authoritative if the two conflict.

Determine current implementation behavior from the checked-in source. The
[`v1/`](v1/) subtree is the historical V1 prototype: use it as historical
evidence rather than current design authority. When changing files under
`v1/`, also follow the more specific [`v1/AGENTS.md`](v1/AGENTS.md).
