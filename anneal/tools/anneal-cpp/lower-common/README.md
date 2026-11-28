<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `anneal-lower-common`

Dependency-free helpers shared by Anneal frontends that render captured
programs as Lean subject terms. `anneal-lower-cpp` uses all three modules.

- `scc::callee_first_sccs`: iterative Tarjan condensation of a call graph,
  ordered callee-first with Kahn's algorithm. Sorting inputs first makes the
  order independent of capture order.
- `chunk::{join_balanced, hoist_list}`: long Lean lists become 16-element leaf
  definitions joined by a balanced `_root_.List.append` tree, so elaboration
  depth stays logarithmic and every definition stays small.
- `digest::{sha256_hex, sha256sum_line}`: FIPS 180-4 SHA-256 for publishing a
  digest next to each emitted file.

The algorithms follow the Rust capture pipeline's sharding and list chunking
(`trusted/rustc-capture`) but do not depend on its IR.
