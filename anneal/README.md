<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a verification framework for Rust under active development.

## Repository layout

The current verifier builds from this directory. The independent workspaces
in [`v1/`](v1/) and [`v2/`](v2/) retain the earlier implementations
and the Aeneas toolchain used by V1.

Zerocopy's [Anneal workflow](../.github/workflows/anneal.yml) calls the
[current verifier checks](../.github/workflows/anneal-current.yml). The
standalone release and review workflows under this directory are retained
for reference. This integration enables CI for the current verifier.
The existing V1 workflow continues to own publication.
