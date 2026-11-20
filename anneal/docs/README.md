<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Developing Anneal

The current MIR-based implementation lives at [`anneal/`](../). See the
[repository layout](architecture.md#repository-layout) for the current
workspace and the roles of V1 and V2.

## Build and test the current toolchain

On Linux with Cargo and Nix flakes enabled, run these commands from the
Zerocopy checkout. The archive bundles the pinned Rust and Lean toolchains,
the compiler driver, and Anneal's Lean sources.

```sh
cd anneal
mkdir -p target
nix build .#omnibus-archive --out-link target/omnibus-link
XDG_CACHE_HOME="$(mktemp -d)" \
  cargo run --locked -p cargo-anneal -- setup --local-archive target/omnibus-link
```

The command uses a fresh cache because setup reuses an existing installation
for the same version key.

To audit the checkout, use the `lean/bin/lean` under the installation path
printed by setup. The full MIR correspondence audit uses Linux bubblewrap
at `/usr/bin/bwrap`.

```sh
cargo run --locked -p anneal-audit -- \
  --lean /path/to/installed/lean/bin/lean --require-correspondence
```

## CI, releases, and review

- Zerocopy's [Anneal Tests workflow](../../.github/workflows/anneal.yml)
  calls the [current verifier checks](../../.github/workflows/anneal-current.yml).
  The current checks build and install the archive, audit the trust boundary,
  and test the Rust workspace.
- The [Anneal release workflow](../../.github/workflows/anneal-release.yml)
  publishes V1. The current verifier's former standalone release and review
  workflows live under [`anneal/.github/`](../.github) for reference.
- The [Codex review guide](codex-review.md) describes review gates and the
  standalone diagnostic evaluator.

## Design and maintenance

- [Project principles](../PRINCIPLES.md), [threat model](../THREAT_MODEL.md),
  and [meta-principles](../META_PRINCIPLES.md) define the promise to users,
  the assumptions and review responsibilities, and the goals that govern
  both documents.
- [Design overview](design.md) explains the intended verification workflow,
  specification forms, and incremental adoption.
- [Architecture](architecture.md) covers the MIR pipeline, repository
  layout, and compiler integration.
- [Trust model and boundary enforcement](trust-model.md) explains the
  `trusted/` boundary, dependency pins, and repository audits.
- [MIR correspondence design](mir-correspondence-design.md) and
  [strategy](mir-correspondence-strategy.md) describe how Anneal relates its
  operational semantics to the pinned reference model.
- [Agent instructions](../AGENTS.md) and the
  [review policy design](review-policy-design.md) describe contributor
  obligations and where the review rules belong.
