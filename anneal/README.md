<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal V2

Anneal is an experimental Rust verification tool built around Charon, Aeneas,
and Lean. Its long-term goal is to support arbitrarily subtle correctness
properties across arbitrary Rust codebases, including the memory-safety
arguments required to make unsafe implementations sound.

This directory contains Anneal V2. V2 is a clean-room, ground-up rewrite and
redesign: it may reuse code or ideas from V1 after reconsidering them, but no V1
interface or architecture is inherited by default. The V1 prototype and its
documentation live in [`v1/`](v1/README.md).

## Status

V2 is under active construction and is not yet a production verifier. The
checked-in executable currently implements toolchain installation through the
`setup` command. The source translation, proof generation, and verification
pipeline described in the design documents is intended architecture rather
than current functionality unless the
[current architecture reference](docs/reference/current-architecture.md) says
otherwise.

The crate metadata still contains placeholder remote archive URLs. Local
development can supply a Nix-built archive explicitly:

```bash
mkdir -p anneal/target
nix build ./anneal#omnibus-archive-ci \
  --out-link anneal/target/anneal-exocrate.tar.zst
cargo run --manifest-path anneal/Cargo.toml -- \
  setup --local-archive anneal/target/anneal-exocrate.tar.zst
```

## Project direction

Anneal is intended to combine two styles of reasoning:

- Aeneas exposes a large, disciplined subset of Rust as a comparatively simple
  functional model.
- Unsafe code and other effects may require ownership, provenance,
  initialization, protocol, or separation-logic resources.

The aim is not to force all of Rust into either model. Anneal should retain the
simplicity of pure reasoning wherever faithful, while preserving richer
resource semantics wherever simplifying them could undermine soundness.
Soundness is non-negotiable; other property domains are extensible and may
depend on soundness or on one another.

Start with the [documentation map](docs/README.md), the
[design principles](docs/design/principles.md), and the
[settled requirements](docs/design/settled-requirements.md).
Agents entering from an unfamiliar checkout should also use the
[agent-corpus preflight](docs/agent-corpus.md).

## Development

From the repository root:

```bash
cargo test --locked --manifest-path anneal/Cargo.toml
cargo fmt --check --manifest-path anneal/Cargo.toml --all
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s anneal/tests -p 'test_*.py'
bash anneal/check-flake-eval.sh
```

The `exocrate_tests` feature assumes that CI has downloaded the prebuilt
toolchain archive to `anneal/target/anneal-exocrate.tar.zst`.

See [V2 development and CI](docs/reference/development-and-ci.md) for the full
current workflow and archive-dependent checks.

Contributors and agents developing V2 should read [`AGENTS.md`](AGENTS.md).
