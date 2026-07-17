<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# V2 Development and CI

Run V2 commands from `anneal/` or pass `--manifest-path anneal/Cargo.toml`
from the repository root. Commands rooted at `anneal/v1/` operate on the V1
prototype.

This page records the current workflow. It is not a stable CLI specification.

## Fast local checks

From the repository root:

```bash
cargo test --locked --manifest-path anneal/Cargo.toml
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s anneal/tests -p 'test_*.py'
cargo fmt --manifest-path anneal/Cargo.toml --all -- --check
```

The repository-wide formatting entry point is:

```bash
./ci/check_fmt.sh
```

That script intentionally formats V2, V1, `exocrate`, the workspace tools,
and Zerocopy. Use the narrower Cargo command while iterating on a V2-only
change; use the repository entry point before handing off a broad change.

## Running setup locally

The checked-in remote archive metadata is placeholder data. Exercise setup
with an archive built locally:

```bash
mkdir -p anneal/target
nix build ./anneal#omnibus-archive-ci \
  --out-link anneal/target/anneal-exocrate.tar.zst
cargo run --manifest-path anneal/Cargo.toml -- \
  setup --local-archive anneal/target/anneal-exocrate.tar.zst
```

The archive argument is interpreted from the command's current directory.
When developing inside `anneal/`, use
`target/anneal-exocrate.tar.zst` instead.

`__ANNEAL_LOCAL_DEV=1` selects the local-development installation location.
It is an internal switch and may change.

## Archive-dependent Rust tests

Tests behind the `exocrate_tests` feature expect this exact path relative to
`anneal/`:

```text
target/anneal-exocrate.tar.zst
```

After building the archive, run:

```bash
cargo test --locked --manifest-path anneal/Cargo.toml --all-features
```

These tests install the archive and build a small generated Lean workspace to
ensure the read-only, precompiled Lake cache can be reused. A missing archive
is a test-fixture failure, not evidence about Anneal's proof design.

## Nix checks

Evaluate every release-relevant flake package for every supported system:

```bash
bash anneal/check-flake-eval.sh
```

Build and validate the archive for the current system:

```bash
nix build ./anneal#omnibus-archive-ci
nix build ./anneal#omnibus-archive-layout-check --no-link
```

Evaluation across four systems is not a cross-platform build. CI's archive
builder builds for its current runner and separately checks that the package
graph evaluates for all declared systems.

When rolling Aeneas, Rust, or Lean inputs, use
`anneal/chase-aeneas-versions.sh` as an aid. It downloads upstream artifacts
and computes coupled hashes. Review every resulting version and hash; Mathlib
cache output may require a subsequent fixed-output hash refresh.

## CI topology

`.github/workflows/anneal.yml` contains both generations:

- `static_checks` runs V1 and V2 support-script tests and the V2 flake
  evaluation check.
- `anneal_tests` and `verify_examples` are V1 jobs rooted at `anneal/v1/`.
- `v2_nix_cache` builds the V2 omnibus archive, checks its layout, and uploads
  it for this workflow run.
- `v2` downloads that exact archive and runs
  `cargo test --workspace --all-features` in `anneal/`.

The Nix caches have a trust boundary. A cache saved by a trusted `main` build
may be reused by pull requests; a pull request writes only its PR-scoped
cache. Preserve that separation when changing cache keys or Actions steps.
The workflow artifact, not the persistent cache, is the cross-job handoff for
the current run.

The release workflow currently publishes the V1 crate from `anneal/v1/` while
using V2's Nix flake to build omnibus toolchain archives. This mixed state is
intentional during the transition. Do not "simplify" paths without first
understanding which generation owns the crate and which owns the archive.

## Platform-specific concerns

- The flake declares Linux and macOS on x86-64 and AArch64.
- Linux builds use an FHS environment for downloaded Lean tooling.
- Ubuntu 24.04 CI temporarily adjusts an AppArmor user-namespace setting for
  the sandboxed Nix build and restores it in an `always()` step. Preserve the
  cleanup path.
- Lake metadata and trace files can contain build-machine absolute paths.
  Archive construction deliberately rewrites them and makes the installed
  Aeneas tree read-only.
- Archive size is checked against GitHub's release-asset limit.

## Scope discipline

Open stacked PRs contain scanner, Cargo resolution, Charon, generation, and
diagnostic work. When developing on a branch below those changes, use the
files actually present in the checkout as the source of truth. Do not add
tests or documentation for an API which only exists in another stack unless
the change explicitly depends on that stack.

When a V2 change touches shared CI or release machinery, also run the relevant
V1 support tests. Otherwise, V1's large integration suite is not the default
validation target for V2 implementation work.
