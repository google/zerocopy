<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Current V2 Architecture

This document describes the code checked into `anneal/` as of 2026-07-17. It
is a reference for what exists, not a promise that the current structure is the
final design. The intended verification architecture is described separately
in [the verification model](../design/verification-model.md).

## Status in one sentence

V2 currently implements toolchain construction, installation, and supporting
cache/archive utilities; it does **not** yet implement Rust discovery, Charon
extraction, Aeneas translation, specification generation, or verification.

Several open, stacked pull requests implement or experiment with later stages.
Open status alone does not say whether a change is present in this checkout:
GHerrit stack ancestors and the current branch may themselves have open PRs.
Inspect the files and history in this checkout before describing a capability;
an open PR's proposed architecture is not authoritative merely because the PR
exists. See the dated [research index](../history/research-index.md).

## Repository boundary

- `anneal/` is Anneal V2 and is the default subject of V2 documentation.
- `anneal/v1/` is the historical V1 prototype. It remains buildable and has
  its own documentation, but it is not an implementation library for V2.
- `exocrate/` is a repository-local crate used to install and locate a
  versioned external toolchain archive.
- `.github/workflows/anneal.yml` runs both V1 and V2 jobs. Job names and
  working directories must be read carefully.

V2 is a clean-room redesign. Moving V1 under `anneal/v1/` made the boundary
visible in the filesystem: a V1 implementation choice does not become a V2
default merely because code for it is nearby.

## Implemented runtime path

The production path in `src/main.rs` is deliberately small:

1. Parse `cargo-anneal setup` (or the Cargo-plugin spelling
   `cargo anneal setup`).
2. Choose a local archive when `--local-archive` is supplied; otherwise choose
   the platform-specific archive described by Cargo package metadata.
3. Ask `exocrate` to resolve an already installed toolchain or install the
   selected archive into a versioned location.
4. Log the resolved installation directory.

`__ANNEAL_LOCAL_DEV` changes the installation location from the normal
user-global location to a repository-local development location. It is an
internal development switch, not a stable user interface.

At present, the remote archive entries in `Cargo.toml` are placeholders. The
CI path supplies a locally built archive explicitly. Consequently, the
checked-in binary is useful for exercising local setup but is not yet a
production remote installer.

`src/util.rs` contains directory-locking, child-process, and test helpers. On
this revision it is not declared by `main.rs`, so it is not part of the
compiled production command path. Open stacked changes build on it; do not
describe those uses as landed behavior.

## Toolchain construction

`flake.nix` constructs a version-pinned toolchain for four host systems:

- `x86_64-linux`
- `aarch64-linux`
- `x86_64-darwin`
- `aarch64-darwin`

The flake fetches or constructs:

- an Aeneas release archive, which also supplies the Charon executable used
  by that release;
- the Rust toolchain expected by that Charon build;
- the Lean toolchain expected by Aeneas;
- Aeneas's Lean dependencies, including the relevant Mathlib sources and
  compiled artifacts; and
- the native `leantar` utility used to unpack Lean caches.

It rewrites Lake dependencies to local vendored paths, compiles Aeneas's Lean
library, prunes unused material, normalizes selected timestamps and paths, and
packages the result as a compressed omnibus archive. Important flake outputs
include `aeneas-compiled`, `omnibus-tar`, `omnibus-archive`,
`omnibus-archive-ci`, and `omnibus-archive-layout-check`.

The supporting scripts have narrow roles:

- `rewrite-lake-vendor.py` converts Lake dependencies and manifests to local
  paths and can remove build-machine prefixes from trace files.
- `prune-lake-cache.py` computes the reachable Mathlib module closure and
  removes unused sources, build products, and package metadata.
- `chase-aeneas-versions.sh` derives coupled Rust and Lean versions and hashes
  from an Aeneas release.
- `check-flake-eval.sh` evaluates the release-relevant package graph for all
  four supported systems without claiming to build all four systems locally.

The archive is infrastructure for the future verifier. Its existence does not
mean that the current V2 executable invokes Charon, Aeneas, Lake, or Lean.

## CI path

The V2 CI path has two main jobs:

1. `v2_nix_cache` builds and layout-checks `omnibus-archive-ci`, manages
   separately scoped Nix caches for trusted `main` builds and pull requests,
   and uploads the exact archive as a workflow artifact.
2. `v2` downloads that archive and runs `cargo test --workspace
   --all-features` from `anneal/`.

The `exocrate_tests` feature makes the Rust tests consume
`target/anneal-exocrate.tar.zst`. Those tests check installation and check that
a fresh generated Lake workspace can use the read-only, precompiled archive
without rebuilding its dependencies.

Static CI also runs the Python utility tests and evaluates the V2 flake. The
same workflow contains V1 verification jobs rooted at `anneal/v1/`; passing a
V1 job says nothing about whether a feature exists in V2.

## Intended, not yet implemented, pipeline

The design direction is an orchestration pipeline broadly shaped like this:

```text
Cargo/rustc compilation artifact
            |
            v
      Charon extraction  -->  LLBC
            |                  |
            |                  v
            |          Aeneas Lean model
            |                  |
            +--------> Anneal contracts and obligations
                               |
                               v
                         Lean verification
                               |
                               v
                       result and trust ledger
```

This diagram expresses responsibilities, not a settled component API. In
particular, annotation transport, the exact Anneal/Aeneas boundary, unsafe
memory semantics, and the shape of proof obligations remain open. See
[Aeneas and Charon](aeneas-and-charon.md) and the
[open design questions](../design/open-questions/README.md).

## Updating this reference

Update this file when a stage lands on the branch, not when a PR is opened.
When implementation and desired architecture differ, describe the
implementation here and the desired behavior in `docs/design/`. Never make an
open PR authoritative by copying its claims into this file without checking
the merged code.

For current build, test, setup, and CI commands, see
[V2 development and CI](development-and-ci.md). For the explicitly
non-normative near-term optimization lens, see
[current priorities](current-priorities.md).
