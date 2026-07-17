<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Current implementation state

**Snapshot date: 2026-07-17.**

This page describes the code checked into `anneal/`. It is a factual snapshot,
not a promise about the final architecture. Inspect the current tree and tests
when a detail matters; update this page when implementation changes make it
stale.

## Status in one sentence

Anneal currently constructs and installs its pinned external toolchain, but it
does not yet discover a Rust compilation subject, generate or check application
proofs, or produce a verification result.

No invocation of the checked-in executable currently proves that an application
is safe or correct.

## Repository boundary

- `anneal/` contains the current clean-room implementation.
- `anneal/v1/` contains the historical prototype and has separate instructions.
- `exocrate/` installs and locates the versioned external toolchain archive.
- `.github/workflows/anneal.yml` contains jobs for both generations; passing a
  V1 job does not establish a V2 capability.

V1 remains useful implementation and design evidence. Its interfaces and
behavior are not defaults for the current implementation.

## Implemented command path

The compiled command currently supports `cargo-anneal setup`, including the
Cargo-plugin spelling `cargo anneal setup`. It selects either a local archive
provided with `--local-archive` or platform metadata from `Cargo.toml`, asks
`exocrate` to install or locate the archive, and reports the installation
directory.

The checked-in remote archive URLs and hashes are placeholders. Development
and CI therefore use a locally constructed archive. `__ANNEAL_LOCAL_DEV`
selects a repository-local development installation; it is not a stable user
interface.

`src/util.rs` contains helpers intended for later orchestration, but it is not
currently part of the compiled production command path. The presence of a
helper or an implementation in an open or sibling branch is not evidence that
the checked-in command exposes that capability.

## Toolchain infrastructure

`flake.nix` pins and packages a coupled Rust, Charon, Aeneas, Lean, Mathlib, and
supporting-tool environment for Linux and macOS on x86-64 and AArch64. It builds
Aeneas's Lean library, vendors Lake dependencies, prunes unused cache material,
normalizes selected paths and timestamps, and produces the omnibus archive used
by setup and CI.

Supporting scripts rewrite vendored Lake metadata, prune the Mathlib closure,
derive coupled upstream versions and hashes, and check that release-relevant
flake outputs evaluate for every declared host system. These are substantial
toolchain and reproducibility capabilities; they are not an application
verification pipeline.

## CI coverage

The V2 CI path builds and layout-checks the omnibus archive, passes that exact
archive to the Rust test job, runs archive-dependent installation and Lake
cache tests, runs support-script tests, and evaluates the flake. Persistent Nix
caches written by pull requests are isolated from the cache populated by
trusted `main` builds.

See [Development and CI](development-and-ci.md) for current commands, fixtures,
and workflow details. That page, the affected manifests, and the workflow files
are the closest sources of truth for validation.

## Verification stages not yet implemented

The checked-in executable does not yet:

- select and identify a Cargo compilation subject;
- invoke Charon or consume LLBC;
- invoke Aeneas or generate a Lean model;
- resolve Anneal specifications or invariants;
- generate and track proof obligations;
- invoke Lean to check an application proof;
- map proof failures back to Rust source;
- compute property dependencies or coverage; or
- emit a scoped result and trust ledger.

The intended high-level flow remains:

```text
Cargo/rustc compilation subject
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
                    scoped result and trust ledger
```

This diagram describes responsibilities, not settled APIs. Annotation
transport, unsafe-memory semantics, the Anneal/Aeneas/Charon boundary, proof
encoding, property representation, and command policy remain open. See the
[open-question index](../design/open-questions/README.md).

## Current reporting and trust gaps

Anneal does not yet produce a compilation-subject manifest, canonical result
identity, proof-coverage report, or audit ledger. It therefore does not yet
report residual trust in Charon, Aeneas, Anneal, Lean, rustc, LLVM, external
semantics, or host and target hardware.

The toolchain archive pins many proof inputs, but the Rust toolchain used to
compile Anneal itself is not yet derived from the archive's pinned Rust
toolchain in CI. Placeholder download metadata also leaves the published
installation path incomplete.

These are implementation limitations, not permission for a future verifier to
omit trust or coverage. The required result semantics live in
[Verification result and trust](../design/result-and-trust.md).

## Using other sources

Open issues and pull requests provide evidence about active work and design
pressure, but they do not describe the capabilities of this checkout. Before
claiming that a stage exists, inspect the checked-in implementation and tests.
Before treating an implementation choice as intended architecture, consult the
normative design documents and accepted decisions.

The dated [current priorities](current-priorities.md) page is non-normative and
may help select near-term work. The [research index](../history/research-index.md)
is a navigation aid for issues and pull requests, not a capability ledger.

## Updating this page

Update this page when behavior lands, not when a pull request opens. Keep:

- implemented facts here;
- commands and CI details in [Development and CI](development-and-ci.md);
- intended guarantees in `docs/design/`;
- unresolved alternatives in `docs/design/open-questions/`; and
- volatile work sequencing in [current priorities](current-priorities.md).
