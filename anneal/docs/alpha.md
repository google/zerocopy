<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR verifier alpha

The developer alpha checks one selected Rust function on x86-64 Linux with
glibc, such as Ubuntu 24.04. It compiles a dependency-free library with the
pinned compiler and checks the
authored Lean proof against the captured MIR, the stated specification, and
Anneal's safety obligations. A successful receipt identifies the selected
function, compilation configuration, input digests, and assumptions.

Use Rust inputs, specifications, and proofs you trust to compile and
elaborate on your machine. Lean elaboration runs as your user. To use the
alpha in automation that processes outside contributions, supply a separate
isolated execution environment for the entire verifier.

## Try a proof

From the Zerocopy checkout, build and install the pinned tools with Nix.
Keep the same installation cache for setup and verification.

```sh
cd anneal
mkdir -p target
nix build .#omnibus-archive --max-jobs 1 --cores 2 --out-link target/omnibus-link
export XDG_CACHE_HOME="$(mktemp -d)"
cargo run --locked -p cargo-anneal -- setup --local-archive target/omnibus-link
cargo run --locked -p cargo-anneal -- verify \
  --request trusted/cargo-anneal/tests/fixtures/scalar/request.json
```

The example proves that `zero()` returns zero. To experiment, make a copy of
the fixture directory and change its Rust function to return one. The same
proof then fails. `--artifacts <new-directory>` retains the captured Lean
program, bound claim, and diagnostic evidence for proof development.

Request roots are relative to the physical directory containing the request
file. Each root must stay inside that directory, and inputs must be declared
regular files under their roots. The request chooses one function and
supplies the paths and roles of its Lean sources.

The alpha uses the x86-64 Linux scalar MIR profile. Calls, pointer accesses,
external dependencies, and whole-crate requests are outside the alpha's
scope. An unsupported input returns an explicit refusal. Verify the stated
configuration when comparing a result with a deployed binary. See the
[threat model](../THREAT_MODEL.md) for the verification assumptions.

## Install a published alpha

```sh
cargo install --locked cargo-anneal@0.2.0-alpha.1
cargo anneal setup
cargo anneal verify --request /path/to/scalar/request.json
```

To install the alpha alongside an earlier version of `cargo-anneal`, use
`cargo install --root <directory>` and invoke
`<directory>/bin/cargo-anneal` directly.

## Cut the release

After the alpha stack lands, run the **Release** workflow on `main` with
version `0.2.0-alpha.1` and track `mir-prepare`. It builds and hosts the
Linux archive, then opens a PR to pin its digest in the CLI.
Review the source commit and digest on the toolchain release before merging
that PR. You can repeat preparation to recover the PR for an existing
archive when the archive-producing inputs still match. Recovery trusts
the repository's release writers to preserve the tag and asset provenance.

Before the first publication, create the GitHub environment
`anneal-mir-release` with required reviewers and a deployment branch rule
allowing only `main`. In the crates.io settings for `cargo-anneal`, add a
trusted publisher for `google/zerocopy`, workflow `release.yml`, and
environment `anneal-mir-release`.
Verify that the `zerocopy` and `zerocopy-derive` registrations for
`release.yml` explicitly require their `release` environment. These
environment bindings keep credentials scoped to each publication job.
See [crates.io Trusted Publishing](https://crates.io/docs/trusted-publishing).

Run the workflow again with track `mir-publish` after the pin lands. A fresh
runner checks the environment protections, installs the packaged crate
outside the checkout, downloads the pinned archive, and runs the scalar
checks. The publisher can run after qualification and environment approval.
