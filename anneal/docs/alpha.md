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

Before the first publication, create the GitHub environment `anneal-release`
with required reviewers and a deployment branch rule allowing only `main`.
In the crates.io settings for `cargo-anneal`, add a
trusted publisher for `google/zerocopy`, workflow `release.yml`, and
environment `anneal-release`.
Verify that the `zerocopy` and `zerocopy-derive` registrations for
`release.yml` explicitly require their `release` environment. These
environment bindings keep credentials scoped to each publication job.
See [crates.io Trusted Publishing](https://crates.io/docs/trusted-publishing).

1. Run **Release** on `main`. Select `anneal`, enter the
   desired alpha version, and keep the target branch set to `main`. The
   workflow prepares that version, builds and hosts its Linux toolchain
   archive, and opens one PR with the version and archive digest.
2. Review the source commit and digest on the toolchain release, then merge
   the PR. A push to `main` that introduces a pinned release starts
   qualification on Ubuntu 24.04. The job checks archive provenance and
   environment protections, then installs the packaged crate and runs the
   scalar checks with the downloaded archive.
3. After qualification succeeds, approve the `anneal-release` deployment to
   publish `cargo-anneal` to crates.io. The workflow then tags the published
   source as `anneal-v<version>` and creates a GitHub prerelease with release
   notes and a link to the toolchain archive.

Rerun preparation to recover the PR for a published archive whose build
inputs still match. Recovery trusts the repository's release writers to
preserve the tag and asset provenance. If qualification or GitHub release
publication fails, rerun the failed jobs on the push that merged the release
PR.
