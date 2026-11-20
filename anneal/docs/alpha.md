<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR verifier alpha

The developer alpha checks one selected Rust function on x86-64 Linux. It
compiles a dependency-free library with the pinned compiler and checks the
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
