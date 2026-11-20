<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a formal verification framework for Rust backed by Lean 4. It proves
that Rust programs—including `unsafe` code—are free of undefined behavior (UB)
and satisfy developer-defined specifications, without requiring Rust programmers
to write proofs in Lean 4.

> **Pre-alpha status:** Anneal is under active development. The current
> toolchain supports pinned archive installation via `cargo anneal setup`;
> end-to-end Rust crate verification (`cargo anneal verify`) is not yet exposed
> in the CLI. To keep this book accurate, every command and code example shown
> here is executed against the current `cargo-anneal` build in CI. Rust
> verification guides will be added as each verification capability lands.

## What Anneal promises

Anneal's guarantee rests on an explicit division of labor between automated
verification and bounded human review (see
[Project Principles](foundations/principles.md) and the
[Threat Model](foundations/threat-model.md)):

- **If** verification runs in an uncompromised execution environment (such as an
  isolated CI runner),
- **a reviewer agrees** with the crate's **stated specifications** (what you
  asked Anneal to prove) and its **TCB audit log** (the trusted code and
  unproved assumptions Anneal relied on), and
- **Anneal emits no errors**,
- **then** the verified code is sound (UB-free) and satisfies its stated
  specifications.

Everything outside those two surfaces—proofs, proof automation, and verified
Rust implementation bodies that do not define specifications or TCB
assumptions—can be safely ignored by human reviewers.

## Current CLI surface

Every command transcript in this book is checked directly against the live
`cargo-anneal` binary in CI:

```console
{{#include ../examples/cli/help/transcript.txt}}
```

## Where to go next

- [Installing the Toolchain](getting-started/installation.md) walks through
  `cargo anneal setup` and shows how Anneal fails closed on invalid archives.
- [CLI Reference](reference/cli.md) documents every supported subcommand, flag,
  and diagnostic emitted by the current CLI.
- [Project Principles](foundations/principles.md),
  [Threat Model](foundations/threat-model.md), and
  [Meta-Principles](foundations/meta-principles.md) define Anneal's correctness
  promise and trust boundaries.
- Contributing to Anneal itself? See the internal developer documentation on
  GitHub:
  [Developing Anneal](https://github.com/google/zerocopy/blob/main/anneal/docs/README.md),
  [Design Overview](https://github.com/google/zerocopy/blob/main/anneal/docs/design.md),
  [Architecture](https://github.com/google/zerocopy/blob/main/anneal/docs/architecture.md),
  and
  [Trust Model](https://github.com/google/zerocopy/blob/main/anneal/docs/trust-model.md).
