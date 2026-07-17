<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Current V2 Limitations

This is a dated description of the checked-in implementation as of
2026-07-17. It prevents plans, open pull requests, and V1 behavior from being
mistaken for V2 capabilities.

## There is not yet a verifier

The only user-facing V2 subcommand is `setup`. V2 cannot currently:

- select a Cargo verification target;
- run Charon or read LLBC;
- run Aeneas or generate a Lean model;
- parse or resolve Anneal annotations;
- generate contracts, safety guards, type invariants, or trait invariants;
- invoke Lean to check an application proof;
- map proof diagnostics back to Rust;
- compute property dependencies; or
- emit a verification result or trust ledger.

Accordingly, no invocation of the checked-in V2 binary presently entitles a
user to a soundness, panic-freedom, termination, or functional-correctness
claim. V1 implements an experimental verification pipeline under
`anneal/v1/`; it is not an implicit fallback for V2.

## Setup requires a local archive in practice

The platform archive URLs and hashes in V2's `Cargo.toml` are placeholders.
CI builds `omnibus-archive-ci` with Nix and passes the resulting archive via
`--local-archive`. Remote installation with the checked-in defaults is not a
production path.

The `--all-features` Rust tests likewise require
`anneal/target/anneal-exocrate.tar.zst`, normally supplied by the CI archive
job. Basic source tests and Python utility tests do not establish that a
fresh archive can be produced or installed.

## The toolchain is more mature than the orchestrator

The Nix flake pins and assembles Rust, Lean, Aeneas, Charon, Mathlib artifacts,
and related tools. It performs substantial cache portability and size work.
That infrastructure should not be confused with end-to-end semantic
integration. The checked-in command path does not use the installed Charon,
Aeneas, or Lean executables after setup.

`src/util.rs` contains helpers intended for later orchestration but is not
currently wired into the compiled binary. Its presence is not evidence that a
generation or verification command exists.

## Reproducibility and trust reporting are incomplete

- V2 CI currently installs the latest nightly Rust to compile the Anneal
  crate, while the archive contains a separately pinned Rust toolchain. The
  workflow has a FIXME to align or derive these versions.
- Archive construction checks layout and selected cache-reuse behavior, but
  V2 has no user-facing compilation-subject manifest, verification-result
  record, or TCB audit ledger.
- Host hardware, target hardware, compiler, LLVM, and proof-tool assumptions
  are not reported to users.
- Placeholder remote metadata means the published-crate installation story is
  not complete.

## The semantic architecture remains open

V2 has not selected final designs for:

- proof arguments versus sidecar theorems for safety guards;
- outcome and property-kind representation;
- combined versus separated progress/correctness reasoning;
- the model of unsafe memory, provenance, layout, and initialization;
- preservation of resource semantics in the Lean model;
- the boundary between Anneal-owned and Aeneas-owned semantics;
- annotation and proof syntax;
- integration with Rust's `unsafe` machinery versus a parallel property
  system;
- enforcement and consumption of type and trait invariants;
- incremental-adoption command modes and the status of incomplete proofs;
- the exact role and permitted authors of axioms; and
- the schema and success policy of the trust ledger.

Constraints on these choices are documented in
[settled requirements](../design/settled-requirements.md); the choices
themselves remain in [open questions](../design/open-questions/README.md).

## Coverage is not yet defined

The initial verification unit will be one fixed compilation artifact, but V2
does not yet discover that artifact or report reachability. There is no
implemented answer for unsupported Rust constructs, opaque dependencies,
generic instantiations, assembly, FFI, concurrency, unwinding, or skipped
code. Future support must fail closed or report explicit audited assumptions;
silence is not coverage.

The initial architecture is expected to make room for deadlock freedom,
cryptographic properties, protocol correctness, quantitative bounds, and
other user-defined domains. V2 is not expected to ship first-class backends
for all of them initially.

## Open PRs are experiments, not capabilities

Current open stacks contain Cargo target resolution, scanning, Charon
execution, dependency chasing, generation, diagnostic mapping, and toolchain
fixups. They are valuable evidence and may be close to landing, but they can
be rebased, redesigned, split, or abandoned. Only update this limitations page
after the corresponding behavior is present and tested on the branch.

See the [research index](../history/research-index.md) for the dated snapshot
and [current architecture](current-architecture.md) for the positive account
of what is implemented.
