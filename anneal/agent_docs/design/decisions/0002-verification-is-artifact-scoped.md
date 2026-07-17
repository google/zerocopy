<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# 0002: Verification is artifact-scoped

- **Status:** Accepted
- **Date:** 2026-07-17

## Context

The meaning of Rust source depends on its compilation. Target, enabled features,
`cfg` values, panic strategy, dependency resolution, compiler behavior, and
environmental inputs can all change the program which is compiled. A claim
phrased only as “this library is verified” would therefore leave its subject
ambiguous.

Anneal may eventually help users verify a matrix of configurations, but a
matrix is a collection of claims and not the initial atomic claim.

## Decision

The initial unit of an Anneal source-level verification claim is one Cargo
compilation artifact under a fixed target, configuration, feature set, panic
strategy, dependency graph, and relevant environment.

A successful verification of one artifact does not imply that another target
or configuration has been verified. A command may eventually orchestrate
several artifacts, but each artifact remains a separately identified claim.

## Rationale

Scoping the claim to the program the compiler actually constructs makes it
precise and auditable. It avoids universal claims over code configurations that
Anneal has not analyzed while leaving room for higher-level matrix tooling.

## Consequences

- Verification output must identify its compilation subject sufficiently for a
  user or auditor to distinguish it from other builds.
- Changing a claim-relevant compilation input produces a different artifact and
  requires a new verification claim.
- Cross-target or all-features assurance requires verifying every intended
  artifact or separately proving why the claim generalizes.
- Caches must not reuse a result across claim-relevant inputs without a sound
  equivalence argument.
- The exact compilation-subject identity, verification-result identity, and
  audit-ledger schema remain design work.

## Alternatives considered

### Claim verification for the source tree

A source tree admits many semantically different builds, so this would obscure
which program was analyzed.

### Require an entire configuration matrix as the atomic unit

This would make early adoption unnecessarily expensive and still require a
definition of which matrix is complete.

### Scope only to a crate and target triple

Features, `cfg`, dependencies, panic behavior, and environmental inputs can
change semantics even when those two values are unchanged.

## Deferred questions

- Which inputs must be recorded, normalized, or content-addressed?
- Which host tools, environment variables, compiler flags, and target
  specifications can change the compilation subject, and which instead belong
  only to verification-result identity or the trust ledger?
- Should `cargo anneal verify` support build matrices, and how should it report
  aggregate results?
- How do compilation-subject and verification-result identities appear in the
  TCB audit ledger?

## Evidence

- The project author selected one fixed Cargo compilation artifact, rather than
  a matrix of builds, as the exact initial unit of a source-level claim.
- Rust's compilation model makes target, `cfg`, features, panic strategy,
  dependencies, and generated inputs semantically relevant.

## Links

- [Generated Rust is input](0003-expanded-generated-rust-is-input.md)
- [The TCB is explicit and shrinkable](0006-the-tcb-is-explicit-and-shrinkable.md)
- [Trust and incremental adoption](../open-questions/trust-and-incremental-adoption.md)
- [Design principles](../principles.md)
