<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# 0006: The TCB is explicit and shrinkable

- **Status:** Accepted
- **Date:** 2026-07-17

## Context

Anneal cannot initially prove every layer on which a Rust execution depends.
Primitive unsafe operations, compiler intrinsics, FFI, assembly, the
verification toolchain, and hardware all introduce facts that may have to be
trusted. Hiding those assumptions behind a successful command would make the
result impossible to audit.

At the same time, treating today's body-unmodeled operations as a permanent
semantic boundary would prevent future work from replacing them with formal
models. For example, a formal ISA model could eventually make some assembly
transparent.

## Decision

Anneal V2 will reduce unproved operational semantics to a small, explicit set
of trusted leaves and will expose the assumptions on which a result depends.
The TCB is an auditable boundary, not an implicit promise.

Initially, trusted semantic leaves are expected to include some unsafe standard
library functions and intrinsics, raw-pointer dereferences, FFI, and inline or
external assembly. Approved axioms and prose justifications must remain visible
as unproved assumptions. Incomplete proofs must remain visible as outstanding
obligations; whether a particular command mode blocks on or conditionally
admits them remains open. None may masquerade as verified facts.

The architecture must permit a trusted leaf or platform assumption to be
replaced by a more detailed formal model later. A fully adopted codebase should
reserve axioms for genuinely external semantics, although the boundary of
“external” can shrink as new models become available.

This decision does not claim that Anneal's complete practical TCB is initially
small. The compiler, translators, proof checker, platforms, and hardware remain
part of the end-to-end TCB until independently justified. “Small” applies first
to the explicit set of trusted program-semantic leaves.

## Rationale

A small and inspectable trusted semantic leaf set, together with an explicit
account of the broader end-to-end TCB, lets a user understand exactly what an
Anneal result entitles them to believe. Making the boundary replaceable
supports stronger assurance over time without requiring the initial
implementation to formalize the Rust compiler, every ISA, and every foreign
system before it is useful.

## Consequences

- Verification results are relative to the correctness of their recorded
  trusted leaves and platform assumptions.
- Anneal needs a TCB audit ledger which includes axioms and unfinished
  obligations, not merely a binary success indicator.
- The ledger must ultimately account for relevant Anneal, Aeneas, Charon,
  rustc, LLVM, host-hardware, and target-hardware assumptions; its exact schema
  is not fixed here.
- Standard-library support may use the same axiom-authoring machinery exposed
  for genuinely external user semantics.
- Replacing an axiom with a proof or a leaf with a model must reduce, rather
  than merely relocate invisibly, the reported trust boundary.
- Anneal authors are responsible for the adequacy of built-in soundness
  preconditions on axiomatic unsafe leaves.

## Alternatives considered

### Prove every leaf before V2 can be useful

This would postpone practical verification until numerous independent compiler,
library, platform, and hardware models exist.

### Trust arbitrary body-unmodeled functions without reporting them

This would verify callers only relative to hidden assumptions and invite users
to overstate the result.

### Make the initial leaf boundary permanent

That would prevent stronger future models from reducing the TCB and would make
implementation expedience part of Anneal's long-term assurance definition.

## Deferred questions

- What is the exact TCB audit-ledger schema and output format?
- Which assumptions cause `cargo anneal verify` to fail, succeed conditionally,
  or succeed with warnings?
- Which initial leaves are axiomatized by Anneal, Aeneas, a platform package, or
  a user?
- Who authors and distributes FFI contracts: library consumers, upstream
  library authors, or both?
- How are toolchain, host, target, and hardware identities represented?
- Which formal Rust, allocator, ISA, concurrency, and foreign-language models
  should replace trusted leaves first?

## Evidence

- The project author defined V2's long-term direction as reducing the TCB to a
  small explicit collection of trusted leaves while preserving the option to
  model those leaves later.
- The project author identified the TCB audit log as an important user-facing
  capability and required axioms and not-yet-proven specifications to appear in
  it.
- The requested trust inventory includes Anneal's dependencies and both host
  and target hardware, even though its exact schema remains open.

## Links

- [Verification is artifact-scoped](0002-verification-is-artifact-scoped.md)
- [Incremental adoption supports prose](0005-incremental-adoption-supports-prose-justifications.md)
- [Trust and incremental adoption](../open-questions/trust-and-incremental-adoption.md)
- [Source/model adequacy](../open-questions/source-model-adequacy.md)
- [Verification result and trust](../result-and-trust.md)
