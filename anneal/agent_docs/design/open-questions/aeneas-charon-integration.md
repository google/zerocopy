<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas and Charon integration

**Status:** Open design discussion.

Anneal is intended to orchestrate and extend Charon's compiler extraction and
Aeneas's Lean translation. V2 must decide which interfaces to consume, which
capabilities to add upstream, and which temporary adaptations Anneal should
own. These are engineering choices governed by semantic fidelity,
maintainability, and user experience rather than a categorical ownership rule.

## Settled constraints

| Authority | Constraint on this question |
| --- | --- |
| [ANNEAL-REQ-001](../settled-requirements.md#anneal-req-001-v2-is-a-clean-room-redesign), [decision 0001](../decisions/0001-v2-is-a-clean-room-redesign.md) | V1 integration techniques carry no presumption into V2. |
| [ANNEAL-REQ-017](../settled-requirements.md#anneal-req-017-initial-claims-are-artifact-scoped), [decision 0002](../decisions/0002-verification-is-artifact-scoped.md) | Integration must identify one compiler-resolved compilation subject. |
| [ANNEAL-REQ-018](../settled-requirements.md#anneal-req-018-generated-rust-is-analyzed-input), [decision 0003](../decisions/0003-expanded-generated-rust-is-input.md) | Expanded generated Rust which enters the artifact is analyzed input. |
| [ANNEAL-REQ-019](../settled-requirements.md#anneal-req-019-coverage-adequacy-is-enforced) | Every potentially invalid operation in the reported coverage envelope must be reconciled with complete obligation coverage. |
| [ANNEAL-REQ-021](../settled-requirements.md#anneal-req-021-results-carry-an-audit-ledger) | Results must record the relevant translator, compiler, and proof-tool identities and gaps. |
| [ANNEAL-REQ-025](../settled-requirements.md#anneal-req-025-existing-proof-machinery-is-preferred), [ANNEAL-REQ-026](../settled-requirements.md#anneal-req-026-upstream-evolution-is-in-scope) | Suitable maintained machinery is preferred, and upstream changes are available when they are the best engineering choice. |

Topic-specific implications:

- The compiler-resolved artifact must remain authoritative. Any source scanner,
  annotation index, generated proof, or sidecar manifest must reconcile with
  it rather than silently creating a shadow view of the Rust program.
- No requirement categorically assigns a capability upstream or downstream.
  Ownership depends on semantic fidelity, interface robustness, maintenance
  burden, and user experience.
- Direct LLBC consumption, structured compiler metadata, Lean syntax
  extensions, and downstream adapters all remain candidates. Fragile textual
  rewriting is evidence that an interface may be missing, not a prohibited
  implementation technique.

V1's duplicate progress and conditional-correctness proofs are evidence in
favor of experimenting with Aeneas's WP specifications and `step`/`step*`
tactics. They do not settle the proof architecture.

## Information boundary

LLBC is a natural semantic input because Charon has already resolved much of
Rust's syntax and types. Anneal annotations also need to bind source intent to
the exact items, fields, operations, and calls that the compiler verifies.
Depending only on a parallel `syn` parse risks creating a shadow view that
disagrees after macro expansion, `cfg` processing, name resolution, or
desugaring.

One candidate is a compiler-resolved annotation or index mode in Charon. It
could expose expanded annotations, stable-within-artifact item identifiers,
signatures, source provenance, monomorphized or resolved call metadata, unsafe
operations, field accesses, and links to LLBC declarations. A source scanner
could remain a bootstrap or authoring aid but would have to reconcile exactly
against this authoritative index.

This candidate has not been accepted. Its motivation is to avoid silent skew,
support generated code, find every obligation, improve diagnostics, and reduce
dependence on generated Lean names. We still need to determine which facts are
already in LLBC, which should be added to Charon, and which Anneal can derive
reliably.

## Questions to resolve

### What should Charon expose?

- How are annotations preserved through expansion and lowering?
- Which identifiers remain stable enough for proof artifacts, incremental
  builds, and diagnostics?
- Can fields, unsafe operations, drop glue, trait dispatch, closures, and
  compiler-generated items be indexed uniformly?
- Does Anneal need MIR-level facts that LLBC intentionally omits?
- How are source spans represented for macro-generated and desugared code?
- Can Charon report unsupported or erased constructs so Anneal fails closed?
- At what compiler phase must extraction occur to avoid transformations that
  assume undefined behavior cannot happen?

The last question is part of the adequacy problem described in
[source/model adequacy](source-model-adequacy.md).

### What should Aeneas expose or own?

- Can unsafe leaves be represented within Aeneas's WP semantics with explicit
  guards and resource effects?
- Which distinctions among return, panic, unwind, abort, divergence, undefined
  operation, and modeling failure should Aeneas preserve?
- How can multiple property obligations share symbolic execution through
  `step` and `step*` without forcing every domain into the same logic?
- What changes are needed for separation-logic objects or capabilities whose
  use must remain affine or linear?
- Should Aeneas emit structured proof metadata alongside Lean definitions?
- Can generated definitions expose stable theorem interfaces rather than
  implementation-specific names?
- How does unsafe and separation-logic work available or proposed in the
  relevant Aeneas revision relate to an Anneal-owned short-term pointer model?

Generic resource machinery may belong in Lean libraries, Rust-specific
semantics in Aeneas, and orchestration in Anneal, but that division is only a
working possibility. See [memory, resources, and effects](memory-resources-and-effects.md).

### How does Anneal attach its contracts?

Candidate techniques include:

- extend LLBC with elaborated contracts and invariant declarations;
- provide Aeneas a structured sidecar manifest keyed by Charon identifiers;
- extend Aeneas lowering so proposition-valued contract arguments appear in
  generated functions;
- generate sidecar WP theorems for every indexed call;
- inject stable Lean macros or syntax that elaborate against generated
  declarations; and
- validate generated Lean against an independent obligation manifest.

The choice should be based on completeness, auditability, compatibility with
Aeneas tactics, diagnostic quality, and maintenance cost. “No textual
post-processing ever” is not a principle, but fragile search-and-replace over
generated code is strong evidence that an upstream interface is missing.

### How are versions and downstream adaptations managed?

- Does Anneal track released Aeneas/Charon versions, pinned revisions, or a
  maintained fork?
- What compatibility contract can upstream realistically offer?
- How do proof artifacts record the exact translator and standard-library
  versions they depend on?
- When should experimental work live downstream before an upstream API is
  proposed?
- Who owns tests demonstrating that an upstream change preserves Anneal's
  semantic assumptions?

## Evaluation criteria

A durable integration must make the compiler-resolved artifact authoritative,
detect annotation or coverage skew, preserve all semantics needed for claimed
properties, and give proof authors stable interfaces. It should reuse upstream
machinery, avoid imposing Anneal-only complexity on all Aeneas users, and leave
a credible path for temporary downstream work to mature upstream.

Useful experiments include a proc-macro-generated unsafe call with an
annotation, a generic trait call resolved after monomorphization, an invariant
on a compiler-generated field access path, shared WP execution for two property
kinds, and a resource assertion that Lean cannot duplicate.

The effect on ordinary users is discussed in
[proof authoring and user experience](proof-authoring-and-user-experience.md).
