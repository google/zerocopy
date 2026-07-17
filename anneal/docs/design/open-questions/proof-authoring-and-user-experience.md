<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Proof authoring and user experience

**Status:** Open design discussion.

Anneal's eventual audience includes ordinary Rust teams, formal-methods
specialists, and coding agents. The aspiration is that even early-career Rust
engineers can participate, potentially with AI assistance, while the resulting
claims remain rigorous and reviewable. The right source syntax, proof workflow,
and division of labor are matters for experimentation.

## Settled constraints

- V2 is a clean-room redesign. V1's indentation-sensitive Lean blocks in Rust
  doc comments were an experiment, not a product commitment.
- The target is broad adoption in normal Rust development, not a tool usable
  only by specialists maintaining a separate proof project.
- AI assistance may make proof authoring tractable, but machine checking—not
  trust in an AI-generated explanation—establishes the formal claim.
- Soundness and auditability cannot be traded away for a smoother interface.
- Small Rust changes should not needlessly destroy proofs. Composability,
  evolvability, and stable abstraction boundaries are core UX properties.
- Existing Lean and Aeneas proof machinery should be reused where suitable,
  though raw generated names and internal WP details need not become the stable
  user interface.
- Incremental adoption must accommodate explicit prose safety justifications
  alongside formal proofs.
- Agents working on Anneal should reason from the same project principles and
  design canon as humans rather than from a divergent, simplified description.

## Who authors what?

Possible workflows include:

- Rust engineers write contracts and proof-relevant explanations while agents
  synthesize Lean proofs;
- agents propose both code and specifications, with humans reviewing intent and
  Lean checking proof correctness;
- formal-methods specialists publish reusable contracts, tactics, and models
  consumed by ordinary teams;
- library authors ship verified interfaces that downstream users consume
  without seeing implementation proofs; and
- humans write all proof material directly for especially sensitive code.

V2 should not assume one universal workflow. It should identify which artifacts
require human judgment—especially the intended meaning of user-defined
specifications—and which can be generated or checked mechanically.

Open questions include:

- What must a Rust author understand about Lean, LLBC, Aeneas WP semantics, and
  memory resources?
- Which proof steps are stable enough for agents to regenerate automatically?
- How does review distinguish a semantic specification change from proof repair
  after a refactor?
- Can organizations require human approval of axioms or soundness contracts
  while automating ordinary proofs?
- How are proof ownership and maintenance responsibility recorded?

## Surface syntax and artifact layout

Candidate locations include Rust attributes, doc comments, inline comments,
adjacent Lean files, generated proof modules with checked-in overlays, or a
combination. Each has different consequences for macro expansion, IDE support,
source control, Rust documentation, and proof reuse.

Questions to resolve:

- How are property kinds, preconditions, postconditions, type invariants, trait
  invariants, exceptional behavior, and resource transfer written?
- Which parts use Rust-like syntax and which expose Lean terms?
- Can specifications remain near Rust while larger proofs live in ordinary Lean
  modules?
- How does a proof refer to compiler-resolved items without depending on
  unstable generated names?
- Are proofs checked in, generated on demand, cached as artifacts, or all three
  under different policies?
- How are macro-generated items annotated or given contracts?
- Can source formatting and rustdoc ignore Anneal content cleanly?
- What is the migration path if syntax evolves rapidly during pre-alpha work?

The compiler binding needed for these choices is discussed in
[Aeneas and Charon integration](aeneas-charon-integration.md).

## Obligation presentation and diagnostics

`cargo anneal verify` should help a Rust engineer understand what must be true
at the relevant source location. It remains open how much of the underlying
Lean goal and Aeneas state is exposed.

Useful diagnostic capabilities may include:

- a Rust-level explanation of the violated callee precondition;
- the property kind and transitive dependency that generated it;
- the exact compiler-resolved operation, including generated code provenance;
- relevant assumptions, type or trait invariants, and owned resources;
- the normal, panic, unwind, or other path on which the obligation occurs;
- a minimal Lean goal for expert debugging;
- an audit distinction among failed, unsupported, incomplete, axiomatic, and
  prose-justified obligations; and
- machine-readable output for IDEs and agents.

Questions include whether Anneal should synthesize counterexamples, symbolic
traces, suggested invariants, or proof skeletons; how it avoids presenting an
unsoundly simplified explanation; and how diagnostics remain stable when
Aeneas internals change.

## Verification loop

The desired workflow should feel proportionate to ordinary Rust development:
fast feedback for local changes, a stronger reproducible check in CI, and a
clear audit artifact for review or release. Design work is needed for:

- incremental extraction and Lean recompilation;
- caching keyed by the exact Cargo artifact and toolchain;
- checking selected property kinds and their dependencies;
- distinguishing quick local checking from release assurance without
  overloading “verified”;
- editing support that navigates between Rust obligations and Lean proofs;
- proof repair when generated definitions change; and
- reducing irrelevant churn in error messages and audit logs.

The command success policy is part of
[trust and incremental adoption](trust-and-incremental-adoption.md), while the
semantics of selected properties are covered in
[property kinds and outcomes](property-kinds-and-outcomes.md).

## Abstraction and leakage

Some Aeneas concepts will inevitably be useful to proof authors. The open
question is which become stable Anneal concepts and which remain expert escape
hatches.

Candidate layers include:

1. Rust-oriented contracts and generated obligations for common proofs.
2. Reusable Anneal tactics and libraries that expose selected WP and resource
   concepts.
3. Full Lean and Aeneas access for specialists and novel domains.

This layering is only a candidate. It must not cause the convenient layer to
hide assumptions or make advanced properties impossible. Likewise, forcing all
users to manipulate generated forward/backward functions or raw separation
logic would undermine the broad-adoption goal if stable abstractions can avoid
it.

## Evaluation criteria and experiments

Evaluate workflows by semantic clarity, error discoverability, proof stability,
auditability, adoption cost, and the ability of both humans and agents to make
safe changes. Raw proof length or the absence of visible Lean is not by itself a
measure of usability.

Experiments should include:

- a new Rust graduate repairing a failed call-site proof with guided tooling;
- an agent updating a proof after a small implementation refactor without
  changing the contract;
- a specialist adding a new resource-aware property domain;
- migration from `// SAFETY:` prose to a formal proof;
- review of a PR that changes both a contract and its proof; and
- downstream use of a verified generic library without dependence on generated
  Aeneas names.

The governing contract and invariant questions are recorded in
[contracts and invariants](contracts-and-invariants.md).
