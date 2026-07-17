<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Memory, resources, and effects

**Status:** Open design discussion.

Aeneas obtains a simple functional model for a large subset of Rust by using
the borrow checker's discipline. Unsafe Rust, interior mutation, allocators,
concurrency, I/O, and similar features can require spatial, temporal, or
effectful reasoning. Anneal's central opportunity is to combine the simple
functional domain with enough resource-aware machinery to verify unsafe code
without imposing a full heap logic on every proof.

## Settled constraints

- Simplicity is preferred, but soundness is non-negotiable. An abstraction may
  hide implementation detail only when doing so preserves all semantics needed
  for the claimed properties.
- Resource tracking is a common case—probably not the only case—in which
  simplifying a predicate to an ordinary reusable fact could undermine
  soundness.
- Lifted separation-logic assertions must retain their resource semantics.
  Ownership, initialization, provenance, or permissions cannot become freely
  duplicable Lean propositions merely because they cross into a functional
  model.
- V2 may require additional monadic, WP, capability, or related machinery,
  likely in cooperation with Aeneas upstream.
- The primary goal of “locality” is modular proof: facts that can be packaged as
  local capabilities, shared invariants, or abstraction contracts should be,
  even if their operational interpretation refers to global state or history.
- The promise at a safe abstraction boundary is robust contextual refinement:
  every type-checked safe use is sound with respect to the declared interface.
  Literal substitution by a pure value transformer is not required.
- Anneal should aim for simple pure contracts at abstraction boundaries where
  they faithfully express behavior. It may expose effectful, world-indexed, or
  protocol interfaces where purity would erase behavior needed for soundness or
  another selected property.
- A “lower-bound memory model” means a conservative abstraction of normative
  Rust guarantees, not merely a convenient explicit set of assumptions.
- In the long term, Rust operational semantics should probably be shared
  infrastructure owned across Rust, Aeneas, Lean efforts, and related projects
  rather than an Anneal-private model. Short-term ownership is pragmatic.

## Locality and abstraction closure

Safe encapsulation demonstrates that unsafe implementation details can often
be hidden behind a safe interface: clients should not need to reason about the
entire program to use a well-designed abstraction soundly. Separation logic
recovers a related locality by splitting global state into composable resources.
Anneal should exploit this symmetry, but must not assume every abstraction can
be represented as a pure function on values.

Open questions include:

- What semantic condition shows that an unsafe implementation refines its safe
  interface in every safe context?
- Which effects can close behind an existential representation invariant, and
  which must remain in the public contract?
- Can allocator state, provenance history, concurrency protocols, and device
  state be represented by local capabilities or shared invariants?
- When a fact is operationally global, what proof rules let a client use a
  localized view without making the proof unsound?
- How are abstraction boundaries nested and composed across crates?

The objective is not purity for its own sake. It is the simplest interface that
is faithful, compositional, understandable, and resilient to implementation
change.

## Questions to resolve

### What resource logic is required?

- Which assertions must be affine, linear, persistent, fractional, or otherwise
  controlled?
- How are allocation, initialization, validity, provenance, aliasing,
  permissions, and lifetime represented?
- Which rules are generic separation-logic infrastructure and which encode
  Rust-specific semantics?
- Can Aeneas's existing state and WP machinery host these assertions, or is a
  new monad or logic required?
- How are resource assertions transferred through Aeneas's forward/backward
  treatment of borrows?
- How do resource obligations appear in ordinary Lean goals and tactics without
  letting users duplicate or discard them illegally?

The design should reuse maintained Lean and Aeneas abstractions wherever they
fit. Reinvention remains possible when an existing abstraction cannot express
the needed guarantee or would impose unacceptable complexity.

### Which effects remain visible?

Representative domains include:

- allocators and address reuse;
- I/O and interaction with an external environment;
- atomics, locks, threads, and scheduling;
- nondeterminism and randomness;
- panic, unwind cleanup, cancellation, and abort;
- volatile or memory-mapped operations;
- FFI and inline or out-of-line assembly; and
- long-running services and reactive protocols.

For each, V2 must decide whether a boundary exposes a state transformer, an
effect trace, a WP, a protocol capability, a nondeterministic relation, or a
simpler derived contract. The answer may vary by property kind. A functional
result theorem may hide scheduling details that a deadlock theorem must retain.

### How conservative is the memory model?

Rust's operational guarantees are still largely written in prose and continue
to evolve. V2 must determine:

- which normative documents and team decisions ground each axiom;
- how ambiguity is handled without accidentally claiming more than Rust
  guarantees;
- when to ask the Rust project to clarify or change the reference;
- how target layout, ABI, compiler, and hardware assumptions enter the model;
- how provenance and aliasing rules are versioned; and
- how proofs remain useful as the model is refined.

The authors' direct involvement with Rust's operational-semantics work makes
upstream clarification possible. It does not remove the need to expose current
assumptions in Anneal's trust ledger.

### Where should the implementation live?

Candidate arrangements include:

- Aeneas owns general unsafe or separation-logic semantics and Anneal supplies
  annotations and orchestration;
- Anneal temporarily owns a conservative pointer/layout layer that later moves
  upstream;
- Lean libraries own generic resource machinery while Aeneas owns Rust
  instantiations; and
- multiple semantic backends coexist behind a common contract interface.

Changes should be upstream when they form reusable Aeneas or Charon
functionality and when the maintenance burden is acceptable. Shipping a sound
and auditable Anneal remains more important than an aesthetically perfect
ownership boundary.

## Evaluation criteria

A candidate must preserve resource usage rules, support modular composition,
state its relationship to normative Rust, and make exceptional and infinite
executions sound. It should keep simple safe-code proofs simple and reveal
complex machinery only where the claimed behavior needs it. It should also
allow the trusted model to shrink or become more precise without rewriting
unrelated user proofs.

Useful experiments include a raw-pointer container that closes to a pure safe
API, an allocator whose capability must remain visible, a lock with a shared
invariant, panic during partially initialized construction, and an I/O protocol
whose functional return value alone is inadequate.

See also [property kinds and outcomes](property-kinds-and-outcomes.md),
[contracts and invariants](contracts-and-invariants.md), and
[Aeneas and Charon integration](aeneas-charon-integration.md).
