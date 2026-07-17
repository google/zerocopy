<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Property kinds and execution outcomes

**Status:** Open design discussion.

Anneal must reason about Rust soundness and also support properties such as
panic freedom, deadlock freedom, cryptographic correctness, protocol
correctness, and resource bounds. Rust's present `safe`/`unsafe` distinction
does not identify these different kinds of obligation. V2 needs an extensible
model, but adopting a taxonomy too early would constrain domains that have not
yet been explored.

## Settled constraints

- Soundness is non-negotiable and special. Rust defines what source-level
  undefined behavior is; it is not merely another user-selected functional
  property.
- Anneal and Aeneas only promise a faithful model of sound Rust. Other verified
  claims therefore depend, directly or transitively, on the relevant soundness
  obligations.
- Anneal's long-term scope includes arbitrarily subtle correctness properties
  and arbitrary Rust codebases. Initial V2 does not need first-class backends
  for every domain, but its architecture must admit new domains without a
  redesign.
- Property kinds cannot be isolated silos. A soundness proof may depend on a
  non-soundness property of a callee, and other properties may depend on one
  another.
- Both type invariants and trait invariants must be able to express arbitrary
  property kinds, not only soundness. See
  [contracts and invariants](contracts-and-invariants.md).
- Users must eventually be able to choose which supported property kinds a
  `cargo anneal verify` invocation enforces. The dependency semantics and
  reporting for that choice remain open.
- Verification must represent sound programs that run indefinitely, programs
  that remain sound while panicking or unwinding, and programs that catch a
  panic and continue. Success cannot be defined as “every execution returns
  normally.”
- A function's local proof establishes the applicable relationship between its
  preconditions and postconditions and establishes the required preconditions
  of its callees. When all dependencies and trusted leaves are accounted for,
  these local results must compose into the corresponding global guarantee.

## Taxonomy remains open

One proposal distinguishes:

- semantic outcomes and effects, such as return, panic or unwind, abort,
  divergence, undefined behavior, and model or tool failure;
- standard assurance policies, such as soundness, panic freedom, termination,
  partial correctness, and total correctness; and
- extensible user property domains, such as functional, relational, trace,
  protocol, quantitative, or probabilistic properties.

This proposal has deliberately been neither accepted nor rejected. These terms
are useful for exploring the space, but must not be exposed as a stable API or
used to infer settled semantics. Among other issues, a property like deadlock
freedom may concern traces, progress, concurrency resources, and termination at
once; “panic freedom” may need to distinguish panic, abort, and unwind; and the
boundary between a policy and a user domain may not survive real examples.

## Questions to resolve

### What is first-class?

- Which concepts, beyond soundness, should Anneal itself understand?
- Should panic, unwind, abort, nontermination, and ordinary return be modeled as
  outcomes, effects, predicates over traces, or some combination?
- Which concepts need dedicated compiler extraction or proof machinery, and
  which can be libraries defined over a smaller semantic core?
- Can one representation cover safety properties, liveness properties,
  hyperproperties, probabilistic claims, and quantitative bounds without
  pretending that their proof rules are identical?

Initial V2 is expected to supply an extensible architecture rather than
complete support for deadlock freedom, hyperproperties, quantitative bounds,
or cryptographic reasoning.

### How are execution paths combined?

V1 split “progress” from conditional correctness. Experience suggests that the
split duplicated symbolic-execution work and fit poorly with Aeneas's WP
specifications and `step`/`step*` tactics. The current direction is to build on
Aeneas's combined machinery and share symbolic execution across obligations.
It remains open:

- how path-specific obligations are attached to normal return, panic, unwind,
  abort, and unbounded execution;
- whether different property kinds consume a common execution certificate or
  require domain-specific proof judgments;
- how cleanup during unwinding is modeled well enough to establish soundness;
  and
- how partial or total correctness is requested without making soundness
  depend on termination.

The Aeneas revision examined during this design discussion represented several
exceptional situations through a coarse failure channel. A bounds check,
arithmetic overflow, explicit panic, undefined operation, unsupported model
feature, and tool failure can have very different implications. Before relying
on this observation, recheck the Aeneas revision pinned by the current
toolchain. We still need to determine which cases it combines, which
distinctions survive LLBC lowering, and whether to refine the semantic result
type, attach metadata, or express the distinctions in WP predicates. This is an
investigation, not a claim about the correct Aeneas API.

### How do dependencies compose?

- How are dependencies between property kinds declared and discovered?
- Should selecting a property automatically select its transitive dependency
  closure?
- If a dependency is excluded, does verification fail, succeed relative to an
  audited assumption, or vary by command profile?
- How should mutually dependent properties be proven? Candidate approaches
  include an explicit joint certificate for each strongly connected component,
  inductive closure, and coinductive closure for appropriate liveness claims.
- How are dependencies represented through generic functions, trait bounds,
  dynamic dispatch, and separately verified crates?

These choices interact with the meaning of an incomplete proof and with trust
reporting; see [trust and incremental adoption](trust-and-incremental-adoption.md).

### What does the user select and see?

- Are property kinds named globally, scoped to crates, or identified by Lean
  propositions or Rust declarations?
- Can projects define new kinds with reusable proof rules, or only attach
  arbitrary propositions to built-in mechanisms?
- Does a command select desired top-level guarantees, obligations to check, or
  both?
- How should output distinguish “not requested,” “proved,” “assumed,” “blocked
  by unsupported semantics,” and “not applicable”?
- Which guarantees belong in machine-readable artifacts so downstream crates
  can rely on them?

## Evaluation criteria

An acceptable design must:

1. Make it impossible to interpret a selected non-soundness property as a
   substitute for soundness.
2. Give panic, divergence, and recovery faithful meanings rather than treating
   them all as failed verification or silently discarding their paths.
3. Preserve compositional reasoning across functions and crates.
4. Avoid performing essentially the same symbolic execution independently for
   every property where evidence can safely be shared.
5. Allow specialized proof systems where sharing would erase a domain's
   semantics.
6. Produce an audit result whose dependencies and assumptions a user can
   understand.
7. Be testable on realistic examples before the vocabulary becomes stable.

## Useful experiments

- A server loop that maintains an invariant forever without promising
  termination.
- A destructor that runs during unwinding and whose unsafe operations must
  remain sound.
- A function whose soundness depends on a callee's cryptographic or protocol
  property.
- A lock abstraction with mutually dependent ownership and deadlock claims.
- One implementation checked for soundness, panic freedom, and a functional
  result property using shared symbolic execution.

Related questions include [Rust safety integration](rust-safety-integration.md),
[memory, resources, and effects](memory-resources-and-effects.md), and
[proof authoring](proof-authoring-and-user-experience.md).
