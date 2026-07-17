<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Glossary

This glossary gives short definitions for vocabulary stable enough to use
throughout the Anneal design. Proposed taxonomies remain in
[open design questions](design/open-questions/README.md) until accepted.

## Assurance and properties

**Soundness**

: A guarantee that the covered Rust behavior has no undefined behavior. A safe
  abstraction is sound only when every type-correct safe use admitted by its API
  within the stated semantic and compilation envelope preserves that guarantee;
  checking selected clients supports a narrower artifact claim. Soundness is
  also a prerequisite for Anneal's promised source-to-model correspondence.

**Unsafe (Rust)**

: Rust syntax which marks an operation as carrying obligations the compiler
  does not check, or marks a region in which the programmer accepts
  responsibility for such obligations. The presence of `unsafe` code does not
  by itself mean that the program is unsound.

**Unsound**

: Capable of causing Rust undefined behavior in a use which the relevant API
  presents as permitted. An implementation may use `unsafe` operations and
  still be sound when it establishes every required condition.

**Property**

: A proposition Anneal is asked to establish about a program or its behavior.
  Examples include soundness, panic freedom, functional correctness, protocol
  conformance, and resource bounds.

**Property kind**

: A class of obligations which may have its own contracts, invariants,
  dependencies, and selection policy. Soundness is necessarily special; which
  other classes receive first-class treatment remains open.

**User-defined correctness property**

: A property's intended meaning as supplied by the user rather than fixed by
  Rust. Anneal can check a precise specification, but cannot decide whether it
  expresses what the user actually wanted.

**Specification adequacy**

: Whether a specification is strong and faithful enough to justify the claim
  made from it. In particular, a weak user contract must not erase a Rust
  soundness requirement which Anneal is responsible for generating.

## Claims, contracts, and composition

**Claim**

: The precise statement a verification result supports. It identifies the
  Rust subject, properties, relevant behavior, coverage, and assumptions; “this
  program is verified” without those qualifications is not a complete claim.

**Contract**

: The requirements under which an item may be used and the guarantees it
  provides. A contract may mention multiple properties or execution outcomes;
  its final source syntax remains open.

**Precondition / caller obligation**

: A requirement which must hold before an operation. At a call site, the caller
  must establish each selected precondition—for example, that a pointer refers
  to live memory. Rust safety requirements and ordinary functional assumptions
  may require different source-language treatment even when Lean represents
  both as propositions.

**Postcondition**

: A guarantee established after an operation for a relevant outcome. Which
  outcomes carry which guarantees is part of the open property/outcome design.

**Local guarantee**

: What is proved about one item: under its preconditions, it establishes its
  postconditions and meets the preconditions of the operations it invokes.

**Global guarantee**

: A claim obtained by composing local guarantees across the covered program,
  relative to its explicitly reported trusted leaves and environmental
  assumptions.

**Robust safety**

: The implementation remains sound under every type-correct safe use admitted
  by its API within an explicitly stated semantic and compilation envelope.
  This is the soundness-specific instance of the broader
  contextual-refinement requirement. A result covering only selected clients
  or calls is an artifact-level claim, not robust safety.

**Contextual refinement**

: Every implementation behavior visible to a context in the claim's quantified
  envelope is permitted by the declared interface, including its stated effects
  and transferred resources. Clients can therefore use the interface without
  inspecting the private body. Checking the calls present in one compiled
  program is narrower than proving this property for every client in such an
  envelope; a result must say which claim it establishes.

## Invariants and resources

**Invariant**

: A condition attached to a program abstraction which its rules require at
  specified boundaries. Those rules determine when the condition may be
  assumed, opened, consumed, and re-established.

**Type invariant**

: An invariant associated with values or storage of a type. Type invariants may
  express arbitrary property kinds, and their enforcement must cover every
  operation which can make the invariant relevant.

**Trait invariant**

: An invariant, of any property kind, which each relevant implementation of a
  trait must establish and code with the corresponding trait bound may use.

**Resource proposition**

: A proposition whose proof carries ownership, permission, or another usage
  discipline, so it cannot necessarily be copied or discarded like an
  ordinary fact. Exclusive ownership and protocol state are common examples.

**Capability**

: Locally held authority or evidence which permits an operation, potentially
  packaging facts about a heap, allocator, concurrency protocol, or external
  environment.

## Models, subjects, and evidence

**Compilation subject (compilation artifact)**

: One compiler-resolved Rust program with fixed target, features, `cfg` values,
  dependencies, panic strategy, generated Rust, and relevant environment. It is
  not a matrix of builds or merely Cargo's emitted native binary.

**Verification result**

: A reported claim about one compilation subject together with the checked
  evidence and classified dependencies which support it. Proof-tool versions,
  proofs, or assumptions can change the result without changing the Rust
  subject.

**Evidence graph**

: The connected local contracts, proofs, call obligations, translation
  evidence, and coverage evidence from which a result is composed. This is a
  conceptual dependency graph; its concrete serialization remains open.

**Residual dependency**

: A dependency, gap, or failure which remains after Anneal evaluates the
  evidence graph. It may condition or narrow a claim, or prevent Anneal from
  establishing one. Examples include a trusted semantic leaf, an incomplete
  proof, a prose justification, unsupported coverage, a toolchain dependency,
  or an environmental assumption. Its status, role, and effect on the claim
  must be explicit.

**Source model**

: The Lean-level semantics used to reason about the compiled Rust program.
  Anneal must justify that this model is faithful for the claim it reports.

**LLBC**

: Charon's compiler-resolved, structured Rust intermediate representation.
  Aeneas consumes LLBC, and current Anneal design work also trends toward
  consuming it directly; the long-term integration boundary remains open.

**Weakest-precondition specification (WP specification)**

: A specification of what must hold before an operation so that a desired
  continuation property holds afterward. Aeneas provides WP machinery and
  tactics such as `step` and `step*` which Anneal should reuse when appropriate.

## Trust and incompleteness

**Trust**

: A claim-relative reliance on a dependency whose correctness is not
  established by checked evidence included in the result at the claimed
  semantic endpoint. Trust can concern program semantics, correspondence and
  integration, tool implementations, or the execution substrate. Not every
  residual dependency is accepted as trust; some gaps and failures block a
  claim instead.

**Trusted computing base (TCB)**

: Everything whose correctness must be assumed for a result to imply its
  claim. This can include semantic leaves, translators, proof checking,
  compilers, semantic assumptions, and relevant host and target hardware.

**Trusted leaf**

: An operation or external component whose specification is assumed rather
  than proved from a body visible to the current verification. A deeper model
  may replace that assumption later.

**Axiom**

: A proposition intentionally admitted without proof in the current model,
  such as a specification of genuine external semantics or an Anneal-provided
  primitive leaf. It must remain distinguishable in the result from an
  unfinished proof or prose justification. Whether those categories share an
  underlying Lean mechanism does not change their different meanings.

**Incomplete proof**

: A declared obligation whose proof has not yet been completed. It is different
  from a claim that a proposition is inherently axiomatic.

**Prose safety justification**

: A human explanation, commonly a Rust `// SAFETY:` comment, accepted
  temporarily in place of a selected formal proof during incremental adoption.
  It is not a machine-checked theorem and must remain visible in the result.

**Audit ledger**

: The human- and machine-readable projection of the identities, residual
  dependencies, coverage gaps, and trust assumptions which qualify a result.
  Its exact schema remains open; its existence is required.

**Fail closed**

: Refuse to report a claim stronger than the available evidence supports. A
  separately identified conditional or incremental result may still be useful
  when every assumption and incomplete obligation is explicit.
