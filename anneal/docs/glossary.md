<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Glossary

This glossary defines vocabulary already stable enough for the V2 design
canon. Proposed taxonomies belong in
[open design questions](design/open-questions/README.md) until accepted.

## Assurance and properties

**Soundness**

: For Anneal's initial focus, the absence of Rust undefined behavior under the
  conditions of the verified claim. For a safe abstraction, soundness means
  that every type-checked use through its safe interface by sound safe Rust
  preserves this guarantee. Soundness is also a prerequisite of the promised
  source-to-model correspondence.

**Property**

: A proposition or family of propositions Anneal is asked to establish about
  an artifact or its behavior. Examples include soundness, panic freedom,
  functional correctness, protocol conformance, and resource bounds. The final
  classification and representation of properties is open.

**Property kind**

: A distinguished class of obligations that may have its own contracts,
  invariants, dependencies, and selection policy. Soundness is necessarily
  special; which other kinds receive first-class treatment remains open.

**User-defined correctness property**

: A property whose intended meaning is supplied by the user rather than fixed
  by Rust. Anneal can check that an axiom for such a property is used
  consistently, but cannot decide whether it expresses the user's actual
  intent.

**Specification adequacy**

: The fact that a specification is strong and faithful enough to support the
  claim made from it. For non-axiomatic soundness obligations, Anneal must not
  let a weak or vacuous user contract erase the requirements imposed by Rust's
  semantics.

## Contracts and composition

**Contract**

: The assumptions under which an item may be used and the guarantees it
  provides, potentially indexed by property kind and execution behavior. The
  final source syntax is open.

**Precondition**

: An obligation a caller must establish before an operation. Rust soundness
  preconditions and ordinary functional-domain assumptions may require
  different source-language treatment even when both appear as propositions in
  Lean.

**Postcondition**

: A guarantee established by an operation for a relevant outcome. Which
  outcomes carry which postconditions is part of the open property/outcome
  design.

**Callee obligation**

: The caller's proof that a call satisfies every selected requirement imposed
  by the callee. Complete coverage of these obligations is essential to global
  composition.

**Local guarantee**

: The claim checked about one item: under its assumptions, it establishes its
  guarantees and satisfies the required obligations of operations it invokes.

**Global guarantee**

: The result obtained by composing local guarantees across an artifact,
  relative to an explicit collection of trusted leaves and environmental
  assumptions.

**Contextual refinement**

: The property that an implementation faithfully realizes its declared
  interface in every client context covered by the claim. The coverage envelope
  must be explicit: concrete calls in one compilation subject and a reusable
  theorem quantified over downstream safe clients are different claims. Anneal
  uses contextual refinement as the durable interpretation of the locality
  behind safe encapsulation, rather than requiring literal syntactic
  substitution of implementations.

## Invariants and resources

**Invariant**

: A condition associated with a program abstraction and a property kind which
  the abstraction's rules require to hold at specified boundaries. Those rules
  also govern when it may be assumed, opened, consumed, and re-established. An
  invariant may contain resources whose use, duplication, and disposal are
  restricted; the general term does not assign a separation-logic modality.

**Type invariant**

: An invariant associated with values or storage of a type. V1 called its
  experimental form `isValid`; that spelling and enforcement mechanism are not
  inherited by V2. V2 type invariants must be able to express arbitrary
  property kinds.

**Trait invariant**

: An invariant promised by implementations of a trait and available where the
  corresponding trait bound is known. V1 called its experimental form
  `isSafe`; V2 must enforce both the implementation obligation and the use-site
  availability, for arbitrary property kinds.

**Resource proposition**

: A proposition whose proof carries ownership, permission, or other usage
  discipline and therefore cannot necessarily be copied or discarded like an
  ordinary freely reusable fact. Initialization, provenance, exclusive
  ownership, and protocol state may require resource semantics.

**Capability**

: Locally held authority or evidence that permits an operation while packaging
  facts that may originate in a global heap, allocator, concurrency protocol,
  or environment.

## Models and artifacts

**Compilation subject (compilation artifact)**

: One concrete compiler-selected Rust program under fixed target, features,
  `cfg` values, dependencies, panic strategy, generated code, and relevant
  environment. It is the subject of an initial V2 claim rather than a matrix of
  possible builds. In this canon it means the compiler-resolved Rust program
  and semantic configuration, not Cargo's emitted native binary. Proof-tool
  versions do not, merely by changing, turn it into a different Rust
  compilation subject.

**Verification result**

: The evidence and claim Anneal produces about one compilation artifact under
  selected properties, translation and proof inputs, coverage, and trust
  assumptions. Changing Aeneas, Anneal, Lean, a checked proof, or an assumption
  can produce a different result without changing the compilation subject. A
  result must identify which claim layer it reports; its exact canonical
  identifier and serialization remain open.

**Source model**

: The Lean-level semantics used to reason about the compiled Rust artifact.
Anneal must justify that the model is faithful for the program whose soundness
it is proving.

**LLBC**

: Charon's structured, serialized Rust intermediate representation consumed by
Aeneas. Current V2 design work trends toward Anneal consuming it directly, but
the checked-in V2 implementation does not yet do so. LLBC is compiler resolved;
its exact role at the long-term integration boundary remains open.

**Weakest-precondition specification (WP specification)**

: A specification describing what must hold before an operation so that a
desired continuation property holds afterward. Aeneas provides WP machinery
and tactics such as `step` and `step*` that V2 should prefer to reuse when
appropriate.

## Trust

**Trusted computing base (TCB)**

: Everything whose correctness must be assumed for an Anneal result to imply
its stated claim. This includes more than explicit Lean axioms: translators,
proof checking, compiler and semantic assumptions, and relevant host and target
hardware may all contribute. The practical end-to-end TCB may be broad even
when the set of opaque program-semantic leaves is small.

**Trusted leaf**

: An operation or external component whose specification is assumed rather
than proved from a body visible to the current verification. Trusted leaves
must be explicit and may later be replaced with deeper models.

**Axiom**

: An assumed proposition admitted without proof in the current model. Axioms
are appropriate for genuine semantic boundaries and may also support
incremental adoption, but every use belongs in the audit ledger.

**Incomplete proof**

: A declared obligation whose proof has not yet been completed. It should be
distinguished from an assertion that is inherently axiomatic. It may block
verification or, in an explicitly incremental mode, make a result conditional;
that command policy remains open.

**Prose safety justification**

: A human-written explanation, commonly a Rust `// SAFETY:` comment, accepted
temporarily in place of a selected formal proof during incremental adoption. It
does not become a machine-checked theorem and must remain visible in reports.

**Audit ledger**

: The machine-readable and human-reviewable account of axioms, trusted leaves,
  incomplete proofs, prose justifications, skipped coverage, toolchain versions,
  and environmental assumptions on which a result depends. Its final schema is
  open; its existence is required.

**Fail closed**

: Refuse to report a claim unless the available evidence justifies that exact
  claim. A separately identified conditional or incremental result may be valid
  when all assumptions and incompleteness are explicit; this definition does
  not decide which command modes exist or which exit statuses they use.
