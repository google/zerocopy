<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Design principles

This page states Anneal's goals and the choice rules used when
[settled requirements](settled-requirements.md) and
[accepted decisions](decisions/README.md) do not determine an answer. Technical
mechanisms belong in the linked design documents; agent procedure belongs in
[`AGENTS.md`](../../AGENTS.md).

## Goals and scope

Anneal's long-term scope includes arbitrarily subtle correctness properties and
arbitrary Rust codebases. That scope guides the architecture; it does not
require the current executable or first milestone to support every Rust
construct or property domain.

Unsafe Rust leaves soundness obligations which Rust's type system does not
discharge. Giving them rigorous, practical treatment is Anneal's foundational
use case, especially in unsafe-heavy systems code. Anneal must nevertheless
support functional correctness, protocols, panic freedom, resource bounds, and
other user-defined properties in the same framework.

Anneal is intended for ordinary Rust organizations. Specialists and AI agents
may assist, but Rust engineers must be able to understand, debug, review, and
incrementally adopt the result.

## Protect soundness and the meaning of every reported claim

A theorem about modeled behavior supports the corresponding Rust claim only
insofar as the covered Rust behavior remains defined. Correspondence over an
execution prefix may help prove this condition, but soundness is still a
prerequisite for interpreting a model theorem as a fact about the Rust artifact.

Anneal must account for every operation which can cause undefined behavior
under the supported Rust semantics and generate adequate obligations for it. A
weak, incomplete, or vacuous user specification cannot remove those
obligations. Unsupported semantics, missing coverage, and insufficient evidence
must narrow, condition, or prevent the reported claim instead of disappearing
behind a successful proof check.

For a user-defined property, Anneal can enforce a precise definition but cannot
infer whether it captures the user's intent. A specification claiming
correspondence with Rust or another external semantics is different: its
adequacy is a claim-relevant dependency which must be justified or reported.
See the [verification model](verification-model.md) and
[result and trust](result-and-trust.md).

## Prove abstraction boundaries once, then compose them

An implementation becomes reusable through an abstraction boundary only after
it has been proved to satisfy the declared interface. That interface must
account for every claim-relevant interaction with the context, including
capabilities or resources exchanged across it. For soundness, a reusable safe
API must remain sound under every type-correct safe use admitted by that API
within the stated semantic and compilation envelope.

Clients may then use the established guarantees without reopening the private
implementation. They may interact through declared mutation, allocation, I/O,
nondeterminism, or other effects, but neither side may impose undeclared
requirements on the other. This interface-relative isolation—not absence of
interaction—is the locality Anneal seeks. See
[contextual refinement](verification-model.md#contextual-refinement).

## Introduce only the semantic machinery the claim requires

A pure value-level contract is preferred when it fully describes the
abstraction boundary. Resource, provenance, initialization, ownership,
concurrency, protocol, or effect semantics are required whenever ignoring them
could invalidate the claim.

For example, a freely reusable Lean fact cannot by itself authorize exclusive
mutation: two consumers could each cite it to justify access. Whether enforced
by a resource proposition, a state- or world-indexed weakest precondition, a
monadic discipline, or another mechanism, the proof interface must retain the
permission's usage rules.

This yields a hybrid model without making “hybrid” a goal. The boundary between
functional translation and richer semantics evolves with Aeneas and Charon.
Revision-sensitive facts belong in the
[Aeneas and Charon reference](../reference/aeneas-and-charon.md); unresolved
architecture belongs in
[memory, resources, and effects](open-questions/memory-resources-and-effects.md).

## Reuse general proof machinery after deriving the right Rust obligation

Rust semantics determine the obligations. Once an obligation becomes a general
proof problem, Anneal favors proof abstractions maintained by Lean and
Aeneas—and compiler-resolved interfaces maintained by Charon—over parallel
special-purpose mechanisms.

For example, `index < slice.len()` is one arithmetic sub-obligation among the
guards for `slice.get_unchecked(index)`. Aeneas's weakest-precondition
machinery and Lean's arithmetic support can derive that inequality from a
preceding bounds check; a separate Anneal bounds logic would duplicate rather
than improve the semantics. Other unsafe operations may additionally require
provenance, liveness, initialization, authority, or similar conditions which
need richer machinery; a concrete mismatch of that kind justifies extending
the underlying abstraction.

This example does not decide how obligations are encoded. Interface and
upstreaming choices remain in the
[Aeneas and Charon integration discussion](open-questions/aeneas-charon-integration.md).

## Expose and reduce every trusted dependency

A dependency is trusted for a claim when the claim relies on its correctness
but the included checked evidence does not establish it at the claimed semantic
endpoint. Translation into Lean does not itself remove trust.

Semantic assumptions, extraction and correspondence, tool correctness,
pipeline integration, and execution-platform assumptions play different roles
and must remain distinguishable. An incomplete proof is an unresolved
obligation, not an approved semantic boundary; coverage gaps and tool failures
may narrow or block a claim rather than become assumptions.

Trusted dependencies must be visible and replaceable by stronger evidence.
Moving one into a helper or upstream component does not reduce trust unless the
end-to-end dependency is removed. Definitions, classifications, and audit
requirements live in [result and trust](result-and-trust.md).

## Make partial adoption useful without calling it complete

Anneal must support incremental adoption, including selected prose
`// SAFETY:` justifications and a distinct representation of unfinished
proofs. Neither may silently become checked evidence. Results must identify what
was checked, what remains, which claim the evidence supports, and what would
strengthen it.

Among designs preserving those distinctions, this principle favors stable
proof interfaces, source-linked diagnostics, resilience to small changes, and
feedback useful to ordinary Rust engineers.

## Relationship among the principles

Soundness and claim integrity constrain acceptable designs. Among those
designs, simplicity, reuse, trust reduction, coverage, maintenance, and user
experience require case-specific judgment rather than a permanent total order.
