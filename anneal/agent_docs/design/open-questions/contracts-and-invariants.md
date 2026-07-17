<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Contracts and invariants

**Status:** Open design discussion.

Function contracts, type invariants, and trait invariants are the principal
units by which local proofs become reusable facts. Their semantic roles are
durable, but their syntax, enforcement mechanisms, and relationship to Rust's
types remain open for V2.

## Settled constraints

| Authority | Constraint on this question |
| --- | --- |
| [ANNEAL-REQ-005](../settled-requirements.md#anneal-req-005-soundness-is-foundational), [ANNEAL-REQ-006](../settled-requirements.md#anneal-req-006-soundness-specifications-produce-adequate-obligations) | User contracts cannot weaken or erase Rust soundness obligations. |
| [ANNEAL-REQ-009](../settled-requirements.md#anneal-req-009-local-contract-obligations), [ANNEAL-REQ-010](../settled-requirements.md#anneal-req-010-local-results-compose-globally) | Item contracts must support local proof and reusable global composition. |
| [ANNEAL-REQ-012](../settled-requirements.md#anneal-req-012-property-dependencies) | Contracts and invariants must express dependencies among property kinds, including cycles treated soundly. |
| [ANNEAL-REQ-014](../settled-requirements.md#anneal-req-014-type-invariants-support-arbitrary-property-kinds), [ANNEAL-REQ-015](../settled-requirements.md#anneal-req-015-trait-invariants-support-arbitrary-property-kinds), [decision 0004](../decisions/0004-invariants-support-all-property-kinds.md) | Both type and trait invariants support arbitrary property kinds, with their respective establishment and use obligations enforced. |
| [ANNEAL-REQ-016](../settled-requirements.md#anneal-req-016-contracts-distinguish-semantic-roles) | The model must distinguish soundness obligations from ordinary functional preconditions and other property roles. |
| [ANNEAL-REQ-019](../settled-requirements.md#anneal-req-019-coverage-adequacy-is-enforced) | Whatever contract encoding is chosen must not omit a potentially invalid operation within the reported coverage envelope. |

Topic-specific implications:

- A safe API cannot make undefined behavior depend on an extra unchecked
  obligation of its safe caller. It may still state conditional functional or
  other guarantees without turning their conditions into soundness
  preconditions.
- Built-in soundness contracts are answerable to Rust's semantics. A
  user-defined correctness axiom records the user's intended property; Anneal
  can enforce and report it but cannot supply its real-world intent.
- V1's `isValid`, `isSafe`, and indentation-sensitive proof syntax are neither
  enforcement mechanisms nor syntax commitments for V2.

## Function contracts

### Safety contracts versus general contracts

Rust's source syntax does not distinguish a soundness precondition from a
precondition for panic freedom, a functional result, or a protocol. V2 needs a
semantic distinction even if the surface syntax is shared.

Questions include:

- Does every clause name its property kind explicitly, inherit one from its
  declaration, or elaborate to a typed Lean-level obligation?
- How does a safe function express “if `x > 0`, the result has property P”
  without suggesting that `x <= 0` may cause undefined behavior?
- Can a single precondition support multiple postconditions or property kinds?
- How are frame conditions, exceptional postconditions, trace conditions, and
  resource transfer represented?
- Are contracts attached to source functions, monomorphized instances, trait
  methods, function values, or compiler-resolved items with quantified
  generics?
- Which contract facts become part of a separately compiled crate's
  verification interface?

The surface should make an accidental weakening of soundness obligations hard
to overlook while remaining usable for general correctness claims.

### Contracts as types or sidecar theorems

One candidate lowers a Rust function with Anneal preconditions to a Lean
function whose proposition-valued arguments must be supplied at every call.
This closely resembles an extension to the type system and makes an omitted
proof ill-typed. Another keeps Aeneas's ordinary function model and proves
sidecar theorems showing that every call satisfies the relevant contract. The
latter aligns more directly with existing Aeneas WP machinery.

This is primarily a representation and enforcement choice. Either is
acceptable only if Anneal can establish complete coverage of all applicable
calls. The deeper circularity in using a soundness-dependent model is treated
in [source/model adequacy](source-model-adequacy.md).

Open details include higher-order calls, recursion, dynamic dispatch, trait
resolution, closures, foreign calls, and how proof obligations survive
monomorphization or separate compilation.

## Type invariants

A type invariant describes facts that valid uses of a value may rely on. It may
support soundness—for example, initialized storage or a valid pointer
relationship—or another property such as a cryptographic representation
invariant or resource bound.

Questions include:

- Is an invariant a proposition over an abstract value, a resource assertion,
  a family indexed by property kind, or an interface that can provide multiple
  forms of evidence?
- At which points must it hold: all observable safe states, function
  boundaries, borrow boundaries, suspension points, panic edges, or some
  declared subset?
- How is an invariant opened temporarily, and what capability guarantees that
  it is restored before control escapes through return, panic, cancellation,
  or destruction?
- Which reads require proof that the invariant holds, and which writes require
  proof that it is re-established?
- How do interior mutability, aliasing, pinning, drop, partial initialization,
  unions, and concurrency change the proof rules?
- Can a type carry several invariants with dependencies between property kinds?

Enforcement might build on Rust unsafe fields or use Anneal-specific analysis;
see [Rust safety integration](rust-safety-integration.md). Resource-bearing
invariants cannot be flattened into freely duplicable propositions; see
[memory, resources, and effects](memory-resources-and-effects.md).

## Trait invariants

The durable idea behind V1's `isSafe` is that an implementation supplies an
invariant promised by the trait, and generic code consumes that invariant from
a known bound. V2 must make both halves enforceable.

Questions include:

- Does the trait declare one invariant per property kind, one structured family
  of invariants, or named obligations with explicit dependencies?
- Which implementations require a proof: unsafe implementations only, all
  implementations of an annotated trait, or a set selected by the property?
- How is evidence made available in a generic context with `T: Trait`?
- How are associated types, constants, generic associated types, supertraits,
  negative reasoning, specialization, and trait objects handled?
- Does dynamic dispatch carry a proof dictionary, rely on a sidecar theorem for
  the vtable, or elaborate through another mechanism?
- How do auto traits and compiler-generated implementations participate?
- Can an implementation assume other property-kind obligations while proving
  its own, and how are cycles certified?

The answer must prevent an implementation from entering verified code without
its declared obligations while avoiding repeated proofs at every generic use.

## Specification adequacy and evolution

Lean can prove a weak or vacuous proposition. For non-axiomatic soundness
specifications, Anneal must connect generated obligations to modeled primitive
semantics strongly enough to guarantee adequacy; human review alone is not the
end state. How it does so is open.

For user-defined properties, specification intent ultimately comes from the
user. Anneal can still help by detecting unused clauses, vacuous implications,
inconsistent assumptions, or contracts that do not cover executions, but such
checks do not create an external ground truth.

Contracts also need an evolution story:

- What changes are compatible for downstream proofs?
- Can implementation details and Aeneas-generated names remain hidden behind a
  stable verification interface?
- How are property-kind dependencies versioned?
- Can automated proof repair absorb small Rust refactorings without concealing
  a semantic contract change?

## Evaluation criteria and examples

A viable design must preserve safe Rust's soundness promise, enforce every
declared implementation obligation, expose exactly the facts a caller may use,
respect resource semantics, and compose across generics and crates.

Representative experiments should cover:

- a safe API around a raw-pointer representation;
- a safe function with a conditional functional guarantee but no caller
  soundness obligation;
- a type whose field invariant is temporarily broken and restored;
- an unsafe trait with generic and dynamically dispatched consumers;
- a trait invariant for a property other than soundness; and
- mutually dependent type, trait, and callee properties.

Proof surface and diagnostics are discussed in
[proof authoring and user experience](proof-authoring-and-user-experience.md).
