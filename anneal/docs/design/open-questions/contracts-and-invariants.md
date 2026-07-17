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

- Locally, a verified function establishes the applicable relationship between
  its preconditions and postconditions and establishes the required
  preconditions of every callee.
- Globally, these local obligations compose into soundness and other selected
  properties once dependencies and trusted leaves are accounted for.
- Soundness specifications for primitive unsafe leaves have an external ground
  truth in Rust's semantics. Anneal is responsible for making those
  specifications adequate, subject to explicit trusted foundations.
- A user-defined correctness axiom expresses the property the user intends.
  Anneal must track and enforce it, but cannot determine whether the user chose
  the “right” cryptographic, protocol, or functional requirement.
- Type invariants and trait invariants are both required and must both support
  arbitrary property kinds.
- A trait invariant must be proved at the implementation site and be available
  as a consumable fact wherever the corresponding trait bound is known.
- A type invariant must remain protected across all operations that can expose
  or mutate the representation. V1 did not enforce this and is not a sound
  template.
- A safe Rust API cannot impose an extra caller obligation whose violation
  permits undefined behavior. Every type-checked safe use must remain sound.
  Safe functions may still have ordinary functional contracts whose violation
  changes which functional result is promised.
- Annotation and proof syntax are entirely open. The V1 names `isValid` and
  `isSafe`, and V1's indentation-sensitive doc-comment blocks, are not V2
  commitments.

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
- a trait invariant for a non-soundness property; and
- mutually dependent type, trait, and callee properties.

Proof surface and diagnostics are discussed in
[proof authoring and user experience](proof-authoring-and-user-experience.md).
