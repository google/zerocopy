<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Integration with Rust's safety machinery

**Status:** Open design discussion.

Rust has a familiar, compiler-enforced vocabulary for `unsafe fn`, `unsafe`
blocks, and unsafe traits. As of this page's 2026-07-17 review, unsafe fields
were under development upstream; that status is volatile and must be rechecked
before it becomes an implementation premise. Rust also has ecosystem
conventions and lints around `# Safety` documentation and `// SAFETY:` comments.
That machinery tracks only one undifferentiated notion of safety, while Anneal
must support multiple property kinds and stronger proof obligations. V2 must
decide where to extend Rust's system and where to create an Anneal-owned system
alongside it.

## Settled constraints

| Authority | Constraint on this question |
| --- | --- |
| [ANNEAL-REQ-001](../settled-requirements.md#anneal-req-001-v2-is-a-clean-room-redesign), [decision 0001](../decisions/0001-v2-is-a-clean-room-redesign.md) | V1 syntax and its mapping to Rust `unsafe` are evidence, not defaults. |
| [ANNEAL-REQ-005](../settled-requirements.md#anneal-req-005-soundness-is-foundational) | Soundness remains mandatory under every integration strategy. |
| [ANNEAL-REQ-014](../settled-requirements.md#anneal-req-014-type-invariants-support-arbitrary-property-kinds), [ANNEAL-REQ-015](../settled-requirements.md#anneal-req-015-trait-invariants-support-arbitrary-property-kinds), [decision 0004](../decisions/0004-invariants-support-all-property-kinds.md) | Type and trait invariants are required and must support arbitrary property kinds. |
| [ANNEAL-REQ-016](../settled-requirements.md#anneal-req-016-contracts-distinguish-semantic-roles) | Rust's single safety axis cannot erase distinctions among Anneal obligation roles. |
| [ANNEAL-REQ-022](../settled-requirements.md#anneal-req-022-incremental-adoption-supports-prose), [decision 0005](../decisions/0005-incremental-adoption-supports-prose-justifications.md) | Selected formal obligations may be replaced temporarily by explicit, audited prose justifications. |
| [ANNEAL-REQ-026](../settled-requirements.md#anneal-req-026-upstream-evolution-is-in-scope) | Rust language and specification evolution is in long-term scope. |

Topic-specific implications:

- A safe Rust API must remain sound for every type-checked safe use, even when
  its implementation uses unsafe code or Anneal tracks additional properties.
- Type invariants cannot be omitted because V1's mechanism was unsound, and V2
  need not wait for unsafe fields: Rust support and Anneal-specific analysis
  are both candidates.
- Rust's existing unsafe boundaries offer familiar enforcement and migration
  points, while arbitrary property kinds may require Anneal-owned scopes. The
  balance between those systems remains the question being decided.

## The central choice

At one end of the design space, Anneal could map formal soundness obligations
closely onto Rust's existing unsafe boundaries. This would reuse compiler
checks, programmer expectations, documentation conventions, Clippy lints, and
incremental workflows. A Rust `unsafe` block could be the place where either a
formal proof or an audited prose justification discharges an obligation.

At the other end, Anneal could maintain a richer parallel system. It could
track separately named property kinds, require proof around operations Rust
does not mark unsafe, and support type invariants before unsafe fields
stabilize. This avoids forcing concepts such as panic freedom or cryptographic
correctness into Rust's single `unsafe` bit.

A hybrid is plausible: use Rust boundaries as authoritative evidence for some
soundness obligations while layering general property tracking and additional
invariant-sensitive operations on compiler-resolved program facts. The exact
division, reconciliation rules, and user vocabulary remain open.

## Questions to resolve

### Which Rust constructs carry Anneal meaning?

- Does every `unsafe` operation generate an Anneal soundness obligation, or do
  obligations attach only to unsafe leaves with modeled semantic guards?
- Is an `unsafe` block evidence of the intended proof scope, a syntactic place
  to write a proof, or merely a Rust type-checking construct?
- How are unsafe functions whose callers provide prose `# Safety` contracts
  related to machine-readable Anneal contracts?
- Can an operation be safe under Rust's soundness axis but guarded under another
  Anneal property kind? If so, what source construct marks it?
- How should unsafe traits and future language features interact with Anneal's
  trait invariants?

Rust's `unsafe` syntax identifies responsibility boundaries; it does not by
itself fully state the semantic preconditions that make an operation sound.
Any design that reuses the syntax still needs an adequate specification of
those preconditions. See [source/model adequacy](source-model-adequacy.md).

### How are property kinds spelled?

A hypothetical Rust feature such as `unsafe(soundness)` or
`unsafe(panic_freedom)` illustrates the desired distinction, but does not exist.
V2 must decide whether annotations:

- name property kinds independently of Rust syntax;
- decorate existing unsafe functions, blocks, traits, and fields;
- introduce Anneal-specific proof scopes for operations that Rust considers
  safe; or
- combine these approaches and require exact reconciliation.

The answer must work for user-defined kinds without requiring a Rust language
change for each new domain. It must also avoid implying that a caller may
violate the soundness of a safe Rust API merely because no Anneal property was
selected.

### How are type invariants protected?

V1's `isValid` concept demonstrated the usefulness of type invariants but did
not prevent safe code from mutating fields without re-establishing them. V2
needs an enforcement boundary. Candidate mechanisms include:

- Rust unsafe fields, once their exact semantics are usable;
- Anneal analysis that marks reads, writes, borrows, moves, construction, and
  destruction of invariant-carrying representation as proof-requiring;
- module or constructor boundaries;
- explicit invariant-opening and invariant-closing operations;
- refinement wrappers whose representation cannot be accessed directly; and
- combinations of these for different kinds of invariant.

The design must account for pattern matching, field projection, mutable and
shared borrowing, interior mutability, destructuring assignment, unions,
layout operations, drop, and code generated by macros. It must say when an
invariant may be temporarily broken, who owns the capability to restore it,
and how resource-sensitive facts are consumed. See
[contracts and invariants](contracts-and-invariants.md) and
[memory, resources, and effects](memory-resources-and-effects.md).

### How does prose coexist with proofs?

Some version of prose-based discharge is required for incremental adoption.
Open choices include:

- whether an existing `// SAFETY:` comment is enough or must carry an explicit
  Anneal marker;
- whether comments discharge individual call-site obligations, whole unsafe
  blocks, or selected subtrees;
- which property kinds may use prose;
- whether prose is recorded as an axiom, an incomplete proof, or a distinct
  audited status;
- whether Anneal checks that every Rust unsafe boundary has either proof or
  prose, even when only part of a crate is formally adopted; and
- how later tooling helps replace prose with proofs without changing the Rust
  code's structure.

Prose can mark a trust gap; it cannot silently supply a machine-checked theorem.
The command and ledger semantics are discussed in
[trust and incremental adoption](trust-and-incremental-adoption.md).

## Evaluation criteria

Compare candidate integrations by asking:

1. Does safe Rust retain its unconditional soundness promise?
2. Can the system express independent and dependent property kinds without
   abusing Rust's single safety axis?
3. Can every invariant-sensitive operation be found in expanded,
   compiler-resolved code, including generated code?
4. Is responsibility visible and familiar enough for Rust engineers to review?
5. Can a project adopt Anneal gradually without disguising trust gaps?
6. Does the design continue to work if Rust gains unsafe fields or richer
   safety annotations?
7. Can the implementation fail closed when Rust and Anneal views disagree?

Useful prototypes should include an invariant-carrying type before unsafe
fields, a crate mixing formal proofs and `// SAFETY:` comments, and a
property other than soundness attached to an operation Rust considers safe. The
compiler metadata needed for those experiments is covered in
[Aeneas and Charon integration](aeneas-charon-integration.md).
