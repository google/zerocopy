<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# 0004: Invariants support all property kinds

- **Status:** Accepted
- **Date:** 2026-07-17

## Context

V1 explored type invariants under the name `isValid` and trait invariants under
the name `isSafe`. Those names suggest that one mechanism concerns validity and
the other concerns soundness. V2 must support soundness, but users also need
invariants for other properties: panic freedom, protocol correctness,
cryptographic conditions, resource bounds, and domains not designed yet.

The exact taxonomy and notation for property kinds remain open.

## Decision

Both type invariants and trait invariants must support arbitrary property kinds.
Neither mechanism is intrinsically restricted to soundness or to one built-in
notion of safety.

Soundness remains special and non-negotiable. Generalizing invariant mechanisms
does not permit a selected non-soundness property to weaken, replace, or bypass
the obligations required for sound Rust.

## Rationale

Types and trait bounds are important abstraction boundaries regardless of the
property being composed. A common architecture avoids duplicating an invariant
system for every domain and leaves V2 extensible to properties whose proof
backends arrive later. Preserving soundness as a mandatory foundation keeps
extensibility from weakening the primary assurance.

## Consequences

- V2's invariant representation cannot hard-code type invariants as “validity”
  or trait invariants as “soundness.”
- Implementations and consumers need a way to identify which property an
  invariant establishes or assumes.
- Adding a new property domain must not require replacing the type- or trait-
  invariant architecture.
- Initial V2 need not implement specialized proof backends for every possible
  property kind; the architecture must leave room for them.
- The V1 names and enforcement mechanisms are not accepted by this decision.

## Alternatives considered

### Restrict both invariant forms to soundness

This would require parallel mechanisms to express the same abstraction pattern
for other correctness properties.

### Reserve type invariants for validity and trait invariants for soundness

The distinction follows V1 terminology rather than a fundamental difference in
where property-carrying invariants are useful.

### Defer extensibility until another property backend exists

That risks embedding soundness-specific assumptions in interfaces which are
difficult to generalize later.

## Deferred questions

- What are property kinds called and how are they declared or selected?
- How are type invariants established, invalidated, opened, and re-established?
- How are trait invariants enforced at implementation sites and made available
  through a bound?
- How does Anneal integrate invariant access with Rust's existing `unsafe`
  machinery or an Anneal-specific parallel analysis?
- How are dependencies and cycles between property kinds represented?
- What should replace the V1 `isValid` and `isSafe` syntax?

## Evidence

- The project author explicitly required both type invariants and trait
  invariants to support arbitrary property kinds.
- Experience with V1 showed that its names and partial enforcement did not
  express this general architecture; see [V1 lessons](../../history/v1-lessons.md).

## Links

- [Contracts and invariants](../open-questions/contracts-and-invariants.md)
- [Property kinds and outcomes](../open-questions/property-kinds-and-outcomes.md)
- [Rust safety integration](../open-questions/rust-safety-integration.md)
- [Design principles](../principles.md)

