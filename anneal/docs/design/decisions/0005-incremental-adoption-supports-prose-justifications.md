<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# 0005: Incremental adoption supports prose justifications

- **Status:** Accepted
- **Date:** 2026-07-17

## Context

Real Rust codebases already justify unsafe operations with prose such as
`// SAFETY:` comments. Requiring every relevant obligation to be formalized and
proved before Anneal provides any value would make adoption all-or-nothing.
Conversely, silently treating prose as a machine proof would make Anneal's
assurance misleading.

The relationship between Anneal property tracking and Rust's existing `unsafe`
machinery remains an open design question, but incremental adoption is a
requirement under either architecture.

## Decision

Anneal must support an incremental-adoption mechanism in which selected formal
proof obligations may temporarily be represented by prose safety
justifications.

Every such substitution is an explicit, auditable trust assumption. Anneal
must not report or consume it as if it were a completed machine-checked proof,
and a user must be able to discover it when evaluating the resulting assurance.

This record requires the capability; it does not decide its syntax, which
obligations may use it, or the success semantics of a command that encounters
one.

## Rationale

Incremental adoption lets users formalize high-value portions of an existing
codebase without first rewriting every safety comment. Making the remaining
human reasoning explicit preserves honest claims and provides a measurable path
toward a fully formal result.

## Consequences

- Anneal needs a durable association between a prose justification and the
  obligation it stands in for.
- Trust reports must expose which obligations rely on prose rather than a
  completed proof; how the final ledger categorizes those assumptions remains
  open.
- Results containing prose justifications are conditional on their correctness.
- Tooling should make it possible to find and reduce the remaining prose
  obligations over time.
- Integration with familiar Rust comments is possible but not mandated by this
  record.

## Alternatives considered

### Require complete formalization before running Anneal

This gives a simple final state but does not support the required path for
adopting Anneal in an existing codebase.

### Treat every unproved obligation as an unrestricted axiom

This loses the connection to the relevant Rust operation and obscures the
different reasons that facts remain trusted.

### Silently skip obligations without proofs

That would make success impossible to interpret and would violate the need for
an auditable trust boundary.

## Deferred questions

- What syntax associates prose with an Anneal obligation?
- Which obligations may use prose and under which command or policy?
- Does a result with prose assumptions exit successfully as “conditionally
  checked,” or use another status distinct from “verified”?
- How are review, ownership, expiry, and migration of prose assumptions tracked?
- How should this mechanism build on Rust `unsafe` blocks, safety comments,
  lints, and possible future language features?

## Evidence

- The project author required some form of prose safety justification to stand
  in for selected Anneal proofs during incremental adoption.
- Existing Rust practice already locates human safety arguments near unsafe
  operations, providing a migration source even though prose is not itself a
  proof.

## Links

- [The TCB is explicit and shrinkable](0006-the-tcb-is-explicit-and-shrinkable.md)
- [Trust and incremental adoption](../open-questions/trust-and-incremental-adoption.md)
- [Rust safety integration](../open-questions/rust-safety-integration.md)
