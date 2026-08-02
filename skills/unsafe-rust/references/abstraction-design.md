# Designing Unsafe Abstractions for Provability

## Contents

- [Keep verification and design separate](#keep-verification-and-design-separate)
- [Establish design requirements](#establish-design-requirements)
- [Extract the minimum capability](#extract-the-minimum-capability)
- [Generate proof-oriented candidates](#generate-proof-oriented-candidates)
- [Prove and compare candidates](#prove-and-compare-candidates)
- [Report the result](#report-the-result)

## Keep Verification and Design Separate

Use this process when the user asks to design or redesign an unsafe abstraction,
or when authoring a new unsafe abstraction. Do not run it automatically during
an immutable acceptance audit unless the user requests design advice.

Judge existing code under its exact current source and controlling contracts.
Inferred intent, a proposed narrower contract, or an easier-to-prove
representation may not:

- reinterpret or weaken a current obligation;
- discharge a premise of the current implementation;
- erase or downgrade a current finding; or
- justify accepting the current artifact.

Keep conclusions about the current artifact logically independent of every
candidate design. A proposal describes a possible future artifact; it has no
`PROVED` verdict. After implementation, identify the new snapshot and apply the
ordinary unsafe-Rust proof workflow anew.

Preserve at least the scoped current finding that motivates the redesign. Do
not expand that step into a whole-crate audit unless the requested audit scope
requires it.

For greenfield work, no current-artifact verdict is necessary. State the design
requirements, construct the candidate, and prove the implemented artifact.

## Establish Design Requirements

Record the constraints that the abstraction must satisfy:

- required externally observable behavior and mandatory postconditions;
- current public contracts and compatibility commitments that must remain;
- exact propositions required by relevant consumers;
- supported Rust versions, targets, features, and configurations;
- representation, performance, interoperability, or integration constraints;
  and
- which semantic or compatibility changes the user has authorized.

Use each source only for the proposition it actually establishes. User
requirements can determine desired behavior. Current contracts determine
current obligations. Call sites, tests, names, comments, history, and
implementation structure may suggest intent or establish literal artifact
facts, but an inference about intent is not a Rust semantic premise and does
not prove implementation correctness.

Known internal consumers do not exhaust the consumers of a public API. Treat
the published contract as a required constraint unless an applicable contract
channel and the user authorize changing it. Surface material ambiguity when
different interpretations would change the public contract, support policy, or
compatibility result.

## Extract the Minimum Capability

For each required behavior, state the exact semantic proposition consumers
need. Separate properties that the current abstraction may have bundled, such
as:

- nominal identity from an operational capability;
- layout from validity, initialization, provenance, alignment, or aliasing;
- metadata from memory projection;
- ownership from access permission;
- one-time establishment from an ongoing invariant;
- safe caller behavior from an unsafe implementer promise; and
- behavior common to many types from one exceptional case.

Identify where each proposition is established, carried, consumed, and
discharged. Prefer a design in which types, validation, privacy, sealing,
typestate, guards, or other locally checkable mechanisms enforce the fact.

Do not make a proof easier merely by transferring an unnecessary or hidden
obligation to callers. Every remaining unsafe caller or implementer obligation
must be explicit, sufficient, and justified by a need the implementation cannot
enforce safely.

## Generate Proof-Oriented Candidates

Consider the smallest transformations that remove the unsupported premise:

- eliminate an unnecessary unsafe operation, impl, configuration, or promise;
- validate the required property before the unsafe operation;
- narrow an API or implementation to the cases actually supported;
- reuse a safe or already-proved primitive whose contract matches exactly;
- specialize a one-off case instead of inventing a generic abstraction;
- split independent capabilities or invariant dimensions;
- seal an implementer boundary or move representation behind a smaller module;
  or
- introduce a new reusable abstraction only when demonstrated consumers share
  the same semantic capability.

For example, if one contract claims both nominal field reflection and pointer
projection while some consumers require only projection, consider separating
those capabilities rather than inventing a nominal field. This is a design
prompt, not a Rust fact; prove the resulting contracts normally.

Do not pad the output with cosmetic or strictly dominated alternatives. When
requirements are ambiguous or viable candidates make materially incomparable
tradeoffs, present the consequential choice instead of choosing silently.

## Prove and Compare Candidates

For each viable candidate, state:

- exact safe and unsafe contracts;
- representation and named invariants;
- how every required consumer proposition is supplied;
- where each remaining obligation is enforced;
- authoritative axioms, dependency contracts, and TCB entries required;
- supported applicability domain;
- unresolved proof obligations; and
- behavior, compatibility, migration, and re-audit consequences.

Construct a conditional proof plan before implementation. After implementation,
prove the exact source rather than the design sketch.

Reject candidates that fail required behavior, proof closure, supported-domain
coverage, or binding compatibility constraints. Among the remainder, prefer a
candidate that preserves required behavior while reducing one or more of:

- unsafe surface exposed to callers or implementers;
- strength or number of unsupported premises;
- invariant access region, lifetime, and fan-out;
- TCB size;
- coupling between independent capabilities;
- version- or configuration-specific proof branches;
- accidental representation commitments; and
- genericity without demonstrated reuse.

Also account for authorized implementation, performance, and migration costs.
Do not collapse incomparable tradeoffs into an invented score, and do not
prefer a small textual diff that silently weakens a relied-upon contract.

Apply
[Evolve contracts deliberately](api-boundaries-and-evolution.md#evolve-contracts-deliberately)
to every candidate contract change.

## Report the Result

Keep these outputs distinct whenever they apply:

1. **Current artifact:** Exact findings and verdict under the current contract.
2. **Design requirements:** Required behavior, constraints, consumer
   propositions, and unresolved intent.
3. **Candidate design:** Exact proposed contracts, invariant model, proof plan,
   and remaining premises.
4. **Compatibility and migration:** Behavior gained or lost, affected callers
   and implementers, contract channel, and re-audit scope.
5. **Recommendation:** The preferred candidate and any human decision required.
6. **Post-change audit:** A separate result for an implemented new snapshot.

In review-only work, provide counterfactual advice without modifying source. In
authoring work, update implementation, contracts, local proofs, TCB entries,
and affected downstream proofs together.
