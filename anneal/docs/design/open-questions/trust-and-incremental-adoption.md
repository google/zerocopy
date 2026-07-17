<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trust and incremental adoption

**Status:** Open design discussion.

Anneal must be useful before an entire codebase has been modeled, while making
it impossible to confuse a partially trusted result with an end-to-end proof.
It must also support genuinely external semantics that may remain axiomatic for
the foreseeable future. V2 therefore needs first-class accounting for trust,
incompleteness, and adoption state.

## Settled constraints

| Authority | Constraint on this question |
| --- | --- |
| [ANNEAL-REQ-006](../settled-requirements.md#anneal-req-006-soundness-specifications-produce-adequate-obligations) | Non-axiomatic soundness specifications require machine-enforced adequacy rather than human intent alone. |
| [ANNEAL-REQ-017](../settled-requirements.md#anneal-req-017-initial-claims-are-artifact-scoped), [decision 0002](../decisions/0002-verification-is-artifact-scoped.md) | Trust and incompleteness qualify a result about one precisely identified compilation subject. |
| [ANNEAL-REQ-020](../settled-requirements.md#anneal-req-020-the-tcb-is-explicit-and-shrinkable), [decision 0006](../decisions/0006-the-tcb-is-explicit-and-shrinkable.md) | Trusted semantic leaves and the broader end-to-end TCB must be explicit and replaceable by deeper models. |
| [ANNEAL-REQ-021](../settled-requirements.md#anneal-req-021-results-carry-an-audit-ledger) | Every result must expose its exact claim, dependencies, trust, incompleteness, coverage, toolchain, environment, and hardware assumptions. |
| [ANNEAL-REQ-022](../settled-requirements.md#anneal-req-022-incremental-adoption-supports-prose), [decision 0005](../decisions/0005-incremental-adoption-supports-prose-justifications.md) | Selected obligations may temporarily rely on prose, but that reliance is an explicit residual dependency rather than a completed proof. |
| [ANNEAL-REQ-023](../settled-requirements.md#anneal-req-023-axioms-cover-genuine-external-semantics) | Fully adopted code should reserve axioms for genuine semantic boundaries; standard-library primitives and FFI remain important expected uses. |
| [ANNEAL-REQ-024](../settled-requirements.md#anneal-req-024-incompleteness-is-distinguishable-from-external-trust) | An intended but unfinished proof must remain distinguishable from an intentionally axiomatic specification. |

Topic-specific implications:

- A result containing residual dependencies must identify their kind, origin,
  and affected claim. When a dependency has a known path to stronger evidence,
  the ledger should expose it; a successful exit code cannot erase the
  dependency.
- The meaning of a user-defined property comes from the user; any unproved
  proposition assumed about it remains a residual dependency. Anneal enforces
  and reports that assumption but cannot validate the intended meaning. This
  differs from responsibility for the adequacy of primitive soundness guards.
- Command statuses, policy profiles, ledger schema, and authorship or
  distribution of external specifications remain open.

## Distinct forms of trust and incompleteness

V2 should not assume that all missing proofs mean the same thing. At minimum,
the design must evaluate distinctions among:

- an axiom representing genuinely external semantics;
- a primitive-semantic assumption, with its actual origin and owner;
- a specification whose proof is intended but not complete;
- a call site temporarily justified by a prose `// SAFETY:` explanation;
- source or generated code intentionally outside the adoption scope;
- a construct whose body is deliberately omitted, or an unsupported construct;
- an admitted Lean theorem or equivalent escape hatch;
- a compiler, translator, kernel, runtime, or hardware assumption; and
- a model/tool failure that prevents any defensible claim.

These may share implementation machinery, but users need to know why each item
is trusted, who owns it, what it affects, and whether a path to stronger
evidence is known.

## Questions to resolve

### What does command success mean?

Candidate policies include:

- `cargo anneal verify` fails on every incomplete proof but permits explicitly
  approved axioms with a ledger;
- a separate incremental profile succeeds with a clearly conditional status;
- one command returns structured assurance grades and uses configurable exit
  policy; or
- distinct commands separate end-to-end verification from partial checking.

The design must avoid a state in which users or CI interpret “success” as a
stronger claim than the artifact supports. Open details include:

- whether unrequested property kinds appear as gaps;
- whether a deliberately excluded dependency is an error or audited
  assumption;
- how policy changes affect reproducibility;
- whether CI can impose a budget or allowlist for trust gaps; and
- what downstream crates may rely on from a partially verified dependency.

### How are incomplete proofs represented?

An explicit “specification present, proof incomplete” status may be preferable
to encoding incremental work as an axiom. It is analogous in purpose to Lean's
`sorry`, but V2 need not expose that mechanism directly.

Questions include:

- Is incompleteness attached to a theorem, obligation, source region, property
  kind, or artifact?
- Does it preserve the intended specification for callers while marking its
  proof as trusted?
- Can a project prohibit new gaps while grandfathering existing ones?
- Does each gap have an owner, rationale, expiration, or issue link?
- How are transitive gaps summarized without losing their origin?
- Can a proof later replace the gap without changing the public verification
  interface?

### How do prose justifications work?

Prose support is required, but its semantics are open. It could be represented
as a specialized admitted obligation associated with a Rust unsafe boundary,
or as a separate trust category with Rust-oriented diagnostics.

We need to decide:

- which comments Anneal recognizes and how they bind to exact compiler-resolved
  operations;
- whether prose is allowed only for soundness or for arbitrary property kinds;
- whether the text is included verbatim or hashed in the ledger;
- whether ordinary Rust linting conventions are reused;
- what happens when code moves and a comment no longer binds unambiguously; and
- how the tool guides conversion from prose to a machine proof.

This intersects with [Rust safety integration](rust-safety-integration.md).

### Who authors and distributes external specifications?

For FFI and platform APIs, the specification might be authored by:

- each Rust consumer;
- the C, C++, assembly, or platform library author;
- an Anneal standard-library or ecosystem package; or
- a third-party verification authority.

V2 needs identities, versioning, target constraints, and a way to distinguish a
widely reviewed specification from a local assertion without turning social
trust into a misleading proof claim. Specifications may eventually be backed
by proofs in another system or by a formal ISA model.

### What exactly is in the ledger?

The canonical minimum inventory is defined in
[result and trust](../result-and-trust.md#audit-ledger). The remaining questions
concern representation and policy: exact field schema and granularity, stable
identities, normalization and reproducibility, serialization, signing, diff
format, retention and privacy, and the relationship between a machine-readable
artifact and a useful human audit view.

## Evaluation criteria

An acceptable design must be fail-closed about unsupported semantics, preserve
the difference between proof and trust, support useful incremental adoption,
and make transitive assumptions visible. It should reward shrinking the TCB,
allow external models to replace axioms, and produce stable artifacts suitable
for code review and CI policy.

Useful experiments include a crate with one prose-justified call, a dependency
with an incomplete functional proof, an FFI binding with target-specific
axioms, and the same code verified under two compiler or hardware assumptions.
The source coverage needed to populate the ledger is discussed in
[source/model adequacy](source-model-adequacy.md).
