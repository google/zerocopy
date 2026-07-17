<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Settled requirements

These requirements record constraints that have been unambiguously accepted
for Anneal V2. They deliberately avoid choosing among implementations still
under discussion. Stable identifiers allow code, decisions, and open questions
to refer to the requirement they serve. They are an atomic registry, not a
second explanation of the design philosophy: use the
[design principles](principles.md) to understand why these constraints matter
and the linked design documents for their canonical elaboration.

## Project scope

### ANNEAL-REQ-001: V2 is a clean-room redesign

V2 must be designed from its goals and current evidence rather than inheriting
V1 by default. V1 code and ideas may be reused deliberately. Their existence is
not evidence that V2 should preserve them.

See [decision 0001](decisions/0001-v2-is-a-clean-room-redesign.md).

### ANNEAL-REQ-002: General properties

The long-term architecture must support arbitrarily complex, user-defined
correctness properties. It must not encode an assumption that soundness is the
only property worth verifying.

### ANNEAL-REQ-003: General Rust use cases

The long-term architecture must be capable of covering arbitrary Rust
codebases and use cases. Initial milestones may support a strict subset, but
the architecture must not require unsafe-heavy domains to abandon their
essential memory, concurrency, or external-effect semantics.

### ANNEAL-REQ-004: Extensibility before breadth

Initial V2 need not ship specialized backends for deadlock freedom,
hyperproperties, cryptographic correctness, quantitative bounds,
probabilistic properties, or every other anticipated domain. It must leave a
path to add such domains without redesigning the core composition model.

## Soundness and semantic fidelity

### ANNEAL-REQ-005: Soundness is foundational

Anneal must treat Rust soundness as a non-optional foundation of a faithful
verification result. Selecting another property kind must not silently disable
the soundness assumptions on which source-to-model correspondence depends.

### ANNEAL-REQ-006: Soundness specifications produce adequate obligations

For every non-axiomatic source of Rust soundness requirements, Anneal must
derive obligations sufficient for the supported semantics. In particular, the
specification of a primitive operation must impose the actual conditions
needed for its sound use. A weak, incomplete, or vacuous user contract must not
be able to erase those conditions.

This is **obligation adequacy**: it concerns whether the generated obligation
is the right one. The separate coverage requirement
[ANNEAL-REQ-019](#anneal-req-019-coverage-adequacy-is-enforced) concerns
whether every relevant operation actually receives and discharges such an
obligation. How Anneal establishes either property is open; see
[source/model adequacy](open-questions/source-model-adequacy.md).

### ANNEAL-REQ-007: The memory model is conservative

Any Anneal-owned abstraction of Rust memory and unsafe operations must be a
conservative formalization of the normative guarantees Anneal claims to
support, not merely an undocumented set of convenient assumptions. Ambiguous
prose in Rust's specifications must be surfaced, resolved with the relevant
Rust teams where possible, and recorded as an assumption until resolved.

### ANNEAL-REQ-008: Resource semantics are preserved

Lifting separation-logic assertions, ownership, provenance, initialization, or
protocol state into Lean must preserve their usage discipline. Such resources
must not become freely reusable ordinary facts when that would invalidate the
reported claim. In particular, simplifying their use may not compromise
soundness.

## Local and global verification

### ANNEAL-REQ-009: Local contract obligations

Locally, verification must establish that an item's preconditions imply its
applicable guarantees and that every invocation satisfies the required
preconditions or properties of its callees.

The exact treatment of normal return, panic, unwind, abort, and divergence is
open; this requirement does not imply that every verified item terminates
normally.

### ANNEAL-REQ-010: Local results compose globally

Local obligations must compose into a whole-artifact guarantee relative to an
explicit set of trusted leaves and environmental assumptions. A caller must not
need to re-verify the private body of a callee whose contract has been
established.

### ANNEAL-REQ-011: Long-running and exceptional behavior

The verification model must be able to express and justify:

- a server that executes without bound while preserving invariants;
- code that remains sound while panicking;
- unwind cleanup relevant to soundness; and
- code that catches a panic and continues execution.

Anneal must not equate successful verification with normal termination in all
cases.

### ANNEAL-REQ-012: Property dependencies

Property kinds may depend on one another. All supported properties ultimately
depend on soundness, and a soundness obligation may itself rely on a declared
guarantee of another property kind. For example, a callee's functional
guarantee that an index is in bounds may discharge a caller's raw-pointer
soundness obligation. The architecture must not isolate each property kind in
a universe that cannot express these dependencies.

“Ultimately depend on soundness” describes the semantic basis needed to
interpret model theorems as claims about Rust; it does not impose an acyclic
proof order in which soundness is always established first. Mutually dependent
obligations must be discharged jointly or by another sound treatment of
cycles. The representation and proof mechanism remain open.

### ANNEAL-REQ-013: Property selection

Users must eventually be able to choose which non-foundational property kinds
are enforced by a `cargo anneal verify` invocation. Dependency closure,
reporting, command modes, and handling of excluded dependencies remain open.

## Contracts and invariants

### ANNEAL-REQ-014: Type invariants support arbitrary property kinds

V2 must support invariants associated with types, and those invariants must not
be limited to soundness. The V1 `isValid` mechanism is not an acceptable
implementation because safe field mutation could bypass invariant
re-establishment.

V2 may build on Rust unsafe fields, perform its own field-access and mutation
analysis, or use another sound mechanism. It need not wait for unsafe fields to
stabilize.

### ANNEAL-REQ-015: Trait invariants support arbitrary property kinds

V2 must support invariants associated with traits for arbitrary property
kinds. It must enforce the invariant at the implementation site and make the
established invariant available where the corresponding trait bound is known.

The V1 spelling `isSafe` is not a commitment to syntax or to a soundness-only
meaning.

### ANNEAL-REQ-016: Contracts distinguish semantic roles

The architecture must be capable of distinguishing a caller obligation needed
for Rust soundness from an ordinary functional-domain precondition and from
obligations of other property kinds. Rust's single `unsafe` axis does not erase
these semantic differences, even if V2 initially maps several of them onto
existing Rust syntax.

## Artifact and translation boundary

### ANNEAL-REQ-017: Initial claims are artifact-scoped

The initial unit of verification is one Cargo compilation artifact with fixed
target, features, `cfg` values, dependencies, panic strategy, generated code,
and relevant environment. A claim across a build matrix requires multiple
artifact claims or future quantified support.

See [decision 0002](decisions/0002-verification-is-artifact-scoped.md).
The subject and result identities are elaborated in
[result and trust](result-and-trust.md).

### ANNEAL-REQ-018: Generated Rust is analyzed input

Rust code produced by proc macros and build machinery and subsequently ingested
by Charon must be treated as part of the artifact being analyzed, rather than
trusted merely because a generator produced it. This does not by itself settle
how to model every non-Rust effect of a build script.

See [decision 0003](decisions/0003-expanded-generated-rust-is-input.md).

### ANNEAL-REQ-019: Coverage adequacy is enforced

Anneal must ensure that every potentially invalid source operation in the
reported coverage envelope is guarded by the obligations needed to justify
the model used for its proof. An operation, path, or relevant generated item
must not disappear from coverage merely because the obligation generator,
translator, or proof interface failed to represent it.

This is **coverage adequacy**: it concerns complete application of obligations
whose semantic content is governed by
[ANNEAL-REQ-006](#anneal-req-006-soundness-specifications-produce-adequate-obligations).
The encoding and enforcement mechanism remain open; see
[source/model adequacy](open-questions/source-model-adequacy.md).

## Trust and adoption

### ANNEAL-REQ-020: The TCB is explicit and shrinkable

V2 may rely on a small set of trusted leaves, but they must be explicit,
auditable, and replaceable by deeper models over time. Near-term examples may
include unsafe standard-library leaves, intrinsics, raw-pointer operations,
FFI, and assembly.

See [decision 0006](decisions/0006-the-tcb-is-explicit-and-shrinkable.md).
The program-semantic leaf boundary and the broader end-to-end TCB are
distinguished in [result and trust](result-and-trust.md).

### ANNEAL-REQ-021: Results carry an audit ledger

Users must be able to determine what remains trusted or incomplete. The ledger
must identify the exact subject and claim, checked evidence, residual
dependencies, coverage limits, relevant toolchain, and host and target
assumptions. The canonical minimum inventory is maintained in
[result and trust](result-and-trust.md#audit-ledger); the exact schema and
presentation remain open.

### ANNEAL-REQ-022: Incremental adoption supports prose

Some form of existing prose safety justification must be able to stand in for
selected Anneal proofs during incremental adoption. Such a justification is
not a machine-checked proof and must be identifiable in the audit ledger.

See [decision 0005](decisions/0005-incremental-adoption-supports-prose-justifications.md).
Its evidence classification is defined in
[result and trust](result-and-trust.md#evidence-and-residual-dependencies).

### ANNEAL-REQ-023: Axioms cover genuine external semantics

In a fully adopted codebase, axioms should be reserved for genuine semantic
boundaries. Anneal's own standard library will likely use the same facility to
specify primitive unsafe operations, and FFI will likely require user- or
library-authored axioms for the foreseeable future. Who should author and
distribute FFI specifications remains open.

### ANNEAL-REQ-024: Incompleteness is distinguishable from external trust

The design must be able to report a proof that is not yet completed separately
from a specification intentionally taken as axiomatic. It is open whether this
uses a first-class incomplete-proof mechanism, command profiles, Lean `sorry`,
or another representation.

## Ecosystem and usability

### ANNEAL-REQ-025: Existing proof machinery is preferred

V2 should build on suitable abstractions maintained by Lean, Aeneas, and their
standard libraries, including WP specifications and tactics, unless a concrete
benefit justifies replacement. This is a strong engineering preference rather
than a prohibition on new machinery.

### ANNEAL-REQ-026: Upstream evolution is in scope

Changes or additions to Aeneas and Charon are in scope. In the longer term,
Rust language and specification changes are also in scope. Short-term
implementation constraints must not be documented as permanent project
philosophy.

### ANNEAL-REQ-027: Ordinary Rust engineers are a target audience

The eventual workflow must be usable in normal Rust organizations, including
by engineers without formal-methods specialization. Human and AI assistance,
diagnostics, stable proof interfaces, and gradual adoption may all contribute;
none may weaken the meaning or auditability of a successful result.
