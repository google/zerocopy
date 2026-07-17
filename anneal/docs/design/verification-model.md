<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Verification model

This document describes how Anneal derives a verification result. It does not
choose an annotation syntax, outcome taxonomy, Lean encoding, command mode, or
report format. Subject and result identity, evidence statuses, trust
boundaries, and the canonical audit-ledger contents are defined in
[result and trust](result-and-trust.md).

The high-level derivation is:

```text
identified Rust subject
+ requested claim dimensions
+ evaluated evidence graph with classified leaves
= reported result stating the established claim and remaining gaps
```

Each term matters. Evidence about an unidentified program is not reproducible.
A theorem without a precise requested claim invites overinterpretation. Local
proofs without an evaluated evidence graph do not establish a global result.
Each leaf must be classified as checked evidence, an admissible assumption, a
coverage limit, or a blocking gap or failure; otherwise an axiom, omitted
operation, or unfinished proof disappears into hidden trust. The reported
result states which claim was actually established, any explicit conditions
on it, and why each residual dependency remains.

The [worked byte-buffer example](worked-example.md) illustrates this model
without ratifying a concrete proof architecture.

## Subject and claim

Anneal initially verifies one concrete Cargo compilation subject. Generated
Rust ingested by Charon is part of that subject rather than trusted because a
proc macro or build process produced it. The exact target, features, `cfg`
values, dependencies, panic strategy, generated inputs, and relevant
environment delimit the program to which the result applies.

A claim about that subject has several independent dimensions:

- the properties and guarantees asserted, including their dependencies;
- the source behaviors to which those guarantees apply, such as normal return,
  panic and unwind, abort, or divergence;
- the client and coverage envelope, from concrete calls in one artifact to
  every supported safe client of an abstraction; and
- the semantic endpoint, from a theorem about a Lean model through a claim
  about the Rust artifact to execution of a compiled binary on target
  hardware; and
- the explicit conditions on which the claim depends.

These dimensions must not be collapsed into one ladder of “verification
levels.” A source-level soundness result need not establish panic freedom. A
whole-artifact proof of concrete calls need not justify every separately
compiled client. A theorem checked by Lean need not establish a hardware
execution claim without the correspondence and toolchain dependencies needed
to connect them.

The reporting definition and identity of each dimension are maintained in
[result and trust](result-and-trust.md#claim-dimensions). This document
describes the proof structure from which they are derived.

## Local obligations

For an item `f` and a selected property `P`, the schematic local claim is:

1. assume `f`'s applicable preconditions, invariants, capabilities,
   environmental conditions, and already established interface guarantees;
2. show that every call and primitive operation made by `f` satisfies the
   required preconditions and property dependencies of the invoked operation;
   and
3. show that every behavior covered by the claim establishes the applicable
   guarantee of `f`'s contract.

For a normal-return functional contract, this specializes to the familiar
statement that preconditions imply postconditions. It does not imply that all
claims require normal termination. A soundness claim may permit divergence or
a safe panic while requiring every executed prefix and relevant unwind cleanup
to remain sound.

The same shape applies when an interface carries resources or effects, but its
assumptions and guarantees are not necessarily freely reusable propositions.
Ownership, provenance, initialization, permissions, protocol state, or an
opened invariant may need to be consumed, transferred, framed, or
re-established. The local proof interface must retain those rules. Treating a
resource as an ordinary duplicable Lean fact would change the claim rather than
simplify its proof.

Type and trait invariants participate in these local interfaces. A type
invariant must be established and preserved at every relevant operation; a
trait invariant must be established by an implementation and made available
where its trait bound is known. Their concrete enforcement and syntax remain
open in [contracts and invariants](open-questions/contracts-and-invariants.md).

## Global closure

Local results form an evidence graph:

- nodes establish item contracts, invariants, primitive specifications, or
  deeper semantic facts;
- call edges require callers to establish callees' preconditions;
- property-dependency edges allow one guarantee to discharge an obligation of
  another property; and
- leaf edges end either in checked evidence or in an explicitly classified
  residual dependency.

For example, a callee's functional guarantee that an index is below a buffer
length may discharge the soundness precondition of a caller's raw-pointer
access. This does not make soundness optional; the functional theorem is an
edge in the proof that the pointer access remains sound.

An artifact-level claim follows only when every relevant non-leaf node
satisfies its local contract, every required edge is discharged, coverage is
adequate, and each remaining assumption is admissible for and included in the
conditions of that claim. Mutually dependent properties may require joint
reasoning; the graph model does not impose an artificial proof order in which
every soundness theorem must be completed before any other property can
contribute to it.

For Rust soundness, the conditions assigned to primitive unsafe leaves must be
adequate. Anneal is responsible for conditions it provides and must report the
adequacy dependency of any specification it imports. If the conditions are
sufficient for the supported Rust semantics and every use establishes them,
the local results compose into an artifact-level soundness claim relative to
the recorded semantic and environmental dependencies.

Classification alone does not discharge a residual dependency. Its status
determines whether Anneal can establish the requested claim relative to an
admissible assumption, must narrow or condition the claim, or cannot establish
a substantive claim at all. A tool failure supplies no evidence, and some
coverage gaps prevent rather than merely qualify a claim. Command policy may
decide which established conditional results count as success; it may not turn
a missing evidentiary connection into an assumption. See [evidence and residual
dependencies](result-and-trust.md#evidence-and-residual-dependencies).

## Adequacy closes the source/model loop

Anneal intends to use a model that is promised to correspond to sound Rust in
order to prove that the Rust subject is sound. It cannot resolve this apparent
cycle by assuming soundness unchecked.

A source-level soundness result therefore needs both complete, adequate guards
for potentially invalid source operations and a justified correspondence from
the guarded source execution to the proof model. It must not assume the very
whole-program soundness that the guards are intended to establish. The exact
correspondence theorem and proof decomposition remain open.

One candidate is a guarded-prefix argument: establish correspondence before a
first invalid source operation, identify and guard every operation that could
be that first invalid operation, and use checked evidence for those guards to
rule such an operation out. A trace simulation, translation validation, or
another construction may establish the same required connection instead. See
[source/model adequacy](open-questions/source-model-adequacy.md).

Whichever proof family is chosen, two different adequacy requirements are
involved:

- **Obligation adequacy** means that each generated guard expresses the right
  Rust validity conditions. Primitive semantics and other non-axiomatic
  sources of Rust requirements must determine those conditions; a user
  contract cannot weaken them away (ANNEAL-REQ-006 in the
  [settled requirements](settled-requirements.md)).
- **Coverage adequacy** means that every potentially invalid operation in
  scope actually receives such a guard and that missing operations, paths, or
  generated items prevent an unconditional result
  ([ANNEAL-REQ-019](settled-requirements.md#anneal-req-019-coverage-adequacy-is-enforced)).

How the guards and correspondence evidence are encoded, proved, and divided
among rustc, Charon, Aeneas, and Anneal remains open. The semantic requirements
do not choose between Lean proof arguments, sidecar theorems, or another
enforcement mechanism.

Specification adequacy differs for a property whose meaning is supplied by the
user. Anneal can check that the declared definition is propagated and
enforced, but cannot infer whether it expresses the user's intended business,
cryptographic, or protocol requirement. If a specification claims
correspondence with Rust, an FFI implementation, an ISA, or another external
semantics, its adequacy remains an explicit trust dependency.

## Contextual refinement

Whole-artifact composition and reusable abstraction verification make
different claims.

A whole-artifact result may cover only the concrete call sites, generic
instances, and reachable behaviors in one compilation subject. This is useful,
but it does not by itself prove a library safe for every future downstream
client.

A reusable safe-API claim requires contextual refinement: the implementation
must realize its declared interface for every type-correct safe use in a stated
semantic and compilation envelope. Clients in that envelope may then rely on
the interface without reopening the private implementation. Rust's underlying
requirement is broad—an API presented as safe must be sound for every
type-correct safe use—even when Anneal can initially report only a narrower
artifact result.

The abstraction boundary may be a pure value-level contract when that is
faithful. Allocators, I/O, atomics, locks, nondeterminism, and other domains may
instead expose effectful or resource-aware interfaces. Contextual refinement
requires the boundary to preserve every observation and discipline relevant to
the claim; it does not require all unsafe implementations to masquerade as
pure functions.

How Anneal exports and checks quantified contracts across separate compilation
remains open. Until it can establish that stronger claim, it must report the
narrower client envelope rather than silently generalize one artifact's
evidence.

## Behavior remains part of the claim

Anneal must support programs that return, panic safely, unwind through
soundness-relevant cleanup, catch a panic and continue, or execute indefinitely
while preserving invariants on every finite prefix. Verification therefore
cannot always mean normal termination.

The proof model must distinguish enough source behavior to justify the
selected claim. It does not yet decide whether soundness, panic freedom,
termination, and other distinctions are built-in property kinds, standard
policies, effects in a weakest-precondition model, or user-defined predicates.
See [property kinds and outcomes](open-questions/property-kinds-and-outcomes.md).

A model or tool failure is not a source-program behavior. It may create an
unsupported or incomplete result, but may never be interpreted as evidence
that the source satisfies a property.
