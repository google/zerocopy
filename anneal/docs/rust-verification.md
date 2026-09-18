<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Rust-level verification

This document defines when evidence about derived proof obligations or models is
sufficient to support an Anneal verification result whose claim is about Rust
program behavior. It derives from the project
[principles](../PRINCIPLES.md), [design contract](../DESIGN.md), and
[verification-result semantics](verification-results.md); those documents remain
authoritative if this one conflicts with them.

The purpose here is to define the semantic connection between a Rust-level claim
and the proof work Anneal asks a checker to perform. This document does not
choose an extraction point, intermediate representation, memory model, proof
encoding, coverage unit, or division of responsibility among Rust, Charon,
Aeneas, Lean, and Anneal.

## Verification as a reduction

Start with an exact Rust-level claim (C), together with the claim-relative TCB
of the result Anneal intends to issue.

Anneal may reduce (C) to a collection of proof obligations. The obligations
may be ordinary propositions, weakest-precondition judgments,
resource-sensitive goals, or some other form appropriate to the claim. Their
representation is not part of this model.

The reduction is **adequate** when the following implication is justified:

    TCB correct
    + generated obligations discharged according to their proof rules
    -----------------------------------------------------------------
    Rust-level claim C

Checked proofs establish the obligations. The adequacy of the reduction is what
connects those checked facts back to Rust.

This model does not require Anneal to expose one canonical mathematical model of
the Rust program. A generated Lean model, an intermediate semantics, a
translation validator, or another formal representation can all participate in
the reduction. They matter only through the evidence or trusted premises needed
to justify the implication above.

## Adequacy is claim-relative

An adequate reduction need not preserve every observable detail of Rust
execution. It needs to preserve enough information to establish the particular
claim.

The same abstraction may therefore be adequate for one claim and inadequate for
another. A model can intentionally forget behavior which cannot affect the claim,
while a claim about that behavior requires a richer model.

For a Rust-level claim, however, well-defined behavior remains foundational.
Anneal cannot erase the semantics needed to establish that the covered Rust
behavior is free from undefined behavior merely because another selected
property does not mention those semantics explicitly.

This is why the criterion is claim preservation rather than full semantic
equivalence. A simpler translation is desirable when the omitted information is
irrelevant to the claim; it is unsound when information capable of falsifying
the claim disappears without justification.

## Common ways a reduction can be inadequate

There are several ways for all generated proof obligations to be successfully
checked while the reduction is still inadequate.

One is a **weak obligation**. An operation may require several conditions for
the Rust claim to hold, while the generated obligation checks only some of
them. Proving that weaker obligation does not establish the Rust requirement.

Another is **unaccounted-for behavior**. A path, operation, generated item, or
other behavior capable of falsifying the claim may fail to influence any
obligation or trusted premise. The obligations which remain may all be true
without establishing the claim.

These are examples of one underlying defect: the discharged obligations and
recorded TCB are not sufficient for (C). They do not need to become separate
top-level kinds of verification result.

In particular, coverage is semantic rather than merely syntactic. Source code
or an intermediate operation may be absent from a later representation without
causing a problem if its absence is itself justified for the claim. Conversely,
the presence of every source construct in an intermediate representation is not
enough if its semantics or obligations are too weak.

## Reductions can compose

A real verification pipeline may contain many stages:

    Rust claim
        -> compiler or extracted representation
        -> verification model
        -> proof obligations
        -> checked evidence

The arrows in this diagram are not automatically trustworthy merely because a
tool produced the next representation.

Each stage may itself be understood as a reduction from a claim or required fact
to lower-level obligations. Adequate reductions compose: if discharging the
lower-level obligations is sufficient for an intermediate fact, and that fact
is sufficient for the Rust claim, then the combined argument can support the
Rust claim.

This lets Anneal use existing translators and proof systems without making their
current architecture part of the semantic model. It also makes their trust
boundary explicit. If the correctness of a stage is not established by the
checked evidence supporting the result, and the result depends on that stage
being correct, that correctness remains in the result's TCB.

A checked theorem about an intermediate model therefore means exactly what the
theorem says about that model. It becomes evidence for a Rust-level claim only
through an adequate chain of reductions back to Rust.

## Undefined behavior and circularity

Undefined behavior makes the adequacy argument especially important. Some
translations or semantic models may be justified only for Rust executions which
are already well-defined.

Such a conditional correspondence cannot by itself prove that the original Rust
program is well-defined. If a stage is valid only under an assumption equivalent
to, or stronger than, the Rust-level claim Anneal is trying to establish, using
that assumption as though it were checked evidence would be circular.

Any such premise must instead be handled explicitly. It may be established by a
separate non-circular argument, or, if an applicable trust policy permits, it may
remain in the result's TCB. In the latter case the result is visibly conditional
on that premise; the premise has not been established merely because the rest of
the model proof succeeded.

This document does not choose how Anneal closes the undefined-behavior loop.
Execution-prefix arguments, simulations, translation validation, compiler
assistance, and other constructions are possible implementations of the same
requirement.

## Unsupported, transformed, or erased behavior

Anneal need not reject every transformation which changes or removes source
structure. Compilers and verification tools routinely desugar, simplify, and
eliminate code.

The relevant question is whether the transformation participates in an adequate
reduction for the claim. If removed behavior is semantically irrelevant under
the justified premises, its absence is harmless. If behavior capable of
falsifying the claim disappears without a justified reason, the reduction is
inadequate even when every remaining proof obligation succeeds.

Likewise, encountering an unsupported construct is not itself a source-program
behavior and supplies no evidence for the claim. If Anneal cannot account for
the construct well enough to maintain an adequate reduction, it cannot issue
the requested ordinary verification result. As defined in
[verification-results.md](verification-results.md), it may instead establish a
genuinely narrower claim, or a later trust policy may explicitly admit a
required premise into the TCB.

Whether generated Rust or other generated artifacts belong to the verified
subject is a separate subject-identity question. Once behavior is within the
claim's subject, this document's adequacy requirement applies regardless of
whether a human wrote it directly.

## Trust in the reduction

The adequacy argument does not have to be fully machine-checked on the first
day Anneal is useful.

A result may depend on the correctness of Rust semantic assumptions, extraction,
translation, modeling, obligation generation, checking integration, or other
parts of the reduction. Any such dependency whose correctness is not established
by the result's checked evidence remains in the claim-relative TCB.

Over time, proof, per-artifact validation, stronger specifications, or other
accepted evidence may remove such dependencies from the TCB without changing
the Rust claim. Merely moving the same unchecked assumption across a tool or
project boundary does not.

This separation also keeps implementation confidence distinct from verification
evidence. Testing a translator or observing that it works on many examples can
be valuable engineering evidence, but it removes a dependency from the TCB only
if Anneal's assurance model explicitly establishes the required correctness from
that evidence.

## What this document leaves open

This model intentionally does not decide:

- the atomic Rust subject to which a claim applies;
- the formal Rust semantics against which a reduction is justified;
- where in the compiler pipeline the authoritative program is captured;
- whether a particular transformation is proved once, validated per artifact,
  or trusted;
- the unit used to enumerate or check claim-relevant coverage;
- the representation and proof rules of generated obligations;
- whether obligations are encoded in translated functions, sidecar theorems,
  weakest-precondition specifications, or another mechanism;
- the memory, provenance, concurrency, resource, or effect logics needed for
  particular claims;
- how local function and abstraction contracts compose into larger claims;
- which responsibilities belong to Charon, Aeneas, Anneal, Lean libraries,
  rustc, or other tools; or
- which trusted premises are admissible under production, incremental, or
  development policies.

Those choices may determine how Anneal realizes or establishes an adequate
reduction. They must preserve the semantic rule defined here: the discharged
obligations, together with the explicitly recorded TCB, must be sufficient for
the exact Rust-level claim Anneal reports.
