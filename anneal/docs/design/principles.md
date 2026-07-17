<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Design principles

This document separates Anneal's goals from the principles used to choose
among designs. The goals describe what Anneal is for. The principles are
choice rules: apply them when the
[settled requirements](settled-requirements.md) and
[accepted decisions](decisions/README.md) do not already dictate an answer.

## Goals and scope

Anneal's long-term goals are to let Rust users verify:

- arbitrarily complex or subtle correctness properties; and
- arbitrary Rust codebases and use cases.

These are architectural scope constraints, not claims about the current
executable or requirements that the first milestone support every Rust
construct and property domain.

Unsafe Rust creates proof obligations that Rust's type system does not
discharge. Giving those obligations a rigorous, practical treatment is a
primary Anneal use case. This demands unusually strong support for memory
safety in unsafe-heavy systems code, but Anneal is not limited to memory
safety. Functional correctness, protocol conformance, panic freedom, resource
bounds, and user-defined properties must be able to participate in the same
verification framework.

Anneal is intended for ordinary Rust organizations, not only
formal-methods specialists. Specialists and AI agents may help author proofs
and evolve specifications, but Rust engineers must be able to understand,
debug, review, and incrementally adopt the resulting workflow.

## Preserve soundness and claim integrity

Rust compilers reserve the right to give arbitrary behavior to a program after
undefined behavior. Anneal's source models likewise promise correspondence
only while Rust's validity requirements hold. Soundness is therefore not just
one optional property among peers: it is a prerequisite for interpreting a
model theorem as a fact about the Rust artifact.

Anneal must account for every operation whose validity is required by the
supported Rust semantics and enforce adequate obligations for it. A weak,
incomplete, or vacuous user specification must not be able to redefine a Rust
soundness requirement away. Unsupported semantics, absent coverage, and
residual trust must qualify or prevent the reported claim rather than
disappear behind a successful proof check.

User-defined properties have a different source of meaning. Anneal must
faithfully enforce a user's definition of cryptographic correctness, protocol
conformance, or another domain property, but cannot infer whether that
definition captures the user's intent. Whenever a specification claims
correspondence with Rust or another external semantics, however, its adequacy
is an auditable trust question rather than a matter of personal intent.

## Prefer local, compositional reasoning

Unsafe code can implement a safe API only when the implementation can be
checked against an abstraction boundary that every supported safe client may
then rely on. Clients should consume established interface guarantees rather
than reopen private implementations or reason about an unrelated remainder of
the program.

The durable formulation is contextual refinement: an implementation realizes
its declared interface in every supported context. The interface may include
values, effects, capabilities, resources, protocols, and invariants. Locality
does not require pretending that every implementation is a pure value
transformer.

Composition then has a uniform shape. Each item establishes its guarantees
under its assumptions, and each use establishes the requirements of the
operations it invokes. Property dependencies are evidence-graph edges. For
example, a callee's ordinary functional guarantee that an index is below a
buffer length may discharge the soundness requirement of a caller's raw
pointer access.

## Prefer the simplest faithful abstraction

Simple mathematical interfaces improve proof readability, stability, and
automation. Prefer a pure functional contract when it faithfully captures the
abstraction boundary. Preserve resource, provenance, initialization,
ownership, concurrency, protocol, and effect semantics whenever erasing them
could invalidate the claim.

This rule leads to a hybrid model rather than making “hybrid” an end in itself.
Some Rust can use Aeneas's simple functional interpretation, while other
operations require richer semantics. The exact supported boundary changes as
Aeneas evolves; consult the revision-sensitive
[Aeneas and Charon reference](../reference/aeneas-and-charon.md) rather than
maintaining a second caveat list here.

Lifting a resource assertion into Lean must not turn it into an unrestricted
fact. Its rules for duplication, consumption, framing, opening, and
re-establishment remain part of its meaning. Separation logic is one important
way to preserve such disciplines, not the only permitted mechanism.

## Prefer general, reusable, maintained foundations grounded in real Rust

Prefer mechanisms that can serve multiple properties and Rust use cases over
hard-coded solutions for a single anticipated domain. Initial milestones may
be narrow, but their abstractions should be exercised against concrete Rust
programs and should leave room to extend coverage without replacing the core
composition model.

Lean, Aeneas, and their libraries already provide proof, weakest-precondition,
simplification, and tactic infrastructure. Build on maintained abstractions
when they meet Anneal's requirements. Replacing them is permissible when a
concrete benefit justifies the additional semantics and maintenance.
Likewise, share common proof reasoning where possible without presupposing
whether every property must use one symbolic execution or one proof backend.

Prefer robust programmatic integration points over textual patching or an
unreconciled source-level shadow of compiler-resolved item identities and
metadata. This does not decide whether Anneal should maintain a safety-tracking
system alongside Rust's own `unsafe` machinery. Changes to Aeneas and Charon
are in scope, as are longer-term changes to Rust and its specification.
Upstream and downstream ownership remain case-specific decisions that must
account for the burden placed on collaborators.

## Make trust explicit, classified, and reducible

Trust is not eliminated by translating Rust into Lean. Every dependency needed
to connect checked evidence to the reported claim must be visible and
classified according to its role. In particular, a small trusted boundary of
program-semantic leaves must not be confused with the broader end-to-end TCB
that includes extraction, translation, proof checking, compilation, platform,
and hardware assumptions.

A trusted leaf can be a legitimate engineering boundary. Hidden trust, a
silently omitted operation, or an unclassified incomplete proof cannot.
Axioms about external semantics, unfinished proofs, prose justifications,
unsupported coverage, and tool failures support different conclusions and
must remain distinguishable.

Trust must also be capable of shrinking. A formal Rust, library, compiler,
instruction-set, foreign-library, or hardware model should be able to replace
a shallower assumption without forcing every client contract to change.
Moving an assumption into a helper whose body is not modeled, or into an
upstream component, does not
reduce trust unless the end-to-end dependency has actually been removed.

## Support honest incremental adoption by ordinary Rust engineers

Real Rust codebases cannot usually formalize every obligation at once. Anneal
must support incremental adoption, including some form of existing prose
`// SAFETY:` justification in place of selected formal proofs. It may also
need a first-class representation of a proof that has not yet been completed.

Incremental adoption must not turn an assumption into a proof. Reports and
diagnostics must make clear what was checked, what remains, what claim that
evidence supports, and what would strengthen it. Favor stable proof interfaces,
diagnostics tied to Rust source, resilience to small program changes, and
failures that explain the outstanding obligation.

AI assistance may reduce the amount of formal expertise needed to author a
proof. It may not excuse an interface whose meaning or trust boundary Rust
engineers cannot audit. Performance and automation matter because feedback
latency shapes adoption, but neither may weaken or obscure the reported claim.

## Applying the principles

The principles often reinforce one another, but they do not define a permanent
total order. When they pull in different directions:

1. state the exact claim each alternative would support;
2. identify added trust, lost coverage, or erased semantic information;
3. ask whether the result still composes at an abstraction boundary;
4. consider usability, maintenance, and the path to broader coverage;
5. prefer reversible experiments while evidence is weak; and
6. record an irreversible choice explicitly.

A convenient design that compromises soundness or claim integrity is
unacceptable. Among designs that preserve those constraints, the balance of
simplicity, coverage, maintenance, and user experience is a case-specific
judgment.
