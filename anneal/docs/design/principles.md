<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Design principles

This document captures Anneal's value function: the principles from which an
agent or human should reason when no concrete decision dictates an answer. The
[settled requirements](settled-requirements.md) turn parts of this philosophy
into explicit constraints.

## General verification for real Rust

Anneal aims to support both:

- arbitrarily complex or subtle correctness properties; and
- arbitrary Rust codebases and use cases.

These are long-term scope constraints and design tests, not claims about the
coverage of the current executable or a requirement that the first milestone
support every Rust construct and property domain.

The first goal calls for a general property and invariant framework rather than
a memory-safety-only checker. The second calls for excellent support for
memory safety, because embedded, kernel, runtime, cryptographic, and other
systems code routinely relies on unsafe Rust.

Anneal is therefore neither merely an unsafe-code lint nor a generic theorem
prover with Rust-shaped syntax. It is a verification environment in which
soundness is foundational and broader correctness properties can compose with
it.

## Soundness is special

Rust compilers reserve the right to give arbitrary behavior to a program after
undefined behavior. Aeneas and Anneal likewise promise faithful models only for
sound Rust programs. Soundness is therefore not just one optional property
among peers: it is a prerequisite for trusting the correspondence between the
source artifact and the Lean model used to prove other properties.

This creates an adequacy obligation for Anneal. It must account for every
operation whose validity is required by Rust and ensure that the corresponding
precondition is established. A weak or vacuous user specification cannot be
allowed to redefine Rust soundness away.

Other properties are different. The user may define what cryptographic
correctness, protocol conformance, or a resource bound means for their system.
Anneal must faithfully enforce those definitions, but there is no external
ground truth by which Anneal can decide whether a user-defined axiom captures
the user's intent.

## Locality enables safe encapsulation

The promise of safe Rust is that any type-checked use of a safe API from sound
safe code remains sound. An implementation using unsafe code can uphold this
promise only if its obligations can be discharged at an abstraction boundary:
clients should reason from the interface rather than re-open the entire
implementation and surrounding program.

The durable formulation is contextual refinement. An implementation must
realize its declared interface in all supported contexts. This need not mean
that the implementation is literally a pure value transformer. It means that
the effects, capabilities, protocols, and resources visible at the interface
are sufficient to justify every client use.

Once obligations are local in this modular sense, composition follows: prove
each implementation against its boundary, prove each caller meets its callees'
requirements, and assemble a program-wide claim from those local results.

## Use a hybrid model

Aeneas exploits a profound property of a substantial safe Rust subset: absent
interior mutation and related effects, its ownership discipline admits a
simple, functional interpretation. Values in that model often correspond
directly to mathematical values, making ordinary functional verification far
simpler than whole-heap operational reasoning.

Unsafe Rust, interior mutation, concurrency, allocators, and external effects
can require richer semantics. Separation logic recovers modular reasoning by
tracking ownership and permissions, but its assertions may themselves be
treated as objects in a higher-level mathematical model. Anneal's central
direction is to combine these levels rather than choose either a purely
functional model of a restricted language or a monolithic separation-logic
model for every instruction.

Prefer a pure, simple contract where it faithfully captures the abstraction
boundary. Soundness is non-negotiable: preserve resource, provenance,
initialization, ownership, protocol, or effect semantics wherever erasing them
could invalidate the claim. Resource tracking is an important example, not an
exhaustive list of cases requiring richer machinery.

In particular, a separation-logic resource must not become an unrestricted
Lean fact merely because it has been lifted into a mathematical domain. Its
rules for duplication, consumption, framing, opening, and re-establishment are
part of its meaning.

## Compose obligations, not duplicated proofs

At a high level, a function must establish its declared guarantees under its
preconditions and must meet the required preconditions or properties of every
callee. Property kinds may depend on one another. A soundness proof may, for
example, require a non-soundness property promised by another operation.

V1 separated progress from conditional correctness. Experience suggested that
the two branches often repeated symbolic-execution work and fit Aeneas's WP
specifications and `step`/`step*` tactics poorly. V2 is leaning toward shared,
combined reasoning, but the precise outcome and property architecture remains
open. The lesson is to avoid needless duplication, not to prematurely ratify a
replacement taxonomy.

## Prefer maintained foundations

Lean and Aeneas already provide significant proof, WP, simplification, and
tactic infrastructure. Anneal should build on maintained abstractions where
they meet its requirements. Reimplementing machinery can be justified, but it
creates semantic duplication and maintenance cost that must buy a concrete
advantage.

The same principle applies to integration. A first-class Charon or Aeneas API,
compiler-resolved metadata, or Lean extension point is generally more robust
than parsing generated text or maintaining a shadow ABI. This is a preference,
not an absolute ban: ownership and upstreaming should be chosen case by case,
including the cost imposed on collaborators.

Anneal's authors collaborate with Aeneas and Charon and participate in Rust
language design. Changes to all three projects are in scope. Short-term designs
must work with the language and tools that exist; long-term designs need not
treat today's limitations as permanent laws.

## Make trust visible and reducible

Some boundaries will remain trusted in the near term: raw-pointer primitives,
compiler intrinsics, unsafe standard-library leaves, FFI, assembly, and hardware
semantics are likely examples. Trusting a leaf can be a sound engineering
choice if its specification and consequences are explicit.

The TCB must be auditable and designed to shrink. A future formal ISA model may
replace an assembly axiom; a verified library model may replace an opaque FFI
boundary. Anneal should not bake opacity into its architecture where deeper
reasoning could later fit.

A successful result must expose its assumptions, incomplete proofs, prose
justifications, opaque items, skipped coverage, tools, configurations, and
environmental dependencies. Hidden trust is a correctness failure, not merely
a reporting defect.

## Support incremental adoption honestly

Real codebases cannot usually formalize everything at once. Anneal must permit
incremental adoption, including some form of existing prose `// SAFETY:`
justification in place of selected formal proofs. It may also need a first-class
not-yet-proved obligation analogous to Lean's `sorry`.

Incremental modes must not blur the difference among a checked proof, an
incomplete proof, a prose review obligation, and an axiom about external
semantics. Each can be useful; each supports a different conclusion and belongs
in the audit ledger.

## Design for ordinary Rust engineers

The aspiration is that ordinary Rust teams ask every engineer, including new
graduates, to use Anneal. Formal-methods specialists and AI agents may help
write proofs and evolve specifications, but the workflow must remain
understandable, debuggable, and reviewable by Rust developers.

Favor stable abstractions over generated-name trivia, diagnostics tied back to
Rust source, proofs resilient to small program changes, and failures that say
what remains unproved. Performance matters because feedback latency shapes
adoption, but speed cannot excuse a weaker or ambiguous claim.

## Reason about tradeoffs from first principles

Soundness, semantic fidelity, auditable trust, useful coverage, debuggability,
ergonomics, upstreamability, and performance often align but sometimes
conflict. There is no permanent total order that resolves every case.

When they conflict:

1. state the claim Anneal would make under each alternative;
2. identify any added trust, lost coverage, or lost semantic information;
3. ask whether the result still composes at an abstraction boundary;
4. prefer reversible experiments while evidence is weak; and
5. record an irreversible choice explicitly.

A design that is pleasant but unsound is unacceptable. Among sound designs,
the right balance of coverage, simplicity, maintenance, and user experience is
a case-specific judgment guided by the mission above.
