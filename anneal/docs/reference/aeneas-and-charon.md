<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas and Charon

Anneal is being developed as an orchestration and verification layer in
collaboration with the [Charon](https://github.com/AeneasVerif/charon) and
[Aeneas](https://github.com/AeneasVerif/aeneas) projects. Contributors need a
precise division of responsibility: a theorem checked in Lean is only as
useful as the extraction and semantic model to which it refers.

This page describes the conceptual roles relevant to Anneal. Upstream
documentation and source remain authoritative for the exact behavior of a
particular pinned release. This page was last reviewed on 2026-07-17, when
`flake.nix` pinned Aeneas release `nightly-2026.06.03`. Statements about
supported constructs, result types, and APIs are revision-sensitive; recheck
the currently pinned release when a design depends on them.

## Charon: compiler-integrated extraction

Charon runs with the Rust compiler and exports Rust programs into LLBC (Low
Level Borrow Calculus), an intermediate representation designed for formal
reasoning. This gives Anneal compiler-resolved information that a source-text
parser cannot reliably reconstruct, including the program after macro
expansion and conditional compilation, resolved item identities and types,
monomorphization-relevant structure, control flow, and source spans.

Charon is not a verifier. Successful extraction means that Charon produced an
LLBC representation for the selected compilation; it does not prove that the
Rust source is sound or that a later Lean model is adequate.

For Anneal, LLBC is valuable for two independent reasons:

1. It is a semantic input to Aeneas's translation.
2. It can be a compiler-authoritative index against which annotations,
   contracts, call edges, and source locations are reconciled.

V2 is trending toward consuming LLBC directly, but exclusive use of LLBC is
not a settled principle. Other compiler-resolved inputs are acceptable when
they produce a clearer or more faithful design. A source scanner may be a
useful bootstrap mechanism; it must not silently become a second, conflicting
Rust ABI or name-resolution system.

## Aeneas: functional translation and proof support

Aeneas consumes LLBC and translates supported Rust into definitions in proof
assistants, including Lean. Its central advantage is that a useful subset of
Rust—roughly, code whose mutation remains disciplined by ordinary borrowing
and which avoids unsupported forms of interior mutation—can be translated as
pure functional transformations rather than as operations over an explicit
heap.

For mutable borrows, Aeneas can represent the forward result together with the
information needed to reconstruct the final borrowed value. This preserves
the meaning of ordinary Rust updates while exposing a mathematical interface
that is substantially simpler than a whole-program heap model.

The Aeneas Lean library also provides maintained proof infrastructure,
including weakest-precondition specifications and tactics such as `step` and
`step*`. V2 should normally compose with this machinery. V1's attempt to split
progress from conditional correctness worked against those abstractions and
often duplicated symbolic-execution work; see
[V1 lessons](../history/v1-lessons.md).

Aeneas is not, by itself, an adequacy proof for every Rust program. Its
translation has a supported language and a semantic envelope. Unsafe
operations, resource-sensitive facts, concurrency, unwinding, and other
effects may require additions to Aeneas or an Anneal layer with semantics that
cannot be erased into unrestricted propositions.

## Anneal: contracts, safety obligations, and orchestration

Anneal's intended responsibilities sit around and above this pipeline:

- identify the exact Cargo/rustc artifact being verified;
- associate source-level contracts and invariants with compiler-resolved
  items;
- supply or generate the semantic obligations of primitive unsafe operations;
- prove each function's postconditions under its preconditions and prove that
  every call satisfies its callee's required properties;
- compose those local facts into program-level guarantees;
- invoke Lean and map diagnostics back to the user's Rust context; and
- report every trusted leaf, incomplete proof, tool version, target
  assumption, and coverage gap.

The checked-in V2 implementation does not yet perform these steps. It
currently builds and installs the toolchain needed to implement them. See
[the current architecture](current-architecture.md).

## Why source/model adequacy matters

Aeneas and Anneal are only expected to model sound Rust faithfully. Anneal is
also intended to prove soundness, which creates an apparent circularity. V2
therefore needs a precise semantic argument connecting the extracted model,
the source operations whose validity matters, and complete enforcement of
their safety obligations. The exact theorem and proof structure remain open.

Safety proofs may appear as propositional arguments to generated functions,
as sidecar theorems over unmodified Aeneas output, or through another
mechanism. The choice remains open. Whichever design is selected must be
complete at call sites, fail closed, and support a convincing adequacy
argument. See
[source/model adequacy](../design/open-questions/source-model-adequacy.md).

## Pure facts versus resources

Lifting separation-logic assertions into Aeneas's mathematical domain is only
sound if their resource behavior survives the lift. Initialization,
provenance, exclusive ownership, fractions, protocol states, and similar
capabilities cannot become freely duplicable ordinary hypotheses merely
because they are represented in Lean.

The design preference is to expose simple, pure contracts at an abstraction
boundary when they faithfully describe every relevant behavior. Simplicity is
not permission to discard facts required for soundness. When resource or
effect semantics matter, the interface must preserve them, potentially using
additional monadic, weakest-precondition, linear, or separation-logic
machinery. Some of that machinery may be best maintained upstream in Aeneas.
See [memory, resources, and effects](../design/open-questions/memory-resources-and-effects.md).

## Upstream collaboration policy

Changes to Aeneas, Charon, and eventually Rust itself are in scope. Prefer a
maintained programmatic interface—an LLBC field, library API, command-line
mode, Lean abstraction, macro, or tactic—when it improves fidelity and reduces
downstream coupling. Avoid patching generated Lean text or maintaining a
parallel `syn`-based model when a first-class interface can reasonably exist.

This is a preference, not a rule that overrides engineering judgment. The
upstream maintenance burden, iteration speed, user experience, and stability
of each solution must be evaluated case by case. A robust downstream adapter
can be appropriate; a clever but well-contained Lean syntax extension may be
safer than invasive upstream churn.

## Information Anneal is likely to need

The exact API is open, but current design work should assume that Anneal needs
authoritative access to:

- stable identities for items within one compilation artifact;
- resolved signatures, generics, trait bounds, implementations, and calls;
- expanded and `cfg`-selected annotations or an exact mapping from source
  annotations to resolved items;
- source spans suitable for diagnostics;
- opacity and reachability decisions;
- the target and compiler settings which affect semantics; and
- enough outcome/effect information to distinguish a Rust behavior from a
  Charon, Aeneas, or Anneal modeling failure.

Whether this arrives in ordinary LLBC, a Charon annotation/index mode, an
Aeneas API, or several coordinated interfaces is an open implementation
question. The motivation is semantic authority and debuggability, not a
commitment to one serialization format.
