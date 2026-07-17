<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Lessons from Anneal V1

Anneal V1 is the experimental prototype in `anneal/v1/`. V2 is a clean-room,
ground-up redesign. V1 supplies observations, examples, and failure modes; it
does not supply defaults. Copy V1 code or concepts only after showing that they
serve V2's principles and current requirements.

This page deliberately distills lessons rather than preserving every
terminological clarification made while discussing V1.

## What the prototype demonstrated

### A useful end-to-end workflow is possible

V1 connected Rust source, Charon, Aeneas, generated Lean, user-authored
contracts, and the Lean checker. It demonstrated that a Cargo-facing tool can
keep formal obligations close to Rust code, automate the toolchain, and map
many failures back into a workflow recognizable to Rust engineers.

That validates the product direction, not V1's particular annotation grammar,
source scanner, generated theorem shapes, or directory layout.

### Aeneas's functional model is a powerful default

For supported Rust, Aeneas turns disciplined borrowing and mutation into
mathematical value transformations. V1 showed the ergonomic payoff of using
that model for ordinary control flow surrounding unsafe leaves. V2 should
build on maintained Aeneas and Lean abstractions where they remain faithful,
including weakest-precondition specifications and existing tactics.

The lesson is not that every behavior must be forced into a pure transformer.
Resource and effect semantics must remain explicit whenever erasing them
could undermine soundness.

### Local contracts can support global reasoning

V1's precondition/postcondition structure exercised the intended composition:
a caller proves a callee's requirements, and a callee proves what it returns
or preserves. This remains the core local shape from which artifact-wide
soundness and user-defined properties should be assembled.

V1 did not prove the complete adequacy theorem connecting arbitrary unsafe
Rust execution to its Lean model. That gap must remain visible rather than
being hidden by successful Lean compilation.

## Designs which should not be inherited

### Orthogonal progress and correctness duplicated work

V1 split proofs into progress and correctness branches. The correctness branch
was conditional on successful execution, while the progress branch established
that execution succeeded. In practice:

- the two proofs often repeated the same symbolic execution;
- the split did not compose naturally with Aeneas's WP specifications or its
  `step` and `step*` tactics; and
- conditional correctness could be vacuous when progress was absent.

V2 is leaning toward a shared Aeneas-style symbolic execution with obligations
for the relevant outcomes. The exact outcome/property architecture is still
open; V1 is evidence against making the orthogonal split the default, not a
decision that every verified function must terminate normally.

Sound infinite execution, sound panic and unwind, and recovery after panic are
required use cases.

### `isValid` was not enforced at mutation boundaries

V1 attached an `isValid` predicate to a type and injected it into function
contracts, but safe Rust code could access or mutate invariant-carrying fields
without re-establishing the predicate. The mechanism was therefore knowingly
unsound and eventually required an explicit opt-in flag.

V2 still requires type invariants for arbitrary property kinds. It must also
enforce opening and re-establishing them at every operation which can violate
them. Rust's proposed unsafe-fields feature could provide the language-level
boundary; Anneal-specific field access and mutation analysis is also in scope.
Waiting for upstream stabilization is not the only option.

### `isSafe` expressed an architecture V1 did not enforce

The durable idea behind V1's `isSafe` was that an unsafe trait implementation
establishes an invariant and generic code with the trait bound can consume it.
V1 documentation and implementation did not consistently enforce both halves.

V2 requires trait invariants, like type invariants, to support arbitrary
property kinds. It must verify the invariant at every applicable
implementation site and expose exactly the corresponding assumption wherever
the trait bound is known. The final name and syntax are open.

### Generated-Lean coupling was brittle

V1 generated theorem signatures and proof scaffolding by predicting details
of Aeneas output: item names, tuple shapes, mutable-borrow returns, and special
treatment of `Unit` and `Never`. Small changes in Aeneas could require matching
Anneal changes or produce opaque Lean type errors.

V2 should prefer compiler-resolved identities and maintained Aeneas interfaces
over textual surgery and a parallel source-derived ABI. This does not mandate
one interface: LLBC fields, library APIs, CLI modes, Lean syntax extensions,
and robust downstream adapters remain case-by-case options.

### The source scanner could disagree with the compiler

Parsing doc comments independently of rustc made it easy to lose the effects
of macro expansion, `cfg`, name resolution, aliases, and Cargo target
selection. A scanner can remain useful for source presentation, but semantic
claims must reconcile exactly with the compiler-selected artifact.

### V1 annotation syntax is an experiment

Indentation-sensitive Lean blocks in Rust documentation comments proved that
literate verification can work. They also exposed parser complexity,
formatting constraints, and leakage of Aeneas-generated names and proof
machinery. V2 is not committed to doc comments, indentation sensitivity, raw
Lean, Rust-like specifications, proof placement, or any V1 keyword.

The audience requirement survives: ordinary Rust teams, including relatively
new engineers and engineers assisted by agents, must eventually be able to use
Anneal. Syntax should be judged by semantic clarity, diagnostics,
evolvability, and workflow—not resemblance to the prototype.

## Trust-boundary lessons

### `unsafe(axiom)` verified callers relative to a leaf

V1's `unsafe(axiom)` made a function body opaque and trusted the user's
behavioral specification. It did not verify that body. This was useful for
composition and incremental coverage, but it left both the opaque
implementation and the specification in the TCB.

V2's production objective is a small, explicit, shrinkable collection of
trusted leaves. Near-term leaves are expected to include some standard-library
unsafe operations and intrinsics, FFI, assembly, and raw-pointer operations.
Future formal ISA, foreign-language, or operational models may remove
individual leaves from the TCB.

The syntax used for axioms is likely also needed by an Anneal standard library.
User-authored axioms will likely remain necessary for FFI for the foreseeable
future. It is open whether a foreign library author or each Rust consumer
normally owns those specifications.

### Incomplete adoption needs a first-class status

V1 supported `sorry`-based development and axiomatic boundaries, but a
production result needs to distinguish trusted external semantics from work
which is merely unfinished. Incremental adoption must also permit some
existing prose `// SAFETY:` justifications in place of formal proofs.

Every such boundary must appear in an audit ledger. Whether an incomplete run
uses a separate command, profile, exit status, or result label remains open.

### Specification adequacy cannot be delegated away

Lean will prove a weak or vacuous specification. For Rust soundness, Anneal
must know or generate the required primitive safety obligations and ensure
that non-axiomatic specifications are adequate for them. Human review alone
is not an acceptable substitute for this mechanical guarantee.

User-defined correctness properties have a different ground truth. Anneal can
ensure that a declared axiom is used and upheld, but cannot decide whether the
user chose the intended cryptographic, protocol, quantitative, or functional
property.

## Product and reporting lessons

- Rust's single `unsafe` axis is too coarse to express all property kinds.
  Anneal must support dependencies among soundness and arbitrary additional
  properties, while the degree of integration with Rust's existing unsafe
  machinery remains open.
- Soundness is special and non-negotiable. Panic freedom, termination,
  deadlock freedom, cryptographic correctness, resource bounds, and other
  properties must not be silently conflated with it.
- A verification result needs an audit ledger. V1's opacity, axioms, `sorry`,
  unsupported code, and toolchain assumptions were too easy to understand
  only by inspecting implementation details.
- Diagnostics are part of semantic usability. When generated names or tuple
  encodings leak into errors, users cannot reliably repair or review proofs.
- Incremental adoption is a core use case, but a partially checked result must
  never masquerade as an unconditional one.

## How to use V1 now

Use `anneal/v1/` to reproduce experiments, inspect examples, and understand
why a V2 question exists. When citing it in a V2 design discussion, state the
observation rather than treating the V1 mechanism as precedent. If evidence
from V1 conflicts with [V2 principles](../design/principles.md) or
[settled requirements](../design/settled-requirements.md), V2 wins.
