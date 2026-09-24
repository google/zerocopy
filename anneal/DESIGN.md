<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal design contract

This document derives design constraints from Anneal's
[`PRINCIPLES.md`](PRINCIPLES.md). The principles define Anneal's promises,
beliefs, and rules for making decisions. This document describes semantic
constraints that any Anneal design must preserve in order to uphold them.

The principles are authoritative over this document. If the two conflict, this
document must be corrected. This document constrains the meaning of Anneal's
results and interfaces, not the mechanisms used to implement them.

## Anneal proves conditional guarantees

At a high level, an Anneal claim has:

- a **subject** whose behavior is being verified;
- **requirements** under which the claim applies; and
- **guarantees** that hold when those requirements are satisfied.

Anneal checks that the requirements imply the guarantees. That checked reasoning
is itself conditional on Anneal's trusted computing base (TCB).

Requirements and TCB assumptions play different roles. A requirement is a
condition on the program's inputs, callers, or environment. It must be satisfied
when the claim is used. A TCB assumption is an unchecked premise in Anneal's
reasoning about whether the claim is true.

Every fact Anneal itself needs to justify a reported claim must therefore either
be established by checked evidence or be represented explicitly in the TCB. A
required fact may not disappear merely because an analysis was skipped,
incomplete, unsupported, or failed.

Why a fact is trusted does not change this core semantics. Anneal may record that
provenance for diagnostics, auditing, or policy, but an unfinished proof, an
external semantic assumption, and another unchecked premise are all trusted
premises at this level.

Checked evidence about an intermediate model supports a Rust-level guarantee only
if the connection from Rust to that model is itself checked or included in the
TCB. An unchecked assumption does not stop being trusted merely because it is
encapsulated in a translator, generated artifact, helper library, compiler, or
other component.

## Anneal connects source-level guarantees to compiled behavior

Anneal ultimately makes claims about code produced by `rustc`, not only about an
intermediate mathematical model.

Every successful Anneal result includes two baseline guarantees:

1. the Rust executions covered by the claim are well-defined; and
2. subject to the TCB, the compiled code corresponds to the Rust source semantics
   strongly enough to preserve the guarantees reported by Anneal.

The second guarantee need not mean that the source and compiled program have
literally identical sets of behaviors. The required relationship is whatever is
strong enough to justify carrying each reported source-level guarantee to the
compiled code.

Developers may ask Anneal to prove additional guarantees beyond well-definedness.
Those guarantees may themselves have requirements. For example, a safe binary
search function may guarantee that its result correctly reports membership only
when its input is sorted. Calling it with an unsorted slice may make that
additional guarantee inapplicable; it must not invalidate Anneal's baseline
guarantee that the safe call is well-defined.

Proving a user-defined guarantee establishes the property that was specified. It
does not establish that the specification captures what its author intended.

## Closed-program guarantees cover complete executions

For a closed program, Anneal's well-definedness guarantee applies to complete
executions covered by the claim.

Anneal may establish this guarantee using local proofs, component contracts,
whole-program reasoning, or another sound method. Regardless of the proof
strategy, those intermediate judgments must ultimately justify the whole-program
claim. Showing that one function or thread is locally well-behaved is insufficient
if another part of the same execution can exhibit undefined behavior.

Additional developer-defined guarantees apply at the scope stated by their
claims. Anneal must not infer a whole-program guarantee from local facts that do
not establish it.

## Library guarantees are contextual

A library cannot guarantee the behavior of an arbitrary surrounding program.
Instead, Anneal verifies an implementation relative to an API contract.

An API contract has:

- **requirements** that a caller must satisfy and that the implementation may
  assume; and
- **guarantees** that the implementation must establish and that a caller
  satisfying the requirements may rely upon.

Anneal's library guarantee is contextual: replacing the abstract API contract
with the verified implementation in an admissible context must preserve
well-definedness and the guarantees of that contract. In particular, if a context
interacting with the abstract contract has well-defined Rust behavior, then
replacing that contract with the verified implementation must not make the
resulting Rust execution undefined, provided the context satisfies the contract's
requirements.

The exact formal account of this contextual relationship is a lower-level design
question. The guarantee must nevertheless be precise enough that it does not rely
on an informal judgment about whether undefined behavior was "caused by" or
"attributable to" the library.

### Admissible use follows Rust's API conventions

The choice of which contexts Anneal considers admissible is a policy choice, not a
mathematical necessity. Anneal chooses this boundary to align its formal
guarantees with Rust's conventions about what callers must establish and what API
implementations may assume.

For a safe API, Anneal's baseline guarantees must hold for every use that:

- is permitted by the Rust type system; and
- supplies values satisfying the invariants associated with their Rust types that
  Rust convention permits implementations to rely upon.

The second condition may be stronger than requiring that constructing or passing
the value has not already caused undefined behavior. For example, an
implementation receiving a `&str` may rely on the invariant that the `str`
contains valid UTF-8.

A safe API may not impose any additional unchecked caller requirement needed for
Anneal's baseline well-definedness guarantee. A type-correct safe caller supplying
values that satisfy the applicable type invariants must not be able to violate
that guarantee merely because it failed to satisfy some hidden condition.

Additional developer-defined guarantees may have additional preconditions. Those
preconditions limit only the corresponding additional guarantees; violating them
must not invalidate the baseline guarantee of a safe API.

For an unsafe API, admissible use additionally requires satisfying the API's
explicit safety requirements. Anneal's baseline guarantee is conditional on those
requirements.

By default, values passed to an unsafe API are also assumed to satisfy their
ordinary type invariants. Some unsafe APIs may need to accept values that violate
invariants normally associated with their types. Whether Anneal permits an unsafe
API contract to relax such an invariant, and how that permission is expressed,
remains unresolved.

## Anneal is general over guarantees and program behaviors

Anneal must allow developers to state and prove correctness guarantees beyond
well-definedness without fixing today's anticipated set of guarantees as a closed
universe.

Anneal also aims to support all program *behaviors*, not every Rust source
program. It may reject particular language features or combinations of features
when the same intended behavior can be expressed in a supported way. When
practical, Anneal should give programmers actionable guidance toward such a form.

Adding support for new guarantees or program behaviors must not weaken the meaning
of existing successful verification results.

## The ordinary interface is Rust-oriented

Ordinary Rust programmers must be able to use Anneal effectively without learning
Lean 4.

When Anneal cannot establish an obligation, its ordinary interface should connect
that failure to the Rust program: what operation or guarantee generated the
obligation, what must be true, and what Anneal could not establish.

The normal workflow should therefore feel like an extension of Rust's existing
compiler-enforced reasoning rather than requiring every Rust programmer to become
a formal-methods specialist.
