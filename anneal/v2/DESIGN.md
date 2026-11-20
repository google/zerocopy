<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal design contract

This document derives durable design constraints from Anneal's
[`PRINCIPLES.md`](PRINCIPLES.md). The principles define Anneal's promises,
beliefs, and rules for making decisions. This document states properties that
any Anneal design must preserve in order to uphold those principles.

The principles are authoritative over this document. If the two conflict, the
principles win and this document must be corrected. Lower-level architecture,
implementation, and user-interface decisions must in turn be consistent with
both.

This document intentionally stops short of choosing mechanisms. It does not
specify an annotation language, proof encoding, result schema, command-line
interface, or division of responsibility among Rust, Charon, Aeneas, Lean, and
Anneal.

## Verification success has a precise meaning

Anneal's promise is conditional but precise: if the code in a result's TCB is
correct, its trusted assumptions are valid, and Anneal emits no errors, then the
covered program behaves as promised.

A successful verification result therefore needs enough identity and scope to
make that implication meaningful. It must identify the program or behavior to
which the result applies, the promises Anneal established, and the trusted code
and assumptions on which those promises depend.

Anneal must never silently report a stronger promise than its evidence supports.
Missing evidence, unsupported semantics, omitted coverage, or a failed tool
cannot acquire the meaning of verification success merely because the pipeline
continued running. Development and incremental-adoption modes may expose useful
partial information, but their meaning must remain distinguishable from an
ordinary successful verification result.

This constraint does not decide the atomic unit of verification, the exact
result format, or how command exit statuses represent incomplete work.

## Rust-level claims require justified Rust semantics

A theorem about a mathematical model supports a claim about Rust only when the
model is connected soundly to the Rust behavior being claimed.

This matters especially for undefined behavior. Anneal cannot simply assume the
whole program is UB-free in order to obtain a faithful model and then cite a
theorem about that model as proof that the program is UB-free. Whatever model
and translation pipeline Anneal uses must provide a justified route from the
Rust program to the proof obligations whose discharge rules out undefined
behavior.

In particular, any sound design must ensure both that:

- the obligations Anneal requires are strong enough to establish the relevant
  Rust validity conditions; and
- every operation and behavior relevant to the reported promise is accounted
  for rather than disappearing because a model, translator, or proof interface
  did not represent it.

User-defined specifications cannot weaken or erase the Rust conditions needed
for well-defined behavior. Conversely, Anneal cannot determine whether a
user-defined property captures what its author intended; it can establish the
property that was actually specified.

This document does not choose the proof of correspondence, the extraction point,
the unit of coverage, or which parts of that connection are initially proved
rather than trusted.

## Verification composes through abstraction boundaries

Anneal should let an implementation establish a promise once at an abstraction
boundary and let clients rely on that promise without reopening the private
implementation.

For a safe Rust API, this includes Rust's existing soundness contract: no
hidden, unchecked obligation of a type-correct safe caller may determine whether
the implementation exhibits undefined behavior. An unsafe interface may place
explicit soundness obligations on its caller, just as Rust does today.

The same compositional idea applies to promises beyond soundness. A function,
type, trait, module, crate, or other abstraction may expose requirements and
guarantees that clients can use without depending on its private proof details.
The exact set of useful abstraction boundaries remains a design question.

An abstraction may hide implementation details only when doing so preserves all
semantics relevant to the promise. A pure value-level contract is preferable
when it is faithful. If ownership, provenance, initialization, concurrency,
protocol state, I/O, nondeterminism, or another effect matters to the promise,
the proof boundary must preserve enough of that structure to remain sound.
Simplifying the proof interface must not change the claim being proved.

## Anneal is general over promises and program behaviors

UB-freedom is foundational and always on, but it is not the only property Anneal
exists to prove. The architecture must allow developers to state and prove
additional correctness properties without baking today's anticipated set of
properties into a closed core.

Different promises may require different semantic or proof machinery. Anneal
should share general machinery when the underlying reasoning is genuinely the
same, without forcing unrelated property domains into one representation that
loses important distinctions.

Anneal also aims to support all program *behaviors*, not every Rust source
program. It is acceptable for Anneal to reject a dark corner of Rust syntax or a
particular combination of features when the same intended behavior can be
expressed through a supported form. When practical, Anneal should give the
programmer actionable guidance for reaching that supported form.

Supporting new properties and behaviors must not weaken the meaning of existing
successful results.

## The ordinary interface is Rust-oriented

Ordinary Rust programmers must be able to use Anneal effectively without
learning Lean 4.

Anneal should present unsatisfied obligations in terms that connect directly to
the Rust program: what operation or promise generated the obligation, what must
be true, and what Anneal could not establish. The normal workflow should feel
like an extension of Rust's compiler-enforced reasoning rather than a demand
that every Rust programmer become a formal-methods specialist.

This does not require hiding Lean or other proof machinery. Specialists may need
full access to Lean, Aeneas, resource logics, generated models, or other
low-level interfaces in order to prove novel properties or extend Anneal.
Those interfaces can coexist with a Rust-oriented ordinary path.

Humans, coding agents, and other tools may also differ in how they author or
repair proofs. They must nevertheless operate against the same program
contracts, promises, trust model, and success semantics. A human explanation or
an agent's confidence is not machine-checked evidence merely because it is
persuasive; formal claims come from the accepted checking boundary.

## Trust is explicit and replaceable by evidence

Anneal cannot initially prove every fact on which an end-to-end result depends.
Everything whose correctness the result relies on but Anneal has not established
must remain visible as part of the relevant trusted computing base.

Different kinds of missing evidence may have different consequences. A trusted
external semantic assumption, an unfinished proof, unsupported source behavior,
and a verifier failure need not be treated alike. The detailed taxonomy belongs
in lower-level design documentation, but the distinctions required to interpret
a result must not be erased by an implementation shortcut.

Trust should also be shrinkable. A component or semantic assumption that is
trusted today should be replaceable by stronger checked evidence tomorrow
without requiring unrelated user contracts to be redesigned. Moving an
assumption into another helper, generated artifact, or upstream component does
not reduce trust unless the result no longer depends on its unchecked
correctness.

## Prefer general, minimally sufficient mechanisms

Anneal should use the simplest model that faithfully supports the promises being
made.

When ordinary functional reasoning is sufficient, richer machinery should not
be imposed merely because Anneal must support harder cases elsewhere. When a
promise depends on ownership, effects, traces, concurrency, or other structure,
that structure must not be discarded merely to preserve a simpler proof model.

Likewise, a practical example should normally be treated as evidence about a
broader class of problems. A one-off mechanism can be a useful experiment, but
it should not become architecture merely because it solves the first known use
case. Designs should leave room to increase expressive power and should prefer
reusable abstractions once the underlying problem is understood.

Existing Rust, Lean, Charon, Aeneas, and ecosystem mechanisms are useful when
they solve the general problem faithfully. No particular ownership boundary or
integration technique is itself a principle: downstream adapters, upstream
changes, new libraries, and temporary experiments remain available when they
better preserve Anneal's promises.

## Deliberate non-decisions

This document constrains later design work without deciding it. In particular,
it does not currently determine:

- the atomic subject of a verification result or how build matrices are handled;
- how generated Rust and other generated artifacts participate in a result;
- the taxonomy or selection model for properties and execution outcomes;
- whether type invariants, trait invariants, or other contract forms are
  first-class Anneal concepts;
- the source syntax, location, or language used for specifications and proofs;
- whether obligations are represented as arguments, sidecar theorems, weakest
  preconditions, or another proof encoding;
- the exact mechanism for prose-based or otherwise incremental adoption;
- the detailed classification of axioms, incomplete proofs, unsupported
  behavior, coverage gaps, and tool failures;
- the contents or serialization of the TCB audit log;
- the meaning of particular command names, profiles, warnings, or exit codes;
- the boundary among Anneal, Rust, Charon, Aeneas, Lean, and reusable proof
  libraries; or
- the exact theorem or validation strategy used to justify source/model
  correspondence and complete obligation coverage.

Those questions should be settled by later design work using the principles and
this contract as constraints. An implementation experiment may explore an
answer without silently turning that answer into a project-wide commitment.
