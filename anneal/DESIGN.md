<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal design contract

This document derives semantic constraints from Anneal's
[`PRINCIPLES.md`](PRINCIPLES.md). The principles define Anneal's promises,
beliefs, and rules for making decisions. This document defines what Anneal's
claims and verification outputs must mean in order to uphold them.

The principles are authoritative. If this document conflicts with them, this
document must be corrected. It constrains semantics, not the mechanisms used to
implement them.

## Claims

An Anneal claim identifies:

- a **scope**: the program artifacts and configurations it concerns, and the
  executions or contexts over which it ranges; and
- one or more **guarantees**, each with any **requirements** under which that
  guarantee applies.

The scope must determine precisely which artifacts, configurations, executions,
or contexts are covered. Within that scope, each guarantee is conditional on its
own requirements. A requirement for one guarantee does not become a requirement
for another.

For example, a safe binary-search function may guarantee correct membership
results when its input is sorted. Calling it with an unsorted slice makes that
guarantee inapplicable; it does not invalidate Anneal's baseline well-definedness
guarantee.

Proving a developer-defined guarantee establishes the property that was
specified. It does not establish that the specification captures what its author
intended.

## Verification results

A **verification result** is a claim-bearing artifact that satisfies Anneal's
project-wide verification requirements and to which Anneal's normal correctness
promise in [`PRINCIPLES.md`](PRINCIPLES.md) applies.

A verification result fixes:

- the exact **claim** Anneal established;
- the complete **trusted computing base (TCB)** on which that claim depends; and
- the exact **trust policy** against which that TCB was evaluated.

Semantically, a verification result asserts both that:

1. its TCB satisfies its trust policy; and
2. if the trusted code in its TCB is correct and its trusted assumptions are
   valid, then its claim holds.

The first assertion establishes that the unchecked trust in the verification
result is permitted. The second establishes the claim under that trust.

The meaning of a verification result must remain stable after it is produced. It
must therefore contain or immutably reference everything whose identity can
affect its claim, its TCB, or whether its TCB satisfies its trust policy. Mutable
names such as branches, profiles, named specifications, or named policies may be
used as inputs, but the verification result must bind the specific identities or
contents actually used.

### Trusted computing base

Every dependency on which Anneal relies without establishing it by checked
evidence belongs in the TCB. This includes both trusted code and trusted
assumptions.

A guarantee's stated requirements are not TCB assumptions merely because Anneal
assumes them when proving that guarantee. They are hypotheses stated by the claim
itself. By contrast, an unchecked premise belongs in the TCB when Anneal relies on
it to justify the claim without making the claim conditional on that premise.

A verification result must identify its complete TCB precisely enough to audit
what it relies upon, either directly or through immutable references. Moving an
unchecked dependency into a translator, generated artifact, helper library,
compiler, or other component does not remove it from the TCB while Anneal's claim
still depends on its unchecked correctness.

### Trust policy

A **trust policy** defines the permitted boundary between checked evidence and the
TCB for a verification result.

It may constrain which components or assumptions may remain trusted, or which
links in the reasoning from a reported guarantee back to Rust must instead be
established by checked evidence. Anything outside the permitted trust boundary
must be checked rather than silently admitted into the TCB.

An unfinished proof, skipped analysis, unsupported operation, or failed tool does
not itself authorize new trust. If Anneal needs the missing fact and the
applicable trust policy does not permit it to remain unchecked, Anneal cannot
issue a verification result under that policy.

Selecting a different, permitted trust policy explicitly changes the verification
being requested; it is not itself a bypass. Anneal must not silently weaken the
applicable policy merely because verification under the original policy failed.

A trust policy cannot waive Anneal's project-wide verification requirements. In
particular, mandatory UB verification cannot be waived by choosing a more
permissive policy.

## Verification outcomes

For a requested claim and trust policy, Anneal cannot issue a verification result
unless it can establish the claim with a TCB that satisfies the policy while also
meeting Anneal's project-wide verification requirements.

When Anneal cannot do so, it may still emit diagnostics, partial checked evidence,
proof state, or other development artifacts. Those artifacts do not acquire
verification-result semantics merely because Anneal produced them.

If Anneal deliberately bypasses a condition required for a verification result
and emits a claim-bearing development artifact, that artifact is a **tainted
output**. A tainted output is not a verification result and must not be interpreted
as one. In particular, when Anneal bypasses mandatory UB verification or turns it
into a warning, both the output and its TCB audit log must be clearly labeled as
tainted or irreparably untrustworthy.

These outcomes apply to individual claims. One invocation may process multiple
claims with different outcomes.

## Guarantees apply to compiled Rust behavior

Anneal may state specifications in terms of Rust source and may prove them using
intermediate semantic models. The guarantees in a verification result must
nevertheless apply to the covered behavior of code produced by `rustc`.

Every connection needed to carry a guarantee from the Rust source or an
intermediate model to the compiled behavior covered by the claim must itself be
established by checked evidence or included in the TCB.

The required source-to-compiled relationship need not imply that source and
compiled code have literally identical sets of behaviors. It must be strong
enough to justify every guarantee Anneal reports.

Accordingly, the claim's scope must identify the compiled realization or
precisely defined family of compiled realizations to which its guarantees apply.
It need not always identify a single final executable. Verifying one source or
build must not bless a materially different compiled realization merely because
both belong to the same nominal project or package.

## Baseline well-definedness

Every verification result includes a guarantee that its covered compiled Rust
behavior is well-defined. Anneal's principles constrain the requirements under
which this baseline guarantee may apply.

### Whole programs

The scope of a whole-program claim ranges over complete executions of covered
compiled realizations.

The baseline well-definedness guarantee may require conditions on external inputs
or environment, but it must not assume the well-definedness of the program
behavior that Anneal is supposed to establish.

Anneal may prove this guarantee using local proofs, component contracts,
whole-program reasoning, or another sound method. Regardless of proof strategy,
those intermediate judgments must justify the guarantee about the complete
execution.

For example, proving that one function or thread is locally well-behaved does not
by itself justify even a local Rust-level behavioral claim about an execution if
another part of that execution may exhibit undefined behavior, because undefined
behavior can invalidate the semantics of the entire execution.

### Libraries

The scope of a library claim ranges over executions in surrounding contexts that
use covered compiled realizations of the library.

A library guarantee's requirements may constrain its caller or surrounding
context. Anneal may assume those requirements when verifying the implementation,
and a caller may rely on the corresponding guarantee when they hold.

The baseline well-definedness guarantee has a contextual requirement: the
surrounding execution must be well-defined when the library is replaced by its
abstract API contract. Its guarantee is that the execution remains well-defined
when the verified implementation is substituted.

This requirement constrains the surrounding context rather than assuming the
well-definedness of the implementation being verified. The lower-level formal
model may express the contextual relationship in different ways, but it must not
depend on an informal judgment that undefined behavior was "caused by" or
"attributable to" the library.

#### Safe and unsafe APIs

Rust's API conventions further constrain the caller requirements permitted for a
library's baseline well-definedness guarantee.

Among contexts satisfying the contextual requirement above, a safe API's baseline
guarantee must cover every type-correct use satisfying the API or library
invariants Rust convention permits the implementation to rely upon. It may impose
no further caller requirement.

Some such invariants are stronger than Rust's requirements for well-defined
execution. For example, Rust libraries may assume that a `str` contains valid
UTF-8 even though constructing a non-UTF-8 `str` is not itself immediate undefined
behavior.

For an unsafe API, the baseline well-definedness guarantee may additionally
require the caller to satisfy the API's explicit safety requirements.

Because the contextual requirement already requires the surrounding execution to
be well-defined under Rust semantics, an unsafe API cannot relax a condition whose
violation is already undefined behavior.

Stronger API or library invariants are different. Some unsafe APIs may need to
accept values that violate invariants normally associated with their types.
Whether Anneal permits an unsafe API contract to relax such an invariant, and how
that permission is expressed, remains unresolved.

## Open-ended guarantees and behaviors

Beyond baseline well-definedness, developers must be able to state and prove
additional correctness guarantees. Anneal must not fix today's anticipated
guarantees as a closed universe.

Anneal likewise aims to support all program *behaviors*, not every Rust source
program. It may reject particular language features or combinations of features
when the same intended behavior can be expressed in a supported way. When
practical, it should give the programmer actionable guidance toward such a form.

## Rust-oriented interface

Ordinary Rust programmers must be able to use Anneal effectively without learning
Lean 4.

When Anneal cannot establish an obligation, its ordinary interface should connect
the failure to the Rust program: what operation or guarantee generated the
obligation, what must be true, and what Anneal could not establish.

The normal workflow should therefore feel like an extension of Rust's existing
compiler-enforced reasoning rather than requiring every Rust programmer to become
a formal-methods specialist.
