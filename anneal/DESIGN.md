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

The scope determines what the claim is about. The requirements of a guarantee are
hypotheses under which that guarantee applies. Thus, for every execution or
context covered by the scope, Anneal claims that if a guarantee's requirements
hold, then that guarantee holds.

Different guarantees may have different requirements. A requirement for one
guarantee does not become a requirement for another.

Requirements are part of the claim, not part of the TCB. Anneal may assume a
guarantee's requirements when proving that guarantee. By contrast, an unchecked
fact that Anneal itself relies upon to justify the implication from requirements
to guarantee belongs in the TCB.

For example, a safe binary-search function may guarantee correct membership
results when its input is sorted. Calling it with an unsorted slice makes that
guarantee inapplicable; it does not invalidate Anneal's baseline well-definedness
guarantee.

The scope may describe one concrete build or a precisely defined family of
artifacts, configurations, executions, or contexts. It must be precise enough to
determine whether a particular artifact, configuration, execution, or context is
covered before asking whether the requirements of any guarantee hold.

Requirements must not be used merely to assume the behavior that a guarantee is
supposed to establish. In particular, Anneal's baseline well-definedness guarantee
cannot be made vacuous by requiring the covered subject itself to already be
well-defined. Later sections further constrain the permissible requirements of
that guarantee for whole programs and libraries.

Proving a developer-defined guarantee establishes the property that was
specified. It does not establish that the specification captures what its author
intended.

## Verification outcomes

For a requested claim and an applicable trust policy, Anneal distinguishes a
**verification result** from a **tainted output**.

A **verification result** is a claim-bearing artifact to which Anneal's normal
correctness promise in [`PRINCIPLES.md`](PRINCIPLES.md) applies. A verification
result makes the trust-policy and conditional-correctness assertions defined
below and satisfies Anneal's project-wide verification requirements.

A **tainted output** is a claim-bearing development artifact emitted even though
the conditions for a verification result were deliberately bypassed. A tainted
output is not a verification result and must not be interpreted as one. In
particular, when Anneal bypasses mandatory UB verification or turns it into a
warning, both the output and its TCB audit log must be clearly labeled as tainted
or irreparably untrustworthy.

If Anneal cannot establish a requested claim with a TCB permitted by the
applicable trust policy, it cannot issue a verification result for that claim
under that policy. It may still emit diagnostics, partial checked evidence, proof
state, or other development artifacts. Those artifacts do not acquire
verification-result semantics merely because Anneal produced them.

This distinction applies to individual claims. One invocation may process
multiple claims with different outcomes.

## Verification results

A verification result fixes:

- the exact **claim** Anneal established;
- the complete **trusted computing base (TCB)** on which that claim depends; and
- the exact **trust policy** that the TCB satisfies.

Semantically, a verification result asserts both that:

1. its TCB satisfies its trust policy; and
2. if the trusted code in its TCB is correct and its trusted assumptions are
   valid, then, for every guarantee in its claim, that guarantee holds throughout
   its scope whenever that guarantee's requirements hold.

The first assertion establishes that the unchecked trust in the verification
result is permitted. The second is the conditional correctness claim that Anneal
has established about the program.

The meaning of a verification result must remain stable after it is produced.
Everything whose identity can affect the claim, the TCB, or whether the TCB
satisfies its trust policy must therefore be contained in the verification result
or immutably referenced by it.

Mutable names such as branches, profiles, named specifications, or named policies
may be convenient inputs to verification. A verification result that depends on
them must bind the specific identities or contents actually used. Later changes
must not retroactively change what an existing verification result claims or
whether its TCB satisfies its trust policy.

### Trusted computing base

Every dependency on which Anneal relies without establishing it by checked
evidence belongs in the TCB. This includes both trusted code and trusted
assumptions.

Moving an unchecked dependency into a translator, generated artifact, helper
library, compiler, or other component does not remove it from the TCB while
Anneal's claim still depends on its unchecked correctness.

Every verification result must expose, or immutably reference, its complete TCB.
Trusted code and assumptions must be identified precisely enough to determine
what the verification result relies upon. The TCB may refer to other immutable,
auditable manifests rather than duplicating their contents, but trust must not
disappear behind an implementation boundary.

At the logical level, trusted premises are simply premises. Why a premise is
trusted does not change the conditional claim Anneal establishes, although its
identity, role, and provenance may matter to the trust policy and to auditing.

### Trust policy

A **trust policy** defines the permitted boundary between checked evidence and the
TCB for a verification result.

It may constrain which components or assumptions may be trusted, or which links
in the reasoning from a reported guarantee back to Rust must instead be
established by checked evidence. Anything outside the permitted trust boundary
must be checked rather than silently admitted into the TCB.

Every verification result must contain or immutably reference the exact trust
policy against which its TCB was evaluated.

An unfinished proof, skipped analysis, unsupported operation, or failed tool does
not itself authorize new trust. If Anneal needs the missing fact and the
applicable trust policy does not permit it to remain unchecked, Anneal cannot
issue a verification result under that policy.

Selecting a different, permitted trust policy explicitly changes the verification
being requested; it is not itself a bypass. Anneal must not silently weaken the
applicable policy merely because verification under the original policy failed.

Anneal's project-wide requirements constrain every trust policy. In particular,
mandatory UB verification cannot be waived by choosing a more permissive policy.
A development mode may bypass or downgrade that requirement only by producing a
tainted output rather than a verification result.

## Guarantees apply to compiled Rust behavior

Anneal may state specifications in terms of Rust source and may prove them using
intermediate semantic models. The guarantees in a verification result must
nevertheless apply to the covered behavior of code produced by `rustc`.

Anneal must therefore establish, or include in the TCB, every connection needed
to carry each guarantee from the Rust source and any intermediate models to the
compiled behavior covered by the claim. A theorem about an intermediate model
does not support a Rust-level guarantee unless the required connection to Rust is
also justified.

The required source-to-compiled relationship need not imply that source and
compiled code have literally identical sets of behaviors. It must be strong
enough to justify every guarantee Anneal reports.

The scope of a claim may identify one compiled artifact or a precisely defined
family of compiled realizations. A whole-program claim may, for example, cover a
particular executable. A library claim may instead cover compiled realizations of
the library when incorporated into downstream programs. A library verification
result therefore need not name one final executable in advance.

In every case, the scope must define the compilation domain precisely enough to
determine whether a compiled realization is covered. Verifying one source or
build must not bless a materially different compiled realization merely because
both belong to the same nominal project or package.

Every verification result includes a baseline guarantee that the covered compiled
Rust behavior is well-defined whenever the requirements of that guarantee hold.

## Whole programs and libraries

Whole-program and library claims use the same claim model. They differ in what
their scopes cover and in the requirements that Anneal permits for their
guarantees.

### Whole programs

For a whole program, the scope covers the complete program and a set of
whole-program executions.

The baseline well-definedness guarantee says that every covered execution
satisfying its requirements is well-defined. Those requirements may constrain
external inputs or environment where appropriate, but they must not assume
well-definedness of the program behavior that Anneal is supposed to establish.

Anneal may prove this guarantee using local proofs, component contracts,
whole-program reasoning, or another sound method. Regardless of proof strategy,
those intermediate judgments must justify the guarantee about the complete
execution.

For example, proving that one function or thread is locally well-behaved does not
by itself justify even a local Rust-level behavioral claim about an execution if
another part of that execution may exhibit undefined behavior, because undefined
behavior can invalidate the semantics of the entire execution.

Developer-defined guarantees follow the same model. Each applies to the covered
executions that satisfy its own requirements. A local fact must not be presented
as a guarantee over a larger scope unless it actually establishes that guarantee.

### Libraries

For a library, the scope covers the library implementation and a defined family
of compiled realizations, surrounding contexts, and executions in which the
library may be used.

The same conditional-guarantee model applies. A guarantee's requirements may
constrain the caller or surrounding context. To rely on the guarantee, the caller
must satisfy those requirements. When verifying the library implementation,
Anneal may assume those requirements and must establish the corresponding
guarantee. A caller satisfying them may then rely on that guarantee.

These are the proof roles induced by the generic claim model; they are not a
separate notion of API contract.

For the baseline well-definedness guarantee, Anneal must establish that replacing
the abstract API contract with the verified implementation preserves
well-definedness for every covered surrounding context satisfying that guarantee's
requirements.

The baseline requirements include that the surrounding context is itself
well-defined when interacting with the abstract API contract. This constrains the
context rather than assuming well-definedness of the implementation being
verified. It therefore does not make the library's baseline guarantee circular.

Other guarantees work the same way: each applies to the covered contexts and
executions that satisfy its own requirements.

The lower-level formal model may express this contextual relationship in
different ways, but it must not depend on an informal judgment that undefined
behavior was "caused by" or "attributable to" the library.

#### Safe and unsafe APIs

Rust's API conventions further constrain the requirements permitted for a
library's baseline well-definedness guarantee.

For a safe API, the baseline guarantee must apply to every covered, type-correct
use from an otherwise well-defined context that satisfies the API or library
invariants Rust convention permits the implementation to rely upon.

Some such invariants are stronger than Rust's requirements for well-defined
execution. For example, Rust libraries may assume that a `str` contains valid
UTF-8 even though constructing a non-UTF-8 `str` is not itself immediate undefined
behavior.

A safe API may not impose any additional hidden caller requirement needed for its
baseline well-definedness guarantee. A caller satisfying the conditions above
must not be able to trigger undefined behavior merely because some additional
unstated condition was false.

Developer-defined guarantees may have additional requirements. Those requirements
constrain only the corresponding guarantees; they do not narrow the baseline
well-definedness guarantee of a safe API.

For an unsafe API, the baseline well-definedness guarantee may additionally
require the caller to satisfy the API's explicit safety requirements.

Because the surrounding context must itself be well-defined under Rust semantics,
an unsafe API cannot relax a condition whose violation is already undefined
behavior.

Stronger API or library invariants are different. Some unsafe APIs may need to
accept values that violate invariants normally associated with their types.
Whether Anneal permits an unsafe API contract to relax such an invariant, and how
that permission is expressed, remains unresolved.

## Open-ended guarantees and behaviors

Well-definedness is mandatory, but developers must also be able to state and prove
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
