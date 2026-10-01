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

A requirement is a condition on the program's inputs, callers, or environment.
Different guarantees may have different requirements. A requirement for an
additional functional guarantee therefore does not become a requirement for
Anneal's baseline well-definedness guarantee.

For example, a safe binary-search function may guarantee correct membership
results only when its input is sorted. Calling it with an unsorted slice makes
that guarantee inapplicable; it does not invalidate Anneal's guarantee that the
safe call is well-defined.

The scope may describe one concrete build or a precisely defined family of
artifacts and configurations. In either case, it must be precise enough to
determine whether a particular artifact, configuration, execution, or context is
covered.

Proving a developer-defined guarantee establishes the property that was
specified. It does not establish that the specification captures what its author
intended.

## Verification outcomes

For a requested claim and an applicable trust policy, Anneal distinguishes a
**verification result** from a **tainted output**.

A **verification result** is a claim-bearing artifact whose complete TCB satisfies
its trust policy and Anneal's project-wide verification requirements. Anneal's
normal correctness promise in [`PRINCIPLES.md`](PRINCIPLES.md) applies to it.
Unless stated otherwise, this document uses *result* to mean a verification
result.

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

This distinction describes the outcome for a particular claim, not necessarily
the status of an entire invocation. One invocation may process multiple claims
with different outcomes.

## Verification results

A verification result fixes:

- the exact **claim** Anneal established;
- the complete **trusted computing base (TCB)** on which that claim depends; and
- the exact **trust policy** that the TCB satisfies.

Semantically, the result asserts that if the trusted code in its TCB is correct
and its trusted assumptions are valid, then its claim holds.

The meaning of a result must remain stable after it is produced. Everything whose
identity can affect the claim, the TCB, or whether the TCB satisfies its trust
policy must therefore be contained in the result or immutably referenced by it.

Mutable names such as branches, profiles, named specifications, or named policies
may be convenient inputs to verification. A result that depends on them must bind
the specific identities or contents actually used. Later changes must not
retroactively change what an existing result claims or whether its trust boundary
was acceptable.

### Trusted computing base

Every dependency on which Anneal relies without establishing it by checked
evidence belongs in the TCB. This includes both trusted code and trusted
assumptions.

Moving an unchecked dependency into a translator, generated artifact, helper
library, compiler, or other component does not remove it from the TCB while
Anneal's claim still depends on its unchecked correctness.

Every result must expose, or immutably reference, its complete TCB. Trusted code
and assumptions must be identified precisely enough to determine what the result
relies upon. The TCB may refer to other immutable, auditable manifests rather
than duplicating their contents, but trust must not disappear behind an
implementation boundary.

At the logical level, trusted premises are simply premises. Why a premise is
trusted does not change the conditional claim Anneal establishes, although its
identity, role, and provenance may matter to the trust policy and to auditing.

### Trust policy

A **trust policy** defines the permitted boundary between checked evidence and the
TCB for a verification result.

It may constrain which components or assumptions may be trusted, or which links
in the reasoning from the reported guarantee back to Rust must instead be
established by checked evidence. Anything outside the permitted trust boundary
must be checked rather than silently admitted into the TCB.

Every result must contain or immutably reference the exact trust policy against
which its TCB was evaluated.

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

## End-to-end Rust guarantees

Every verification result establishes at least that:

1. the Rust executions within its scope are well-defined; and
2. the behavior of the compiled artifact corresponds to the Rust source semantics
   strongly enough to preserve every guarantee Anneal reports.

The second guarantee does not require the source and compiled program to have
literally identical sets of behaviors. Their relationship need only be strong
enough to justify carrying the reported guarantees from source semantics to
compiled behavior.

A theorem about an intermediate model supports a Rust-level guarantee only when
the connection between Rust and that model is itself checked or represented in
the TCB.

The claim's scope must cover the source and compiled artifacts, or precisely
characterized families of artifacts, for which this end-to-end relationship was
established. Verifying one source or build must not bless a different binary
merely because both belong to the same nominal project or package.

## Closed programs and libraries

Anneal's baseline well-definedness guarantee applies both to closed programs and
to libraries, but the surrounding conditions differ.

### Closed programs

For a closed program, the guarantee applies to complete executions within the
claim's scope.

Anneal may establish this using local proofs, component contracts, whole-program
reasoning, or another sound method. Regardless of proof strategy, those
intermediate judgments must justify the whole-program guarantee. Showing that one
function or thread is locally well-behaved is insufficient if another part of the
same covered execution can exhibit undefined behavior.

Developer-defined guarantees apply only at the scopes and under the requirements
stated by the claim. Local facts must not be presented as whole-program guarantees
unless they establish them.

### Libraries

A library's guarantees are necessarily contextual. Its API contract uses the same
claim model described above: requirements are facts a caller must establish and
the implementation may assume; guarantees are facts the implementation must
establish and a caller satisfying the corresponding requirements may rely upon.

For the baseline well-definedness guarantee, Anneal must establish that replacing
the abstract API contract with the verified implementation preserves
well-definedness for every surrounding context that:

- is itself well-defined when interacting with the abstract API contract; and
- satisfies the caller requirements of that baseline guarantee.

Other guarantees apply analogously to contexts satisfying their corresponding
requirements.

The lower-level formal model may express this contextual relationship in
different ways, but it must not depend on an informal judgment that undefined
behavior was "caused by" or "attributable to" the library.

#### Safe and unsafe APIs

Well-defined Rust behavior alone does not capture every assumption that Rust
convention permits an API implementation to make.

Some APIs rely on **API or library invariants** stronger than Rust's requirements
for well-defined execution. For example, Rust libraries may assume that a `str`
contains valid UTF-8 even though constructing a non-UTF-8 `str` is not itself
immediate undefined behavior.

For a safe API, Anneal's baseline guarantee must hold for every type-correct use
from an otherwise well-defined context that satisfies the API or library
invariants Rust convention permits the implementation to rely upon.

A safe API may not impose any other hidden caller requirement needed for its
baseline well-definedness guarantee. A caller satisfying the conditions above
must not be able to trigger undefined behavior merely because some additional
unstated condition was false.

Other developer-defined guarantees may have additional requirements. Those
requirements constrain only their corresponding guarantees; they cannot weaken
the baseline guarantee of a safe API.

For an unsafe API, the baseline guarantee may additionally require the caller to
satisfy the API's explicit safety requirements.

Because the surrounding context must already be well-defined under Rust
semantics, an unsafe API cannot relax a condition whose violation is itself
undefined behavior.

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
