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
results must mean in order to uphold them.

The principles are authoritative. If this document conflicts with them, this
document must be corrected. It constrains semantics, not the mechanisms used to
implement them.

## What an Anneal claim means

An Anneal claim identifies:

- a **scope**: the program artifacts, configurations, and executions to which the
  claim applies; and
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
determine whether a particular artifact, configuration, and execution is covered.

Proving a developer-defined guarantee establishes the property that was
specified. It does not establish that the specification captures what its author
intended.

## What a successful result establishes

An ordinary successful Anneal result fixes:

- the exact **claim** Anneal established;
- the complete **trusted computing base (TCB)** on which that claim depends; and
- the exact **assurance policy** under which that TCB was accepted.

These must have stable meaning. Everything whose identity can affect the claim or
whether the result qualifies as successful must be contained in the result or
immutably referenced by it.

Mutable names such as branches, profiles, or named policies may be convenient
inputs to verification. The result must bind the specific artifacts,
specifications, configurations, policies, and other relevant inputs that were
actually used. Later changes to those inputs must not change the meaning or
success status of an existing result.

### The TCB contains all unchecked trust

Every fact Anneal needs in order to justify a claim must either be established by
checked evidence or represented in the TCB.

An unchecked assumption does not stop being trusted because it is encapsulated
inside a translator, generated artifact, helper library, compiler, or another
component.

Every successful result must expose, or immutably reference, its complete TCB.
Trusted code and assumptions must be identified precisely enough to determine
what the result relies upon. The TCB may refer to other immutable, auditable
manifests rather than duplicating their contents, but trust must not disappear
behind an implementation boundary.

At the logical level, trusted premises are simply premises. Why a premise is
trusted does not change the conditional claim Anneal establishes, although its
identity and provenance may matter when deciding whether that trust is acceptable.

### The assurance policy constrains acceptable trust

Recording every unchecked premise is not enough to make verification successful.
Otherwise Anneal could fail to prove an obligation, add that obligation to the
TCB, and report success.

The assurance policy defines which unchecked premises may appear in the TCB while
the result still counts as successful. It may identify trusted components,
semantic boundaries, classes of assumptions, guarantees that must be established
by checked evidence, or other principled trust boundaries.

A successful result must contain or immutably reference the exact assurance
policy against which its TCB was evaluated. A mutable policy name may select that
policy before verification, but changing the name's definition later must not
change an existing result.

An unfinished proof, skipped analysis, unsupported operation, or failed tool does
not itself authorize new trust. If the resulting unchecked premise is not
permitted by the applicable assurance policy, Anneal has not produced a successful
result.

Anneal's principles also impose minimum assurance requirements that a policy
cannot weaken. In particular, a required UB obligation cannot become ordinary
verification success merely by moving it into the TCB.

Anneal may provide development-only modes that bypass UB checks or turn them into
warnings. Such outputs are not ordinary successful verification results and must
clearly label both the result and its TCB audit log as tainted or irreparably
untrustworthy, as required by [`PRINCIPLES.md`](PRINCIPLES.md).

## Every successful result makes an end-to-end Rust claim

Every ordinary successful result establishes at least that:

1. the Rust executions within its scope are well-defined; and
2. the behavior of the compiled artifact corresponds to the Rust source semantics
   strongly enough to preserve every guarantee Anneal reports.

The second guarantee does not require the source and compiled program to have
literally identical sets of behaviors. Their relationship need only be strong
enough to justify transferring the reported guarantees from source semantics to
compiled behavior.

A theorem about an intermediate model supports a Rust-level guarantee only when
the connection between Rust and that model is itself checked or represented in
the TCB.

The claim's scope must cover the source and compiled artifacts, or precisely
characterized families of artifacts, for which this end-to-end relationship was
established. Verifying one source or build must not bless a different binary
merely because both belong to the same nominal project or package.

## Well-definedness depends on what is being verified

Anneal's baseline well-definedness guarantee has the same purpose for closed
programs and libraries, but their scopes differ.

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

A library cannot guarantee the behavior of an arbitrary surrounding program.
Anneal therefore verifies a library relative to an API contract and quantifies
its guarantees over **admissible contexts**.

The API contract uses the same model as any other Anneal claim: its requirements
are facts a caller must establish and the implementation may assume; its
guarantees are facts the implementation must establish and a caller satisfying
the corresponding requirements may rely upon.

An admissible context must itself have well-defined Rust behavior when interacting
with the abstract API contract. An API contract cannot make behavior defined that
Rust semantics already makes undefined.

Anneal's library guarantee is contextual: replacing the abstract API contract
with the verified implementation in an admissible context must preserve
well-definedness and every other guarantee whose requirements that context
satisfies.

The lower-level formal model may express this relationship in different ways, but
it must not depend on an informal judgment that undefined behavior was "caused
by" or "attributable to" the library.

#### Safe and unsafe API conventions

Well-defined Rust behavior alone does not capture every assumption that Rust
convention permits an API implementation to make.

Some APIs rely on **API or library invariants** stronger than Rust's requirements
for well-defined execution. For example, Rust libraries may assume that a `str`
contains valid UTF-8 even though constructing a non-UTF-8 `str` is not itself
immediate undefined behavior.

For a safe API, Anneal's baseline guarantee must hold for every well-defined,
type-correct use that also satisfies the API or library invariants Rust convention
permits the implementation to rely upon.

A safe API may not impose any other hidden caller requirement needed for its
baseline well-definedness guarantee. A caller satisfying the conditions above
must not be able to trigger undefined behavior merely because some additional
unstated condition was false.

Other developer-defined guarantees may have additional requirements. Those
requirements constrain only their corresponding guarantees; they cannot weaken
the baseline guarantee of a safe API.

For an unsafe API, admissible use additionally requires satisfying the API's
explicit safety requirements. Anneal's baseline guarantee is conditional on those
requirements.

Because an admissible context must already be well-defined under Rust semantics,
an unsafe API cannot relax a condition whose violation is itself undefined
behavior.

Stronger API or library invariants are different. Some unsafe APIs may need to
accept values that violate invariants normally associated with their types.
Whether Anneal permits an unsafe API contract to relax such an invariant, and how
that permission is expressed, remains unresolved.

## Anneal remains open-ended

Well-definedness is mandatory, but developers must also be able to state and prove
additional correctness guarantees. Anneal must not fix today's anticipated
guarantees as a closed universe.

Anneal likewise aims to support all program *behaviors*, not every Rust source
program. It may reject particular language features or combinations of features
when the same intended behavior can be expressed in a supported way. When
practical, it should give the programmer actionable guidance toward such a form.

Adding support for new guarantees or behaviors must preserve the meaning of
existing successful results.

## The ordinary interface is Rust-oriented

Ordinary Rust programmers must be able to use Anneal effectively without learning
Lean 4.

When Anneal cannot establish an obligation, its ordinary interface should connect
the failure to the Rust program: what operation or guarantee generated the
obligation, what must be true, and what Anneal could not establish.

The normal workflow should therefore feel like an extension of Rust's existing
compiler-enforced reasoning rather than requiring every Rust programmer to become
a formal-methods specialist.
