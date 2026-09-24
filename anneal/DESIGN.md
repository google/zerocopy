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

## Verification results have stable meaning

An ordinary successful Anneal result fixes three things:

- the **claim** Anneal established;
- the complete **trusted computing base (TCB)** on which that claim depends; and
- the **assurance policy** under which that TCB was accepted.

Everything whose identity can affect the meaning of the claim or whether the
result qualifies as successful must be fixed by the result, either directly or
through an immutable reference.

A later change to source code, generated input, a specification, a dependency, a
TCB manifest, an assurance policy, or another referenced input must not
retroactively change what an existing result means or whether it qualified as
successful when produced.

Mutable names and configuration such as branches, profiles, or named policies may
be convenient inputs to verification. A result that depends on them must bind the
specific identities or contents that were actually used.

## Anneal proves conditional guarantees

An Anneal claim has a **scope** and one or more **guarantee clauses**.

The scope identifies the program artifacts, configurations, and executions to
which the claim applies.

Each guarantee clause has:

- **requirements** under which the clause applies; and
- a **guarantee** that holds within the claim's scope when those requirements are
  satisfied.

Different guarantees may therefore have different requirements. A requirement
for an additional functional guarantee does not automatically become a
requirement for Anneal's baseline well-definedness guarantee.

The scope must bind the claim unambiguously to what was actually verified. A
result for one revision, generated input, dependency set, feature configuration,
target, profile, compiled artifact, or other relevant input must not silently
apply to materially different code or configuration.

A claim may cover a precisely defined family rather than a single concrete build.
In either case, its scope must be precise enough to determine whether a particular
artifact, configuration, and execution is covered.

Requirements and trusted assumptions play different roles. A requirement is a
condition on the program's inputs, callers, or environment. It must be satisfied
when the corresponding guarantee is used. A trusted assumption is an unchecked
premise in Anneal's reasoning that the guarantee follows from its requirements.

## Successful verification has an auditable trust boundary

Anneal establishes its claims using checked evidence and a TCB.

Every fact Anneal itself needs to justify a reported claim must either be
established by checked evidence or represented in the TCB. An unchecked
assumption does not stop being trusted merely because it is encapsulated in a
translator, generated artifact, helper library, compiler, or other component.

Every successful result must expose, or immutably reference, the complete TCB on
which its guarantees depend. Trusted code and assumptions must be identified
precisely enough to determine what the result relies upon. A TCB may itself refer
to other immutable, auditable manifests rather than duplicating their contents,
but trust must not disappear behind an implementation boundary.

Merely recording every unchecked premise is not sufficient for verification
success. Otherwise, Anneal could fail to prove an obligation, add that obligation
to the TCB, and report success without providing the assurance the user requested.

A successful result is therefore also evaluated against an **assurance policy**.
The assurance policy constrains which unchecked premises may appear in the TCB
while the result still counts as successful. It may identify trusted components,
semantic boundaries, classes of assumptions, guarantees that must be established
by checked evidence, or other principled trust boundaries.

The result must contain or immutably reference the exact assurance policy under
which it reports success. A mutable policy name may select a policy before
verification, but later changes to that name must not alter the interpretation of
an existing result.

An unfinished proof, skipped analysis, unsupported operation, or failed tool does
not by itself authorize new trust. If the resulting unchecked premise is not
permitted by the applicable assurance policy, Anneal has not produced a successful
result.

The project principles impose minimum assurance requirements that an assurance
policy cannot weaken. In particular, a required UB obligation cannot become an
ordinary successful verification result merely by moving that obligation into the
TCB.

Anneal may provide development-only modes that bypass UB checks or turn them into
warnings. Such outputs do not have ordinary successful-verification semantics and
must clearly label both the result and its TCB audit log as tainted or irreparably
untrustworthy, as required by `PRINCIPLES.md`.

At the logical level, trusted premises are simply premises: why a fact is trusted
does not change the conditional claim Anneal has established. Its identity or
provenance may nevertheless matter to the assurance policy, auditing, diagnostics,
or other interpretation of the result.

Checked evidence about an intermediate model supports a Rust-level guarantee only
if the connection from Rust to that model is itself checked or represented in the
TCB.

## Anneal connects source-level guarantees to compiled behavior

Anneal ultimately makes claims about code produced by `rustc`, not only about an
intermediate mathematical model.

Every successful Anneal result includes baseline guarantee clauses establishing
that:

1. the Rust executions covered by the claim are well-defined; and
2. the behavior of the compiled artifact corresponds to the Rust source semantics
   strongly enough to preserve the guarantees Anneal reports.

The second guarantee need not mean that the source and compiled program have
literally identical sets of behaviors. The required relationship is whatever is
strong enough to justify carrying each reported source-level guarantee to the
compiled code.

The claim's scope must bind this end-to-end guarantee to the source and compiled
artifacts, or precisely characterized families of artifacts, for which that
relationship was established. Verifying one source or build must not bless a
different binary merely because they belong to the same nominal project or
package.

Developers may ask Anneal to prove additional guarantees beyond well-definedness.
Those guarantees may have their own requirements. For example, a safe binary
search function may guarantee correct membership results only when its input is
sorted. Calling it with an unsorted slice makes that guarantee inapplicable; it
does not invalidate Anneal's baseline guarantee that the safe call is
well-defined.

Proving a developer-defined guarantee establishes the property that was
specified. It does not establish that the specification captures what its author
intended.

## Closed-program guarantees cover complete executions

For a closed program, Anneal's well-definedness guarantee applies to complete
executions covered by the claim.

Anneal may establish this guarantee using local proofs, component contracts,
whole-program reasoning, or another sound method. Regardless of the proof
strategy, those intermediate judgments must ultimately justify the whole-program
claim. Showing that one function or thread is locally well-behaved is insufficient
if another part of the same covered execution can exhibit undefined behavior.

Additional developer-defined guarantees apply at the scopes and under the
requirements stated by their guarantee clauses. Anneal must not infer a
whole-program guarantee from local facts that do not establish it.

## Library guarantees are contextual

A library cannot guarantee the behavior of an arbitrary surrounding program.
Instead, Anneal verifies an implementation relative to an API contract and
quantifies its guarantees over **admissible contexts**.

An API contract contains guarantee clauses just like any other Anneal claim. Its
requirements are conditions a caller must satisfy and that the implementation may
assume. Its guarantees are conditions the implementation must establish and that a
caller satisfying the corresponding requirements may rely upon.

An admissible context must itself have well-defined Rust behavior when interacting
with the abstract API contract. This already excludes contexts that violate Rust's
language-level requirements for well-defined execution; an API contract cannot
make behavior defined that Rust semantics already makes undefined.

Anneal's library guarantee is contextual: replacing the abstract API contract
with the verified implementation in an admissible context must preserve the
baseline well-definedness guarantee and the other guarantees whose requirements
the context satisfies.

The exact formal account of this contextual relationship is a lower-level design
question. It must be precise enough that the guarantee does not depend on an
informal judgment about whether undefined behavior was "caused by" or
"attributable to" the library.

### Admissible use follows Rust's API conventions

Well-defined Rust behavior alone does not capture every assumption that Rust
convention permits an API implementation to make.

Some Rust APIs rely on **API or library invariants** that are stronger than the
language requirements for well-defined execution. For example, Rust libraries may
assume that a `str` contains valid UTF-8 even though constructing a non-UTF-8
`str` is not itself immediate undefined behavior.

For a safe API, Anneal's baseline guarantee must hold for every well-defined,
type-correct use that also satisfies the API or library invariants that Rust
convention permits the implementation to rely upon.

A safe API may not impose an additional hidden caller requirement needed for its
baseline well-definedness guarantee. A caller meeting the conditions above must
not be able to trigger undefined behavior merely because it failed to satisfy some
other unstated condition.

Additional developer-defined guarantees may have additional requirements. Those
requirements limit only their corresponding guarantees; violating them must not
invalidate the baseline guarantee of a safe API.

For an unsafe API, admissible use additionally requires satisfying the API's
explicit safety requirements. Anneal's baseline guarantee is conditional on those
requirements.

Because an admissible context must already be well-defined under Rust semantics,
an unsafe API cannot relax a condition whose violation is itself already undefined
behavior.

Stronger API or library invariants are different. Some unsafe APIs may legitimately
need to accept values that violate invariants normally associated with their
types. Whether Anneal permits an unsafe API contract to relax such an invariant,
and how that permission is expressed, remains unresolved.

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
