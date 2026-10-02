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
document must be corrected. It constrains the guarantees Anneal provides, not a
particular proof architecture or output format.

## Claims

An Anneal claim identifies:

- a **scope**: the program artifacts, configurations, and execution semantics it
  concerns, and the executions or contexts over which it ranges; and
- one or more **guarantees**, each with any **requirements** under which that
  guarantee applies.

The scope is shared by the guarantees in the claim. Within that scope, each
guarantee is conditional on its own requirements. A guarantee may concern
individual executions or relationships among executions; its quantification and
the definitions used to express it must have precise meanings.

A requirement for one guarantee does not automatically become a requirement for
another. For example, a safe binary-search function may guarantee correct
membership results when its input is sorted. An unsorted input makes that
functional guarantee inapplicable; it does not remove the baseline guarantee
that the safe call is free of undefined behavior (UB).

Scope and requirements are parts of the specification, not intrinsically distinct
kinds of logical condition. Restricting a quantification domain and adding a
precondition can express the same proposition. What matters is the meaning of
the complete claim, not which field contains a condition.

## Verification results

A **verification result** is a claim-bearing artifact that satisfies Anneal's
project-wide verification requirements and to which Anneal's normal correctness
promise in [`PRINCIPLES.md`](PRINCIPLES.md) applies.

A verification result fixes:

- the exact **claim** Anneal established;
- the complete **trusted computing base (TCB)** on which its assertions depend;
  and
- the exact **trust policy** against which that TCB was evaluated.

Semantically, a verification result asserts both that:

1. its TCB satisfies its trust policy; and
2. if the trusted code in its TCB is correct and its trusted assumptions are
   jointly valid, then its claim holds.

The first assertion concerns authorization of trust; the second concerns
conditional correctness. Neither assertion is independent of the correctness of
the machinery that establishes it. Unchecked dependencies of proof checking,
policy checking, and identification of the claim and TCB belong in the TCB too.

The meaning of a verification result must remain stable after it is produced. It
must therefore contain or immutably reference everything whose identity affects
its claim, its TCB, or its policy compliance. Mutable names such as branches,
profiles, named specifications, or named policies may be inputs, but the
verification result must bind the specific identities or contents actually used.

### Trusted computing base

The TCB includes the code and assumptions on whose correctness Anneal relies
without establishing that correctness by checked evidence. A verification result
must identify those dependencies precisely enough to audit them, including
unchecked dependencies reached through intermediate theorems or components.

A guarantee's requirements are hypotheses within the claim being proved. Anneal
may assume them while proving the corresponding implication without thereby
asserting that they hold. TCB assumptions instead support the justification of
that implication. These roles are determined by the specified claim and trust
policy, not by an intrinsic distinction between the propositions themselves.

Moving an unchecked dependency into a translator, generated artifact, helper
library, compiler, or other component does not remove it from the TCB. The audit
log accounts for the dependencies of the accepted justification; it need not
identify a logically minimal set of assumptions.

### Trust policy

A **trust policy** specifies which unchecked dependencies and evidence mechanisms
Anneal may use in establishing a claim. Its authorization rules and the checks or
evidence required to establish compliance must have precise meanings. A trust
policy cannot waive Anneal's project-wide verification requirements, including
mandatory UB verification.

Without such rules, a failed proof could become apparent verification simply by
replacing the missing step with an assumption. Suppose a policy requires checked
evidence that a buffer operation is safe. Declaring its safety as an axiom does
not satisfy that requirement. Importing a helper theorem that relies on the same
axiom does not satisfy it either: the unchecked dependency remains, so the policy
must reject both uses.

The policy may also permit Anneal to delegate proof work. For example, it may
authorize a particular external verifier and specify the evidence needed to
accept its answer. That verifier may establish the entire proposition. Anneal
may then rely on its answer if the acceptance conditions are met and any
unchecked reliance on the verifier is included in the TCB.

Both cases can leave a short local proof citing a declaration of the same
proposition. The difference is the evidence and authorization for relying on that
declaration. Anneal must check those conditions and the declaration's unchecked
dependencies, rather than infer compliance from proof length or module placement.

An unfinished proof, skipped analysis, unsupported operation, or failed tool does
not by itself authorize a new unchecked dependency. Anneal must enforce the
applicable policy rather than silently weaken it after verification fails.
Explicitly selecting another permitted policy changes the verification being
requested; it does not establish that the original request was satisfied.

Authorized trust remains trust. A policy may permit reliance on a component's
contract without proving that the component satisfies it. Policy compliance
therefore establishes compliance with the declared rules, not that the permitted
assumptions are true, consistent, semantically independent of the conclusion, or
useful to the user.

## Evidence must establish the requested claim

A valid proof with permitted dependencies is not enough: Anneal must check that
the accepted evidence establishes the requested claim, or establishes a claim
from which the requested claim follows through checked reasoning.[^validation]

This correspondence includes the subject, scope, requirements, guarantees, and
the definitions and semantics that give them meaning. Matching a theorem's name
or displayed text is not enough. The machinery that constructs obligations from
the verification request and the Rust program must itself be checked or included
in the TCB.

Anneal's mandatory baseline contract must specify the required Rust safety
proposition, including its permitted caller and environmental conditions. The
formal obligations must be justified as establishing that proposition. Proof
construction must not report the request as satisfied after weakening the
baseline contract by changing a definition, excluding an unproved case, or adding
a requirement.

For example, evidence that binary search is UB-free on sorted inputs does not
establish UB-freedom for all inputs. Moving sortedness into the claim's scope does
not change this mismatch. Anneal must not substitute an empty domain or assume
the required safety conclusion in place of discharging the requested obligation.

This requirement applies whether a specification is written by a developer,
extracted from code, or revised alongside an implementation. For example, an
analysis might generate a specification describing only the paths it successfully
handled. A proof of that specification must not be presented as establishing
safety for every execution the original request covers.

Checking that evidence establishes the requested claim is distinct from checking
whether that claim has useful content. In particular, it does not establish that
the requested claim has satisfiable requirements. The consequences of that limit
are described under [Vacuity, consistency, and specification adequacy](#vacuity-consistency-and-specification-adequacy).

## Verification outcomes

Anneal may issue a verification result for a requested claim only when the
required evidence, trust-policy checks, and project-wide verification
requirements are satisfied. A run that cannot meet these conditions must not
report that request as verified.

Anneal may still emit diagnostics, partial checked evidence, or proof state. It
may also establish a smaller claim, provided that claim independently meets the
conditions for a verification result and is not presented as fulfilling the
larger request. An omitted additional guarantee does not remove mandatory
baseline obligations.

If Anneal deliberately bypasses a condition required for a verification result
and emits a claim-bearing development artifact, that artifact is a **tainted
output**, not a verification result. In particular, when Anneal bypasses mandatory
UB verification or turns it into a warning, both the output and its TCB audit log
must be clearly labeled as tainted or irreparably untrustworthy.

These distinctions concern the claims established, not merely a command's mode or
exit status. One invocation may process multiple claims with different outcomes.

## Rust-source and compiled-behavior guarantees

Every verification result must establish the baseline Rust-source well-definedness
guarantee described below. Its advertised behavioral guarantees must also hold
for the covered compiled code under their corresponding requirements. Merely
showing that machine code has defined behavior does not establish that its Rust
source was UB-free.

Anneal may express specifications using Rust source or intermediate models. Every
connection needed to relate those models to Rust and to the code produced by
`rustc` must be established by checked evidence or explicitly included in the
TCB.

For each reported guarantee, that reasoning must establish that covered compiled
behavior satisfies the advertised guarantee when its requirements hold. It must
account for the interpretation of the requirements as well as the guarantee
across semantic layers. A preservation argument for one class of properties must
not be presumed to preserve every other class.

This does not require identical source and target behavior sets or a particular
simulation relation. It requires specified source and target semantics and
justified preservation of the properties actually reported. A theorem about an
intermediate model is not by itself evidence that those connections hold.

The scope must identify the source, compilation configuration, and compiled
artifact or precisely characterized family of compiled artifacts to which the
argument applies. A library verification result need not identify one final
executable, but downstream compiled uses must fall within the established domain.
A package name alone cannot bind evidence to the code it justifies.

### Execution models and physical systems

The claim must state its execution semantics and environmental contracts so that
users can determine when its guarantees apply. Describing a condition as an input
constraint, an environmental contract, or a context obligation does not remove
the need to state and justify its role in the claim.

Applying a formal guarantee to a physical execution also depends on the relevant
system realizing the modeled semantics. For example, a hardware defect may
violate that premise; running code on a different instruction set may require a
compatibility argument not covered by the original claim. Such connections must
be accounted for explicitly, as checked evidence or trust, rather than silently
asserted to follow from the program proof.

## Baseline Rust well-definedness

Every verification result includes a guarantee of freedom from Rust undefined
behavior under the baseline contract's specified conditions. An additional
functional guarantee cannot narrow those conditions merely because its own
requirements are stronger.

The semantics and obligation generation must account for every behavior relevant
to this safety guarantee. Undefined behavior must not disappear because the
model has no representation for it. Likewise, quantifying only over normally
terminating executions must not omit faults on executions that fail to terminate
normally. UB-freedom alone does not promise termination or absence of panics.

### Whole programs

For a whole-program claim, the baseline covers all Rust executions enabled by the
covered program under the declared input and environmental conditions, including
all nondeterministic choices allowed by the execution model. Conditions on the
outside world must be explicit parts of the specified baseline, not additional
assumptions introduced to avoid proof obligations.

Anneal may use local proofs, component contracts, whole-program reasoning, or
another sound method. Those judgments must together justify the guarantee about
the complete execution.

For example, proving that one function or thread is locally well-behaved does not
by itself justify even a local Rust-level behavioral claim about an execution if
another part of that execution may exhibit undefined behavior, because undefined
behavior can invalidate the semantics of the entire execution.

### Libraries

A library's baseline guarantee is contextual: for every surrounding context
permitted by the specified API and execution contracts, combining that context
with the verified implementation must produce Rust executions free of UB.
Additional guarantees apply under their corresponding requirements.

A caller must establish the requirements of a guarantee before relying on it.
When verifying the implementation, Anneal may assume those requirements and must
establish the guarantee.

The formal account must justify that its permitted contexts include the clients
the API policy promises to support. Conditions on a context must account for its
own operations and obligations, including those of any unsafe code it contains.
A verified library does not make arbitrary surrounding UB harmless. Defining
permitted contexts as exactly those in which the implementation happens to be
safe would not establish the promised coverage.

Anneal may prove the final contextual guarantee directly or through intermediate
abstractions. An argument using an abstract API component must justify that the
abstraction supports the permitted clients safely as well as that replacing it
with the implementation preserves the required guarantees. A replacement theorem
alone, including reflexive replacement of an implementation by itself, does not
establish contextual safety. No particular abstraction architecture is required.

#### Safe and unsafe APIs

Anneal's API policy aligns the baseline guarantee with Rust's safe and unsafe API
conventions. Within the specified execution domain, a safe API must support every
type-correct use with values satisfying the applicable type and library
invariants. It may impose no further unchecked caller obligation needed to avoid
UB. Additional functional guarantees may have stronger requirements without
weakening this baseline.

Some library invariants are stronger than Rust language validity. For example,
Rust libraries may assume that a `str` contains valid UTF-8 even though
constructing a non-UTF-8 `str` is not itself immediate UB.[^str]

The applicable invariants and type interpretations must be specified, and their
use must be justified as part of the abstraction's safety argument. A declared
invariant does not by itself prove that safe constructors and operations preserve
it or that safe clients cannot violate it. Nor does the absence of a failure in
today's implementation establish the full contract of an API.

An unsafe API may additionally require its explicit safety preconditions. Its
caller must establish them; conditional verification does not establish them for
arbitrary calls. No API contract can suspend Rust's language-level UB rules.
Whether and how an unsafe API may explicitly relax stronger library invariants
remains unresolved. A precise account of which such invariants Anneal permits
safe APIs to assume also remains a lower-level semantic obligation, not a
promise of automatic inference from existing implementations.

## Vacuity, consistency, and specification adequacy

An additional guarantee can be proved exactly as requested without applying to
any possible input. For example, a function may be specified to return `42`
whenever its integer argument is both positive and negative. Proving that
implication says nothing about the return value for any possible call. The proof
matches the request, but the requested condition is impossible. This does not
remove the separate obligation to establish the mandatory baseline guarantee.

Establishing a conditional claim does not also establish that its requirements
are satisfiable, that a covered case occurs, or that the specification expresses
what its author intended. A verification request may require additional evidence
for particular such facts. Anneal must report what that evidence establishes
rather than infer these facts from proof acceptance.

Some empty cases are legitimate. An impossible branch condition or an
uninhabited input type may justify a conditional safety theorem. A proof that
local hypotheses are contradictory is not by itself evidence that the global
trusted assumptions are inconsistent. The distinction matters when interpreting
proofs by contradiction or reasoning about unreachable code.

Trusted assumptions being jointly valid means that they hold together in the
interpretation used to connect the claim to the program and its environment.
Consistency alone is weaker: assumptions may be consistent without correctly
describing the intended program or physical system.

Admitting axioms or finding no contradiction does not by itself establish that
the trusted assumptions are jointly true or consistent. Accepting a proof
establishes its stated proposition under its assumptions, not a general guarantee
about those assumptions. A policy may require a model, a witness, or other
evidence for specified consistency or applicability claims. The force of such
evidence remains relative to the foundations and checking machinery used.
Foundational soundness that has not been established remains part of the trust
boundary.[^axioms]

Trust-policy compliance and proof validity therefore do not provide a general
certificate of non-vacuity, semantic independence, or specification adequacy. Any
additional check for one of those properties must have a specified meaning and
justify the particular conclusion Anneal reports.

## Open-ended guarantees and behaviors

Beyond baseline well-definedness, developers must be able to state and prove
additional correctness guarantees. Anneal must not fix today's anticipated
guarantees as a closed universe.

Anneal likewise aims to support all program *behaviors*, not every Rust source
program. It may reject particular language features or combinations of features
when the same intended behavior can be expressed in a supported way. When
practical, it should give the programmer actionable guidance toward such a form.
Supporting additional guarantees or behaviors must not weaken existing promises.

## Rust-oriented interface

Ordinary Rust programmers must be able to use Anneal effectively without learning
Lean 4.

When Anneal cannot establish an obligation, its ordinary interface should connect
the failure to the Rust program: what operation or guarantee generated the
obligation, what must be true, and what Anneal could not establish.

The normal workflow should therefore feel like an extension of Rust's existing
compiler-enforced reasoning rather than requiring every Rust programmer to become
a formal-methods specialist.

[^validation]: Lean's [proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
    distinguishes checking a proof from checking the meaning of its theorem
    statement. This is a supporting example, not a requirement to use a particular
    Lean validation tool.

[^str]: See the standard library's [`str` invariant documentation](https://doc.rust-lang.org/std/primitive.str.html#invariant).

[^axioms]: Lean's [axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms/)
    explains how admitted axioms affect soundness and what axiom-dependency
    reporting establishes.
