---
name: unsafe-rust
description: "Author, document, review, audit, or redesign unsafe Rust with proof-grade rigor. Use for unsafe blocks and functions, unsafe traits and impls, raw pointers, FFI, inline assembly, intrinsics, layout or validity reasoning, concurrency and atomics, SIMD and target features, allocators, invariant-bearing fields, safety comments or `# Safety` documentation, soundness reviews, TCB audits, generated unsafe code, changes to safety or behavioral contracts, and proof-oriented redesign of unsafe abstractions."
---

# Unsafe Rust Authoring and Audit

Treat each safety contract as an English-language theorem and each safety
comment as its proof. Reject hand-waving, folklore, hidden assumptions, and
proof by testing.

## Establish the Exact Claim

Unless the user specifies a narrower claim, establish:

> For the exact audited source snapshot, every supported compilation
> configuration, every valid in-scope use in a context satisfying all
> out-of-scope safety obligations preserves freedom from Rust undefined behavior
> under the documented Rust abstract semantics, and every mandatory in-scope
> documented postcondition holds, assuming only the explicitly recorded trusted
> computing base (TCB).

Interpret valid use as follows:

- For a safe API, quantify over every well-typed safe use. Impose no hidden
  safety precondition.
- For an unsafe API, quantify over every use satisfying all documented initial,
  ongoing, and terminal safety obligations.
- For a binary or other entrypoint, quantify over executions satisfying the
  explicitly recorded deployment assumptions. Do not transfer those
  assumptions silently to a safe library API.

Prove every documented postcondition of each unsafe API in scope and every
documented guarantee consumed by an in-scope soundness proof. Include broader
safe-API robustness only when the user or audit scope requests it.

Prove source-level Rust soundness first. State claims about a particular
compiler backend, binary, platform, security property, probability, or
deployment separately with their additional premises.

## Recover the Required Domain

Before proving the claim body or issuing a full verdict, derive the exact
domain quantified by the claim. Let a `case` retain every relevant dimension of
one valid use or execution: artifact, toolchain, configuration, input, state,
time, and any other dimension on which an obligation or premise can vary. Let
`Required(case)` denote the cases the claim requires and `Covered(case)` hold
exactly where every obligation the claim requires for that case has a complete
derivation from applicable premises. A local argument may project onto fewer
dimensions only when it proves the lemma for every required case in each
omitted-dimension fiber—parametrically or by proving those dimensions
irrelevant—and must restore the full case before claim-level closure.

Within one obligation, valid case lemmas may be unioned. Across distinct
obligations, claim-level coverage is their pointwise conjunction—not a union of
regions in which different obligations happened to be proved.

- Preserve the controlling domain expressions symbolically, including ranges,
  unions, exclusions, quantifiers, and conditional or moving policies. Record
  their exact sources and audit cutoff.
- If applicable project sources conflict or materially underdetermine support,
  obtain an authorized resolution, derive an explicit conservative audit
  domain containing every materially supported candidate predicate, or leave
  the affected combined claim `UNPROVED`. Do not call a conservative audit
  domain the resolved project promise.
- Treat every asserted set relationship, normalization, enumeration,
  partition, exclusion, and policy merge as a proof step. Prove the definition
  of the exact relation asserted. For example, `A = B` needs `A ⊆ B` and
  `B ⊆ A`; `A ⊊ B` needs `A ⊆ B` and a witness `w ∈ B \ A`;
  incomparability needs witnesses `a ∈ A \ B` and `b ∈ B \ A`, with each
  membership and nonmembership proved. Equivalent symbolic derivations are
  acceptable, but required witnesses must remain explicit. Prove the
  required containment before using a conservative superset and
  `Required ⊆ Covered` before concluding `PROVED`.
- A finite inventory requires evidence both that every listed member belongs
  and that no required member is omitted. Endpoints, one representative per
  apparent category, CI jobs, lockfiles, and other samples do not prove an
  interval or set inventory.
- Prefer a parametric proof over the symbolic predicate when enumeration would
  be large or its exact membership is unavailable. Otherwise report proved
  regions and the unresolved remainder; do not turn it into an implicit
  exclusion.
- An audit cutoff limits the temporal scope of a claim. It does not establish
  semantic continuity, enumerate releases before the cutoff, or make sampled
  documentation applicable between samples.

Apply
[configuration recovery](references/configurations-and-generated-code.md#recover-the-required-supported-set)
to derive supported compilation cases and prove every transformation of that
predicate.

## Use Only Applicable Premises

- Bottom out Rust-language and standard-library facts in exact applicable text
  from versioned Rust Reference or standard-library documentation.
- Quote and link the smallest sufficient set of passages whose explicitly
  stated propositions, together with justified inference steps, entail the
  fact. Open each citation and verify its wording, qualifications, version, and
  scope. A page, allowlist entry, broad label such as “cfg semantics,” or nearby
  cited clause does not supply a material proposition the proof never states.
- Attach an applicability domain to every claim and premise, whether stated
  locally or inherited from an identified project policy or canonical entry. A
  derivation proves only the cases covered by all premises it consumes.
- Apply a guarantee documented for an older Rust release to a later stable
  release only when an exact applicable Rust backwards-compatibility
  commitment preserves that exact proposition throughout the later release's
  relevant domain. An API's stability badge does not by itself preserve every
  behavioral statement in its current documentation. Record a
  non-authoritative compatibility premise explicitly in the TCB. Never infer
  an earlier-version guarantee merely from later documentation.
- Do not promote this skill, the Rustonomicon, Unsafe Code Guidelines, RFCs,
  blogs, issue discussions, implementation behavior, Miri, or common practice
  to Rust axioms. Use them to discover risks and authoritative text, or record
  the exact additional proposition as a TCB assumption.
- Trust a deliberately selected safe dependency API to behave as documented
  only when that exact trust is explicit in the TCB. Do not extend this
  exception to caller-controlled safe code, callbacks, values, or safe trait
  implementations.
- Audit a third-party unsafe API through to admissible premises or record its
  exact implementation and contract as an additional TCB assumption.

When no admissible direct or derived proof can be completed because
authoritative documentation is ambiguous or insufficient, identify the
smallest missing proposition. Do not repair it with intuition. Report a
documentation gap and suggest an upstream improvement when appropriate.

## Compose Proofs Locally and Literally

- Identify the controlling contract independently of the existing safety
  comment. Distinguish normative contract text from examples, rationale,
  implementation comments, and inferred design intent.
- Read the controlling contract according to its actual text. Decompose every
  applicable conjunction, implication, quantifier, temporal clause,
  precondition, and postcondition into separately reviewable obligations. Do
  not replace a literal requirement with an operationally similar property.
  Give every normative clause a disposition even when no known consumer uses
  it.
- Reify every fact used nonlocally as a named contract or invariant carried by a
  type, field, function boundary, guard, typestate, lock, token, or other
  locally checkable mechanism. A function contract about global state is an
  acceptable degenerate case.
- Prove that each state transition establishes, preserves, transfers,
  deliberately suspends under an explicit obligation, or discharges every
  applicable invariant. At each consumer, prove that the current invariant
  entails the exact needed precondition.
- Trace dataflow across calls and time rather than limiting review to lexical
  unsafe blocks. Account for every producer, transition, and consumer.
- Do not promote a producer's preconditions into a universal invariant of its
  output type. Any type- or abstraction-wide conclusion needs a complete
  derivation independent of that invalid reversal—for example, applicable
  authoritative premises, construction-and-preservation closure under an
  enforced boundary, or an admissible explicit TCB premise. Local checks and
  other applicable derivations may instead prove the proposition for the
  particular consumed values or quantified subset.
- For new code, place invariant-bearing representation in the smallest
  practical leaf module, keep safely accessible representation fields private
  to it, and treat safe code outside that module—including the rest of the same
  crate—as untrusted.

## Follow the Proof Workflow

1. **Frame the claim.** Record the artifact identity, exact scope, valid uses or
   executions, mandatory postconditions, TCB, exclusions, and whether design
   alternatives are requested.
2. **Frame the full case domain.** Identify every relevant dimension and
   preserve the controlling expressions, sources, candidate relationships, and
   unresolved conflicts. State the proposed `Required` domain and how proof
   cases will retain every dimension.
3. **Inventory surfaces and transformations.** Enumerate every in-scope safe
   and unsafe API surface, obligation site, invariant
   producer/transition/consumer, and each material stage and alternative exit
   by which build or generation inputs can affect the theorem domain, a
   consumed premise, shipped artifacts or selected source, reachability, or an
   in-scope postcondition.
4. **State atomic obligations and premises.** Obtain each controlling contract,
   decompose it literally, and state the exact proposition and applicability to
   prove. Classify every material premise and identify its exact source.
5. **Construct the derivation.** Derive `Required`, every asserted domain
   relationship, and every claim conjunct from checked local facts, named
   invariants, applicable authoritative axioms, tool-derived theorems, or
   explicit TCB entries. Unfold definitions and composite transformations;
   preserve material operation order and alternative exits; seek indirect
   multi-premise derivations; and justify every intermediate inference.
6. **Close, lint, and challenge.** Give every literal contract clause and safe
   surface a disposition and establish domain closure. Reverse-trace each
   conclusion used by a verdict or regional result through every material
   inference to explicit, applicable premises; reconcile every Rust premise
   with its checked quotation and link; and ensure no later-stage fact is
   consumed on a path that exited earlier. Then try to falsify the domain
   recovery, contract reading, derivations, and coverage with boundary and
   adversarial cases derived from the actual clauses.
7. **Certify and report.** Apply the quantifier-sensitive certificates below.
   Keep every unresolved obligation visible and state the smallest missing
   implication. Record proofs, TCB, coverage, findings, postcondition failures,
   documentation gaps, and residual scope without optimism.

## Write and Review Proof-Grade Documentation

Read [proof-obligations.md](references/proof-obligations.md) before authoring or
reviewing an unsafe contract, invariant, `SAFETY` comment, or local proof.

Keep each proof adjacent to the smallest cohesive unsafe operation or assertion.
State the exact operation and its preconditions, cite checked facts and named
invariants, show the derivation, and prove resulting postconditions and
invariant state on every applicable exit.

When existing code can be validated only by reconstructing a material
derivation absent from its safety comment, do not accept it silently. Include
the reconstructed derivation—or the smallest missing portion—in the review,
with its citations and applicability. Classify implementation correctness
separately from proof-documentation quality. If changes are authorized, improve
the adjacent proof; otherwise provide proposed wording. Do not use a
reconstructed implementation proof to invent or strengthen a caller-facing
contract retroactively.

## Close API and Configuration Boundaries

Read
[api-boundaries-and-evolution.md](references/api-boundaries-and-evolution.md)
for fields, constructors, methods, traits, sealing, macros, public or hidden
APIs, robustness, or contract evolution.

Apply this mandatory safe-surface checklist: public fields, constructors, safe
methods, safe trait methods, and macro-generated APIs all count as safe API
surfaces. Include language-reachable `#[doc(hidden)]` safe items for soundness
even when excluded from documentation or compatibility promises.

Treat caller-provided safe code as adversarial within the behaviors permitted
by safe Rust and its types. Seal a trait or make it unsafe when soundness
requires an unenforced implementer behavior.

Read
[configurations-and-generated-code.md](references/configurations-and-generated-code.md)
for every full audit and whenever supported-toolchain policy, conditional
compilation, targets, generated code, FFI, assembly, SIMD, allocators, linking,
or build tooling is relevant.
Every supported combination of compilation options that can ship downstream
must be sound. Use parametric proofs or exhaustive partitions when literal
enumeration would explode; do not substitute a tested sample.

## Evaluate Trust and Evidence

Read [tcb-and-evidence.md](references/tcb-and-evidence.md) for every full audit
and whenever a proof uses dependencies, external specifications, tools,
testing, formal verification, environmental restrictions, or cryptographic or
probabilistic assumptions.

Judge evidence by the exact proposition it establishes, its artifact and model,
its quantified domain and bounds, its premises, and its residual trust—not by a
label such as testing, static analysis, model checking, or formal verification.

## Design for Provability When Requested

Read [abstraction-design.md](references/abstraction-design.md) when the user asks
to design, refactor, or reconsider an unsafe abstraction, or when authoring a
new unsafe abstraction.

Judge existing code under its current source and controlling contract. Inferred
intent or a preferable model may guide a separate proposal but may not narrow,
reinterpret, or discharge a current obligation. Treat implemented changes as a
new artifact and audit them anew.

## Use Exact Verdicts

Read [audit-reporting.md](references/audit-reporting.md) before delivering a
persistent or full audit.

| Verdict | Required certificate |
|---|---|
| **PROVED** | Every obligation for the exact named claim has a checked derivation over its complete applicability, `Required ⊆ Covered`, and every premise is proved from admissible sources or appears as an accepted entry in the stated TCB. |
| **UNPROVED** | A required derivation, premise, applicability or domain-closure argument, postcondition proof, or citation remains missing, ambiguous, circular, or unverifiable, and no applicable existential refutation below is complete. |
| **UNSOUND** | There exists a proved valid in-scope use or execution which reaches an executed operation or semantic event, its exact required safety proposition is false there, and applicable authoritative semantics—possibly together with an explicit TCB premise about the implementation—entails undefined behavior. |
| **CONTRACT-BROKEN** | There exists a proved valid in-scope execution which, considered as a whole, contains no undefined behavior and falsifies a documented postcondition. |

Failure to prove a universal obligation is enough for `UNPROVED`; do not invent
a counterexample. Conversely, once all parts of an existential UB certificate
are proved, report the scoped soundness claim `UNSOUND`; do not continue to
demand a universal positive lemma and dilute the result to `UNPROVED`. A
violation of user-authored safety prose is not by itself a runtime UB event:
trace the certificate through applicable contracts to the exact authoritative
or explicitly trusted UB consequence.

An existential certificate closes the universal verdict but does not excuse
omitting another in-scope surface, operation, contract clause, or mandatory
postcondition. Continue the inventory and give each independent obligation a
disposition. Do not claim that a proved or affected region is exact or maximal
unless its full case-domain equality is established; maximal positive remainder
characterization is required only when the audit scope requests it.

Classify a witness using the execution as a whole, not observations from a
prefix of an execution that later reaches undefined behavior. An
undefined-behavior-containing execution can witness `UNSOUND` but cannot
establish the existential claim required for `CONTRACT-BROKEN`. If it is the
only behavioral evidence, report soundness as `UNSOUND` and the postcondition
as `UNPROVED`. An independent UB-free witness or equivalent existence proof
may establish `CONTRACT-BROKEN`; separate proofs may therefore establish both
verdicts.

Apply verdicts separately to soundness, documented postconditions, and
conditional application claims. State exact scope, applicability, and TCB
beside every verdict. For every affirmative claim spanning multiple Rust
releases, identify a parametric proof, an exhaustive applicable partition, or
an exact proposition-preserving compatibility premise whose covered domain
contains the claimed release set. Never substitute endpoints, sparse samples,
an audit cutoff, “looks sound,” “probably sound,” or test success.

For a persistent audit, complete:

- [tcb-audit-log-template.md](assets/tcb-audit-log-template.md)
- [unsafe-code-audit-report-template.md](assets/unsafe-code-audit-report-template.md)

For an inline review, provide the equivalent material compactly. Reuse an
existing canonical project log rather than creating a competing trust model.
