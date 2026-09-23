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

## Use Only Applicable Premises

- Bottom out Rust-language and standard-library facts in exact applicable text
  from versioned Rust Reference or standard-library documentation.
- Quote and link the smallest sufficient set of passages whose propositions,
  together with justified inference steps, entail the fact. Open each citation
  and verify its wording, qualifications, version, and scope.
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
- For new code, place invariant-bearing representation in the smallest
  practical leaf module, keep safely accessible representation fields private
  to it, and treat safe code outside that module—including the rest of the same
  crate—as untrusted.

## Follow the Proof Workflow

1. **Frame the claim.** Record the artifact identity, exact scope, valid uses or
   executions, Rust and dependency versions, supported configuration set,
   mandatory postconditions, TCB, exclusions, and whether design alternatives
   are requested.
2. **Inventory the surface.** Enumerate every in-scope safe and unsafe API
   surface, obligation site, invariant producer/transition/consumer, and
   generated or expanded artifact across the supported set.
3. **State every obligation.** Obtain each controlling contract, decompose it
   literally, and state the exact proposition and applicability to prove.
4. **Construct the derivation.** Derive every conjunct from checked local facts,
   named invariants, applicable authoritative axioms, tool-derived theorems, or
   explicit TCB entries. Unfold definitions and seek indirect multi-premise
   derivations; absence of one direct sentence is not itself a documentation
   gap. Justify every intermediate inference.
5. **Close composition.** Ensure every literal contract clause and safe surface
   has a disposition, every premise consumed by unsafe code has an admissible
   source, and every supported configuration region is proved by an abstract
   argument or exhaustive partition. Try to falsify the contract reading,
   inference chain, and coverage before concluding `PROVED`.
6. **Report exactly.** Keep unresolved obligations visible and state the
   smallest missing implication. Record proofs, TCB, coverage, findings,
   postcondition failures, documentation gaps, and residual scope without
   optimism.

Do not require a concrete UB counterexample to reject an incomplete proof. A
missing, ambiguous, circular, or inapplicable derivation is sufficient for
`UNPROVED`.

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
for every full audit and whenever conditional compilation, targets, generated
code, FFI, assembly, SIMD, allocators, linking, or build tooling is relevant.
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

- **PROVED:** Every obligation for the exact named claim is discharged over its
  complete applicability, relative to the stated TCB.
- **UNPROVED:** At least one required derivation, premise, applicability or
  coverage argument, postcondition proof, or citation is missing, ambiguous,
  circular, or unverifiable.
- **UNSOUND:** A valid use or in-scope execution is proved to reach undefined
  behavior.
- **CONTRACT-BROKEN:** A documented postcondition is proved false even though
  undefined behavior need not occur.

Apply verdicts separately to soundness, documented postconditions, and
conditional application claims. State exact scope, applicability, and TCB
beside every verdict. Never substitute “looks sound,” “probably sound,” or test
success.

For a persistent audit, complete:

- [tcb-audit-log-template.md](assets/tcb-audit-log-template.md)
- [unsafe-code-audit-report-template.md](assets/unsafe-code-audit-report-template.md)

For an inline review, provide the equivalent material compactly. Reuse an
existing canonical project log rather than creating a competing trust model.
