# Design of the Unsafe Rust Authoring and Audit Skill

> **Status and audience**
>
> This document governs maintenance of the `unsafe-rust` skill. It is not part
> of the installable skill package, is not loaded during ordinary skill use, and
> must never serve as a premise in an unsafe-code proof. Human maintainers—and
> agents specifically tasked with maintaining the skill—should read it before
> changing agent-facing instructions.
>
> The installed skill revision governs an agent's operational procedure. Exact
> Rust Reference and standard-library documentation, together with explicit TCB
> entries, govern proof premises. This document governs how maintainers evolve
> that procedure. A conflict between this document and the installed skill is a
> maintenance defect, not a hidden runtime instruction.

## Purpose

The skill exists to make unsafe Rust authoring and review produce proof-grade
results. It succeeds when an agent:

- finds every in-scope soundness obligation and every mandatory postcondition
  obligation;
- discharges each obligation from verified facts and conspicuous trust;
- detects incomplete, circular, or overbroad reasoning;
- covers every supported shippable configuration;
- distinguishes proof from counterexample-finding evidence;
- reports the exact theorem established without optimism.

The design optimizes for correct behavior, not encyclopedic coverage or
pedagogical completeness. Agent context is finite. Material belongs in the
runtime package only when it predictably changes authoring, review, or verdict
behavior.

## Three Separate Layers

The system deliberately separates:

1. **Proof authority.** Versioned Rust Reference and standard-library text
   supplies Rust axioms. Explicit TCB entries supply admitted non-axiomatic
   premises.
2. **Operational procedure.** `skills/unsafe-rust/SKILL.md` and its conditional
   references tell an agent what to do.
3. **Maintenance rationale.** This document explains why that procedure has its
   present shape and how proposed changes are judged.

The maintainer document may cite RFCs, research, tools, community practice, and
incidents to explain design choices. Such material does not become a Rust proof
authority merely because maintainers found it persuasive.

## Governing Model

Unsafe Rust authoring and audit is obligation discharge.

The default result sought is source-level Rust soundness under documented Rust
abstract semantics for an exact source snapshot, for every valid use and every
supported compilation configuration, relative to explicit trust. The mandatory
behavioral extension covers every documented postcondition of an unsafe API in
scope and every documented guarantee consumed by an in-scope soundness proof.
Other safe-API robustness, binary, deployment, security, or probabilistic claims
are separate, explicitly scoped theorems with separate premises.

This model yields the core design:

- A safety contract is an English-language theorem.
- A safety comment is an English-language proof.
- Inspection establishes literal artifact structure, not the semantic effect
  of that structure. Every conclusion must follow from checked artifact facts,
  applicable authoritative axioms or explicit TCB premises, and explicit
  derivations through established lemmas and invariants.
- Every missing implication makes the result unproved; demonstrating an actual
  UB execution is not required to reject the proof.
- Proofs compose through contracts and invariant-carrying state, so global
  soundness follows from complete local discharge.

The skill does not need a philosophical ontology or a closed taxonomy of
unsafe operations. It does need a finite operational classification for every
proof proposition or premise, explicit treatment of material inferences, and
the artifact/semantics distinction, because those rules change whether an
apparently complete proof actually has admissible premises.

## Design Principles

### Obligation-first, not taxonomy-first

Closed lists of “core unsafe operations” are fragile, invite category debates,
and can cause auditors to miss declarations, generated behavior, invariant
transitions, or future language features. The skill instead asks what exact
precondition or postcondition each proof site supplies or consumes and follows
that proposition through the dataflow.

Terminology is retained only when it changes behavior. Distinguishing a contract
boundary from an operation that can exhibit UB can explain composition, but an
auditor need not adopt that philosophy if every obligation is still discharged.

### Local composition, not informal global reasoning

Nonlocal state is unavoidable; nonlocal informal proof is not. Every shared fact
must be reified as a named invariant or contract that producers establish and
consumers can invoke locally. A function contract about the whole program state
is an acceptable degenerate invariant.

An explicit dependency graph can help some humans, but requiring one does not
improve correctness when complete location-by-location proofs already record
every producer, consumer, and transition. The runtime procedure requires
coverage, not a particular visualization.

### Module boundaries are the preferred ownership boundary

Rust crate-relative visibility is mechanically convenient but enlarges the
region in which a safe edit can invalidate an invariant without an unsafe marker.
For new code, the skill therefore treats code outside the smallest owning module
as foreign and recommends private representation fields. This is stricter than
ordinary same-crate trust and is intended to reduce human proof scope.

Existing code with broader visibility remains auditable by computing the real
access region. The skill warns rather than fabricating privacy.

Compiler-enforced unsafe fields are different. They deliberately create a
field-level unsafe boundary analogous to an unsafe function and may have broad
visibility. The skill must still require complete operation contracts and proof
of implicit safe behavior such as destruction. Because the feature's semantics
can evolve, runtime wording remains conditional on the exact audited Rust
version and authoritative documentation.

The initial design follows the explicit analogy and destructor caveat in
[RFC 3458](https://rust-lang.github.io/rfcs/3458-unsafe-fields.html), while
treating the RFC as advisory and the
[language tracking issue](https://github.com/rust-lang/rust/issues/132922) as a
trigger to revisit the runtime wording when authoritative specification and
stabilization change.

### Safe caller code is adversarial; selected dependencies are deliberate trust

Unsafe code cannot rely on arbitrary caller-provided safe callbacks, values, or
safe trait implementations behaving according to prose. Such behavior is not
enforced by the caller accepting an unsafe obligation.

A project may intentionally trust a selected safe dependency to behave as
documented. That is an explicit opt-in relationship, so the skill permits it
only when the TCB records the exact dependency and contract. Contract channels
include SemVer ranges, exact pins, maintained forks, out-of-band agreements, and
consumer-specific promises.

Unsafe dependency implementations receive no silent extension of this
exception. They must be recursively audited or explicitly admitted.

### Authority and trust must be visible

The project chose a deliberately narrow Rust authority policy: exact Reference
and standard-library text. Explanatory material remains useful for discovery but
cannot silently repair missing authoritative semantics.

Versioned, narrowly scoped quotations prevent an agent from relying on memory,
search snippets, or wording that changed with Rust. Reviewers must verify that
citations actually entail the attributed fact. When they do not, the correct
result is a documentation gap or TCB admission, not confident paraphrase.

A TCB audit log makes all remaining trust reviewable. It must not make a theorem
vacuous by admitting the very in-scope implementation or conclusion that the
audit purports to prove.

### Applicability travels with every premise

A true proposition outside its domain is not a premise for the case being
proved. Source identity, Rust version, target, configuration, input/state
domain, and execution interval therefore belong to the proof, not merely to
report metadata.

The required theorem domain must itself be recovered without loss before its
body can be proved. Support declarations, build admission or enforcement, and
observations such as CI have different roles. The auditor preserves controlling
ranges, unions, exclusions, and conditions symbolically; resolves material
ambiguity through project authority or an explicit conservative audit domain;
and treats every normalization, enumeration, partition, or exclusion as a
proof-bearing transformation. Replacing a source predicate requires equality;
using a conservative audit domain requires containment. Claims that predicates
are strict subsets or incomparable additionally require the corresponding
nonmembership witnesses; preserving formulas is not itself a proof of their
relationship.

Recovering the required domain and proving coverage of it are distinct
derivations. Let `Required` denote the exact full cases quantified by the
theorem—without losing relevant artifact, configuration, input, state, or
execution dimensions—and `Covered` the cases whose semantic obligations have
complete applicable proofs. An affirmative result requires
`Required ⊆ Covered`. A projection may organize a local argument but cannot
silently redefine claim-level coverage; the lemma must cover every required
case in each omitted-dimension fiber, parametrically or by proving the omitted
dimensions irrelevant, and must restore the full case before closure.
Exhaustive enumeration is one possible proof technique, not the model: symbolic
and parametric proofs are preferable when exact membership is large, dynamic,
or unnecessary. Samples and endpoints can falsify coverage but cannot establish
an interval or inventory.

This is also why versioned citations alone are insufficient. Reusing an older
Rust guarantee on a later stable release requires an exact
proposition-preserving backwards-compatibility premise; an item's stability
badge is not a blanket promise about every sentence later attached to its
documentation. A cutoff bounds when the theorem was evaluated but supplies no
semantic continuity. Each case lemma's premise applicability must survive
composition across the whole claimed release and configuration region.

### Proof kernels separate artifact structure from semantics

An artifact fact is a directly checked property of the audited material:
tokens, declarations, attributes, ordering, explicit annotations, generated
text, or comparable literal structure. A Rust axiom is the exact semantic
proposition entailed by applicable versioned Reference or standard-library
text. A derived lemma follows from artifact facts, applicable semantic
premises, earlier proved lemmas or invariants, and explicit logic or
mathematics. Selected-dependency facts, verified tool theorems, and admitted
TCB propositions retain their distinct trust treatment.

The presence of syntax does not establish what compiling or executing it
means. Type value domains, evaluation and return, branching and matching,
arithmetic, configuration selection, accessibility, typing/coherence, and
caller-side unsafe obligations are semantic propositions even when the
relevant syntax is visible. Likewise, the text of a named invariant may be an
artifact fact, but its truth at a consumer is a derived lemma requiring
establishment and preservation proofs.

The runtime procedure therefore uses one kernel discipline and requires a
closed evidence-bearing kernel for each certified conclusion:

```text
artifact fact
  + exact applicable Rust/stdlib axiom, selected-dependency fact,
    verified tool theorem, or explicit TCB premise
  + earlier proved lemma or invariant
  + explicit logic or mathematics
  -> derived lemma
  -> consumer or certified conclusion
```

Kernel closure is a precondition to certification, not merely a final lint. A
reviewer must be able to recover every consumed premise and inferential edge,
applicability domain, source, and entailment direction. A broad topic label,
page-level citation, or named TCB entry supplies only the proposition explicitly
extracted and proved applicable. Ordinary proof prose and the obligation ledger
may carry each kernel; an explicit global graph or second proof artifact is
unnecessary.

### Producer contracts retain their quantifiers

A precondition on one constructor, conversion, deserializer, FFI ingress, or
other producer is a proposition about that invocation. Treating it as a
universal fact about the output type replaces an implication about one
invocation with an unproved universally quantified conclusion.

The runtime procedure requires a complete derivation for the exact quantified
set without reversing the producer implication. Authoritative premises, a
closed and enforced abstraction proof, a verified tool theorem, or an
admissible explicit TCB entry can contribute such a derivation. A consumer may
instead establish the fact for the values it consumes from local checks and
proved producer/transition history. This is a general dataflow rule rather than
a constructor-specific hazard list.

### Literal verification precedes design

An auditor must verify the artifact against its controlling contract as written.
Names, tests, implementation shape, comments, history, and known consumers can
help infer design intent, but inferred intent cannot narrow a public contract or
discharge a current proof obligation.

Design advice is nevertheless valuable when modification is authorized. A
proof-oriented redesign can extract the minimum capability consumers need,
separate accidentally coupled properties, and replace unsupported assumptions
with validation, types, privacy, or smaller contracts. The runtime package keeps
this as a conditional design process within the same skill because it shares
the authority, contract, TCB, and re-audit rules. It maintains a verdict
firewall: the current artifact is judged literally, a proposal receives only a
conditional proof plan, and an implemented redesign is a new artifact requiring
a fresh audit.

### Reconstructed proofs must improve the proof artifact

Fail-closed review does not mean giving up when no single citation states the
desired conclusion. Agents should seek admissible indirect derivations from
multiple clauses, definitions, local facts, and named invariants before
finalizing an obligation as unproved.

If that work reconstructs a material derivation omitted from the existing
safety comment, silently accepting the code wastes the audit's most useful
result. The runtime procedure therefore requires exposing the reconstruction
and separately classifying implementation correctness and proof-documentation
quality. This does not permit retroactively adding a caller obligation or a
provider guarantee to the controlling contract.

### Verdicts close according to their quantifiers

Fail-closed reasoning has two different outcomes. A universal soundness proof
with a missing implication is `UNPROVED` even when no exploit is known. An
existential refutation is complete only when a valid in-scope use reaches an
operation or event whose exact required safety proposition is false and the
applicable semantics entails UB; once those facts are proved, the scoped result
is `UNSOUND` even though other executions were not analyzed universally.

The valid-use premise discharges safety obligations owned outside the audited
scope, including obligations imposed on caller or implementer code supplied by
the witness. It must not assume the in-scope assertion being audited. Otherwise
a bad crate-owned `unsafe impl`, unsafe declaration, or boundary assertion would
become impossible to classify: its implementer contract would be assumed true
before the certificate could prove that exact assertion false.

The runtime therefore uses explicit verdict certificates. This prevents both
optimistic acceptance from absence of a witness and over-cautious dilution of a
proved witness into proof debt. Counterexamples do not replace obligation
coverage: one witness fixes the aggregate soundness verdict, while a
comprehensive audit still gives every independently in-scope obligation and
surface a disposition. It need not enumerate every client program exhibiting
the same false obligation or compute a maximal positive remainder unless that
regional theorem is requested. Any regional claim it does make must retain the
full relevant case dimensions and prove its stated boundary exactly.

### Configuration coverage is universal but need not be enumerative

Every supported combination that can ship downstream must be sound. Features,
targets, SIMD, allocators, assertions, generators, and build/link inputs interact,
so testing a matrix is insufficient.

Requiring literal enumeration would create combinatorial busywork. The skill
accepts parametric proofs, exhaustive partitions, generator proofs, and other
valid universal arguments. It requires the theorem, not one audit technique.

### Generated behavior is behavior

Macros, proc macros, build scripts, generated bindings, and linker/build outputs
can create public APIs and unsafe operations whose properties depend on caller
tokens, configuration, hygiene, or the destination crate. Auditing only a
generator's handwritten implementation can miss the actual shipped theorem.

The claim-relevant mapping is not always an atomic function from one input to
one output. Generators and build scripts execute ordered, fallible operations,
may leave partial effects, may terminate before later selector handling, and
may be cached or rerun under a separate invalidation contract. Build tools then
interpret emitted directives or artifacts before the compiler selects source.
Collapsing this staged relation to its successful endpoint can make true but
unproved claims about rejection, reachability, or freshness.

The runtime procedure therefore proves every stage, path, and exit that can
change the theorem domain, a consumed premise, the selected artifact/source,
reachability, or an in-scope postcondition. It still permits an exact-output
audit or a theorem about every supported output; the staged proof determines
when either result applies without requiring irrelevant build behavior.

### Soundness and promised behavior are separate obligations

There is no settled universal definition of API robustness broad enough for this
skill to impose. There is, however, a load-bearing minimum: satisfying an unsafe
API's documented safety preconditions obligates the implementation both to
avoid UB and to establish that API's documented postconditions. Any documented
guarantee consumed by a soundness proof is likewise a mandatory proof
obligation.

The skill reports postcondition failures separately because they can exist
without UB and can also invalidate downstream unsafe proofs. The witness rules
must respect time-traveling UB: an execution that ever exhibits UB has no
defined observation before or after it. Such an execution can refute soundness,
but cannot itself prove that a documented postcondition is false. A
`CONTRACT-BROKEN` finding therefore requires proof that a valid UB-free
execution falsifies the postcondition; when the only behavioral witness
contains UB, soundness is `UNSOUND` and the postcondition remains `UNPROVED`.
Independent proofs may establish both findings.

### Evidence is judged by its theorem, not its tool category

Blanket statements about testing or static analysis are inaccurate. A sampled
run may find only counterexamples; a sound over-approximation, exhaustive model
checker, or deductive verifier may prove a universal fact within its model.

The runtime rule therefore asks what exact proposition a result establishes,
over what domain, under what assumptions, with what remaining TCB. This rule is
both more rigorous and less likely to bitrot than a named-tool hierarchy.

The contrast between [Miri's explicitly execution-specific
guarantee](https://github.com/rust-lang/miri/#readme) and proof-oriented tools
such as [Kani](https://model-checking.github.io/kani/) helped expose why the
category label is not the load-bearing distinction. Their documentation informs
skill design but is not a Rust semantic axiom.

### Probabilistic and deployment claims remain conditional

A negligible-probability path to UB still refutes unconditional Rust soundness.
Cryptographic assumptions and deployment restrictions can support useful binary
or application theorems, so the skill permits them as conspicuous TCB entries
and requires qualified verdicts. They may not become hidden preconditions of a
safe library API.

### Compatibility follows propositions, not signatures

Safety preconditions and documented postconditions are contracts consumed by
proofs. Strengthening a caller obligation or weakening a provider guarantee can
break existing code even when types do not change. Trait contracts have
implementer and consumer directions that must be analyzed separately.

SemVer, exact pins, forks, and out-of-band agreements govern which changes are
permitted or expected; none independently proves a semantic fact. Audits record
their skill, TCB, source, and contract revisions so later changes can identify
affected proofs.

## Artifact Architecture

The installable package is structurally confined to `skills/unsafe-rust/`.
Nothing in the runtime package links to `maintainers/`.

- [`SKILL.md`](../skills/unsafe-rust/SKILL.md) contains the theorem, mandatory
  workflow, always-loaded proof-kernel gate, hard trust/locality rules, routing,
  verdicts, and output contract.
- `agents/openai.yaml` contains UI metadata only and must not become a second
  instruction channel.
- [`proof-obligations.md`](../skills/unsafe-rust/references/proof-obligations.md)
  contains detailed evidence classification, kernel construction and closure,
  valid-use, contract, invariant, citation, and comment technique.
- [`abstraction-design.md`](../skills/unsafe-rust/references/abstraction-design.md)
  contains the conditional proof-oriented design process and the firewall
  between current-artifact verification and candidate design.
- [`api-boundaries-and-evolution.md`](../skills/unsafe-rust/references/api-boundaries-and-evolution.md)
  contains module/API/trait/macro/dependency/robustness/evolution guidance.
- [`configurations-and-generated-code.md`](../skills/unsafe-rust/references/configurations-and-generated-code.md)
  contains supported-domain recovery and transformation, staged build and
  generation relations, configuration closure, target, FFI, assembly,
  allocator, and linking guidance.
- [`tcb-and-evidence.md`](../skills/unsafe-rust/references/tcb-and-evidence.md)
  contains trust categories, dependency relationships, conditional claims, and
  tool-evidence evaluation.
- [`audit-reporting.md`](../skills/unsafe-rust/references/audit-reporting.md)
  contains scope, obligation-ledger, proof-kernel preservation, root/blocker,
  finding, verdict, and audit-preservation rules.
- `assets/` contains copyable audit artifacts, not additional hidden
  instructions.
- Future evaluations belong outside the installable package.

Use this sentence-level inclusion test:

> Every agent-facing sentence must set a required result, require an action or
> verification, define a term needed by such a requirement, route to
> conditionally needed material, or provide the smallest example necessary to
> disambiguate one of those things.

Anything else belongs here or nowhere. Prefer removing redundant explanation to
adding “do not worry about this” qualifications.

## Resolved Design Decisions and Traceability

This table records stable rationale, not conversational history. The final
column records candidate semantic evaluation scenarios, not execution results.

| ID and decision | Failure prevented | Agent-facing consequence | Runtime location | Evaluation requirement |
|---|---|---|---|---|
| D01 — Require exact proof obligations rather than a primitive-operation taxonomy | Missing future, generated, declaration, or state-transition obligations | Follow every consumed contract to premises | [Core composition](../skills/unsafe-rust/SKILL.md#compose-proofs-locally-and-literally); [proof reference](../skills/unsafe-rust/references/proof-obligations.md) | EV01 — omitted non-syntactic invariant consumer |
| D02 — Reify nonlocal facts in named local invariants | Hand-waved global state and circular proofs | Establish/preserve/consume at local boundaries | [Core composition](../skills/unsafe-rust/SKILL.md#compose-proofs-locally-and-literally); [invariant mechanics](../skills/unsafe-rust/references/proof-obligations.md#carry-invariants-locally) | EV02 — delayed field consumer across calls |
| D03 — Prefer smallest-module ownership | Safe same-crate mutation silently invalidates invariants | Private fields; outside module untrusted | [Core composition](../skills/unsafe-rust/SKILL.md#compose-proofs-locally-and-literally); [module privacy](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#use-module-privacy) | EV03 — `pub(super)` invariant mutation |
| D04 — Permit compiler-enforced public unsafe fields | Treating an explicit unsafe API as hidden safe access | Document and prove every operation plus implicit behavior | [Unsafe fields](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#handle-unsafe-fields) | EV04 — public unsafe field with drop caveat |
| D05 — Treat caller safe code adversarially | Unsafe code trusts unenforced callback/trait behavior | Seal, validate, or make implementer contract unsafe | [API closure](../skills/unsafe-rust/SKILL.md#close-api-and-configuration-boundaries); [traits](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#audit-traits-and-sealing) | EV05 — malicious safe trait impl |
| D06 — Permit explicit selected-safe-dependency trust | Pointless recursive audits of intentionally chosen safe APIs | Record exact safe contract in TCB | [Premise policy](../skills/unsafe-rust/SKILL.md#use-only-applicable-premises); [dependency contracts](../skills/unsafe-rust/references/tcb-and-evidence.md#record-dependency-contracts) | EV06 — selected sort API versus caller comparator |
| D07 — Audit or admit unsafe dependencies | Satisfying caller contract mistaken for implementation correctness | Recursive proof or `UNSAFE-DEP` entry | [Premise policy](../skills/unsafe-rust/SKILL.md#use-only-applicable-premises); [dependency contracts](../skills/unsafe-rust/references/tcb-and-evidence.md#record-dependency-contracts) | EV07 — unsound third-party unsafe helper |
| D08 — Restrict Rust axioms to versioned Reference/std text | Folklore and explanatory documents become premises | Quote, link, and verify exact authority | [Premise policy](../skills/unsafe-rust/SKILL.md#use-only-applicable-premises); [proof kernel](../skills/unsafe-rust/references/proof-obligations.md#build-the-evidence-bearing-proof-kernel) | EV08 — mischaracterized citation |
| D09 — Recover the full theorem domain losslessly and carry applicability through every derivation | A range, union, condition, input, or moving policy is contracted or projected away; a false set relationship or out-of-domain premise is then used to assert closure | Preserve the full case tuple and source predicates; use relation-appropriate containment/equality/witness certificates; require `Required ⊆ Covered`; certify every multi-version premise region | [Domain recovery](../skills/unsafe-rust/SKILL.md#recover-the-required-domain); [applicability](../skills/unsafe-rust/references/proof-obligations.md#qualify-applicability); [supported set](../skills/unsafe-rust/references/configurations-and-generated-code.md#recover-the-required-supported-set) | EV09 — nonlinear incomparable policies plus a configuration/input product and sparse version evidence |
| D10 — Require indirect-derivation search before final failure | Valid multi-clause proofs are rejected because no single sentence states the conclusion | Unfold definitions, combine exact premises, and identify the smallest remaining gap | [Proof workflow](../skills/unsafe-rust/SKILL.md#follow-the-proof-workflow); [kernel closure](../skills/unsafe-rust/references/proof-obligations.md#close-and-lint-the-proof-kernel) | EV10 — validity derived from orthogonal std guarantees |
| D11 — Expose material reconstructed proofs | Reviewer silently accepts code whose safety comment omits the actual argument | Report reconstructed proof and proof-artifact defect separately | [Proof-grade documentation](../skills/unsafe-rust/SKILL.md#write-and-review-proof-grade-documentation); [proof review](../skills/unsafe-rust/references/proof-obligations.md#review-and-reconstruct-a-proof) | EV11 — sound operation with hand-waving comment |
| D12 — Include every safe API surface | Public field, trait, constructor, hidden item, or macro bypasses invariant | Apply explicit surface checklist | [API closure](../skills/unsafe-rust/SKILL.md#close-api-and-configuration-boundaries); [surface inventory](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#enumerate-every-surface) | EV12 — macro-generated safe constructor |
| D13 — Cover every supported configuration abstractly or concretely | Tested matrix misses shippable combination | Recover the required set and prove closure abstractly or by justified exhaustive cases | [API/configuration closure](../skills/unsafe-rust/SKILL.md#close-api-and-configuration-boundaries); [configuration reference](../skills/unsafe-rust/references/configurations-and-generated-code.md) | EV13 — feature/target interaction |
| D14 — Prove the staged build/generation relation and shipped output | Endpoint mapping hides earlier failure, partial effects, stale reuse, or unsafe expansion | Follow every claim-relevant ordered operation and exit through emitted effects and tool interpretation; identify an exact output or prove the generator property | [Build and generation](../skills/unsafe-rust/references/configurations-and-generated-code.md#prove-build-and-generation-pipelines); [macros](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#audit-macros-and-hidden-apis) | EV14 — fallible ordered build directives plus caller-token-dependent proc-macro output |
| D15 — Prove mandatory documented postconditions over defined executions | UB freedom masks broken guarantees, or an observation from a UB-containing execution is treated as defined | Prove unsafe-API and soundness-consumed guarantees; require proof of a valid UB-free falsifying execution for `CONTRACT-BROKEN`; trace consumers | [Exact claim](../skills/unsafe-rust/SKILL.md#establish-the-exact-claim); [verdicts](../skills/unsafe-rust/SKILL.md#use-exact-verdicts); [documented behavior](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#prove-documented-behavior) | EV15 — UB-only apparent behavior failure plus an independent UB-free contract failure |
| D16 — Judge tools by exact theorem | Both false confidence in clean runs and false rejection of formal proof | Check scope/model/bounds/TCB | [Evidence policy](../skills/unsafe-rust/SKILL.md#evaluate-trust-and-evidence); [tool theorem](../skills/unsafe-rust/references/tcb-and-evidence.md#judge-tools-by-their-theorem) | EV16 — bounded result versus completeness proof |
| D17 — Make deployment/crypto assumptions conditional | Negligible or restricted UB mislabeled unconditional soundness | Explicit TCB and qualified theorem | [External/deployment assumptions](../skills/unsafe-rust/references/tcb-and-evidence.md#record-external-and-deployment-assumptions); [report aggregation](../skills/unsafe-rust/references/audit-reporting.md#aggregate-verdicts) | EV17 — signature-gated bad path |
| D18 — Preserve `#[doc(hidden)]` soundness but not implied SemVer | Hidden reachability becomes hidden safety precondition | Audit direct safe use; separate compatibility | [API closure](../skills/unsafe-rust/SKILL.md#close-api-and-configuration-boundaries); [hidden APIs](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#audit-macros-and-hidden-apis) | EV18 — reachable hidden safe constructor |
| D19 — Treat contract changes as proof changes | Safety prose changes without caller/implementer re-audit | Directional compatibility analysis and triggers | [Contract evolution](../skills/unsafe-rust/references/api-boundaries-and-evolution.md#evolve-contracts-deliberately); [TCB evolution](../skills/unsafe-rust/references/tcb-and-evidence.md#review-and-evolve-the-tcb) | EV19 — strengthened unsafe precondition |
| D20 — Separate literal audit from proof-oriented redesign | Inferred intent launders a current defect, or review misses a much simpler sound model | Preserve current verdict; derive minimum capability and re-audit implemented redesign | [Design routing](../skills/unsafe-rust/SKILL.md#design-for-provability-when-requested); [design reference](../skills/unsafe-rust/references/abstraction-design.md) | EV20 — overbroad nominal field abstraction |
| D21 — Certify verdicts by logical proof shape | Invalid proof is accepted because no exploit is known, a proposed witness has an unproved safe-use path, or a completed existential UB derivation is diluted to `UNPROVED` | Use `UNPROVED` for an incomplete universal proof; use `UNSOUND` only after valid-use, reachability, false safety proposition, and UB consequence certificates all close | [Verdict certificates](../skills/unsafe-rust/SKILL.md#use-exact-verdicts); [valid uses](../skills/unsafe-rust/references/proof-obligations.md#certify-valid-uses); [report aggregation](../skills/unsafe-rust/references/audit-reporting.md#aggregate-verdicts) | EV21 — paired incomplete obligation with no witness and multi-premise exact-version witness whose safe-call status must be proved |
| D22 — Preserve producer-contract quantifiers | One constructor's precondition is promoted into a postcondition or invariant of every value of its output type | Prove the exact consumed values or quantified set without reversing the producer implication | [Core composition](../skills/unsafe-rust/SKILL.md#compose-proofs-locally-and-literally); [producer quantifiers](../skills/unsafe-rust/references/proof-obligations.md#preserve-producer-quantifiers) | EV22 — unsafe constructor contract plus a separate safe producer that violates the assumed property |
| D23 — Require a closed evidence-bearing proof kernel | Inspected syntax or a topical citation is treated as the semantic proposition needed, or a report reaches the right endpoint while omitting a consumed premise, inferential edge, applicability restriction, or exact entailment direction | Separate artifact facts from semantic premises; derive every consumed proposition explicitly; verify version, applicability, quotation direction, and closure before certification; reuse ordinary proof prose and the obligation ledger | [Proof-kernel gate](../skills/unsafe-rust/SKILL.md#close-an-evidence-bearing-proof-kernel); [kernel method](../skills/unsafe-rust/references/proof-obligations.md#build-the-evidence-bearing-proof-kernel); [kernel preservation](../skills/unsafe-rust/references/audit-reporting.md#preserve-closed-proof-kernels) | EV23 — visible construct with one uncited semantic edge plus a citation supporting only the wrong implication direction |
| D24 — Separate root proof gaps from dependent fan-out | One missing premise is reported as many independent defects, or downstream obligations are silently accepted | Assign one stable root blocker/gap ID, mark every dependent positive obligation `UNPROVED`, and preserve independent direct defects | [Kernel closure](../skills/unsafe-rust/references/proof-obligations.md#close-and-lint-the-proof-kernel); [reporting](../skills/unsafe-rust/references/audit-reporting.md#preserve-closed-proof-kernels) | EV24 — one missing semantic premise feeding several obligations plus a separate direct defect; require one root finding and complete dependent dispositions |

## Explicit Non-goals

The runtime skill does not:

- teach ordinary Rust syntax or ownership fundamentals;
- reproduce the Rust Reference or standard-library documentation;
- claim an exhaustive list of UB, unsafe operations, hazards, configuration
  axes, or proof obligations;
- require finite enumeration when a symbolic or parametric domain proof is
  complete;
- require enumeration of every client program witnessing one already-identified
  false obligation;
- require a maximal positive-region characterization after a complete
  existential refutation unless that separate regional theorem is in scope;
- require an explicit safety-dependency graph;
- require a second proof-record schema beyond ordinary contracts, invariants,
  obligation coverage, and audit artifacts;
- impose a proof-state machine or engagement-mode matrix in addition to the one
  proof workflow;
- split proof-oriented redesign into a separate skill with a duplicate
  authority or verdict model;
- prescribe a fixed number of redesign candidates or an arbitrary scoring
  formula;
- standardize undocumented API robustness;
- decide project support or SemVer policy without evidence;
- turn advisory sources, current implementation behavior, or this document into
  Rust axioms;
- equate all static analysis with bug finding or all formal tools with proof;
- preserve tentative terminology, resolved debate, or historical hedging in
  agent-facing prose;
- certify a compiler-generated binary when only source semantics were proved;
- use inferred intent or a proposed redesign as evidence for the current
  artifact.

Rejected alternatives belong here only when recording the decision prevents a
plausible regression. This document is not a transcript or a repository for
every idea considered.

## Change-Acceptance Protocol

Every behavior-changing proposal must answer:

1. What concrete omission, false acceptance, false rejection, or recurring
   author/reviewer error does it prevent?
2. What observable agent behavior must change?
3. What authoritative basis, incident, proof principle, or explicit project
   policy supports it?
4. Does it belong in always-loaded instructions, a conditional reference, a
   deterministic tool/template, an evaluation, this document, or nowhere?
5. Is existing text already sufficient?
6. What runtime context/token cost does it add?
7. What semantic evaluation would demonstrate the improvement without leaking
   the intended answer?
8. Does it alter theorem scope, authority, trust, verdict meaning, compatibility,
   or previously issued audit judgments?
9. What material can be simplified or removed once the change exists?

Classify the change:

- **Editorial:** No intended change in agent behavior or accepted proofs.
- **Operational:** Changes authoring, review, coverage, artifact, or verdict
  behavior.
- **Foundational:** Changes the primary theorem, authority model, trust policy,
  scope, or status meanings.

Operational changes must update traceability and semantic evaluations.
Foundational changes must amend this document in the same change and identify
how existing audits should be interpreted. Editorial changes should not smuggle
in new obligations.

## Evolution and Compatibility of the Skill

Every persistent audit should identify the skill revision used. A later,
stricter procedure can reveal that an earlier proof was incomplete; it does not
retroactively make the old report complete or silently change its stated
theorem.

Treat these as behaviorally significant skill changes:

- accepting or rejecting a new kind of proof premise;
- changing Reference/std authority policy;
- changing selected dependency or unsafe dependency trust;
- expanding or narrowing valid-use or configuration quantification;
- changing the meaning or precedence of verdicts;
- changing required postcondition/robustness scope;
- changing persistent audit artifacts in a way that drops information.

When authoritative Rust documentation evolves, update routing or examples only
after checking exact support ranges and compatibility promises. Avoid embedding
semantic fact lists in the skill; that is the main defense against bitrot.

When a relevant unstable feature stabilizes, replace conditional wording only
after authoritative documentation exists for the supported Rust range. Do not
derive a stable rule solely from an accepted RFC or implementation.

## Validation Strategy

Validate behavior with semantic fixtures, not snapshots of preferred wording.
Use fresh agents with only the skill, task, and raw artifact under review. Do
not leak the expected bug or intended conclusion.

The evaluator-only [source catalog](../evals/unsafe-rust/source-catalog.md) and
[testing plan](../evals/unsafe-rust/testing-plan.md) define corpus provenance,
oracle isolation, fresh-agent execution, scoring, and release gates. They are
maintenance artifacts and must not be linked from the installable skill.

Give every operational decision in the traceability table a semantic fixture or
an explicit reason why another fixture exercises the same behavior. Across the
suite, require independent coverage of:

- lossless full-case theorem-domain recovery, including symbolic ranges,
  unions, conditions, configuration/input products, relation-appropriate
  witnesses, justified projections and enumerations, `Required ⊆ Covered`,
  and multi-release premise applicability;
- separation of artifact observations from semantic effects, closed
  evidence-bearing kernels, exact citation-entailment direction and
  applicability, indirect derivation, producer quantifiers, valid-use
  certificates, local invariant/dataflow composition, and exposed
  reconstructed proofs;
- adversarial safe callers, every safe API boundary, interacting compilation
  configurations, and staged generated behavior with ordered fallible exits,
  tool interpretation, partial effects, and freshness where applicable;
- exact TCB/dependency relationships and both limited and genuinely universal
  tool evidence;
- all verdict certificates, including incomplete proofs without invented
  witnesses, completed multi-premise UB witnesses, whole-execution
  postcondition reasoning, and conditional deployment/probabilistic claims;
- reporting behavior that preserves exact scope, proves every relationship it
  asserts, and exposes proof-artifact defects without imposing a separate
  graph or exhaustive inventory of equivalent client witnesses; and
- the abstraction-design firewall, minimum-capability modeling, consequential
  candidate comparison, compatibility/migration analysis, rejection of
  proposal laundering, and fresh audit of implemented changes.

Every real audit incident should be considered for a regression fixture. Static
artifact review is not behavioral validation; run evaluations only in an
explicitly scoped validation phase.

## Anti-drift Controls

Maintain these controls as the project grows:

- Keep the installable package allowlisted or structurally isolated from
  `maintainers/`.
- Reject runtime-package links into maintainer material.
- Check one-way traceability links from this document to stable runtime headings.
- Require operational changes to update traceability and evaluations, or state
  why no existing behavior changes.
- Periodically perform a subtractive review: remove each agent-facing paragraph
  hypothetically and retain it only if correct behavior becomes worse.
- Review the skill when supported Rust ranges change, relevant features
  stabilize, authoritative documentation changes materially, or an incident
  exposes a gap.
- Use short decision records for major reversals, including the evidence and
  conditions that would reverse the decision again. Do not duplicate Git history
  in a generic changelog.
- Keep templates structural. Do not let them become a second source of
  operational rules that diverges from the references.

## Known Documentation Sensitivities

Some topics, especially evolving unsafe-field, aliasing/provenance, FFI,
target-feature, and compiler/linker behavior, may lack authoritative text strong
enough for a requested proof. The runtime response must be `UNPROVED` or
conditional on an explicit TCB entry, plus a narrowly stated documentation gap.

This section records why the skill remains authority-driven and conditional; it
must not grow into an alternative semantic specification.
