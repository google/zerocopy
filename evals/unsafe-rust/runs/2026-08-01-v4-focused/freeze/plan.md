# Unsafe Rust V4 Focused Confirmation Plan

> Evaluator-only material. Never expose this file to evaluated agents.
>
> **Preregistration status:** FROZEN. This status is effective only when
> `LOCK.json` authenticates the complete freeze tree and records two independent
> oracle-review signoffs. No evaluated report may be collected before
> `protocol.py verify-static --locked` passes.

## Purpose

This evaluation tests whether V4 reliably fixes the concrete reasoning failures
observed in V3 while preserving V3's already-demonstrated quantifier/verdict and
abstraction-design capabilities. It is an absolute capability confirmation for
V4 with V3 as a diagnostic comparator, not a causal estimate of isolated text.

The run is deliberately focused. Passing permits another broad release gate;
it does not establish that every unsafe-Rust task or every model invocation will
succeed.

## Conditions and design

The intended package conditions are:

| Role | Package tree SHA-256 | `SKILL.md` SHA-256 |
|---|---|---|
| V4 candidate | `6d7e197e431b82eb81dbe7eefc79fde811e0e238435d38c69460cc068e631abb` | `ad48b3811cf2054be76e4b461a36f63e636afb246c5dd7a75e85756a53b22d83` |
| V3 comparator | `fc486dedde1f82ba232b4492808af85a12b27fa2aa27b1a35a3847b2b89f72e0` | `0e23f7747cc63014bade7543efaf745e7e9a7e5d6dee2a48c602ef7a3eba091e` |

Use five modes, two conditions, and five fresh replicates per cell:

> 5 modes × 2 conditions × 5 replicates = 50 reports.

Each agent sees one neutral package, one neutral target, the mode's URL-only
allowlist, and one empty output directory. Condition and mode labels are sealed
before collection. Five replicates are an engineering reliability threshold,
not a population estimate; averages cannot rescue a failed exact gate.

## Modes

### P — exact predicates, conservative containment, and exclusions

Tests recovery of two nonlinear policy predicates, explicit separating
witnesses and the exact set relationship, conservative full-case containment
before any configuration projection, distinction between project promise and
audit superset, effective exclusion, and closure of the local unsafe operation
and documented postcondition over every full case.

### B — ordered and fallible build relation

Tests whether the audit models the claim-relevant build script as an ordered,
fallible state transition rather than an endpoint environment-to-cfg map. It
covers partial output prefixes, process outcome, Cargo's interpretation,
freshness/rerun behavior, selected generated source, supported exclusions, the
unsafe operation, postcondition, and exact configuration-by-input sound region.

### L — local proof reconstruction and authority reconciliation

Tests separation of implementation correctness from proof-artifact adequacy,
exposure of a proof the reviewer had to reconstruct, complete local arithmetic
and control-flow reasoning, useful replacement `SAFETY` wording, and a bijection
between materially consumed Rust/std premises and checked version-matched
citations.

### Q — quantifier and verdict control

Unchanged semantic control from V3. It pairs a complete safe-use UB witness,
which must close as `UNSOUND`, with an unavailable third-party unsafe
implementation, which must remain `UNPROVED` without fabricated behavior or
silent trust.

### R — abstraction-design control

Unchanged semantic control from V3. It tests adversarial caller-provided safe
trait behavior, literal current-artifact review, extraction of the minimum
required capability, a more parsimonious locally enforced safe design, contract
delta analysis, and non-certification of an unimplemented proposal.

The oracle freezes the exact propositions. Every atom has a stated
`scope_basis` and dependency list so scoring requirements cannot be introduced
merely because an evaluator prefers a particular vocabulary or presentation.

## Hypotheses

- **H-P:** V4 passes every P atom in all five replicates without a P/global,
  TCB/authority, scope, budget, or completion defect.
- **H-B:** V4 passes every B atom in all five replicates under the same defect
  gate, including all ordered/fallible build-stage propositions.
- **H-L:** V4 passes every L atom in all five replicates under the same defect
  gate, including exposed reconstruction and premise/citation reconciliation.
- **H-controls:** V4 passes every Q and R atom in all five replicates without a
  defect, preserving established V3 capability.

V4 5/5 with lower V3 performance is evidence consistent with targeted lift.
Matched 5/5 is ceiling replication. Since the coherent packages differ in more
than one instruction, neither pattern is isolated causal proof.

## Primary gate

V4 passes only if all of these hold after dual scoring, consistency review, and
adjudication:

1. Every frozen V4 atom passes 5/5.
2. V4 has zero mode-specific or global hard errors.
3. V4 has zero proposal laundering and zero TCB/authority defects.
4. V4 has zero terminal semantic noncompletions.
5. Every V4 report respects the frozen visible-source scope, recorded
   operational scope, and word cap.
6. Q and R independently satisfy items 1–5; strength on new modes cannot mask a
   control regression.
7. Every scorer disagreement, every positive hard/global/TCB/scope/proposal
   flag (even when both scorers agree), every consistency-review challenge, and
   every novel finding receives a preserved adjudicated disposition.
8. V4 has zero independently confirmed novel material defects.
9. All freeze, packet, attempt, preservation, and byte-tree identity checks
   pass without manual permission repair or post-freeze mutation.

Failure of any item fails the run. Do not weaken an atom or hard-error rule
after seeing reports, average a failure away, or use V3 weakness as an excuse.

## Diagnostic comparison

After unblinding:

- report V4 and V3 pass counts separately for every atom;
- identify any V4 atom below its matched V3 count;
- classify V4 5/5 plus lower V3 as targeted-lift evidence;
- classify matched 5/5 as ceiling replication;
- classify any other improvement as suggestive but insufficient for the
  absolute gate; and
- do not pool heterogeneous atoms or modes into one headline score.

## Global scoring constraints

Mode rubrics may specialize but not weaken the common rules. In particular, a
report must not:

- certify a universal positive claim after contracting or failing to justify
  its required full-case domain;
- claim closure without a reviewable `Required(case) ⊆ Covered(case)`
  derivation;
- project to configuration while silently dropping input, state, time,
  artifact, process-outcome, or other material fibers;
- invent policy precedence or call a conservative audit superset the project's
  promise;
- issue `UNSOUND` without valid use, reachability, falsity of the exact safety
  proposition, and an applicable authoritative UB consequence;
- issue only `UNPROVED` after explicitly closing all four UB-certificate links;
- silently trust an unsafe dependency or caller-controlled safe behavior;
- certify an unimplemented design or use it to narrow the current artifact;
- necessarily rely on unchecked, invalid, version-mismatched, or inapplicable
  authority; or
- inspect prohibited oracle, sibling, map, prior-report, or evaluator material.

A missed atom is not automatically a hard error. Apply hard errors only under
their exact frozen definition. Extra correct regional detail is harmless, but a
maximal positive remainder is not required unless the target request expressly
asks for one.

## Collection protocol

Before collection, freeze and hash:

- both complete package trees;
- every target tree;
- evaluated-agent, scorer, consistency-reviewer, and adjudicator prompts;
- oracle, common rules, and per-mode rubrics;
- URL-only per-mode allowlists plus retrieval identities;
- schedule, blind maps, presentation orders, and commitments;
- schemas, validation/aggregation code, word caps, and policies.

Every report and evaluator agent uses a fresh context, `gpt-5.6-sol`, reasoning
effort `ultra`, `fork_turns="none"`, and no helper agents. The orchestration API
does not expose an exact hosted build or sampling seed; record this limitation.
Collection follows five balanced waves with at most three report agents active.
The next wave cannot be prepared until the preceding wave is terminal and the
authority verifier reproduces the frozen records.

Each report agent must inspect only its neutral packet and the exact permitted
official pages; it must not build, test, execute, expand, edit, or inspect
evaluator material. It writes one canonical `report.md`. That file is the sole
evaluated response channel. The orchestration transcript may retain chat-return
prose, but the run does not copy or score it; attempt metadata records the agent
identity and API completion state. Caps are identical across conditions: P
3,000 words, B 3,200, L 2,200, Q 1,800, and R 1,800.

Only genuine infrastructure failure permits a fresh retry. Refusal, budget
exhaustion, scope deviation, or semantic noncompletion is terminal. Preserve
every attempt and reason. A report without usable output gets a canonical
evaluator placeholder and fails missing propositions plus the completion gate;
a non-rerunnable invalid scorer, consistency reviewer, or adjudicator makes the
run `INVALID`.

## Blind scoring, consistency review, and adjudication

After all reports are preserved and before unblinding:

1. Materialize the pre-frozen anonymous label map within each mode.
2. Give two fresh scorers the target, common rules, exact mode rubric, and ten
   anonymous reports—never packages, maps, sibling modes, or prior scores.
3. Have a third fresh, condition-blind reviewer compare all ten reports and both
   raw score sets for every atom, hard-error, and global-defect family, attest
   each complete ten-report comparison, and challenge inconsistent decisions.
4. Construct review cells from all scorer disagreements, all agreed-positive
   defect flags, all consistency challenges, and all novel findings.
5. Give a fresh adjudicator only those cells and their source material; do not
   conceal an agreed positive flag or force preservation of an agreed error.
6. Preserve raw scores, consistency reviews, adjudications, events, packets,
   and all integrity bindings before unblinding.

The runner independently records word count, completion, and operational scope.
Scorers judge only what report text exposes. Aggregation combines those sources
without asking a scorer to infer unavailable telemetry.

## Integrity model

Copies and packet bindings use byte-tree identity: relative file path, file
kind, and bytes. Permission metadata is validated separately where relevant and
must not alter content identity. Every canonical artifact is captured once,
hashed, and preserved; later packets bind to the preserved digest. Append-only
events authenticate state transitions. A run-wide operation lock serializes
checks and writes.

The shared host does not provide cryptographically enforced filesystem or
network isolation. Neutral paths, procedural restrictions, exhaustive packet
inventories, before/after identity checks, and failure snapshots reduce but do
not eliminate that limitation. Disclose it in results.

## Oracle review and freeze

Before `LOCK.json`, two independent reviewers who did not author the fixtures
must inspect every target, request, atom, hard error, and cited proposition.
Each must confirm:

- the expected result follows from the exact source and request;
- every atom is necessary, proposition-focused, and has a valid `scope_basis`;
- dependencies are explicit and do not cause double credit or hidden demands;
- every Rust/std premise is supported by applicable versioned authority;
- every accepted TCB proposition has exact identity, scope, and consumer;
- no target leaks condition, oracle, verdict, historical provenance, or rubric;
- positive obligations are actually provable over the full declared case set;
- Q and R remain semantically equivalent controls across V3 and V4; and
- no maximal-region or stylistic requirement has entered scoring without an
  explicit request basis.

Record both signoffs, each reviewer's independent-non-author attestation, and
all unresolved ambiguities in the lock. A review timestamp may not follow the
lock timestamp. Any substantive change after review invalidates the signoffs
and requires fresh review.

## Forward-test discipline

Do not edit the skill, packages, fixtures, oracle, rubrics, protocol, policies,
or analysis rules after the lock or after seeing any evaluated output. If the
freeze is defective, mark the run invalid or exploratory, correct the design in
a new versioned run, and start fresh. The aggregate must preserve failures and
limitations rather than retrofitting the test to the observed reports.
