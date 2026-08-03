# Unsafe Rust V3 Targeted Confirmation Plan

> **Evaluator-only material. Do not expose this file to evaluated agents.**
>
> **Preregistration status:** DRAFT. No evaluated report may be collected until
> the packages, fixtures, prompts, oracle, rubrics, schedule, condition map, and
> gates are independently checked, frozen, and identified in the run manifest.

## Purpose

This confirmatory evaluation tests whether the V3 skill revision reliably
changes the specific proof behavior that prevented V2 from passing its strict
release gates, while preserving the abstraction-design and general-audit
behaviors that V2 already performed well.

It tests mechanisms, not release readiness. Passing this evaluation permits a
later broad release gate; it does not replace that gate.

## Frozen candidate conditions

The intended conditions are:

| Condition | Package tree digest | `SKILL.md` digest | Role |
|---|---|---|---|
| V3 | `668f70202c7bc8f23f7f894fb784a9629fd292c7f6fe69ede815b0e4c10137bf` | `0e23f7747cc63014bade7543efaf745e7e9a7e5d6dee2a48c602ef7a3eba091e` | treatment |
| V2 | `40b4171cc9daf7e51ba032aef52157a85a49c4c12cea8696deadb948e0867897` | `a0a75ef8a14497aa78b50b459981097ee99605c57fec95c637cf59aaa20fe766` | pre-change comparator |

The comparison uses the coherent V2 package, not a synthetic deletion
ablation. V3's changes are distributed across the core workflow, specialized
references, and templates; deleting isolated passages would create a package
that no maintainer proposes to ship. A no-skill baseline belongs in the later
broad gate.

## Design

Use eight focused modes, two conditions, and five fresh replicates per cell:

> 8 modes × 2 conditions × 5 replicates = 80 reports.

Each evaluated agent receives one opaque package, one opaque target, and one
empty output directory. Reports are randomized across conditions and modes.
Condition identity is revealed only after reports have been preserved, hashed,
blind-scored twice, and adjudicated.

Five replicates are an engineering reliability minimum, not a population-level
estimate of model behavior. The primary gates are exact per-replicate capability
requirements; pooled averages and statistical significance cannot rescue a
failure.

## Modes

### S — Symbolic interval and patch-release closure

Tests preservation of a symbolic stable-release interval, membership of a
non-`.0` patch release, rejection of sampled CI/toolchains as an inventory, and
closure by a version-parametric proof over a justified superset.

### C — Conflicting policies, conservative union, and exclusions

Tests exact recovery of two nonlinear current policies, construction of a
conservative audit domain without mislabeling it the project promise, a policy
exclusion backed by effective rejection, and a parametric proof over a simple
superset without Cartesian enumeration.

### X — Conditional feature/target/allocator cross-product

Tests recovery of an easily missed simultaneous configuration, distinction
between a supported bad case and a genuinely enforced exclusion, and a complete
region-scoped UB certificate.

### Q — Existential refutation versus incomplete universal proof

Pairs a complete valid-use UB witness, which must close as `UNSOUND`, with an
unavailable third-party unsafe implementation, which must remain `UNPROVED`
without fabricated UB or silent trust.

### W — Whole-execution UB and behavioral contracts

Tests that observations from an execution containing UB cannot establish a
postcondition counterexample, while an independent UB-free wrong-result path
can establish `CONTRACT-BROKEN`. Soundness and each behavioral theorem must be
reported separately.

### M — Multi-release affirmative certificates

Tests the three admitted positive proof forms independently: a parametric proof,
an exact exhaustive applicable partition, and an exact proposition-preserving
compatibility premise. A fourth claim has endpoint-only evidence and must retain
an `UNPROVED` interior. A cutoff, stability badge, or later documentation may
not supply continuity or backward propagation.

### R — Abstraction-redesign regression

Tests literal current-artifact review of an unsafe abstraction backed by a
caller-implementable safe trait, recovery of the minimum required capability,
a parsimonious locally enforced redesign, compatibility analysis, and the
firewall between an `UNSOUND` current artifact and an uncertified proposal.

### K — Multi-issue regression control

Tests adversarial caller-provided safe behavior, exposure of a materially
reconstructed local proof, preservation of every clause in a published contract
despite sparse visible consumers, continued coverage after the first aggregate
UB witness, and non-certification of proposed repairs.

The exact individually scored propositions are frozen in the oracle and copied
into per-mode blind-scoring rubrics before collection.

## Hypotheses

- **H-domain:** V3 passes every S, C, and X atom in all five replicates with
  zero hard errors.
- **H-verdict:** V3 passes every Q and W atom in all five replicates with zero
  hard errors.
- **H-release:** V3 passes every M atom in all five replicates with zero hard
  errors.
- **H-regression:** V3 passes every R and K atom in all five replicates, with
  zero proposal laundering and zero hard errors.

## Primary gates

The targeted confirmation passes only if all of the following hold:

1. Every V3 semantic atom passes 5/5.
2. V3 has zero hard errors.
3. V3 has zero proposal laundering.
4. V3 silently admits no TCB premise and uses no invalid or inapplicable
   authority as a necessary proof premise.
5. Every V3 report respects the frozen source-only scope and word budget.

Failure of any primary gate fails the run. Do not average failures away, weaken
an atom after seeing reports, or use V2 weakness to excuse a V3 error.

## Secondary comparison

After unblinding:

- report V3 and V2 separately for every atom and mode;
- require that no V3 atom has fewer passes than its matched V2 atom;
- call V3 5/5 plus lower V2 performance evidence of targeted lift;
- call matched 5/5 performance ceiling replication, not causal improvement;
- do not pool heterogeneous modes into a headline score.

## Global hard errors

The frozen oracle may specialize these rules, but may not weaken them:

- asserting full `PROVED` after contracting or failing to justify `Required`;
- claiming closure without `Required ⊆ Covered`;
- inventing policy precedence or calling a conservative audit domain the project
  promise;
- treating CI, endpoints, sparse documentation, a cutoff, or a stability badge
  as interval coverage;
- issuing `UNSOUND` without valid use, reachability, a false exact safety
  proposition, and an applicable UB consequence;
- issuing only `UNPROVED` after explicitly proving all four UB links;
- issuing `CONTRACT-BROKEN` using only an execution containing UB;
- claiming any observation remains guaranteed because it occurs before UB;
- silently trusting a third-party unsafe implementation or caller-controlled
  safe behavior;
- certifying an unimplemented design or allowing it to narrow a current-artifact
  obligation;
- using an unchecked, invalid, or inapplicable authority as a necessary premise;
- reading oracle, sibling, condition-map, prior-report, or evaluator material.

A missed atom is not automatically a hard error. It becomes one only when it
also satisfies a frozen hard-error definition, usually by making an affirmative
false claim.

## Evaluated-agent protocol

Before collection, freeze and hash:

- both package trees;
- all target trees and opaque runtime copies;
- the evaluated-agent prompt;
- the oracle and per-mode scoring rubrics;
- exact official documentation URLs or a byte-identified mirror;
- the randomized schedule and condition map;
- output schema, word budgets, tool policy, and rerun policy.

Each report agent must:

- be fresh and receive no prior conversation (`fork_turns="none"`);
- audit exactly one cell without helper agents;
- inspect only its opaque target, package, exact permitted official Rust/std
  documentation, and empty output directory;
- avoid building, testing, executing, or macro-expanding the target;
- write one `report.md` and return the same report;
- stay within 1,800 words, except that K receives the same preregistered
  2,200-word cap in both conditions.

Only genuine infrastructure failures may be rerun. Budget exhaustion, refusal,
or semantic noncompletion is an incomplete/failed replicate, not infrastructure.
Preserve every invalid attempt and document the disposition before retrying.

## Blind scoring and adjudication

After collection and before unblinding:

1. Preserve and hash every raw report.
2. Assign random anonymous labels independently within each mode.
3. Give two fresh scorers the target, common scoring rules, exact per-mode
   rubric, and ten anonymous reports, but no package, condition map, sibling
   package, or prior scores.
4. Score explicit propositions and valid derivations, not preferred terminology.
5. Use a fresh adjudicator only for scorer disagreements.
6. Adjudicate novel findings against source and authority before unblinding.
7. Preserve raw scores, adjudications, ledgers, and all integrity checks.

The scorer must not infer a missing material premise from vague shorthand. The
rubric must state in advance which compact formulations count, especially where
one conceptual defect admits multiple independently scored witnesses.

## Oracle review

Before the first report, two independent reviews must confirm:

- each atom expresses one necessary proposition rather than a compound grading
  preference;
- the expected verdict follows from the exact source and claim;
- every required Rust/std proposition is supported by the cited versioned
  authority;
- no target leaks its oracle, expected verdict, historical issue identity, or
  condition;
- positive fixtures are actually provable, not merely free of an obvious bug;
- the V2 comparator is not penalized for terminology introduced only in V3;
- shorthand and alternative correct proofs are accepted consistently.

Any correction before collection changes fixture/oracle digests and is recorded
as preregistration work. Any semantic correction after collection invalidates
the affected mode for confirmatory use; it cannot be repaired in place.

## Later broad release gate

Run the broad gate only if this targeted confirmation passes. It must include
the full abstraction-design and legacy suites, corrected V2 modes, historical
vulnerable/fixed pairs, generated/configuration cases, authoring and repair,
current zerocopy owning shards and integration, opaque holdouts, and matched V2
and no-skill subsets. It retains zero hard errors, zero proposal laundering,
focused zero-miss recovery, no repaired-side recurrence, and artifact-integrity
requirements.

