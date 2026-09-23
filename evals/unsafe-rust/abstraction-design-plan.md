# Unsafe Rust Abstraction-Design Evaluation Plan

> **Evaluator-only material.** Do not expose this plan, fixture sibling names,
> or expected atoms to evaluated agents.

## Objective and honest scope

Determine whether the conditional abstraction-design workflow causes fresh
agents to produce better proof-oriented unsafe-Rust designs without laundering
the current artifact's obligations.

“Exhaustive” here means every behavior required by the new design reference has
an explicit fixture atom and disposition. It does not mean that nine snippets
represent every possible unsafe abstraction, model, or codebase.

## Frozen treatment and comparator

- **Treatment:** the complete frozen `unsafe-rust` package, including
  `references/abstraction-design.md`.
- **Core ablation:** the same frozen package with the abstraction-design
  workflow, its activation/routing, its report-template section, and its
  cross-references removed. All ordinary unsafe-Rust proof, authority, TCB,
  API, configuration, and verdict guidance remains byte-for-byte identical.

This comparator isolates the added workflow better than a no-skill baseline.
It is not a prior released skill and must not be described as one.

Freeze and record both package digests before the first run. Do not edit either
package after observing results.

## Capability-closure matrix

| Mode | Capability under test | Fixture |
|---|---|---|
| A | Immutable third-party acceptance; literal current verdict; no unsolicited redesign | `a_acceptance` |
| R | Intent discovery; minimum capability; parsimony; current/proposal firewall | `b_projection_redesign` |
| T | Local enforcement versus hidden/transferred caller obligations | `c_ticket` |
| P | Unknown public consumers; unsafe-trait commitments; SemVer directionality | `d_published_contract` |
| C | Rust/feature/target/profile domain closure; no silent support contraction | `e_configuration_domain` |
| S | Sealing and module privacy; smallest invariant boundary | `f_sealed_boundary` |
| G | Greenfield specialization and safe reuse; no invented generic abstraction | `g_greenfield` |
| H | Incomparable performance/proof tradeoffs; no invented score | `h_tradeoff` |
| N | Implemented candidate is a new snapshot requiring a fresh audit | `i_new_snapshot` |

The evaluator-only fixture registry in
[`fixtures/abstraction-design-v1/README.md`](fixtures/abstraction-design-v1/README.md)
defines every exact atom and accepted alternative.

## Conditions, repetitions, and order

Run three independent fresh agents for each `(mode, condition)` cell:

```text
9 modes × 2 conditions × 3 replicates = 54 evaluated runs
```

Randomize cells across waves. Each agent sees one opaque target copy, one opaque
skill package, the neutral request, exact official versioned Rust documentation
as needed, and its own output path. It must not see another mode, replicate,
condition, report, oracle, plan, package, history, or evaluator file.

Use `fork_turns="none"`; do not reuse agents and forbid evaluated agents from
spawning helpers. The two conditions receive byte-identical prompts except for
the opaque skill-package path.

## Frozen prompt

```text
Act as a fresh source-review and design agent. Read the complete unsafe Rust
skill package rooted at [PACKAGE]/SKILL.md and every reference it directs you
to for this task, then follow it. Read REQUEST.md and the other files in
[TARGET], and complete exactly the requested review/design work.

Inspect only [TARGET], [PACKAGE], and exact versioned official Rust Reference
or standard-library documentation needed to verify claims. Do not inspect
sibling directories, another package or target, the enclosing repository,
version-control history, evaluator material, or prior reports. Do not modify,
build, test, macro-expand by execution, or otherwise execute the target. Do not
spawn helper agents.

Write the report to [OUTPUT] using apply_patch, then return the same report in
your final response. Keep the report focused and no longer than 1,400 words.
This is a focused review/design report, not a persistent whole-crate audit;
provide the equivalent proof material compactly.
```

Target-neutral requests to conclude without widening scope are permitted and
must be recorded. Any substantive hint invalidates and reruns the cell.

## Scoring

Score each preregistered atom as pass/fail. Equivalent reasoning counts;
headings, vocabulary, candidate names, and preferred prose do not.

An atom passes only if the report makes the required reasoning explicit. An
omission, ambiguous implication, or contradiction fails it. Do not infer credit
from a generally sophisticated report.

For each mode report:

- atom recovery and hard errors;
- current-artifact verdict accuracy;
- requirement and consumer-proposition extraction;
- candidate validity and proof plan;
- proof-surface/TCB/invariant reduction;
- public-contract and compatibility analysis;
- supported-domain coverage;
- current/candidate/post-change output separation; and
- unsupported certainty or obligation transfer.

After all evaluated runs finish, normalize reports under random labels and use
fresh blind scorers which know the mode oracle but not condition identity. A
separate adjudicator resolves disputed semantic claims against raw source and
applicable official documentation.

## Hard errors

Any one fails the run regardless of atom count:

- inferred intent, tests, known consumers, or a proposal narrows or discharges
  a current obligation;
- a proposal erases/downgrades a current finding or receives `PROVED` before
  implementation and fresh audit;
- an enforceable obligation is recommended as a hidden or unnecessary unsafe
  caller/implementer obligation;
- repository-visible consumers are treated as exhaustive for a public API;
- a binding public, SemVer, behavioral, MSRV, target, feature, profile, or
  performance constraint is silently weakened;
- an immutable acceptance-only task receives redesign, migration, or source
  changes;
- incomparable candidates are collapsed into an invented numerical score or
  unsupported priority;
- a new implementation inherits the design sketch's proof instead of receiving
  an exact-source audit;
- current-artifact, candidate, compatibility, and post-change conclusions are
  conflated;
- a fixed/sound current artifact is condemned without proof, or an unsound one
  receives unsupported `PROVED`; or
- forbidden oracle, paired-side, condition, or prior-report material is read.

## Preregistered gates

- Zero treatment hard errors.
- Every atom passes in at least `2/3` treatment replicates.
- The verdict-firewall atoms A1–A3 and R1, support-preservation atoms P2–P4 and
  C3–C4, and fresh-audit atoms N1–N4 pass `3/3` treatment replicates.
- No treatment replicate launders T's obligation or calls G's sketch proved.
- Report per-atom treatment/ablation rates and paired differences without
  pooling modes into a misleading single theorem.

The suite is exploratory if physical isolation, model identity, seed control,
offline documentation, or independent multi-scorer adjudication is missing,
even when all semantic gates pass.
