# Technical reference corpus

This orphan branch contains a self-contained corpus of technical reference
reports. Its purpose is to preserve precise, expensive-to-recover knowledge for
future agents: behavior discovered through source inspection, execution,
specifications, documentation synthesis, or other evidence that would otherwise
need to be researched again.

The corpus is general-purpose. It may cover Lean, Rust, Charon, Aeneas, Anneal,
zerocopy, or other systems.

## Start here

Agents must read [`AGENTS.md`](AGENTS.md) before using or changing the corpus.
It defines the branch's authority, evidence discipline, and publication rules.

Before authoring a report, also read [`FORMAT.md`](FORMAT.md). It defines the
current report structure, subject-identification requirements, evidence roles,
scope boundaries, and revalidation guidance.

Technical reports live under `reports/`. Each report is a self-contained
directory whose entry point is `REPORT.md`; a report may also preserve local
evidence or probes when doing so materially reduces future research cost.

The current tip of `refs/heads/reference` is the canonical corpus state. Git
history records how that state evolved, but readers should not need to reconstruct
the current corpus from historical commits.

## What this corpus is for

Use this branch for durable technical knowledge whose future retrieval or
reconstruction would be meaningfully expensive, especially when the result is
subtle, version-sensitive, distributed across several primary sources, or easy to
overgeneralize.

Reports are intentionally precise about what was examined and what the evidence
establishes. An old report remains useful evidence about the exact subject it
identifies when upstream software moves on.

This branch is not a mirror of upstream documentation and is not authoritative
for the systems it describes. Primary upstream sources retain that authority.
