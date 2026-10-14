# Execution milestones for Anneal semantic and certificate goals

## Summary

The follow-on execution initiative defines 49 milestones covering all 52 previously investigated MiniRust/assembly topics and the older R095/P127/P131 prototype outcomes. It separates 16 experiments, 3 prototypes and 30 proof goals. These are completion criteria for new work, not a claim that the work has been performed.

The public execution tracker is [issue3876](https://github.com/google/zerocopy/issues/3876). The source reports completed the research agenda; their investigated limitations now supply concrete executions and semantic connections to establish. Closing a report topic did not discharge these new milestones.

## Applicability

This package preserves the issue/acceptance snapshot observed 2026-10-14, relative to reference 32f279dc7f8faa27ded717ba664c5d30df5503a2. It is an agent-authored execution plan. Its criteria do not define normative Rust, instruction-set or theorem-prover behavior.

`milestones.json` gives stable E01–E49 identities, kinds, snapshot open states and MR/AS associations. `baseline-frontiers.json` preserves every original frontier and its exact question hash as starting evidence. Those historical states are not a live progress dashboard: later execution reports and the issue record actual results. The grouping remains revisable while the original questions and stronger acceptance goals remain recoverable.

## Findings

### Work is organized around missing semantic connections

Basis: the published baseline's findings and explicitly derived execution decomposition.

1. Source and import: restore exact tools, capture configured/resolved/generated subjects, run minimize/Miri/formality, and certify an actual minimal source-to-model fragment.
2. Semantic definitions and effects: obtain exact artifacts, give verified Specr/choice semantics, and instantiate coupled MiniRust handlers with adequacy.
3. Memory and library reasoning: establish numeric/FP, representation/layout/provenance/borrow/race invariants, connect actual operations to storage, port real APIs, and prove permitted-client abstraction soundness.
4. Machine code: bind parser/layout/decoded instructions, complete accesses, reference ISA behavior and selected upstream backend configurations.
5. Rust/assembly composition: check ABI witnesses, inline allocation/effect/continuation rules, resource entry/prefix/exit relations and behavioral replacement.
6. Extensions: execute and prove required weak-memory, unwind, security and environment contracts.
7. Acceptance and costs: implement a small consumer, prove certificate soundness/binding, complete strict four-law SMT checking and compare equivalent workloads and upgrade repair.

Several backend experiments are alternative routes. A useful comparison requires the same accepted domain and observations; a compiler or language name does not establish a semantic connection. A selected prototype can inform architecture choice without closing the broader theorem.

### Experiment, prototype and theorem completion require different evidence

An experiment needs an actual identified tool/model run, complete command statuses, retained useful inputs/outputs and discriminating controls. An access failure, missing tool or failed execution remains a distinct result. A negative experiment can settle its tested hypothesis while leaving the intended proof goal open.

A prototype needs a real implemented interface and an exercised acceptance path. Producer-supplied identities, predicates or success flags cannot define the independently required claim. Changed-subject, omitted-operation, hidden-assumption and weakened-domain controls must reach the actual consumer.

A proof milestone needs a checked theorem at its declared program, model, resource, target and artifact domain, with exact direction/quantifiers and dependency assumptions. An owned fragment, finite agreement, source Qed or build success cannot stand in for a broader upstream or Rust-source theorem. A proof whose hypotheses assume the missing connection leaves that connection open.

E10/P127 preserves the initial Rust-source/import adequacy goal; E19/P131 preserves actual memory-operation/storage interpretation; E47/R095 preserves unchanged whole-law strict certificate acceptance. Their narrower earlier specimens and raw outcomes remain valuable evidence without satisfying these stronger criteria.

### Publication and progress remain separately accountable

Completed results should be persisted in coherent validated reference trees with immutable subjects, exact evidence and narrow revalidation. The actual remote identity must be read back before issue completion state changes. Record partial results against their milestones without replacing the larger acceptance criteria. If evidence disproves a desired claim or an artifact remains inaccessible, preserve the outcome and the required resolution explicitly.

The initial execution order starts the actual frontend/Miri pipeline, four-law certificate completion and a checked scalar assembly adapter. Subsequent work uses complete byte/alias and machine paths to guide logic ports, extended domains and matched measurements. Task-private tool restoration, isolated writable scratch and bounded/serialized large builds keep experiments reproducible and resource use reviewable.

## Boundaries

This package establishes a complete mapping of the 52 starting frontier identities into 49 execution/proof milestones. It does not establish any of those semantic goals, adopt an architecture, provide a completion-time estimate or convert a conditional model theorem into a physical or source-Rust guarantee. The issue's checkboxes and later result packages must carry separately supported progress.

Exact inaccessible artifacts may require an accessible source mirror. Some broad goals require substantial new formalization; installing a prover or replaying a related theorem does not discharge them. Experimental and production claim domains must remain explicit throughout.

## Evidence

- `milestones.json`: 49 stable criteria with kinds and source-question associations.
- `baseline-frontiers.json`: 52 exact starting question hashes, bounded findings, bindings and stronger/unperformed frontiers from the pinned published baseline.
- `issue-snapshot.md`: exact public issue snapshot, hash-bound in metadata.
- [Baseline synthesis](../anneal-minirust-assembly-coverage-and-adoption-synthesis-2026/REPORT.md): semantic connections, conditional alternatives and performed evidence.

No new semantic experiment is claimed by this plan. Its counts and associations are navigation and accountability checks, not proof of semantic completion.

## Revalidation

Reconcile later issue edits with stable E and MR/AS identities. Before closing an item, inspect its actual result, scope, assumptions, negative controls and published artifact identity against the unchanged acceptance goal. Revalidate only affected tool/model/source/configuration premises after changes; never infer success from the presence of a report or identifier.

*Authored by an AI agent acting on joshlf's behalf.*
