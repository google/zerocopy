<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent skills for Anneal

This directory holds the pure-Markdown policy skills specific to the Anneal
verifier. Shared repository-owned skills and vendored `joshlf/skills` packages
live in [`../../skills/`](../../skills/README.md), the `cargo-anneal` CLI skill
lives in
[`../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md`](../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md),
and [`../.agents/skills.json`](../.agents/skills.json) exposes all three skill
directories for discovery. See [`../AGENTS.md`](../AGENTS.md) for standing
rules and the [task routing table](#task-routing) below.

| Skill | Source | Purpose |
| :--- | :--- | :--- |
| [`change-review`](change-review/SKILL.md) | Repository-owned | Local and hosted review workflow, risk sizing, pipelining, and receipts ([maintainer contract](../docs/review-policy-design.md)) |
| [`proof-scaling`](proof-scaling/SKILL.md) | Repository-owned | Lean proof scaling, representation shifts, bundled `Anneal.*` libraries, Pass-1 `TrustedBoundary` rules, and cliff escape |
| [`source-control`](source-control/SKILL.md) | Repository-owned | Adapted from [`google/zerocopy`'s Contributing Guide](https://github.com/google/zerocopy/discussions/1318); commits, worker quarantine, publication, and stacks |
| [`spec-authoring`](spec-authoring/SKILL.md) | Repository-owned | Body-last spec archaeology, total-logic defaults, anti-echo, `[A4]` pre-proof sanity, and `Spec` isolation |
| [`trust-review`](trust-review/SKILL.md) | Repository-owned | Derived from [`META_PRINCIPLES.md`](../META_PRINCIPLES.md), [`PRINCIPLES.md`](../PRINCIPLES.md), [`THREAT_MODEL.md`](../THREAT_MODEL.md), and [`docs/trust-model.md`](../docs/trust-model.md) |

Anneal's Pass 1 containment applies across all skill roots (see
[`../AGENTS.md`](../AGENTS.md#code-review-rules)). Provenance and SHA-256
digests for vendored `joshlf/skills` packages are recorded in
[`../../skills/README.md`](../../skills/README.md) and
[`../../skills/vendor-lock.json`](../../skills/vendor-lock.json).

## Task routing

Use this table with the
[`Required skills`](../AGENTS.md#required-skills) rules. Paths in code
spans below are relative to `anneal/`.

| Activity | Required skills |
| :--- | :--- |
| Authoring changes for publication, reviewing code/commits/PRs, or auditing trust boundaries | [`change-review`](change-review/SKILL.md) (delegated reviewers: Part I only), [`trust-review`](trust-review/SKILL.md) |
| Designing, implementing, refactoring, or reviewing code for comprehension, invariants, or safe evolution | [`robust-code`](../../skills/robust-code/SKILL.md) |
| Writing, revising, or reviewing technical prose (docs, comments, commits, PRs, issues) | [`reader-oriented-explanation`](../../skills/reader-oriented-explanation/SKILL.md), [`clear-writing`](../../skills/clear-writing/SKILL.md) (writing skills) |
| Adding, revising, or reviewing explanatory inline (`//`, `--`) or doc (`///`, `//!`, `/--`, `/-!`) comments | [`comment-guidelines`](../../skills/comment-guidelines/SKILL.md), plus writing skills |
| Structuring commits, commit messages, worker integration, stack locking/rebasing, or PR publication | [`source-control`](source-control/SKILL.md), [`commit-message`](../../skills/commit-message/SKILL.md), [`authorship-disclosure`](../../skills/authorship-disclosure/SKILL.md), plus writing skills |
| Preparing or updating Git commits, PR descriptions, or externally visible prose | [`authorship-disclosure`](../../skills/authorship-disclosure/SKILL.md) |
| Designing or redesigning a system, subsystem, semantic model, protocol, or framework end to end | [`architectural-design`](../../skills/architectural-design/SKILL.md), [`model-refinement`](../../skills/model-refinement/SKILL.md), [`swarm-model-refinement`](../../skills/swarm-model-refinement/SKILL.md), plus writing skills |
| Simplifying or generalizing conceptual models, semantic interfaces, schemas, protocols, or instructions | [`model-refinement`](../../skills/model-refinement/SKILL.md) |
| Coordinating multi-agent conceptual model refinement across theories, designs, schemas, or instructions | [`swarm-model-refinement`](../../skills/swarm-model-refinement/SKILL.md), [`model-refinement`](../../skills/model-refinement/SKILL.md) |
| Creating, revising, evaluating, or retiring agent skills or maintainer guidance | [`skill-authorship`](../../skills/skill-authorship/SKILL.md), [`model-refinement`](../../skills/model-refinement/SKILL.md) |
| Verifying Rust, authoring specs, or scaling Lean proofs | [`cargo-anneal`](../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md), [`spec-authoring`](spec-authoring/SKILL.md), [`proof-scaling`](proof-scaling/SKILL.md) |
| Leading ambiguous efforts, recovering requirements, evaluating architecture, or recovering context | [`tech-lead`](../../skills/tech-lead/SKILL.md), plus writing skills |
| Multi-round research on Rust/`rustc`/Lean 4 or harvesting findings into the reference corpus (with user approval) | [`reference-research`](https://github.com/google/zerocopy/blob/reference/skills/reference-research/SKILL.md) (`google/zerocopy` `reference` branch; see [Technical reference corpus](#technical-reference-corpus)) |

## Architecture and trust boundary

Anneal's design checks `Trusted.CrateTheorem` in Lean 4 over typed
`Runtime(PostCleanup)` MIR and compiler facts. A result asserts that its TCB
meets its trust policy and that the verified code is UB-free and meets its
stated specifications if its trusted code is correct and the logged
assumptions are jointly valid. See the [trust model](../docs/trust-model.md).

Keep first-party verifier code that requires trust in `trusted/`. Audit the
pinned build inputs, `ci/`, and Zerocopy's root workflows as part of boundary
enforcement.

- Limit `trusted/` to primitive definitions that state or gate
  `Trusted.CrateTheorem` and `VerificationResult`, the CI correspondence
  adapter and claims, and the effectful auditor, CLI, and capture code.
- Keep `theory/` and `correspondence/` pure and effect-free. The auditor and
  Lean kernel check both.
- The SHA-256-pinned `vendor/lean-miri/` model is audited and kernel-replayed
  for CI correspondence only. Keep it out of the toolchain archive and the
  imports of `trusted/lean/` and `theory/`.

## Commenting in `trusted/`

Audit of `trusted/` and its pinned manifests must suffice to check the project
principles and threat model. All `trusted/` code receives human review. Use
[`comment-guidelines`](../../skills/comment-guidelines/SKILL.md) and its writing
skills to give human reviewers explicit rationale, invariants, assumptions,
and contracts for all `trusted/` code.

Any code in `trusted/` modeling Rust semantics or `rustc` structures must
explain the correspondence in comments and both quote and cite
`rust-lang/reference` or `rust-lang/rust` at a pinned commit hash.

## Dependencies in `trusted/`

Use battle-tested crates (parsing, serialization, hashing, logging) to limit
bespoke TCB code; prefer focused deps with few transitives and low soundness
risk. Check provenance, pinned checksums, and transitives on additions/updates.

## Technical reference corpus

- Before repeating broad research, consult the orphan `reference` branch if
  accessible and follow its
  [`AGENTS.md`](https://github.com/google/zerocopy/blob/reference/AGENTS.md).
  Filter `CATALOG.json` programmatically and check each report's `REPORT.json`,
  `Applicability`, and `Boundaries` against Anneal's pins. In `trusted/`, quote
  and cite authoritative primary upstream sources.
- Consider `reference-research` when design or soundness depends on
  undocumented behavior absent from the catalog, or for findings costly to
  recover. Present the questions or findings and ask the user to choose
  planning only or execution and publication. Get explicit approval before
  running the skill or pushing to `google/zerocopy`.
