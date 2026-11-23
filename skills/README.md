<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent skills

This directory holds repository-wide agent skills shared across
`google/zerocopy`, along with crate-specific Zerocopy skills. Anneal verifier
review, trust-boundary, and source-control policy skills live in
[`../anneal/skills/`](../anneal/skills/README.md). See
[`../zerocopy/AGENTS.md`](../zerocopy/AGENTS.md) and
[`../anneal/AGENTS.md`](../anneal/AGENTS.md) for subtree standing rules and task
routing.

## Repository-owned skills

| Skill | Scope | Purpose |
| :--- | :--- | :--- |
| [`unsafe-rust`](unsafe-rust/SKILL.md) | Shared / Rust | Proof-grade unsafe Rust authoring, safety documentation, soundness review, and TCB auditing |
| [`zerocopy-development`](zerocopy-development/SKILL.md) | `zerocopy/` | Implementation, toolchain gating, macro generation, UI tests, and validation for `zerocopy` and `zerocopy-derive` |
| [`zerocopy-review`](zerocopy-review/SKILL.md) | `zerocopy/` | Pull-request and patch review for `zerocopy` and `zerocopy-derive` |

## Vendored `joshlf/skills` packages

Vendor only the documentation and data each skill needs. Keep supporting
material, such as bibliographies and development notes, upstream. Every skill
in this directory outside the repository-owned set listed above needs an entry
in [`vendor-lock.json`](vendor-lock.json), which pins upstream revisions and
per-file SHA-256 digests. [`../ci/check_skills.py`](../ci/check_skills.py)
verifies the lock and enforces the repository-owned set.

All skill roots loaded by Anneal accept non-executable documentation and data
files. Keep scripts, executables, and ambient agent or build configuration
out of these roots.

`research-wheel` supports multi-wave inquiry and can run on its own.
`architectural-design` uses it for research that needs several adaptive
rounds. The [Anneal reference corpus guidance][reference-corpus] applies
when working with the separately distributed corpus.

[reference-corpus]: ../anneal/AGENTS.md#technical-reference-corpus

| Skill | Source | Upstream path & revision |
| :--- | :--- | :--- |
| [`architectural-design`](architectural-design/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`architectural-design/` at `fcd5ac02ddc0ad1002db890a7b94c355bb73226b`](https://github.com/joshlf/skills/tree/fcd5ac02ddc0ad1002db890a7b94c355bb73226b/architectural-design) |
| [`authorship-disclosure`](authorship-disclosure/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`authorship_disclosure/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/authorship_disclosure) |
| [`clear-writing`](clear-writing/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`clear-writing/` at `12c20182ac57213eebb3f6ade950911e7b563c2a`](https://github.com/joshlf/skills/tree/12c20182ac57213eebb3f6ade950911e7b563c2a/clear-writing) (see below) |
| [`comment-guidelines`](comment-guidelines/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `comment_guidelines/` at `b563468a8148df117283494915cee5b6561cc47f` (historical pin) |
| [`commit-message`](commit-message/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`commit-message/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/commit-message) |
| [`model-refinement`](model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`model-refinement/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/model-refinement) |
| [`reader-oriented-explanation`](reader-oriented-explanation/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`reader-oriented-explanation/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/reader-oriented-explanation) |
| [`research-wheel`](research-wheel/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`research-wheel/` at `95420245403de7d840c8469e2bb4dc747e4ab6cd`](https://github.com/joshlf/skills/tree/95420245403de7d840c8469e2bb4dc747e4ab6cd/research-wheel) |
| [`robust-code`](robust-code/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`robust-code/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/robust-code) (see below) |
| [`skill-authorship`](skill-authorship/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`skill-authorship/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/skill-authorship) |
| [`swarm-model-refinement`](swarm-model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`swarm-model-refinement/` at `f0afc6cb1203fff09089112f31cc481df7f1de75`](https://github.com/joshlf/skills/tree/f0afc6cb1203fff09089112f31cc481df7f1de75/swarm-model-refinement) (see below) |
| [`tech-lead`](tech-lead/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `tech-lead/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d` (historical pin) (see below) |

The current public export omits `comment-guidelines` and `tech-lead` and
no longer resolves their recorded upstream revisions. The lock still
verifies the copies checked into this repository.

## Local modifications

Most vendored `joshlf/skills` packages are kept byte-for-byte identical to
upstream. The following packages carry intentional, documented local
modifications (also recorded in [`vendor-lock.json`](vendor-lock.json)):

- **`skills/robust-code/references/design-examples.md` and
  `skills/tech-lead/references/context-recovery.md`:** Carry the repository
  copyright and license header while preserving their upstream bodies unchanged.

- **`skills/clear-writing/`:** Links to the pinned upstream
  `references/SOURCES.md` bibliography.

- **`skills/swarm-model-refinement/`:** Omits the executable upstream
  `scripts/holdout-seal.py` helper. Cooperative same-UID `sealed-file` mode
  requires a separately supplied host helper. The skill uses
  `private-subagent` only if the host can resume a private worker, and
  records holdout mode `none` if neither mode is available. Discovery-only
  runs return to the caller after Phase 1. T3 handles repairable checks
  and bounded retries before T1 can stop the run.

- **`skills/robust-code/`:**
  - **Omitted file:** `references/agent-scaffolding.md`, which covers external
    agent evaluation harness design, multi-arm benchmarking methodology, and
    prompt contract templates managed separately in repository-owned files. The
    core scaffolding honesty and boundary principles remain in `SKILL.md`.
  - **`SKILL.md` patch:** Removes the sentence referencing
    `agent-scaffolding.md` so no broken link remains in-tree.

Except for documented local modifications, keep vendored `joshlf/skills`
packages unmodified so they can be updated cleanly from upstream; place
project-specific conventions in repository-owned `AGENTS.md` and skill files.
