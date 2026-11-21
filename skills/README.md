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
| [`architectural-design`](architectural-design/SKILL.md) | Shared | End-to-end architectural design, empirical grounding, conceptual model refinement, and specification authoring |
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

Both skill roots loaded by Anneal accept non-executable documentation and data
files. Keep scripts, executables, and ambient agent or build configuration
out of these roots.

| Skill | Source | Upstream path & revision |
| :--- | :--- | :--- |
| [`authorship-disclosure`](authorship-disclosure/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`authorship_disclosure/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/authorship_disclosure) |
| [`comment-guidelines`](comment-guidelines/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`comment_guidelines/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/comment_guidelines) |
| [`commit-message`](commit-message/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`commit-message/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/commit-message) |
| [`model-refinement`](model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`model-refinement/` at `0073be02ea65150ad56ded426261245ec1a22848`](https://github.com/joshlf/skills/tree/0073be02ea65150ad56ded426261245ec1a22848/model-refinement) |
| [`reader-oriented-explanation`](reader-oriented-explanation/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`reader-oriented-explanation/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/reader-oriented-explanation) |
| [`robust-code`](robust-code/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`robust-code/` at `468f74547999ad6879905c91398b1a218b010791`](https://github.com/joshlf/skills/tree/468f74547999ad6879905c91398b1a218b010791/robust-code) (patched; see below) |
| [`skill-authorship`](skill-authorship/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`skill-authorship/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d`](https://github.com/joshlf/skills/tree/3bf3f345b2916f8417306ba197f779b0b4429c1d/skill-authorship) |
| [`swarm-model-refinement`](swarm-model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`swarm-model-refinement/` at `f0afc6cb1203fff09089112f31cc481df7f1de75`](https://github.com/joshlf/skills/tree/f0afc6cb1203fff09089112f31cc481df7f1de75/swarm-model-refinement) (patched; see below) |
| [`tech-lead`](tech-lead/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`tech-lead/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d`](https://github.com/joshlf/skills/tree/3bf3f345b2916f8417306ba197f779b0b4429c1d/tech-lead) (header added; see below) |
| [`williams-style`](williams-style/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`williams-style/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/williams-style) (patched; see below) |

## Local modifications

Most vendored `joshlf/skills` packages are kept byte-for-byte identical to
upstream. The following packages carry intentional, documented local
modifications (also recorded in [`vendor-lock.json`](vendor-lock.json)):

- **`skills/robust-code/references/design-examples.md` and
  `skills/tech-lead/references/context-recovery.md`:** Carry the repository
  copyright and license header while preserving their upstream bodies unchanged.

- **`skills/williams-style/`:** Omits the upstream `references/SOURCES.md`
  bibliography and removes its optional link from `SKILL.md`.

- **`skills/swarm-model-refinement/`:** Omits the upstream
  `scripts/holdout-seal.py` helper (executable scripts stay out of vendored
  skill roots) and removes its relative link from `SKILL.md`; hosts supplying
  an external, unpinned `holdout-seal.py` still enable cooperative same-UID
  `sealed-file` mode, otherwise `private-subagent` or fail-closed `none`
  applies.

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
