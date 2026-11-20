<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent skills for Anneal

This directory holds the pure-Markdown policy skills specific to the Anneal
verifier. Shared repository-owned skills and vendored `joshlf/skills` packages
live in [`../../skills/`](../../skills/README.md), and
[`../.agents/skills.json`](../.agents/skills.json) exposes both directories for
skill discovery. See [`../AGENTS.md`](../AGENTS.md) for standing rules and the
task routing table.

| Skill | Source | Purpose |
| :--- | :--- | :--- |
| [`change-review`](change-review/SKILL.md) | Repository-owned | Local and hosted review workflow, risk sizing, pipelining, and receipts ([maintainer contract](../docs/review-policy-design.md)) |
| [`source-control`](source-control/SKILL.md) | Repository-owned | Adapted from [`google/zerocopy`'s Contributing Guide](https://github.com/google/zerocopy/discussions/1318); commits, worker quarantine, publication, and stacks |
| [`trust-review`](trust-review/SKILL.md) | Repository-owned | Derived from [`META_PRINCIPLES.md`](../META_PRINCIPLES.md), [`PRINCIPLES.md`](../PRINCIPLES.md), [`THREAT_MODEL.md`](../THREAT_MODEL.md), and [`docs/trust-model.md`](../docs/trust-model.md) |

Anneal's Pass 1 containment applies to both skill roots (see
[`../AGENTS.md`](../AGENTS.md#code-review-rules)). Provenance and SHA-256
digests for vendored `joshlf/skills` packages are recorded in
[`../../skills/README.md`](../../skills/README.md) and
[`../../skills/vendor-lock.json`](../../skills/vendor-lock.json).
