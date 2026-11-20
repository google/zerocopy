<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent skills for Anneal

This directory contains the agent skills required when working on
`joshlf/anneal`. See [`../AGENTS.md`](../AGENTS.md) for standing repository
rules and the routing table that maps tasks to these skills.

## Provenance

| Skill | Source | Upstream path & revision |
| :--- | :--- | :--- |
| [`authorship-disclosure`](authorship-disclosure/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`authorship_disclosure/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/authorship_disclosure) |
| [`comment-guidelines`](comment-guidelines/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`comment_guidelines/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/comment_guidelines) |
| [`commit-message`](commit-message/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`commit-message/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/commit-message) |
| [`model-refinement`](model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`model-refinement/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/model-refinement) |
| [`reader-oriented-explanation`](reader-oriented-explanation/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`reader-oriented-explanation/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/reader-oriented-explanation) |
| [`williams-style`](williams-style/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`williams-style/` at `b563468a8148df117283494915cee5b6561cc47f`](https://github.com/joshlf/skills/tree/b563468a8148df117283494915cee5b6561cc47f/williams-style) |
| [`source-control`](source-control/SKILL.md) | Repository-owned | Adapted from [`google/zerocopy`'s Contributing Guide](https://github.com/google/zerocopy/discussions/1318) and [`joshlf/gherrit`](https://github.com/joshlf/gherrit) |

Keep the vendored `joshlf/skills` packages unmodified so they can be updated
cleanly from upstream; place Anneal-specific conventions in repository-owned
files (`AGENTS.md` and `skills/source-control/`).
