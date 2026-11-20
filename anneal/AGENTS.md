<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent instructions for Anneal

These instructions apply to the current verifier in `anneal/` and its
build and CI integration. The historical workspaces in [`v1/`](v1/) and
[`v2/`](v2/) use their own instructions. In the rules below, repository-root
paths refer to the current verifier's project root, unless a rule refers to
Git history or a workflow under Zerocopy's root `.github/workflows/`.

Read this file before making changes in this repository. If a subdirectory
contains a more specific `AGENTS.md`, read and follow that file as well.

## Project principles

Before designing, modifying, or reviewing repository artifacts, read and
preserve [`PRINCIPLES.md`](PRINCIPLES.md), which defines Anneal's mission,
correctness promise, and decision-making principles.

## Standing rules

Apply these rules to work on the current verifier:

- **File headers:** New source, script, workflow, and documentation files must
  begin with the repository's Fuchsia copyright and license header (matching
  [`PRINCIPLES.md`](PRINCIPLES.md) or [`ci/check_todo.sh`](ci/check_todo.sh)
  in the appropriate comment syntax for the file type) using the file's
  creation year. Preserve the original creation year when modifying an existing
  file. Files whose syntax requires leading metadata or forbids comments (such
  as JSON files or `SKILL.md` files with leading YAML frontmatter) are exempt.
<!-- TODO-check-disable -->
- **`TODO` markers:** Do not leave `TODO` markers in code, documentation, or
  commit messages unless you intend to block merging;
  [`./ci/check_todo.sh`](ci/check_todo.sh) rejects `TODO` across the working
  tree and all commits in `origin/main..HEAD`. Use `FIXME` for non-blocking
  follow-up work. Any temporary or exempted `TODO` must cite an issue using
  `TODO(#123):`.
<!-- TODO-check-enable -->
- **Prose and comment wrapping:** Wrap prose in code comments and Markdown
  files at 80 columns from the left margin when practical, including any
  comment prefix (`//`, `///`, `//!`). Do not wrap Markdown tables, ASCII
  diagrams, long URLs, code blocks, or trailing inline comments when wrapping
  would impair readability. Indent wrapped bullet continuation lines by two
  spaces, and put a blank line between paragraphs and after section headings.
- **Pre-commit validation:** Run `./ci/check_todo.sh` (along with any build or
  test checks applicable to the changed files) before finishing a task or
  committing.

## Required skills

The [`skills/`](skills/README.md) directory contains the skills that govern work
in this repository. Whenever your task involves an activity in the table below,
open and read the full `SKILL.md` for every listed skill (plus any
`references/` files it routes you to) before performing that work. Do not infer
a skill's rules from its name or summary. Skills compose: when more than one
applies, follow all of them.

| Activity | Required skills |
| :--- | :--- |
| Writing, revising, or reviewing any technical prose (documentation, code comments, commit messages, PR descriptions, or issue bodies) | [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Adding, revising, or reviewing explanatory inline (`//`) or documentation (`///`, `//!`) code comments | [`comment-guidelines`](skills/comment-guidelines/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Structuring commits, drafting or revising commit messages, rebasing or amending commits, or managing native GitHub stacks | [`commit-message`](skills/commit-message/SKILL.md), [`authorship-disclosure`](skills/authorship-disclosure/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Preparing or updating Git commits, pull request descriptions, or other externally visible prose | [`authorship-disclosure`](skills/authorship-disclosure/SKILL.md) |
| Designing, simplifying, or generalizing conceptual models, semantic interfaces, schemas, protocols, or instructions | [`model-refinement`](skills/model-refinement/SKILL.md) |
