---
name: source-control
description: >-
  Structure commits, format commit messages to Anneal repository conventions,
  and manage GHerrit stacked pull requests. Use when slicing changes into
  commits, drafting or revising commit messages, rebasing or amending commits,
  or pushing a branch in joshlf/anneal. Composes with commit-message and
  authorship-disclosure.
---

# Source control and commit conventions

Use this skill whenever organizing changes into commits, writing or revising
commit messages, rebasing or amending history, or synchronizing a branch in
`joshlf/anneal`.

This skill supplies Anneal's repository-specific commit structure, message
formatting, issue-linking, and [GHerrit](https://github.com/joshlf/gherrit)
stack rules. Combine it with:

- [`commit-message`](../commit-message/SKILL.md) for commit-message content
  and change-vs.-parent accuracy;
- [`reader-oriented-explanation`](../reader-oriented-explanation/SKILL.md) and
  [`williams-style`](../williams-style/SKILL.md) for explanation selection and
  prose style; and
- [`authorship-disclosure`](../authorship-disclosure/SKILL.md) for Git commit
  trailers.

## Structure and size commits for review

Arrange commits so a reviewer can read and verify each step independently:

1. **Separate incidental changes from behavioral changes.** Commit code
   movement, file renames, and formatting adjustments in their own commits
   rather than mixing them with functional or behavioral changes.
2. **Keep each commit focused.** Each commit should perform one logical change,
   such as adding a feature, fixing a bug, or refactoring a component.
3. **Size commits thoughtfully.** Split overly large or multi-part changes into
   logical commits, but avoid fragmenting a change so finely that reviewers
   must hold several commits in working memory to understand how the pieces fit
   together.

## Format commit messages to repository conventions

Commit messages must be concise and self-contained. Explain the rationale and
necessary context in the commit message itself rather than relying on an issue
link to supply the explanation; Git history is more durable than issue-tracker
history. Avoid superfluous details and session narrative.

### Subject line and body layout

Follow these formatting rules:

1. **Subsystem prefix:** When a commit affects a specific subsystem, prefix the
   subject line with `[subsystem]` in square brackets, omitting any `anneal`
   prefix (for example, `[ci] Audit merge commits and simplify check_todo.sh`).
2. **Imperative, capitalized subject:** Write the subject in the imperative
   mood (`Add`, `Support`, `Fix`, `Remove`), capitalize the first word after
   any `[subsystem]` prefix, and do not end the subject line with a period.
3. **50-character subject target:** Keep the subject line within 50 characters
   when practical without truncating identifiers or obscuring the change.
4. **Blank line before the body:** Separate the subject line from the body with
   a blank line. Omit the body when the subject line is genuinely
   self-explanatory (such as fixing a typo).
5. **72-character body wrapping:** Wrap body prose at 72 columns, except for
   long URLs, code blocks, or machine-readable trailers. Use the body to
   explain *what* changed and *why*, not merely *how*.

### Issue references

Include relevant GitHub issue references (`#123`) so GitHub links the commit
and the issue:

- When a commit completely resolves an issue, put `Closes #123`, `Fixes #123`,
  or `Resolves #123` on its own line in the body or footer.
- When a commit advances an issue without resolving it, put
  `Makes progress on #123` on its own line.

### Prohibited references and task markers

Commit messages must never contain references to:

1. **Relative moments in time** (such as "currently", "today", "recently", or
   "soon").
2. **Individuals** (by name or handle, outside standard Git attribution
   trailers).
3. **Hosted code reviews or pull requests** (such as
   `https://github.com/joshlf/anneal/pull/...`). Refer to commits in this
   repository by their SHA-1 hash, and refer to commits in other repositories
   by their public commit URL (for example,
   `https://github.com/google/zerocopy/commit/789b3deb`).
4. **Other ephemeral entities** that may not make sense to arbitrary future
   readers.

<!-- TODO-check-disable -->
Do not include `TODO` markers (or their disable/enable directives) anywhere in
a commit message; `./ci/check_todo.sh` audits commit messages across
`origin/main..HEAD` and rejects them.
<!-- TODO-check-enable -->

## Maintain the GHerrit stack

This repository uses [GHerrit](https://github.com/joshlf/gherrit) to synchronize
a local stack of commits with chained Pull Requests on GitHub.

### Branch setup and hooks

1. Inspect the current branch and stack state before changing history.
2. In a new checkout or worktree, ensure GHerrit's Git hooks (`commit-msg`,
   `post-checkout`, and `pre-push`) are installed (`gherrit install`).
3. Work on a GHerrit-managed branch rather than directly on `main`. By default,
   local branches are configured as private stacks (`gherrit manage --private`),
   which sets loopback remotes (`pushRemote = .`) so `git push` synchronizes PR
   phantom branches and version tags to `origin` without pushing the local
   branch name itself. Use `gherrit manage --public` only when publishing the
   local branch ref is intended.

### Trailers across rebases and amendments

1. **Preserve `gherrit-pr-id`:** Each commit on a managed branch has a
   `gherrit-pr-id: G...` trailer that binds the commit to its Pull Request
   across rebases and amendments. Never remove or alter an existing commit's
   `gherrit-pr-id` when running `git commit --amend` or `git rebase -i`.
2. **Assign new IDs to new commits:** When adding a new commit or splitting a
   commit into a separate logical change, let the `commit-msg` hook generate a
   fresh `gherrit-pr-id` for the new commit.
3. **Maintain authorship disclosure:** Keep the required
   `Agent-authored-by: AI agent acting on <user>'s behalf` trailer (with
   `(content only)` or `(commit message only)` when applicable, per
   [`authorship-disclosure`](../authorship-disclosure/SKILL.md)) in the commit's
   final trailer block alongside `gherrit-pr-id`. Recompute the trailer
   qualifier when amending, rebasing, or squashing.

### Pushing and PR descriptions

Push only when authorized. On a managed branch, `git push` invokes GHerrit's
`pre-push` hook, which pushes each commit to its phantom branch (`G...`), tags
the patch version (`refs/tags/gherrit/<id>/v<N>`), creates or updates one Pull
Request per commit, and regenerates PR descriptions from commit messages.

Do not manually edit GHerrit-managed PR descriptions on GitHub; let GHerrit own
the PR body. Because GHerrit populates each PR description directly from the
commit message (including its `Agent-authored-by` trailer), the commit's own
[`authorship-disclosure`](../authorship-disclosure/SKILL.md) trailer is
sufficient—do not add a separate prose disclosure notice to the PR body.
