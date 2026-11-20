---
name: source-control
description: >-
  Structure commits and format commit messages to Anneal repository
  conventions. Use when slicing changes into commits, drafting or revising
  commit messages, rebasing or amending commits, or managing branches and pull
  requests in joshlf/anneal. Composes with commit-message and
  authorship-disclosure.
---

# Source control and commit conventions

Use this skill whenever organizing changes into commits, writing or revising
commit messages, rebasing or amending history, or managing branches and pull
requests in `joshlf/anneal`.

This skill supplies Anneal's repository-specific commit structure, message
formatting, issue-linking, and pull request conventions. Combine it with:

- [`commit-message`](../commit-message/SKILL.md) for commit-message content
  and change-vs.-parent accuracy;
- [`reader-oriented-explanation`](../reader-oriented-explanation/SKILL.md) and
  [`williams-style`](../williams-style/SKILL.md) for explanation selection and
  prose style; and
- [`authorship-disclosure`](../authorship-disclosure/SKILL.md) for Git commit
  trailers and pull request descriptions.

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

## Branches and pull requests

Inspect the current branch before changing history; whether to create a
separate branch or work on the current branch is a case-by-case decision.

Push branches (`git push`, passing `--set-upstream origin <branch>` when no
upstream is configured) or open, update, merge, or close pull requests (`gh pr`
or `gh stack`; see `gh pr --help` and `gh stack --help`) only when authorized.
For multi-part changes on same-repository branches, consider organizing pull
requests as a stack with [`gh stack`](https://gh.io/stacks) (see the
[`gh-stack` skill](https://github.com/github/gh-stack/tree/main/skills/gh-stack))
when it aids review, or use a single pull request when that is simpler—leave
the choice to the developer. Because `gh stack submit --auto` publishes pull
requests before custom bodies can be supplied, preserve
[`authorship-disclosure`](../authorship-disclosure/SKILL.md) on initial
publication by pushing the stack branches (`gh stack push`, or
`git push --set-upstream origin <branch>` for each branch), creating each pull
request with its prepared body (`gh pr create`, passing
`--base <previous-branch>` above the first layer), and linking the stack in
bottom-to-top order (`gh stack link <branch-or-pr>...`, or `gh stack sync` when
the stack is already tracked locally).
