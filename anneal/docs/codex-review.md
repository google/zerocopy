<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Gate 2 review policy and diagnostics

Anneal pairs local `change-review`, `trust-review`, CI, and human review with
an independent cross-family automated review (**Gate 2**). Gate 2 accepts
either an independent cross-family `COMMENT` review carrying a structured
`anneal-gate2-review:v1` footer or, for backwards compatibility, a healthy
`chatgpt-codex-connector[bot]` review summary. Until
[#4013](https://github.com/google/zerocopy/issues/4013) is resolved, Gate 2 is
enforced by the manual merge gates below rather than by a GitHub ruleset.

## Merge gates

Do not merge a pull request—and never use admin-bypass merges such as
`gh pr merge --admin`—until all five gates below pass for the PR's current
**identity** with full review history preserved (for stacked PRs, land
bottom-up so each PR meets Gate 4 on `main` before merging). A PR's identity
is the content it would land:

- For a PR with one commit on top of its target base, the identity is the
  triple (tree of the commit's parent, tree of the commit, full commit
  message).
- For a PR with several commits, the identity is the exact
  `(target_base, head)` SHA pair.

In both cases `merge_base == target_base`: the PR's commits sit directly on
the head of its target base, which is `main` for a lone PR or the bottom PR of
a stack, and the head of the PR directly below it otherwise.

Review evidence recorded on this PR for one identity (review receipts, Gate 2
reviews, and human approvals) remains valid for every later head of the same
PR with that identity, however that head was produced, and for no other,
subject to the Gate 5 rules for the Review Receipt comment's `Human review
surface` block. Evidence never transfers
between pull requests. In particular, when a lower stack PR is squash-merged
and the PR above it is rebased onto that squash commit (whose tree equals the
lower PR's reviewed head tree), the upper PR's identity—and its review
evidence—is unchanged. The identity omits author and committer metadata, and
GitHub reports CI per commit SHA, so every new head still needs its own
SHA-bound deterministic preflight (including the authorship and trailer checks
in [`AGENTS.md`](../AGENTS.md#standing-rules)) and its own Gate 3 CI. Any
change to either tree or to the commit message changes a one-commit PR's
identity, and any change of SHA changes a multi-commit PR's identity;
re-confirm every affected gate whenever the identity changes:

1. **Gate 1 — Local review and receipt:** Local
   [`change-review`](../skills/change-review/SKILL.md) and
   [`trust-review`](../skills/trust-review/SKILL.md) have converged on the
   current identity, every open trust question is resolved by evidence or
   explicit human maintainer disposition, no confirmed in-scope defect remains
   unresolved, and the PR author or acting agent has posted a Review Receipt
   comment naming a reviewed `head` SHA with the current identity that includes
   an accurate `Human review surface` block.
2. **Gate 2 — Independent cross-family review and finding dispositions:** At
   least one complete automated Gate 2 review posted on this PR covers the
   current identity, and no Gate 2 review requested on this PR, for any
   identity, may still be running at merge time. A Gate 2 review is valid only
   when produced via one of two mechanisms:
   - **Structured cross-family `COMMENT` review (`anneal-gate2-review:v1`):**
     A PR review submitted with `event: "COMMENT"` (never `APPROVE`, keeping
     Gate 5 human approval strictly separate) by an authorized reviewer
     (repository owner, org member, or collaborator, or an explicitly
     configured review bot identity) using an automated model family strictly
     distinct from the PR's authoring model family
     (`reviewer_family != author_family`), executed from a clean `<target_base>`
     checkout or neutral directory without author or Gate 1 conversation
     history. When Gate 1 already used a distinct model family from the author,
     prefer a third distinct model family for Gate 2 when available; otherwise,
     pair Gate 2 with a distinct model family from the author in a fresh,
     unprimed harness. Its body must contain exactly one machine-readable
     footer:

     ```html
     <!-- anneal-gate2-review:v1 {"base_sha":"<40-hex>","head_sha":"<40-hex>","tree_sha":"<40-hex>","reviewer_family":"<family>","author_family":"<family|human>","verdict":"clean|findings|incomplete","findings":[{"severity":"P0|P1|P2|P3","path":"<path|null>","line":1,"summary":"<text>"}]} -->
     ```

     Here `author_family` names the authoring model family (or `"human"` for a
     wholly human-authored PR), `reviewer_family` names an automated model
     family distinct from `author_family` (never `"human"` or a placeholder; or
     `"multi"` when `panel_seats[]` is present with at least one completed
     cross-family seat), `verdict` is `"clean"` (`findings: []`), `"findings"`
     (non-empty `findings`), or `"incomplete"`, and optional `parent_tree`,
     `commit_msg_sha256`, `reviewed_at`, `round`, `risk_tier`, `merge_base`,
     `identity_key`, `panel_seats[]`, `prior_findings_status[]`, and `coverage`
     (plus per-finding `fingerprint`, `surface`, `consensus_count`,
     `raised_by[]`, and `repro_status`) may carry one-commit identity or
     multi-seat diagnostic metadata. Gate 2 provides the cold cross-family
     review and falsification pass after Gate 1's pre-push convergence.
   - **Legacy Codex summary (`codex-review-state:v1`):** For backwards
     compatibility, a complete code review by an authentic
     `chatgpt-codex-connector[bot]` covering the current identity.

   An aborted run, a request answered with an error, a `verdict: "incomplete"`
   run, or a run that has not completed is never a passing Gate 2 review. Every
   finding that a Gate 2 reviewer posts on this PR, for any identity and
   including findings from incomplete or errored runs, is resolved in exactly
   one of two ways:
   - **Fixed:** after the finding, the surface it concerns changes (the PR's
     tree; its commit message; or, for a finding about something outside the
     identity, such as the PR description or Review Receipt comment, that
     surface), and Gate 1 confirms
     on the PR's current state that the fix is still present and still
     addresses the finding, mapping it to the fixing hunk or edit in the
     Review Receipt. Any later edit to that surface reopens the finding until
     Gate 1 confirms the fix again. A finding anchored to code or describing
     the tree's behavior concerns the tree, and an ambiguous finding counts as
     a tree finding. A finding about the tree or commit message that was
     raised on the current identity cannot be fixed without a new identity.
   - **Dispositioned:** the finding appears in a `Gate 2 finding dispositions`
     (or legacy `Codex finding dispositions`) list inside the Review Receipt
     comment's `Human review surface` block, with a proposed disposition and
     its evidence, and the maintainer's Gate 5 approval, newer than that
     comment's creation and last edit, accepts it. A disposition may
     refute a finding with falsifiable evidence or defer an out-of-scope
     finding (handling pre-existing hazards as
     [`trust-review`](../skills/trust-review/SKILL.md#report-findings-and-pre-existing-hazards)
     requires); a confirmed in-scope trust or soundness defect must be fixed,
     never deferred.

   Automated review is nondeterministic: repeated reviews of identical content
   regularly raise new findings, so a later review's silence about a finding
   never resolves it. Requesting several reviews of one identity, including in
   parallel, is permitted and only adds findings to resolve. Resolving a review
   thread never resolves a finding by itself, and a green `codex-review.yml`
   diagnostic workflow run is never a Gate 2 review. When a hosted provider
   filters output by severity (for example, GitHub Codex defaulting to P0 and
   P1 issues per the [Codex GitHub integration docs][codex-github]; re-verify
   periodically if provider behavior changes), Gate 1 owns open trust questions
   and lower-severity defects. If a PR added or modified an unauthorized nested
   `AGENTS.md` or any `AGENTS.override.md` that tainted an automated review,
   remove it and require a new complete Gate 2 review of the resulting
   identity; when a PR edits root policy files (prefer dedicated policy-only
   PRs so automated reviewers do not evaluate product code under modified
   rules), policy-stability verification against the base rules comes from
   Gate 1 (local review against `<target_base>`) and Gate 5, not Gate 2 alone.
   An acting agent may propose dispositions, but never waives Gate 2, declares
   it passed with an unresolved finding, or authors, edits, or simulates the
   maintainer's acceptance.
3. **Gate 3 — Green required CI:** All required GitHub Actions checks pass on
   GitHub's current pull-request test-merge commit for the exact final
   `(target_base, head)` (reported on `head` by `pull_request`-triggered
   workflows), and—for any Anneal-relevant merge—either on the merge queue's
   `merge_group` commit (always full-strength) or on a `pull_request` run with
   the `run-ci` label attached (without `run-ci`, draft PRs skip
   `current_anneal` including `static-checks` and skip heavy `ci.yml` jobs,
   while ready Anneal-relevant `pull_request` runs execute only
   `static-checks`). GitHub reports checks per commit SHA, so a rewrite that
   preserves the identity still needs green checks on the new `head`.
4. **Gate 4 — Bottom-of-stack ordering:** For stacked PRs, every lower PR in
   the stack has merged and this PR is rebased onto `main` so
   `merge_base == target_base` before merging or entering GitHub's merge queue
   (`merge_group`).
5. **Gate 5 — Human approval:** An independent human maintainer account (never
   a bot or acting agent) has approved the pull request on GitHub, confirming
   every item listed in the Review Receipt comment's `Human review surface`
   block (defined in [`AGENTS.md`](../AGENTS.md#code-review-rules), including
   stated specs and every definition their meaning transitively depends on,
   plus any editor or agent config, intentional policy relaxation, or proposed
   Gate 2 finding disposition). An approval holds across a pure rebase only if
   no subsequent push changes this PR's own Human review surface, no
   rebased-over commit modifies a definition in a stated spec's transitive
   dependency closure (verified via `git range-diff` and inspecting touched
   dependencies), and no subsequent Review Receipt comment or edit modifies the
   `Human review surface` block or relevant commit bodies. An unchanged
   identity satisfies the first two conditions, and a push that leaves the
   identity unchanged affects none of those surfaces; the `Human review
   surface` condition still applies. Verify that the approval's timestamp is
   newer than both the last push affecting those surfaces and the latest Review
   Receipt comment's creation and last edit (via GitHub's comment timestamps
   and edit history); any later change requires fresh human maintainer
   approval. Because agents may act under credentials matching a human account,
   agents must never self-approve pull requests or author, edit, or simulate
   maintainer dispositions or acceptance.

## Automated Gate 2 reviewers and skill boundaries

Automated Gate 2 reviewers follow the
[Code Review Rules](../AGENTS.md#code-review-rules) (mirrored verbatim in
[`.gemini/styleguide.md`](../.gemini/styleguide.md)) and report within host
output and severity limits per
[`change-review`](../skills/change-review/SKILL.md#report-within-the-hosts-constraints);
these instructions never create a setting for unlimited findings or override a
service limit. See
[`docs/review-policy-design.md`](review-policy-design.md#policy-ownership) for
file ownership across skills and docs.

## Live GitHub ruleset state and diagnostic workflow

The diagnostic [workflow](../.github/workflows/codex-review.yml) runs only on
manual dispatch: it checks out the adapter from `main`, uses read-only
permissions, runs default diagnostic mode, and neither publishes **Codex
review** statuses nor records summary deletions. PRs, comments, merge groups,
and pushes do not trigger it automatically.

While [#4013](https://github.com/google/zerocopy/issues/4013) remains open:

- Keep
  [`.github/codex-review-ruleset.json`](../.github/codex-review-ruleset.json)
  at `"enforcement": "disabled"` (retaining its original status context and
  GitHub Actions App binding for future work).
- Keep GitHub ruleset **Main — Codex review** (ID `26810364`) set to
  `disabled`.
- Leave rulesets `26220506` and `26637514`—and all CI and human-review branch
  protections—enabled and unchanged.

Changing Git files does not change GitHub's live rulesets. Disabling ruleset
`26810364` never waives the five merge gates above.

## Run read-only diagnostics

When authorized, the workflow can be dispatched manually on `main`:

```sh
gh workflow run codex-review.yml --repo google/zerocopy --ref main
gh run list --repo google/zerocopy --workflow codex-review.yml
```

For local read-only diagnosis (without write-effect flags):

```sh
GH_TOKEN="$(gh auth token)" python3 -I -B ci/codex_review.py \
  --repository google/zerocopy
```

The evaluator reads live PRs, PR reviews, summaries, commit trees, historical
deletion records, and merge queue state, then prints proposed verdicts. For
`anneal-gate2-review:v1` reviews, it validates `base_sha`, `head_sha`,
`tree_sha`, `reviewer_family != author_family`, `COMMENTED` state, and
`findings[]` fail-closed. For legacy `codex-review-state:v1` summaries, its
freshness rules still reject a completed review when Codex edits an older
summary or supplies only a prose receipt; deletion records are no longer updated
automatically. Treat diagnostic output as evidence and inspect actual Gate 2
reviews before making a manual merge decision.

## Preserve the evaluator and re-enablement criteria

The [adapter](../ci/codex_review.py) and its tests remain available for
[#4013](https://github.com/google/zerocopy/issues/4013) as **supporting
infrastructure for automated Gate 2 verification**. Run the simulated tests
locally with:

```sh
python3 -B -m unittest discover -s ci -p 'test_codex_review.py' -v
```

These tests use fake API data, make no GitHub changes, and include a deployment
assertion requiring `.github/codex-review-ruleset.json` to remain disabled.
Passing these tests does **not** by itself validate live GitHub ruleset
enforcement or a reviewer's model-family honesty without an authenticated bot
identity.

Before re-enabling ruleset `26810364` and automated status publication:

1. Address [#4013](https://github.com/google/zerocopy/issues/4013) (including
   authenticating a dedicated Gate 2 bot identity via `--reviewer-login` or
   bot-ID pinning if required) and exercise both **acceptance and refusal**
   against the live GitHub integration before enabling enforcement.
2. Deploy and validate the evaluator and provide a **recovery path that
   preserves review history** rather than deleting prior reviews.
3. Reconcile the live GitHub ruleset with the checked-in ruleset template (and
   update the disabled-template deployment test deliberately).

Re-enabling enforcement without those checks would restore the unresolved
failure modes.

[codex-github]: https://developers.openai.com/codex/integrations/github/
