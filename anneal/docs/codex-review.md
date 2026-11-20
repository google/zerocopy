<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Codex review policy and diagnostics

Anneal uses Codex review alongside local `change-review`, `trust-review`, CI,
and human review. Until [#236](https://github.com/joshlf/anneal/issues/236) is
resolved, Codex review is enforced by the manual merge gates below rather than
by a GitHub ruleset.

## Merge gates

Do not merge a pull request—and never use admin-bypass merges such as
`gh pr merge --admin`—until all five gates below pass on the exact final
`(target_base, head)` with `merge_base == target_base` and full review history
preserved (for stacked PRs, land bottom-up so each PR meets Gate 4 on `main`
before merging). Re-confirm every affected gate after any code, history, or
base edit:

1. **Gate 1 — Local review and receipt:** Local
   [`change-review`](../skills/change-review/SKILL.md) and
   [`trust-review`](../skills/trust-review/SKILL.md) have converged on the
   final `(target_base, head)`, every open trust question is resolved by
   evidence or explicit human maintainer disposition, no confirmed in-scope
   defect remains unresolved, the PR description opens with an accurate `Human
   review surface` block, and the PR author or acting agent has posted a Review
   Receipt comment covering the exact final `head` SHA.
2. **Gate 2 — Genuine Codex approval:** An authentic
   `chatgpt-codex-connector[bot]` review summary covers the current PR head and
   comparison base on GitHub with no unresolved Codex findings. Resolving
   review threads never satisfies Gate 2 without addressing the underlying
   finding and obtaining fresh Codex approval, and a green `codex-review.yml`
   diagnostic workflow run is never Codex approval. Because GitHub Codex
   defaults to flagging P0 and P1 issues (per the
   [Codex GitHub integration docs][codex-github]; re-verify periodically if
   provider behavior changes), Gate 1 owns open trust questions and
   lower-severity defects. If a PR added or modified an unauthorized nested
   `AGENTS.md` or any `AGENTS.override.md` that tainted Codex's review, remove
   it and require a fresh Codex review; when a PR edits root policy files
   (prefer dedicated policy-only PRs so Codex does not review product code
   under modified rules), policy-stability verification against the base rules
   comes from Gate 1 (local review against `<target_base>`) and Gate 5, not
   Gate 2 alone. If a Codex finding is demonstrably refuted by falsifiable
   evidence (for example requesting a TCB-violating edit), when authorized
   reply inline with the verification evidence and request a fresh Codex
   review, escalating to a human maintainer if the hosted reviewer remains
   stuck; an acting agent never waives Gate 2 or declares Gate 2 passed without
   genuine Codex approval.
3. **Gate 3 — Green required CI:** All required GitHub Actions checks pass on
   GitHub's current pull-request test-merge commit for the exact final
   `(target_base, head)` (reported on `head` by `pull_request`-triggered
   workflows), or on the merge queue's `merge_group` commit when merging via
   GitHub's merge queue.
4. **Gate 4 — Bottom-of-stack ordering:** For stacked PRs, every lower PR in
   the stack has merged and this PR is rebased onto `main` so
   `merge_base == target_base` before merging or entering GitHub's merge queue
   (`merge_group`).
5. **Gate 5 — Human approval:** An independent human maintainer account (never
   a bot or acting agent) has approved the pull request on GitHub, confirming
   every item listed in the `Human review surface` block (defined in
   [`AGENTS.md`](../AGENTS.md#code-review-rules), including stated specs and
   every definition their meaning transitively depends on, plus any editor or
   agent config or intentional policy relaxation). An approval holds across a
   pure rebase only if no subsequent push changes this PR's own Human review
   surface, no rebased-over commit modifies a definition in a stated spec's
   transitive dependency closure (verified via `git range-diff` and inspecting
   touched dependencies), and no subsequent edit modifies the PR description's
   `Human review surface` block or relevant commit bodies. Verify that the
   approval's timestamp is newer than both the last push affecting those
   surfaces and the last edit to the `Human review surface` block (via GitHub's
   PR description edit history); any later change requires fresh human
   maintainer approval. Because agents may act under credentials matching a
   human account, agents must never self-approve pull requests or author, edit,
   or simulate maintainer dispositions.

## Hosted reviewers and skill boundaries

Hosted reviewers follow the [Code Review Rules](../AGENTS.md#code-review-rules)
(mirrored verbatim in [`.gemini/styleguide.md`](../.gemini/styleguide.md)) and
report within host output and severity limits per
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

While [#236](https://github.com/joshlf/anneal/issues/236) remains open:

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
gh workflow run codex-review.yml --repo joshlf/anneal --ref main
gh run list --repo joshlf/anneal --workflow codex-review.yml
```

For local read-only diagnosis (without write-effect flags):

```sh
GH_TOKEN="$(gh auth token)" python3 -I -B ci/codex_review.py \
  --repository joshlf/anneal
```

The evaluator reads live PRs, summaries, historical deletion records, and merge
queue state, then prints proposed verdicts. Its freshness rules can reject a
completed review when Codex edits an older summary or supplies only a prose
receipt; deletion records are no longer updated automatically. Treat its output
strictly as diagnostic evidence and inspect Codex's actual approval before
making a manual merge decision.

## Preserve the evaluator and re-enablement criteria

The [adapter](../ci/codex_review.py) and its tests remain available for
[#236](https://github.com/joshlf/anneal/issues/236) as **research material,
rather than a selected design for restoring enforcement**. Run the simulated
tests locally with:

```sh
python3 -B -m unittest discover -s ci -p 'test_codex_review.py' -v
```

These tests use fake API data, make no GitHub changes, and include a deployment
assertion requiring `.github/codex-review-ruleset.json` to remain disabled.
Passing these tests does **not** validate the live provider's association
between a review and its head/base comparison.

Before re-enabling ruleset `26810364` and automated status publication:

1. Address [#236](https://github.com/joshlf/anneal/issues/236) and exercise
   both **acceptance and refusal** against the live GitHub integration before
   enabling enforcement.
2. Deploy and validate the evaluator and provide a **recovery path that
   preserves review history** rather than deleting prior reviews.
3. Reconcile the live GitHub ruleset with the checked-in ruleset template (and
   update the disabled-template deployment test deliberately).

Re-enabling enforcement without those checks would restore the unresolved
failure modes.

[codex-github]: https://developers.openai.com/codex/integrations/github/
