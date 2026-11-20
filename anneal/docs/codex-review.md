<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Codex review policy and diagnostics

Codex approval is checked by the maintainer or acting agent while automated
Codex enforcement is disabled. [Issue
#236](https://github.com/joshlf/anneal/issues/236) tracks restoring reliable
enforcement for the actual PR comparison.

Before merging a PR, confirm all of the following:

- Codex has genuinely approved the current change, with no outstanding findings.
- The user has reacted with 👍 to the PR description.
- Required build and test CI is green for the current head.
- The PR is at the bottom of its stack, with its prerequisites already merged.

Inspect the actual review, user approval, CI results, and stack position. A
green run of the diagnostics workflow reports that the evaluator ran; it does
not approve a merge. Keep prior reviews intact rather than deleting review
history to force a new summary.

## Disable automated enforcement

The [workflow](../.github/workflows/codex-review.yml) runs only on manual
dispatch. It checks out the adapter from `main`, uses read-only permissions, and
runs the adapter's default diagnostic mode. It does not publish **Codex review**
statuses or record summary deletions. PRs, comments, merge groups, and pushes no
longer trigger it automatically.

The checked-in [ruleset template](../.github/codex-review-ruleset.json) has
`enforcement` set to `disabled`. Its original status context and GitHub Actions
App binding remain available for future work.

Changing Git files does not change GitHub's live rulesets. Deployment also
requires disabling the existing **Main — Codex review** ruleset, ID `26810364`.
Set only that ruleset's enforcement to `disabled`, then confirm the live result.
Leave rulesets `26220506` and `26637514` and their CI and human-review
protections unchanged. Deactivating the Codex rule does not waive the manual
merge policy above.

## Run read-only diagnostics

Once the workflow is on `main`, it can be dispatched manually:

```sh
gh workflow run codex-review.yml --repo joshlf/anneal --ref main
gh run list --repo joshlf/anneal --workflow codex-review.yml
```

For local diagnosis, run the default mode without either write-effect flag:

```sh
GH_TOKEN="$(gh auth token)" python3 -I -B ci/codex_review.py \
  --repository joshlf/anneal
```

The evaluator reads live PRs, summaries, historical deletion records, and merge
queue information, then prints proposed verdicts. Its existing freshness rules
can reject a completed review when Codex edits an older summary or supplies only
a prose receipt. Deletion records are no longer updated automatically. Treat the
output as diagnostic evidence, and inspect Codex's actual approval of the
current change before making the manual merge decision.

## Preserve the evaluator for follow-up work

The [adapter](../ci/codex_review.py) and its regression tests remain available
for issue #236. They preserve the former gate's strict summary authentication,
exact-head checks, base-change freshness policy, shared-head handling, deletion
records, merge queue handling, and publication logic. That retained behavior is
research material, rather than a selected design for restoring enforcement.

Run the simulated tests locally with:

```sh
python3 -B -m unittest discover -s ci -p 'test_codex_review.py' -v
```

The tests use fake API data and make no GitHub changes. They cover accepted and
rejected review evidence, concurrent changes, API failures, and simulated status
publication. The deployment assertion requires the retained ruleset template to
remain disabled. Passing these tests does not validate the live provider's
association between a review and its head/base comparison.

Before re-enabling enforcement, address issue #236, exercise acceptance and
refusal against the live integration, deploy and validate the evaluator, and
reconcile the live rules with the checked-in configuration. Provide a recovery
path that preserves review history. Re-enabling the former required status
without those checks would restore the unresolved failure modes.
