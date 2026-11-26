<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `ci-core` review rules

Zerocopy runs its declarative `ci-core` check graph as its required CI. These
surfaces trigger Pass 2:

- the caller workflows `ci-core-pr.yml`, `ci-core-trusted.yml`,
  `ci-review-signal.yml`, and `ci-review-rerun.yml` in Zerocopy's root
  `.github/workflows/`;
- `anneal-pr-hygiene.yml`, which reports the other required check;
- repository-root `ci/checks.toml`, which those workflows load as trusted
  config; and
- repository-root `.github/CODEOWNERS`, which `ci-core` enforces.

Apply the rules below in addition to the
[Code Review Rules](../../../AGENTS.md#code-review-rules) and
[Pass 2](../SKILL.md#pass-2-tcb-and-ci-surfaces). They relax no base rule
except the per-workflow `permissions:` scopes listed under
[Least privilege](#least-privilege), which apply only to these four callers.

## Keep `ci-core / gate` and `PR hygiene` required

- The `main` ruleset requires exactly two checks: `ci-core / gate`
  (`[tcb.caller] gate_check_name`), which replaces `all-jobs-succeed`, and
  `PR hygiene` from `anneal-pr-hygiene.yml`. Reject dropping either.
- `ci-core` replaces the retired `anneal.yml` -> `anneal-current.yml`.
  Keep requiring every base CI gate that workflow ran. `check_pr_hygiene.py`
  reads Git history, which `ci-core` checks lack, so `PR hygiene` runs it.
- `ci-core-pr.yml` passes `shadow_mode: false`, so pull-request runs execute
  check shards. Reject re-enabling shadow mode, and never accept a `ci-core`
  change as grounds to drop or weaken a base CI gate.
- `PR hygiene` is soft-blocking: a `Skip-pr-hygiene:` trailer on the PR's
  `HEAD` commit may waive named checks, as
  [`docs/scaffolding.md`](../../../docs/scaffolding.md) describes. Report
  each waiver so the Gate 5 approver can accept it, and reject one that hides
  a trust or soundness defect. The tree invariants `agents-budget` and
  `code-review-rules-parity` run in `ci-core`'s `skills-check` and are never
  waivable.
- `anneal-pr-hygiene.yml` holds only `contents: read` and runs
  `check_pr_hygiene.py` on every `opened`, `synchronize`, `reopened`, and
  `edited` pull-request event; only `merge_group` runs skip checkout and exit
  0. Reject any fast path that reports success for a pull-request event
  without running the check.

## SHA pinning

- Each caller pins its `joshlf/ci-core` reusable workflow to a full 40-char
  commit SHA. `[repo] trusted_engine_shas` in `ci/checks.toml` lists the
  engine workflow SHAs whose signed claims, images, and caches `ci-core`
  accepts; keep it in lockstep with the callers' pin.
- On every pin or `trusted_engine_shas` change, audit the engine source at the
  new SHA, the release-archive SHA-256 digests (`CORE_ARCHIVE_SHA256_*`) that
  the reusable workflows verify before running the engine binary, and the
  provenance of those archives.

## Least privilege

Every caller sets workflow-level `permissions: {}` and grants only these
scopes to its single job:

| Workflow | Triggers | Job scopes |
| :--- | :--- | :--- |
| `ci-core-pr.yml` | `pull_request` | `actions`, `contents`, `packages`, `pull-requests`: `read` |
| `ci-core-trusted.yml` | `merge_group`, `push` to `main` | `actions`, `contents`, `pull-requests`: `read`; `packages`, `id-token`: `write` |
| `ci-review-signal.yml` | `pull_request_review` | `{}` |
| `ci-review-rerun.yml` | `workflow_run` of `CI Review Signal` | `actions`: `write`; `contents`, `pull-requests`: `read` |

- The pinned reusable workflows narrow these scopes per job. In
  `ci-core-trusted.yml`, only the `publish` job holds `packages: write` and
  `id-token: write`; `plan`, `build-images`, `execute`, and `gate` stay
  read-only. No reusable job uses `actions/checkout`.
- `ci-review-signal.yml` runs no code beyond `true` and uploads no artifacts.
  `ci-review-rerun.yml` consumes no artifacts and passes `workflow_run` fields
  to the engine only through `env:`, never by interpolation into `run:`.
- These scopes are the only exceptions, for these four callers, to the base
  rules that keep `permissions: contents: read` on PR- and comment-triggered
  jobs and reserve write or OIDC scopes for release jobs in `release.yml`.
  Reject any broader or additional scope, and any job that runs PR-controlled
  code while holding a write or OIDC token.

## Gate integrity and `CODEOWNERS`

- `ci-core verify-repo` rejects sibling jobs and caller-job names that could
  spoof `ci-core / gate`. Never add a job whose check name could collide with
  it.
- `ci-core` requires an unoverridden recursive `/.github/**` rule owned by
  `[tcb.caller] codeowners` and checks that those owners dominate consumer-TCB
  paths under last-match-wins. Keep `.github/CODEOWNERS` rules free of
  backslashes, negations, and character classes, and never narrow owner
  coverage of Anneal-trusted paths.
- `[tcb] non_tcb_workflows` is empty, so `ci-core` treats every workflow as
  TCB. Reject any entry: `ci-core` cannot prove that a workflow reads no
  secrets, uses no OIDC token, and spoofs no required check name. Reject
  additions to `non_tcb_subtrees` that would cover an Anneal-trusted surface.

## Sandboxing and environment

- Anneal checks in `ci/checks.toml` run under `sandbox = "nested_bwrap"`
  (`NestedBwrap`), except `anneal-clippy`, which uses the default `Container`
  sandbox. Reject any change that downgrades them.
- `ci-core` starts every check from a cleared environment and drops all
  `GITHUB_*`, `ACTIONS_*`, and `RUNNER_*` keys from image and check `env`, so
  check commands never receive `ACTIONS_CACHE_URL`, `ACTIONS_RESULTS_URL`,
  `ACTIONS_RUNTIME_TOKEN`, or `GITHUB_TOKEN`. Keep that guarantee.

## Attested `miri-v1` cache

- `[caches.miri-v1]` is a `public_cas` slot mounted at `/ci-cache/miri`,
  outside the checkout. Its key binds the `anneal-tc` image manifest digest
  and `flake.nix`, `flake.lock`, `trusted/lean/lean-toolchain`,
  `trusted/lean/foundation-lock.json`, and
  `vendor/lean-miri/UPSTREAM_PIN.json`.
- Only the checkout-free `publish` job of `ci-core-trusted.yml` (on
  `merge_group` and `main` `push`) can push and keyless-sign cache entries.
  Pull-request runs hold no `packages: write`.
- `anneal-audit` still verifies every restored file against
  `UPSTREAM_PIN.json` and replays the vendored closure in the standalone
  kernel on every run, as described in
  [`docs/trust-model.md`](../../../docs/trust-model.md). Reject removing key
  inputs, switching the slot to cross-image scope, or granting cache writes to
  PR-triggered runs.
