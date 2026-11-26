<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# CI Architecture (`ci-core`)

`google/zerocopy` runs its CI check graph through the externalized, SHA-pinned
`ci-core` engine configured by [`checks.toml`](checks.toml).

## Layout

- [`checks.toml`](checks.toml): Declarative repository identity, consumer TCB
  rules, data pins, content-addressed OCI toolchain images, cache slots, and
  check matrix definitions.
- `ci/pins/`: Flat TOML data-pin manifests (`rust-toolchains.toml`,
  `kani-pin.toml`, `semver-baseline.toml`, `layout-seed.toml`) kept in lockstep
  with `zerocopy/Cargo.toml` and `ci/docker/zc-*.Dockerfile` by
  [`ci/scripts/check_toolchains_sync.py`](scripts/check_toolchains_sync.py).
- `ci/docker/`: Digest-pinned OCI Dockerfiles (`zc-stable-msrv`, `zc-build-rs`
  for `modern` and `legacy` feature-detection tiers, `zc-nightly`, `zc-kani`,
  `anneal-tc`, `anneal-arm64`) built into content-addressed GHCR images.
- `ci/scripts/` and `anneal/ci/run_anneal_check.sh`: Offline check adapters that
  execute over read-only `/work` mounts with writable `/scratch` and `/outputs`.
- `.github/workflows/ci-core-pr.yml` and
  `.github/workflows/ci-core-trusted.yml`: Thin, SHA-pinned caller workflows
  that report the required `ci-core / gate` check, paired with
  `.github/workflows/ci-review-signal.yml`,
  `.github/workflows/ci-review-rerun.yml`, and `.github/CODEOWNERS`.
- `.github/workflows/anneal-pr-hygiene.yml`: Reports the other required
  check, `PR hygiene`, which runs `anneal/ci/check_pr_hygiene.py` over a pull
  request's commits and diff. Its findings are soft-blocking: a
  `Skip-pr-hygiene:` trailer on the PR's `HEAD` commit can waive named checks
  (see [`anneal/docs/scaffolding.md`](../anneal/docs/scaffolding.md)).

`[tcb] non_tcb_workflows` is empty, so `ci-core` treats every workflow as
trusted configuration. `run_anneal_check.sh` and the `ci/scripts/run_*.sh`
entrypoints cap their checks with `timeout`.

## Rulesets

After the cutover below, two rulesets protect `main`:

- **Required checks** (no bypass actors): requires `ci-core / gate` and
  `PR hygiene` from GitHub Actions, linear history, resolved review threads,
  and squash merges through the merge queue, which allows checks 240 minutes.
- **Human review** (repository administrators exempt): requires one
  approval, including `CODEOWNERS` review, and dismisses stale approvals on
  push, so an approval never carries over to a later commit, such as one
  that replaces a caller workflow.

The tag ruleset (`26220859`) protects `refs/tags/v*` from deletion and
force-pushes; the cutover extends it to `refs/tags/anneal-*`. The maintenance
ruleset (`26220870`) covers `v*.*.x` branches, which still run the legacy
`ci.yml` and its `All checks succeeded` check. A `v0.9.x` or later
maintenance branch cut from a `main` without the legacy `ci.yml` needs its
own ruleset requiring `ci-core / gate` and `PR hygiene` instead.

The cutover from ruleset `26220845` to the two `main` rulesets runs in this
order, so that no queued PR waits on a check that `main` cannot yet produce:

1. Get a co-owner's GitHub approval on the cutover PR's final head SHA, so
   that both of its checks pass. `ci-core` reads `allow_owner_self_approval`
   from `main`, so the PR that enables it cannot rely on it.
2. Replace `26220845` with both rulesets, requiring only `ci-core / gate`,
   expand the tag ruleset, and enqueue the cutover PR.
3. Once it lands, add `PR hygiene` to the required checks.
4. Use the next owner-authored TCB PR to confirm that `/ci-core approve`
   reruns the gate and the PR merges.

## Local verification and reproduction

Validate `ci/checks.toml`, `.github/CODEOWNERS`, and all sibling workflows
statically:

```bash
ci-core verify-repo --config ci/checks.toml
```

Reproduce any individual check inside the exact same hermetic `Container` or
`NestedBwrap` sandbox used in CI (with `docker` or rootless `podman`):

```bash
ci-core run-local --config ci/checks.toml --check meta-actions
ci-core run-local --config ci/checks.toml --check anneal-flake-eval
```
