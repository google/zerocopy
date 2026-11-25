<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# CI Architecture (`ci-core`)

`google/zerocopy` runs its CI check graph through the externalized, SHA-pinned
`ci-core` engine configured by [`checks.toml`](checks.toml). Pull-request runs
(`ci-core-pr.yml`) use shadow mode (`shadow_mode: true`): they verify the plan
and reuse receipts without executing check shards. Trusted runs
(`ci-core-trusted.yml`, on `merge_group` and pushes to `main`) execute the
affected checks and evaluate `ci-core / gate` for real. Until cutover,
`ci-core / gate` is not a required status check; the legacy `ci.yml` and
`anneal.yml` workflows remain the required checks.

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
  whose gate check is `ci-core / gate` (not required until cutover), paired
  with `.github/workflows/ci-review-signal.yml`,
  `.github/workflows/ci-review-rerun.yml`, and `.github/CODEOWNERS`.

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
