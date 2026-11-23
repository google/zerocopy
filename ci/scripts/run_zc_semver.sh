#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail

: "${PIN_RUST_TOOLCHAINS__STABLE:?}" "${PIN_SEMVER_BASELINE__SKIP:?}" "${SEMVER_SCOPE:?}"

if [[ "$PIN_SEMVER_BASELINE__SKIP" == "true" ]]; then
  echo "Skipping cargo-semver-checks per ci/pins/semver-baseline.toml (skip = \"true\")."
  exit 0
fi

case "$SEMVER_SCOPE" in
  pr)
    TARGETS=(
      i686-unknown-linux-gnu
      x86_64-unknown-linux-gnu
      x86_64-pc-windows-msvc
    )
    ;;
  extra)
    TARGETS=(
      arm-unknown-linux-gnueabi
      aarch64-unknown-linux-gnu
      powerpc-unknown-linux-gnu
      powerpc64-unknown-linux-gnu
      riscv64gc-unknown-linux-gnu
      s390x-unknown-linux-gnu
    )
    ;;
  *)
    echo "error: unknown SEMVER_SCOPE: $SEMVER_SCOPE" >&2
    exit 1
    ;;
esac

export CARGO_NET_OFFLINE=true
SCRATCH_ROOT="${HOME:-/scratch}"

for target in "${TARGETS[@]}"; do
  baseline_json="/opt/semver-baseline/rustdoc/${target}.json"
  if [[ ! -f "$baseline_json" ]]; then
    echo "error: missing pre-generated baseline rustdoc JSON: $baseline_json" >&2
    exit 1
  fi
  target_scratch="${SCRATCH_ROOT}/semver-target/${target}"
  rm -rf "$target_scratch"
  mkdir -p "$target_scratch"

  RUSTC_BOOTSTRAP=1 \
  RUSTDOCFLAGS="-Z unstable-options --output-format json -Dwarnings" \
  CARGO_TARGET_DIR="$target_scratch" \
  cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" doc \
    --locked --offline \
    --manifest-path Cargo.toml \
    --package zerocopy \
    --no-deps \
    --no-default-features \
    --features __internal_use_only_features_that_work_on_stable \
    --target "$target"

  current_json="${target_scratch}/${target}/doc/zerocopy.json"
  if [[ ! -f "$current_json" ]]; then
    echo "error: expected current rustdoc JSON missing: $current_json" >&2
    exit 1
  fi

  cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" semver-checks check-release \
    --baseline-rustdoc "$baseline_json" \
    --current-rustdoc "$current_json"

  rm -rf "$target_scratch"
done
