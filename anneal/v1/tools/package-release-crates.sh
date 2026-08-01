#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Exercise the exact package boundary used by anneal-release.yml, including
# Cargo's verification build. Keep this order, cargo-anneal's exact exocrate
# dependency, and the workflow's release plan coordinated.

set -euo pipefail
cd "$(dirname "$0")/../../.."

temporary_root="$(mktemp -d)"
verification_target="$temporary_root/verification"
archive_target="$temporary_root/archive"
cleanup() {
  rm -rf -- "$temporary_root"
}
trap cleanup EXIT

CARGO_TARGET_DIR="$verification_target" cargo package --locked \
  --manifest-path exocrate/Cargo.toml \
  --registry crates-io

# exocrate may not exist in the registry yet. The patch is only a local
# packaging-time override; the normalized crate manifest retains the exact
# crates.io dependency declared in anneal/v1/Cargo.toml.
exocrate_path="$PWD/exocrate"
CARGO_TARGET_DIR="$verification_target" cargo package --locked \
  --manifest-path anneal/v1/Cargo.toml \
  --registry crates-io \
  --config "patch.crates-io.exocrate.path='$exocrate_path'"

# Keep the final compressed archives byte-identical to the privileged
# reconciler and `cargo publish`, which use `--no-verify` to avoid executing
# package code with release credentials. Cargo does not reliably truncate a
# longer archive when overwriting it, so write these publish-equivalent bytes
# into a fresh target rather than reusing either the verified output or a
# previous run's output. The verified builds above retain the stronger
# publishability check.
CARGO_TARGET_DIR="$archive_target" cargo package --locked --no-verify \
  --manifest-path exocrate/Cargo.toml \
  --registry crates-io
CARGO_TARGET_DIR="$archive_target" cargo package --locked --no-verify \
  --manifest-path anneal/v1/Cargo.toml \
  --registry crates-io \
  --config "patch.crates-io.exocrate.path='$exocrate_path'"

# anneal-release.yml expects these conventional workspace target paths. The
# fresh target must contain exactly the two entries in that workflow's trusted
# release plan; force coordinated updates if the package set ever changes.
archives=("$archive_target"/package/*.crate)
if [ "${#archives[@]}" -ne 2 ]; then
  echo "expected exactly two Anneal release archives, found ${#archives[@]}" >&2
  exit 1
fi
mkdir -p exocrate/target/package anneal/v1/target/package
cp "$archive_target"/package/exocrate-*.crate exocrate/target/package/
cp "$archive_target"/package/cargo-anneal-*.crate anneal/v1/target/package/
