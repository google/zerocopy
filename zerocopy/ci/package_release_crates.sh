#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Exercise the exact package boundary used by release.yml, including Cargo's
# verification build. Keep the dependency order and local patch coordinated
# with that workflow's release plan: zerocopy-derive is published first, while
# zerocopy's packaged manifest retains its registry dependency on that version.

set -euo pipefail

# release.yml keeps the trusted copy of this driver in the workflow checkout,
# while an exact historical main commit supplies the crate source. Accept that
# source explicitly without making PR CI duplicate the checkout layout. Keep
# this interface coordinated with release.yml's `release-source` checkout and
# test_release_workflows.py's structural contract.
script_directory="$(cd "$(dirname "$0")" && pwd)"
repo_root="$(cd "$script_directory/../.." && pwd)"
case "$#" in
  0)
    source_root="$script_directory/.."
    ;;
  2)
    if [ "$1" != "--source-root" ]; then
      echo "usage: $0 [--source-root ZEROCOPY_DIR]" >&2
      exit 2
    fi
    source_root="$2"
    ;;
  *)
    echo "usage: $0 [--source-root ZEROCOPY_DIR]" >&2
    exit 2
    ;;
esac
source_root="$(cd "$source_root" && pwd)"
release_cargo="$repo_root/ci/run_cargo_for_release.sh"

# Build the trusted driver and install the stable version selected by the
# source manifest before changing any Cargo configuration. All four packaging
# calls below then use that exact prebuilt driver. release.yml enforces the
# same sequence before its credential-bearing reconciler starts.
"$release_cargo" --source-root "$source_root" +stable --version
cd "$source_root"

temporary_root="$(mktemp -d)"
verification_target="$temporary_root/verification"
archive_target="$temporary_root/archive"

restore_config() {
  if [ -e .cargo/config.toml.release ]; then
    mv .cargo/config.toml.release .cargo/config.toml
  fi
}

cleanup() {
  restore_config
  rm -rf -- "$temporary_root"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Published packages must resolve against the live registry, not the repository
# vendor directory. The trap restores developer and CI state on every exit.
mv .cargo/config.toml .cargo/config.toml.release

CARGO_TARGET_DIR="$verification_target" "$release_cargo" \
  --prebuilt --source-root "$source_root" +stable package --locked \
  --package zerocopy-derive --registry crates-io

derive_path="$PWD/zerocopy-derive"
CARGO_TARGET_DIR="$verification_target" "$release_cargo" \
  --prebuilt --source-root "$source_root" +stable package --locked \
  --package zerocopy --registry crates-io \
  --config "patch.crates-io.zerocopy-derive.path='$derive_path'"

# Cargo uses a different compressed representation when verification is
# enabled, even though the archive expands to identical bytes. It also does
# not reliably truncate an existing, longer archive when overwriting it. Use a
# second, initially empty target directory so the final bytes cannot retain a
# suffix from either the verified pass or an earlier invocation. The
# privileged reconciler and `cargo publish` both use `--no-verify` to avoid
# running crate code with credentials, so these final commands otherwise use
# their exact flags.
CARGO_TARGET_DIR="$archive_target" "$release_cargo" \
  --prebuilt --source-root "$source_root" +stable package \
  --locked --no-verify \
  --package zerocopy-derive --registry crates-io
CARGO_TARGET_DIR="$archive_target" "$release_cargo" \
  --prebuilt --source-root "$source_root" +stable package \
  --locked --no-verify \
  --package zerocopy --registry crates-io \
  --config "patch.crates-io.zerocopy-derive.path='$derive_path'"

# release.yml consumes archives from cargo-zerocopy's conventional stable
# target directory. The fresh target above must contain exactly the two crates
# in that workflow's trusted release plan; if that contract changes on either
# side, fail here instead of silently uploading an incomplete artifact.
archives=("$archive_target"/package/*.crate)
if [ "${#archives[@]}" -ne 2 ]; then
  echo "expected exactly two core release archives, found ${#archives[@]}" >&2
  exit 1
fi
mkdir -p target/by-toolchain/stable/package
cp "${archives[@]}" target/by-toolchain/stable/package/
