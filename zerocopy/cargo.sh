#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail

ZEROCOPY_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_DIR="$(dirname "$ZEROCOPY_DIR")"

# Parse the tools compiler rather than relying on rustup's directory lookup.
# An explicit `+<toolchain>` takes precedence over both RUSTUP_TOOLCHAIN and a
# persisted `rustup override set` in this checkout. Keep this parser coordinated
# with `tools/rust-toolchain.toml`, `ci/check_tools.sh`, and win-cargo.bat. The
# deliberately narrow format makes a changed or duplicate declaration fail
# closed instead of silently selecting a different compiler.
TOOLS_TOOLCHAIN="$(
  sed -nE 's/^channel = "([0-9]+\.[0-9]+\.[0-9]+)"$/\1/p' \
    "$REPO_DIR/tools/rust-toolchain.toml"
)"
if [[ -z "$TOOLS_TOOLCHAIN" || "$TOOLS_TOOLCHAIN" == *$'\n'* ]]; then
  echo "Expected one exact channel in tools/rust-toolchain.toml" >&2
  exit 1
fi

# Build `cargo-zerocopy` without any RUSTFLAGS, CARGO_TARGET_DIR, or
# RUSTUP_TOOLCHAIN set in the environment. The explicit toolchain is the
# compiler pin; clearing the variables also keeps their other effects out of
# the build. Building from `tools` stays outside Zerocopy's vendored Cargo
# configuration. `--locked` prevents this bootstrap step from silently
# changing the tools dependency graph.
(
  cd "$REPO_DIR/tools"
  env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTUP_TOOLCHAIN \
    cargo "+$TOOLS_TOOLCHAIN" build --locked --manifest-path Cargo.toml \
      -p cargo-zerocopy -q
)

# Keep this working directory coordinated with cargo-zerocopy's `ci` route,
# `tools/zc/src/cli.rs`, and win-cargo.bat. The typed CI commands pass `..` as
# the repository root, so both platform wrappers must invoke cargo-zerocopy
# from the Zerocopy crate directory.
cd "$ZEROCOPY_DIR"
exec "$REPO_DIR/tools/target/debug/cargo-zerocopy" "$@"
