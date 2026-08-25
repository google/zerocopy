#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/../tools"

# The stable-toolchain roller intentionally updates these two files together.
# Check the copy here as well so a hand edit cannot make local tool builds use
# a different compiler from the stable CI lane. Require one exact declaration
# in each file; a future reorganization must update this check explicitly.
# `zerocopy/cargo.sh` and `zerocopy/win-cargo.bat` also parse the tools channel
# so they can defeat persisted rustup directory overrides. Keep all three
# parsers coordinated with the deliberately narrow format below.
#
# Store the complete sed output so an embedded newline exposes duplicate
# declarations. Do not use `mapfile`: macOS still ships Bash 3.2, which does
# not provide that builtin.
TOOLS_CHANNEL="$(
  sed -nE 's/^channel = "([0-9]+\.[0-9]+\.[0-9]+)"$/\1/p' \
    rust-toolchain.toml
)"
STABLE_CHANNEL="$(
  sed -nE \
    's/^pinned-stable = "([0-9]+\.[0-9]+\.[0-9]+)"$/\1/p' \
    ../zerocopy/Cargo.toml
)"
if [[ -z "$TOOLS_CHANNEL" || "$TOOLS_CHANNEL" == *$'\n'* || \
      -z "$STABLE_CHANNEL" || "$STABLE_CHANNEL" == *$'\n'* ]]; then
  echo "Expected one tools channel and one Zerocopy stable channel" >&2
  exit 1
fi
if [[ "$TOOLS_CHANNEL" != "$STABLE_CHANNEL" ]]; then
  echo "Tools compiler $TOOLS_CHANNEL does not match Zerocopy stable" \
    "compiler $STABLE_CHANNEL" >&2
  exit 1
fi

# RUSTUP_TOOLCHAIN overrides tools/rust-toolchain.toml. Use an intentionally
# invalid value to prove that the Unix wrapper's explicit pin defeats this
# ambient override while it builds cargo-zerocopy, then reports the configured
# stable version.
WRAPPER_STABLE="$(
  RUSTUP_TOOLCHAIN=zerocopy-ci-intentionally-invalid \
    ../zerocopy/cargo.sh --version stable
)"
if [[ "$WRAPPER_STABLE" != "$STABLE_CHANNEL" ]]; then
  echo "cargo.sh resolved stable to $WRAPPER_STABLE, expected $STABLE_CHANNEL" \
    >&2
  exit 1
fi

# Pass the parsed toolchain explicitly so a persisted rustup directory override
# cannot change the compiler. Keep the lockfile read-only: repository tools are
# part of CI's trusted setup, so an unreviewed dependency change must never be
# created as a side effect of testing them.
env -u RUSTUP_TOOLCHAIN \
  cargo "+$TOOLS_CHANNEL" test --locked --workspace

# Exercise the public repository-level route in addition to the library tests.
# The wrapper must establish the expected working directory, and the inventory
# command must pin its own Cargo metadata invocation instead of inheriting this
# deliberately invalid ambient override. Keep this command coordinated with
# `tools/cargo-zerocopy/src/main.rs` and `tools/zc/src/cli.rs`.
RUSTUP_TOOLCHAIN=zerocopy-ci-intentionally-invalid \
  ../zerocopy/cargo.sh ci audit >/dev/null
