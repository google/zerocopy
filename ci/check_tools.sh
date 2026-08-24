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
mapfile -t TOOLS_CHANNELS < <(
  sed -nE 's/^channel = "([0-9]+\.[0-9]+\.[0-9]+)"$/\1/p' \
    rust-toolchain.toml
)
mapfile -t STABLE_CHANNELS < <(
  sed -nE \
    's/^pinned-stable = "([0-9]+\.[0-9]+\.[0-9]+)"$/\1/p' \
    ../zerocopy/Cargo.toml
)
if [[ ${#TOOLS_CHANNELS[@]} -ne 1 || ${#STABLE_CHANNELS[@]} -ne 1 ]]; then
  echo "Expected one tools channel and one Zerocopy stable channel" >&2
  exit 1
fi
if [[ "${TOOLS_CHANNELS[0]}" != "${STABLE_CHANNELS[0]}" ]]; then
  echo "Tools compiler ${TOOLS_CHANNELS[0]} does not match Zerocopy stable" \
    "compiler ${STABLE_CHANNELS[0]}" >&2
  exit 1
fi

# Running from this directory makes rustup honor `tools/rust-toolchain.toml`.
# Keep the lockfile read-only: repository tools are part of CI's trusted setup,
# so an unreviewed dependency change must never be created as a side effect of
# testing them.
cargo test --locked --workspace
