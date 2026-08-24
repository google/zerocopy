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

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

# shellcheck source=toolchain.sh
source "$TOOLS_DIR/toolchain.sh"

# Do not rely on rustup's directory lookup here. RUSTUP_TOOLCHAIN and a
# persisted `rustup override set` both take precedence over a toolchain file,
# while an explicit `+<toolchain>` takes precedence over those overrides. Keep
# this deliberately narrow parser coordinated with rust-toolchain.toml,
# toolchain.sh, and ../ci/check_tools.sh. A changed or duplicate declaration
# must fail closed instead of silently selecting another compiler. The shared
# parser accepts a pre-existing Windows worktree whose TOML still uses CRLF.
if ! TOOLS_TOOLCHAIN="$(
  zc_read_exact_rust_version_assignment \
    "$TOOLS_DIR/rust-toolchain.toml" toolchain channel
)"; then
  echo "Expected one canonical [toolchain] channel" \
    "in tools/rust-toolchain.toml" >&2
  exit 1
fi
if [[ -z "$TOOLS_TOOLCHAIN" || "$TOOLS_TOOLCHAIN" == *$'\n'* ]]; then
  echo "Expected one exact channel in tools/rust-toolchain.toml" >&2
  exit 1
fi

# Establish the tools workspace as Cargo's discovery directory. This keeps
# every caller on the checked-in tools lockfile and Cargo configuration unless
# the caller explicitly supplies different command-line options.
#
# Cargo subcommands can launch Cargo again. Export the same validated pin so a
# child process cannot fall back to the caller's RUSTUP_TOOLCHAIN or a persisted
# directory override after the explicit outer `+<toolchain>` has done its job.
export RUSTUP_TOOLCHAIN="$TOOLS_TOOLCHAIN"
cd "$TOOLS_DIR"
exec cargo "+$TOOLS_TOOLCHAIN" "$@"
