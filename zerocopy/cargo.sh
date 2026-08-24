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

# Build `cargo-zerocopy` without any RUSTFLAGS, CARGO_TARGET_DIR, or
# RUSTUP_TOOLCHAIN set in the environment. Rustup gives RUSTUP_TOOLCHAIN higher
# precedence than a directory's rust-toolchain.toml, so clearing it is part of
# the compiler pin rather than merely environment cleanup. Building from
# `tools` then selects the checked-in compiler and stays outside Zerocopy's
# vendored Cargo configuration. `--locked` also prevents this bootstrap step
# from silently changing the tools dependency graph.
(
  cd "$REPO_DIR/tools"
  env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTUP_TOOLCHAIN \
    cargo build --locked --manifest-path Cargo.toml -p cargo-zerocopy -q
)

cd "$ZEROCOPY_DIR"
exec "$REPO_DIR/tools/target/debug/cargo-zerocopy" "$@"
