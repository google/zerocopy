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

# Inside prebuilt CI or sandbox environments, reuse a prebuilt `cargo-zerocopy`
# binary (such as `/usr/local/bin/cargo-zerocopy` built during
# `build_docker_env`) so each invocation does not re-fetch crates.io
# dependencies and recompile `cargo-zerocopy`. Explicit `CARGO_ZEROCOPY_BIN`
# fails closed when non-executable; legacy `CARGO_ZEROCOPY_PREBUILT` falls back
# to a source build when absent.
if [[ -n "${CARGO_ZEROCOPY_BIN:-}" ]]; then
  PREBUILT_BIN="$CARGO_ZEROCOPY_BIN"
  if [[ "$PREBUILT_BIN" != /* ]]; then
    PREBUILT_BIN="$PWD/$PREBUILT_BIN"
  fi
  if [[ ! -f "$PREBUILT_BIN" || ! -x "$PREBUILT_BIN" ]]; then
    echo "[cargo-zerocopy] error: CARGO_ZEROCOPY_BIN is not an executable file: $PREBUILT_BIN" >&2
    exit 1
  fi
  cd "$ZEROCOPY_DIR"
  exec "$PREBUILT_BIN" "$@"
elif [[ -n "${CARGO_ZEROCOPY_PREBUILT:-}" ]]; then
  PREBUILT_BIN="$CARGO_ZEROCOPY_PREBUILT"
  if [[ "$PREBUILT_BIN" != /* ]]; then
    PREBUILT_BIN="$PWD/$PREBUILT_BIN"
  fi
  if [[ -f "$PREBUILT_BIN" && -x "$PREBUILT_BIN" ]]; then
    cd "$ZEROCOPY_DIR"
    exec "$PREBUILT_BIN" "$@"
  fi
fi

# Build `cargo-zerocopy` without any RUSTFLAGS or CARGO_TARGET_DIR set in the
# environment. Build it from the repository root so that Zerocopy's vendoring
# config does not apply to the unvendored `tools/cargo-zerocopy` crate. Prefer
# `stable` when installed, and fall back to `pinned-stable` from `Cargo.toml`
# so slim CI images do not have to ship both an unpinned and a pinned stable
# toolchain.
BUILD_TOOLCHAIN="stable"
if command -v rustup >/dev/null 2>&1; then
  INSTALLED_TOOLCHAINS="$(rustup toolchain list)"
  if [[ "$INSTALLED_TOOLCHAINS" != *$'\n'stable-* && "$INSTALLED_TOOLCHAINS" != stable-* ]]; then
    PINNED_STABLE="$(sed -n 's/^[[:space:]]*pinned-stable[[:space:]]*=[[:space:]]*"\([^"]*\)"[[:space:]]*\(#.*\)\{0,1\}$/\1/p' "$ZEROCOPY_DIR/Cargo.toml")"
    PINNED_STABLE="${PINNED_STABLE%%$'\n'*}"
    if [ -n "$PINNED_STABLE" ]; then
      BUILD_TOOLCHAIN="$PINNED_STABLE"
    fi
  fi
fi
(
  cd "$REPO_DIR"
  env -u CARGO_ENCODED_RUSTFLAGS -u RUSTFLAGS -u CARGO_TARGET_DIR cargo "+$BUILD_TOOLCHAIN" build --locked --manifest-path tools/cargo-zerocopy/Cargo.toml -q
)

cd "$ZEROCOPY_DIR"
exec "$REPO_DIR/tools/cargo-zerocopy/target/debug/cargo-zerocopy" "$@"
