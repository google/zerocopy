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

# Inside `zc-stable-msrv`, `ENV CARGO_HOME=/usr/local/cargo` is baked in with
# its registry wiped; switch to the mounted `cargo_locked` cache at
# `/cargo-home` whenever present unless a caller explicitly set a different
# `CARGO_HOME`.
#
# Refuse to use a mounted Cargo cache that could steer later cargo runs:
# `config`/`config.toml` can set `build.rustc-wrapper`, target runners, or
# source replacement, `credentials`/`credentials.toml` must never reach a
# shared cache, and `bin/` can shadow cargo subcommands. Any entry with one of
# these names, including a symlink, fails closed.
require_inert_cargo_home() {
  local cargo_home="$1" name
  for name in config config.toml credentials credentials.toml bin; do
    if [[ -e "$cargo_home/$name" || -L "$cargo_home/$name" ]]; then
      echo "error: refusing CARGO_HOME $cargo_home: it contains $name" >&2
      exit 1
    fi
  done
}

# Apply `require_inert_cargo_home` to `<mount>` whenever the effective
# `CARGO_HOME` (`<cargo_home>`) names it, whether the caller preset it or this
# script adopted it. Trailing slashes and, via `realpath -m`, `.`/`..`
# components and symlinks are normalized before comparing.
guard_mounted_cargo_home() {
  local cargo_home="$1" mount="$2"
  [[ -n "$cargo_home" ]] || return 0
  while [[ "$cargo_home" == */ && "$cargo_home" != / ]]; do
    cargo_home="${cargo_home%/}"
  done
  while [[ "$mount" == */ && "$mount" != / ]]; do
    mount="${mount%/}"
  done
  if [[ "$cargo_home" == "$mount" ]] || {
    command -v realpath >/dev/null 2>&1 \
      && [[ "$(realpath -m -- "$cargo_home")" == "$(realpath -m -- "$mount")" ]]
  }; then
    require_inert_cargo_home "$mount"
  fi
}

SCRATCH_ROOT="${HOME:-/scratch}"
if [[ -d /cargo-home && ( -z "${CARGO_HOME:-}" || "${CARGO_HOME}" == "/usr/local/cargo" ) ]]; then
  export CARGO_HOME="/cargo-home"
fi
guard_mounted_cargo_home "${CARGO_HOME:-}" /cargo-home
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/exocrate-target}"
mkdir -p "$CARGO_TARGET_DIR"

export RUSTFLAGS="-Dwarnings"
cargo test --locked --offline \
  --manifest-path exocrate/Cargo.toml \
  --lib \
  --tests
cargo test --locked --offline \
  --manifest-path exocrate/Cargo.toml \
  --doc
