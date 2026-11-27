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

# Bound this check's wall-clock time: on first entry, re-execute under
# coreutils `timeout`, which at the limit sends SIGTERM to the process group
# and exits 124, then sends SIGKILL (exit status 137) 120 seconds later.
# Other exit statuses and signals pass through unchanged.
# One small untrusted tool workspace's clippy and tests, in the same tier as
# the other short checks.
TIMEOUT_SECS=1800
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE

: "${PIN_RUST_TOOLCHAINS__STABLE:?}"

# Mirrors the Cargo cache guards in `ci/scripts/run_exocrate_test.sh`.
#
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
: "${CARGO_TARGET_DIR:=${SCRATCH_ROOT}/anneal-scaffold-target}"
export CARGO_TARGET_DIR
mkdir -p "$CARGO_TARGET_DIR"

STABLE="${PIN_RUST_TOOLCHAINS__STABLE}"
cd anneal/tools/anneal-scaffold

cargo "+${STABLE}" clippy --locked --offline --workspace --all-targets \
  -- -D warnings
# The unit tests read `anneal/trusted/rustc-capture/src/{ir,lean}.rs` and
# `anneal/trusted/cargo-anneal/src/verify.rs` from the checkout to catch drift
# from the capture format and the reserved module roots.
cargo "+${STABLE}" test --locked --offline --workspace
