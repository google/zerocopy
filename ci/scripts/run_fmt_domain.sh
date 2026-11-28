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
# Only `cargo fmt --check`; legacy `ci.yml` p99 was under 1 minute.
TIMEOUT_SECS=1800
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE

: "${FMT_DOMAIN:?}"

case "$FMT_DOMAIN" in
  zerocopy)
    ./zerocopy/ci/check_fmt.sh
    ;;
  tools)
    NIGHTLY="${PIN_RUST_TOOLCHAINS__NIGHTLY:-$(./zerocopy/cargo.sh --version nightly)}"
    # Keep in sync with `ci/check_fmt.sh`, which explains `--all`.
    for manifest in \
      anneal/tools/anneal-scaffold/Cargo.toml \
      anneal/tools/anneal-spec/Cargo.toml \
      tools/cargo-zerocopy/Cargo.toml \
      tools/generate-readme/Cargo.toml \
      tools/ui-runner/Cargo.toml \
      tools/anneal-mir-eval/Cargo.toml; do
      cargo +"$NIGHTLY" fmt --manifest-path "$manifest" --all --check >&2
    done
    ;;
  exocrate)
    NIGHTLY="${PIN_RUST_TOOLCHAINS__NIGHTLY:-$(./zerocopy/cargo.sh --version nightly)}"
    cargo +"$NIGHTLY" fmt --manifest-path exocrate/Cargo.toml --check >&2
    ;;
  *)
    echo "error: unknown FMT_DOMAIN: $FMT_DOMAIN" >&2
    exit 1
    ;;
esac
