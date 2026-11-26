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
# About 1.5x the slowest per-shard p99 (11.9 minutes) of the legacy
# `ci.yml` Kani jobs, which had no limit, on `main` pushes in Nov 2026.
TIMEOUT_SECS=1080
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE

: "${KANI_CONFIG:?}"

SCRATCH_ROOT="${HOME:-/scratch}"
KANI_CARGO_HOME="${SCRATCH_ROOT}/kani-cargo-home"
mkdir -p "$KANI_CARGO_HOME"
cat > "$KANI_CARGO_HOME/config.toml" <<EOF
[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "${PWD}/zerocopy/vendor"
EOF

export CARGO_HOME="$KANI_CARGO_HOME"
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/kani-target}"
mkdir -p "$CARGO_TARGET_DIR"

EXTRA_ARGS=()
case "$KANI_CONFIG" in
  no-features)
    export KANI_SHARD="1/1"
    EXTRA_ARGS=(--no-default-features --only-codegen)
    ;;
  stable-shard-1)
    export KANI_SHARD="1/2"
    EXTRA_ARGS=(--features __internal_use_only_features_that_work_on_stable)
    ;;
  stable-shard-2)
    export KANI_SHARD="2/2"
    EXTRA_ARGS=(--features __internal_use_only_features_that_work_on_stable)
    ;;
  *)
    echo "error: unknown KANI_CONFIG: $KANI_CONFIG" >&2
    exit 1
    ;;
esac

./.github/scripts/run_kani_sharded.sh \
  --manifest-path zerocopy/Cargo.toml \
  --package zerocopy \
  "${EXTRA_ARGS[@]}" \
  --output-format=terse \
  -Zunstable-options \
  -j \
  -Zfunction-contracts \
  --randomize-layout \
  --memory-safety-checks \
  --overflow-checks \
  --undefined-function-checks \
  --unwinding-checks
