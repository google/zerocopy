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
# One cross-target build or check; legacy `ci.yml` p99 was under 2 minutes.
TIMEOUT_SECS=1800
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE

: "${SPECIAL_TARGET:?}" "${PIN_LAYOUT_SEED__SEED:?}"

SCRATCH_ROOT="${HOME:-/scratch}"
MERGED_VENDOR="${SCRATCH_ROOT}/merged-vendor"
python3 -I -B ../ci/scripts/merge_vendor.py \
  /opt/rust-src-vendor "$PWD/vendor" "$MERGED_VENDOR"

export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/zc-cross-target}"
mkdir -p "$CARGO_TARGET_DIR"
export RUSTDOCFLAGS="-Dwarnings --cfg=zerocopy_unstable_ptr"

VENDOR_OVERRIDE="source.vendored-sources.directory=\"${MERGED_VENDOR}\""

case "$SPECIAL_TARGET" in
  aarch64_be)
    RUSTFLAGS="-Dwarnings -Zrandomize-layout -Zlayout-seed=${PIN_LAYOUT_SEED__SEED}" \
      ./cargo.sh +nightly build --offline \
        --config "$VENDOR_OVERRIDE" \
        --target=aarch64_be-unknown-linux-gnu \
        -Zbuild-std \
        --features simd
    ;;
  avr)
    RUSTFLAGS="-C target-cpu=atmega328p" \
      ./cargo.sh +nightly check --offline \
        --config "$VENDOR_OVERRIDE" \
        --target=avr-none \
        -Zbuild-std=core \
        --features simd,simd-nightly,float-nightly,derive
    RUSTFLAGS="-C target-cpu=atmega328p" \
      ./cargo.sh +nightly clippy --offline \
        --config "$VENDOR_OVERRIDE" \
        --target=avr-none \
        -Zbuild-std=core \
        --features simd,simd-nightly,float-nightly,derive
    ;;
  *)
    echo "error: unknown SPECIAL_TARGET: $SPECIAL_TARGET" >&2
    exit 1
    ;;
esac
