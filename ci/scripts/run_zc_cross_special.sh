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
