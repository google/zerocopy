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

SCRATCH_ROOT="${HOME:-/scratch}"
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/zc-coverage-target}"
mkdir -p "$CARGO_TARGET_DIR"
export RUSTFLAGS="-Dwarnings"
export RUSTDOCFLAGS="-Dwarnings --cfg=zerocopy_unstable_ptr"

OUT_FILE="${ZC_COVERAGE_OUT:-/outputs/lcov.info}"
mkdir -p "$(dirname "$OUT_FILE")"

./cargo.sh +nightly llvm-cov \
  --offline \
  --package zerocopy \
  --target x86_64-unknown-linux-gnu \
  --all-features \
  --doctests \
  --lcov \
  --output-path "$OUT_FILE" \
  --verbose

test -s "$OUT_FILE"
