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
