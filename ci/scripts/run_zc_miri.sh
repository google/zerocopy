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
# The legacy `ci.yml` `miri` job had the same 45-minute limit, which also
# covered checkout and image setup.
TIMEOUT_SECS=2700
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE

: "${CRATE:?}" "${FEATURE_PROFILE:?}" "${TARGET:?}" "${MIRI_MODEL:?}" "${PIN_LAYOUT_SEED__SEED:?}"

FEATURE_ARGS=()
case "$FEATURE_PROFILE" in
  default) ;;
  stable)
    FEATURE_ARGS=(--no-default-features --features __internal_use_only_features_that_work_on_stable)
    ;;
  all)
    FEATURE_ARGS=(--all-features)
    ;;
  *)
    echo "error: unknown FEATURE_PROFILE: $FEATURE_PROFILE" >&2
    exit 1
    ;;
esac

MODEL_FLAGS=""
case "$MIRI_MODEL" in
  stacked) MODEL_FLAGS="" ;;
  tree) MODEL_FLAGS="-Zmiri-tree-borrows" ;;
  *)
    echo "error: unknown MIRI_MODEL: $MIRI_MODEL" >&2
    exit 1
    ;;
esac

# Pre-build the Miri sysroot from outside `/work/zerocopy` so Cargo loads
# `$CARGO_HOME/config.toml` (`/opt/rust-src-vendor`) rather than
# `zerocopy/.cargo/config.toml` (`zerocopy/vendor`, which does not contain
# `rust-src` dependencies). Once populated under `$XDG_CACHE_HOME/miri`,
# `run_miri_batched.sh` reuses the cached sysroot and resolves zerocopy's own
# crate dependencies from `zerocopy/vendor`.
SCRATCH_ROOT="${HOME:-/scratch}"
MIRI_CARGO_HOME="${SCRATCH_ROOT}/miri-cargo-home"
mkdir -p "$MIRI_CARGO_HOME"
cat > "$MIRI_CARGO_HOME/config.toml" <<'EOF'
[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "/opt/rust-src-vendor"
EOF

export CARGO_HOME="$MIRI_CARGO_HOME"
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/zc-miri-target}"
MIRI_CACHE_SRC="${MIRI_SYSROOT_CACHE_DIR:-${SCRATCH_ROOT}/miri-cache}"
if [[ -d "$MIRI_CACHE_SRC" && ! -w "$MIRI_CACHE_SRC" && "$MIRI_CACHE_SRC" != "${SCRATCH_ROOT}/miri-cache" ]]; then
  export XDG_CACHE_HOME="${SCRATCH_ROOT}/miri-cache"
  rm -rf "$XDG_CACHE_HOME"
  cp -a "$MIRI_CACHE_SRC" "$XDG_CACHE_HOME"
  chmod -R u+w "$XDG_CACHE_HOME"
else
  export XDG_CACHE_HOME="$MIRI_CACHE_SRC"
fi
mkdir -p "$CARGO_TARGET_DIR" "$XDG_CACHE_HOME"

export RUSTFLAGS="-Dwarnings -Zrandomize-layout -Zlayout-seed=${PIN_LAYOUT_SEED__SEED}"
export RUSTDOCFLAGS="-Dwarnings --cfg=zerocopy_unstable_ptr"
export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-backtrace=full ${MODEL_FLAGS}"

TC="$(./cargo.sh --version nightly)"
(
  cd "$MIRI_CARGO_HOME"
  env -u RUSTUP_TOOLCHAIN rustup run "$TC" cargo miri setup --target "$TARGET"
)

../.github/scripts/run_miri_batched.sh \
  --toolchain nightly \
  --package "$CRATE" \
  --target "$TARGET" \
  -- "${FEATURE_ARGS[@]}"
