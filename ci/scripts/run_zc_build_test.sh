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
# The legacy `ci.yml` `build_test` job had the same 30-minute limit.
TIMEOUT_SECS=1800
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE

: "${TOOLCHAIN:?}" "${CRATE:?}" "${FEATURE_PROFILE:?}" "${TARGET:?}"

SCRATCH_ROOT="${HOME:-/scratch}"
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/zc-target}"
export ZEROCOPY_UI_TEST_OUT_DIR="${ZEROCOPY_UI_TEST_OUT_DIR:-${SCRATCH_ROOT}/ui-test-artifacts}"
mkdir -p "$CARGO_TARGET_DIR" "$ZEROCOPY_UI_TEST_OUT_DIR"

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

export RUSTFLAGS="-Dwarnings"
export RUSTDOCFLAGS="-Dwarnings --cfg=zerocopy_unstable_ptr"
if [[ "$TOOLCHAIN" == "nightly" ]]; then
  : "${PIN_LAYOUT_SEED__SEED:?}"
  export RUSTFLAGS="$RUSTFLAGS -Zrandomize-layout -Zlayout-seed=${PIN_LAYOUT_SEED__SEED}"
fi

CROSS_TARGETS=()
if [[ "$TARGET" == "x86_64-pc-windows-msvc" ]]; then
  case "$TOOLCHAIN" in
    no-zerocopy-aarch64-simd-1-59-0|no-zerocopy-aarch64-simd-be-1-87-0|no-zerocopy-allocator-api-1-100-0|no-zerocopy-core-error-1-81-0|no-zerocopy-diagnostic-on-unimplemented-1-78-0|no-zerocopy-generic-bounds-in-const-fn-1-61-0)
      echo "error: $TOOLCHAIN should exclude x86_64-pc-windows-msvc" >&2
      exit 1
      ;;
    *)
      CROSS_TARGETS=(x86_64-pc-windows-msvc)
      ;;
  esac
elif [[ "$TARGET" == "cross-extra" ]]; then
  case "$TOOLCHAIN" in
    no-zerocopy-aarch64-simd-1-59-0|no-zerocopy-aarch64-simd-be-1-87-0)
      CROSS_TARGETS=(aarch64-unknown-linux-gnu)
      ;;
    no-zerocopy-allocator-api-1-100-0|no-zerocopy-core-error-1-81-0|no-zerocopy-diagnostic-on-unimplemented-1-78-0|no-zerocopy-generic-bounds-in-const-fn-1-61-0)
      echo "error: $TOOLCHAIN should exclude cross-extra" >&2
      exit 1
      ;;
    *)
      CROSS_TARGETS=(
        arm-unknown-linux-gnueabi
        aarch64-unknown-linux-gnu
        powerpc-unknown-linux-gnu
        powerpc64-unknown-linux-gnu
        riscv64gc-unknown-linux-gnu
        s390x-unknown-linux-gnu
      )
      if [[ "$FEATURE_PROFILE" == "default" ]]; then
        CROSS_TARGETS+=(thumbv6m-none-eabi)
      fi
      if [[ "$TOOLCHAIN" != "stable" ]]; then
        CROSS_TARGETS+=(wasm32-unknown-unknown)
      fi
      ;;
  esac
fi

if [[ "$TARGET" == "x86_64-unknown-linux-gnu" || "$TARGET" == "i686-unknown-linux-gnu" ]]; then
  ./cargo.sh +"$TOOLCHAIN" test \
    --locked --offline \
    --package "$CRATE" \
    --target "$TARGET" \
    "${FEATURE_ARGS[@]}" \
    --verbose
else
  if [[ "${#CROSS_TARGETS[@]}" -eq 0 ]]; then
    echo "error: empty CROSS_TARGETS for TARGET=$TARGET" >&2
    exit 1
  fi
  failures=0
  for cross_target in "${CROSS_TARGETS[@]}"; do
    if [[ "$cross_target" == "thumbv6m-none-eabi" ]]; then
      if ! ./cargo.sh +"$TOOLCHAIN" check \
        --locked --offline \
        --package "$CRATE" \
        --target "$cross_target" \
        "${FEATURE_ARGS[@]}" \
        --verbose; then
        failures=1
      fi
    else
      if ! ./cargo.sh +"$TOOLCHAIN" check --tests \
        --locked --offline \
        --package "$CRATE" \
        --target "$cross_target" \
        "${FEATURE_ARGS[@]}" \
        --verbose; then
        failures=1
      elif ! ./cargo.sh +"$TOOLCHAIN" build \
        --locked --offline \
        --package "$CRATE" \
        --target "$cross_target" \
        "${FEATURE_ARGS[@]}" \
        --verbose; then
        failures=1
      fi
    fi
  done
  if [[ "$failures" -ne 0 ]]; then
    exit 1
  fi
fi

if [[ "$TOOLCHAIN" == "nightly" ]]; then
  if [[ "$TARGET" == "x86_64-unknown-linux-gnu" || "$TARGET" == "i686-unknown-linux-gnu" ]]; then
    ./cargo.sh +nightly clippy \
      --locked --offline \
      --package "$CRATE" \
      --target "$TARGET" \
      "${FEATURE_ARGS[@]}" \
      --tests \
      --verbose
  else
    failures=0
    for cross_target in "${CROSS_TARGETS[@]}"; do
      if [[ "$cross_target" == "thumbv6m-none-eabi" ]]; then
        if ! ./cargo.sh +nightly clippy \
          --locked --offline \
          --package "$CRATE" \
          --target "$cross_target" \
          "${FEATURE_ARGS[@]}" \
          --verbose; then
          failures=1
        fi
      else
        if ! ./cargo.sh +nightly clippy \
          --locked --offline \
          --package "$CRATE" \
          --target "$cross_target" \
          "${FEATURE_ARGS[@]}" \
          --tests \
          --verbose; then
          failures=1
        fi
      fi
    done
    if [[ "$failures" -ne 0 ]]; then
      exit 1
    fi
  fi
fi

if [[ "$TARGET" == "x86_64-unknown-linux-gnu" ]] || \
   [[ "$TARGET" == "cross-extra" && ( "$TOOLCHAIN" == "no-zerocopy-aarch64-simd-1-59-0" || "$TOOLCHAIN" == "no-zerocopy-aarch64-simd-be-1-87-0" ) ]]; then
  if [[ "$TOOLCHAIN" == "nightly" ]]; then
    DOCS_RS_ARGS="$(env -u RUSTFLAGS -u RUSTDOCFLAGS ./cargo.sh +nightly metadata --manifest-path Cargo.toml --no-deps --offline --format-version 1 \
      | jq -r '.packages[] | select(.name == "zerocopy").metadata.docs.rs."rustdoc-args"[]' \
      | tr '\n' ' ')"
    export RUSTDOCFLAGS="-Z unstable-options --document-hidden-items $DOCS_RS_ARGS $RUSTDOCFLAGS"
  fi
  ./cargo.sh +"$TOOLCHAIN" doc \
    --locked --offline \
    --no-deps \
    --document-private-items \
    --package "$CRATE" \
    "${FEATURE_ARGS[@]}"
  if [[ "$CRATE" == "zerocopy" ]]; then
    DOC_DIR="${CARGO_TARGET_DIR}/doc/zerocopy"
    grep -q 'codegen-tabs' "$DOC_DIR/trait.TryFromBytes.html"
    grep -q 'method\.try_mut_from_bytes\.codegen' "$DOC_DIR/trait.TryFromBytes.html"
    grep -q 'Code Generation' "$DOC_DIR/split_at/struct.Split.html"
    RUSTDOCFLAGS="--cfg=no_zerocopy_codegen_docs $RUSTDOCFLAGS" \
      ./cargo.sh +"$TOOLCHAIN" doc \
        --locked --offline \
        --no-deps \
        --document-private-items \
        --package "$CRATE" \
        "${FEATURE_ARGS[@]}"
    MATCHES="$(find "$DOC_DIR" -path "$DOC_DIR/util/macros*" -prune -o -name '*.html' -exec grep -E 'codegen-tabs|Code Generation|\.codegen["'\''#)]' {} + || true)"
    if [[ -n "$MATCHES" ]]; then
      echo "$MATCHES" >&2
      exit 1
    fi
  fi
fi
