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

# The test process symlinks this script into PATH as `yq`. Delegate ordinary
# parsing to the real implementation, then mutate only its JSON output. This
# leaves the worktree untouched and reuses the real Cargo metadata and executor.
if [[ -n "${ZEROCOPY_CI_CHECK_REAL_YQ:-}" ]]; then
  invoked_name="${0##*/}"
  if [[ "$invoked_name" == "tomlq" ]]; then
    # Python yq ships TOML parsing as a separate executable. Inject the parsed
    # table, rather than depending on one particular TOML spelling, to prove
    # that every quoted/dotted/inline representation is caught structurally.
    [[ -n "${ZEROCOPY_CI_CHECK_REAL_TOMLQ:-}" ]] || exit 1
    "$ZEROCOPY_CI_CHECK_REAL_TOMLQ" "$@" | jq -c '.profile.test = {}'
    exit
  fi
  if [[ "${1:-}" == "--version" ]]; then
    exec "$ZEROCOPY_CI_CHECK_REAL_YQ" "$@"
  fi
  # Go yq parses TOML through the same executable. Detect that input mode and
  # apply the same parsed-table mutation as the Python tomlq branch above.
  for arg in "$@"; do
    if [[ "$arg" == "-p=toml" || "$arg" == "--input-format=toml" ]]; then
      "$ZEROCOPY_CI_CHECK_REAL_YQ" "$@" | jq -c '.profile.test = {}'
      exit
    fi
  done
  # Exercise ten independent ownership boundaries in one checker run:
  #
  # - a parsed Cargo test-profile override;
  # - a target added without an executor classification;
  # - deletion of a required workflow trigger;
  # - exclusions which erase every natively-runnable target;
  # - a narrow exclusion which erases one required cross-target feature set;
  # - removal of an exclusion which admits an unsupported matrix cell;
  # - removal of an exclusion from a reviewed native-only threshold;
  # - AArch64-specific toolchains accidentally redirected to ARM32;
  # - removal of the workflow's sole executor bridge; and
  # - removal of dedicated codegen lint ownership.
  #
  # Requiring every diagnostic below is important: the checker accumulates
  # failures, so one early mutation must not mask a later invariant.
  "$ZEROCOPY_CI_CHECK_REAL_YQ" "$@" | jq -c '
    del(.on.push)
    | .jobs.build_test.strategy.matrix.target +=
      ["__mutation_unclassified_target__"]
    | .jobs.build_test.strategy.matrix.exclude += [
        {"target": "i686-unknown-linux-gnu"},
        {"target": "x86_64-unknown-linux-gnu"},
        {
          "toolchain": "nightly",
          "target": "wasm32-unknown-unknown",
          "crate": "zerocopy"
        }
      ]
    | .jobs.build_test.strategy.matrix.exclude |= map(select((
        (.toolchain == "stable"
          and .target == "wasm32-unknown-unknown")
        or (.toolchain == "no-zerocopy-core-error-1-81-0"
          and .target == "arm-unknown-linux-gnueabi")
      ) | not))
    | (
        .jobs.build_test.strategy.matrix.exclude[]
        | select(
            (.toolchain == "no-zerocopy-aarch64-simd-1-59-0"
              or .toolchain == "no-zerocopy-aarch64-simd-be-1-87-0")
            and .target == "arm-unknown-linux-gnueabi"
          )
        | .target
      ) = "aarch64-unknown-linux-gnu"
    | .jobs.build_test.steps |= map(select(.name != "Build and test"))
    | (.jobs.codegen.steps[] | select(.name == "Clippy").run) |=
        gsub("--test codegen"; "")
  '
  exit
fi

cd "$(dirname "$0")/.."

readonly CHECKER="./ci/check_all_toolchains_tested.sh"
REAL_YQ="$(command -v yq)"
readonly REAL_YQ
REAL_TOMLQ="$(command -v tomlq || true)"
readonly REAL_TOMLQ
TEMP_DIR="$(mktemp -d)"
readonly TEMP_DIR
trap 'rm -rf -- "$TEMP_DIR"' EXIT

# Feature-graph semantics belong to test_feature_policy.sh, which was added
# with the policy itself. This test mutates only the executor and matrix
# contracts introduced alongside run_build_test_cell.sh.
ln -s "$PWD/ci/test_check_all_toolchains_tested.sh" "$TEMP_DIR/yq"
ln -s "$PWD/ci/test_check_all_toolchains_tested.sh" "$TEMP_DIR/tomlq"

if output="$(
  PATH="$TEMP_DIR:$PATH" \
    ZEROCOPY_CI_CHECK_REAL_YQ="$REAL_YQ" \
    ZEROCOPY_CI_CHECK_REAL_TOMLQ="$REAL_TOMLQ" \
    "$CHECKER" 2>&1
)"; then
  echo "mutation unexpectedly passed $CHECKER" >&2
  exit 1
fi

for expected_diagnostic in \
  "Cargo.toml overrides profile.test" \
  "build/test executor targets is missing required entries:" \
  "workflow triggers is missing required entries:" \
  "post-exclusion build-matrix cells is missing required entries:" \
  "post-exclusion build-matrix cells contains unexpected entries:" \
  $'merge_group\tzerocopy\tnightly\tdefault\tx86_64-unknown-linux-gnu' \
  $'merge_group\tzerocopy\tnightly\tall\twasm32-unknown-unknown' \
  $'merge_group\tzerocopy\tstable\tdefault\twasm32-unknown-unknown' \
  $'merge_group\tzerocopy\tno-zerocopy-core-error-1-81-0\tdefault\tarm-unknown-linux-gnueabi' \
  "merge_group targets for cross-only toolchain 'no-zerocopy-aarch64-simd-1-59-0' is missing required entries:" \
  "build/test executor-step count: expected '1', found '0'" \
  "codegen Clippy step is missing '--test codegen'"; do
  if ! grep -Fq "$expected_diagnostic" <<< "$output"; then
    echo "mutation did not produce: $expected_diagnostic" >&2
    echo "$output" >&2
    exit 1
  fi
done
