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
  # Exercise six independent ownership boundaries in one checker run:
  #
  # - a parsed Cargo test-profile override;
  # - a target added without an executor classification;
  # - exclusions which erase every natively-runnable target;
  # - AArch64-specific toolchains accidentally redirected to ARM32;
  # - removal of the workflow's sole executor bridge; and
  # - removal of dedicated codegen lint ownership.
  #
  # Requiring every diagnostic below is important: the checker accumulates
  # failures, so one early mutation must not mask a later invariant.
  "$ZEROCOPY_CI_CHECK_REAL_YQ" "$@" | jq -c '
    .jobs.build_test.strategy.matrix.target +=
      ["__mutation_unclassified_target__"]
    | .jobs.build_test.strategy.matrix.exclude += [
        {"target": "i686-unknown-linux-gnu"},
        {"target": "x86_64-unknown-linux-gnu"}
      ]
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

# Exercise the feature-policy implementation directly. The main checker feeds
# this same file with real Cargo metadata, so these synthetic graphs can cover
# feature syntax which the repository does not use yet without temporarily
# rewriting Cargo.toml (which would race other hooks or developer commands).
assert_policy() {
  local label="$1"
  local query="$2"
  local policy="$3"
  if ! jq -e "$query" >/dev/null <<< "$policy"; then
    echo "feature-policy assertion failed: $label" >&2
    jq . <<< "$policy" >&2
    exit 1
  fi
}

dependency_default_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: ["dep:optional-dependency"],
      stable: []
    },
    optional_dependencies: ["optional-dependency"],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "dep: default requires a no-default profile" \
  '.default_is_nonempty == true' \
  "$dependency_default_policy"
assert_policy \
  "dep: default must be part of the stable profile" \
  '.default_outside_stable == ["dep:optional-dependency"]' \
  "$dependency_default_policy"

covered_dependency_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: ["optional-dependency/serde"],
      stable: ["optional-dependency/serde"]
    },
    optional_dependencies: ["optional-dependency"],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "non-weak forwarding records activation and dependency feature" \
  '(.default_closure | sort) ==
    (["dep:optional-dependency", "optional-dependency/serde"] | sort)' \
  "$covered_dependency_policy"
assert_policy \
  "stable may intentionally cover a dependency-feature default" \
  '.default_outside_stable == []' \
  "$covered_dependency_policy"

local_feature_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: ["alloc"],
      stable: ["alloc"],
      alloc: []
    },
    optional_dependencies: [],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "ordinary local features remain in the semantic closure" \
  '(.default_is_nonempty == true) and
    (.default_closure == ["alloc"]) and
    (.default_outside_stable == [])' \
  "$local_feature_policy"

inactive_weak_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: ["optional-dependency?/serde"],
      stable: []
    },
    optional_dependencies: ["optional-dependency"],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "weak forwarding without activation has no semantic effect" \
  '(.default_is_nonempty == false) and
    (.default_closure == []) and
    (.default_outside_stable == [])' \
  "$inactive_weak_policy"

active_weak_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: [
        "dep:optional-dependency",
        "optional-dependency?/serde"
      ],
      stable: [
        "dep:optional-dependency",
        "optional-dependency?/serde"
      ]
    },
    optional_dependencies: ["optional-dependency"],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "weak forwarding takes effect after dependency activation" \
  '(.default_closure | sort) ==
    (["dep:optional-dependency", "optional-dependency/serde"] | sort)' \
  "$active_weak_policy"
assert_policy \
  "stable may cover an activated weak dependency feature" \
  '.default_outside_stable == []' \
  "$active_weak_policy"

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
  "post-exclusion runnable build-matrix cells is missing required entries:" \
  "merge_group targets for cross-only toolchain 'no-zerocopy-aarch64-simd-1-59-0' is missing required entries:" \
  "build/test executor-step count: expected '1', found '0'" \
  "codegen Clippy step is missing '--test codegen'"; do
  if ! grep -Fq "$expected_diagnostic" <<< "$output"; then
    echo "mutation did not produce: $expected_diagnostic" >&2
    echo "$output" >&2
    exit 1
  fi
done
