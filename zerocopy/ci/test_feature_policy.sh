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
cd "$(dirname "$0")/.."

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
  '.default_feature_exists == true' \
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
      stable: ["optional-dependency/serde"],
      "optional-dependency": ["dep:optional-dependency", "extra"],
      extra: []
    },
    optional_dependencies: ["optional-dependency"],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "non-weak forwarding records the local and dependency features" \
  '(.default_closure | sort) ==
    ([
      "dep:optional-dependency",
      "extra",
      "optional-dependency",
      "optional-dependency/serde"
    ] | sort)' \
  "$covered_dependency_policy"
assert_policy \
  "non-weak forwarding follows the dependency local feature" \
  '(.stable_actual | sort) ==
    (["extra", "optional-dependency", "stable"] | sort)' \
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
  '(.default_feature_exists == true) and
    (.default_closure == ["alloc"]) and
    (.default_outside_stable == [])' \
  "$local_feature_policy"

empty_default_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: [],
      stable: []
    },
    optional_dependencies: [],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "an empty default feature still requires a no-default profile" \
  '(.default_feature_exists == true) and
    (.default_closure == []) and
    (.default_outside_stable == []) and
    (.profile_features.default == ["default"]) and
    (.profile_features["no-default"] == [])' \
  "$empty_default_policy"

inactive_weak_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: ["optional-dependency?/serde"],
      stable: ["optional-dependency"],
      "optional-dependency": ["dep:optional-dependency"]
    },
    optional_dependencies: ["optional-dependency"],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "inactive weak forwarding leaves only the default cfg observable" \
  '(.default_feature_exists == true) and
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

no_default_feature_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      stable: ["derive"],
      derive: []
    },
    optional_dependencies: [],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "profiles are explicit when Cargo has no default feature" \
  '(.profile_features.default == []) and
    (.profile_features["no-default"] == []) and
    ((.profile_features.stable | sort) == ["derive", "stable"]) and
    ((.profile_features.all | sort) == ["derive", "stable"])' \
  "$no_default_feature_policy"

transitive_default_policy="$(jq -cn '
  {
    stable_feature: "stable",
    graph: {
      default: ["helper"],
      stable: ["helper"],
      helper: ["derive"],
      derive: []
    },
    optional_dependencies: [],
    nightly: []
  }
' | jq -c -f ./ci/feature_policy.jq)"
assert_policy \
  "default eligibility follows transitive local features" \
  '((.profile_features.default | sort) ==
      ["default", "derive", "helper"]) and
    (.profile_features["no-default"] == []) and
    ((.profile_features.stable | sort) ==
      ["derive", "helper", "stable"])' \
  "$transitive_default_policy"
