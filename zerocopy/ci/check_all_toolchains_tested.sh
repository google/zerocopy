#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -uo pipefail
cd "$(dirname "$0")/.."

readonly SCRIPT_NAME="ci/check_all_toolchains_tested.sh"
readonly WORKFLOW="../.github/workflows/ci.yml"
readonly STABLE_FEATURE="__internal_use_only_features_that_work_on_stable"
readonly BUILD_TEST_EXECUTOR="./ci/run_build_test_cell.sh"
readonly UI_TEST_CFG="__ZEROCOPY_INTERNAL_USE_ONLY_UI_TEST_TOOLCHAIN"

failed=0

fail() {
  echo "$SCRIPT_NAME: $*" >&2
  failed=1
}

# Treats the two newline-delimited arguments as sets, while separately
# rejecting duplicate entries in the actual value.
check_set() {
  local label="$1"
  local actual="$2"
  local expected="$3"
  local duplicates missing unexpected

  duplicates="$(printf '%s\n' "$actual" | sed '/^$/d' | sort | uniq -d)"
  missing="$(comm -23 \
    <(printf '%s\n' "$expected" | sed '/^$/d' | sort -u) \
    <(printf '%s\n' "$actual" | sed '/^$/d' | sort -u))"
  unexpected="$(comm -13 \
    <(printf '%s\n' "$expected" | sed '/^$/d' | sort -u) \
    <(printf '%s\n' "$actual" | sed '/^$/d' | sort -u))"

  if [[ -n "$duplicates" ]]; then
    fail "$label contains duplicate entries:"
    sed 's/^/  /' <<< "$duplicates" >&2
  fi
  if [[ -n "$missing" ]]; then
    fail "$label is missing required entries:"
    sed 's/^/  /' <<< "$missing" >&2
  fi
  if [[ -n "$unexpected" ]]; then
    fail "$label contains unexpected entries:"
    sed 's/^/  /' <<< "$unexpected" >&2
  fi
}

check_value() {
  local label="$1"
  local actual="$2"
  local expected="$3"
  if [[ "$actual" != "$expected" ]]; then
    fail "$label: expected '$expected', found '$actual'"
  fi
}

# Rustfmt and TOML formatting may move declarations across lines. For a small
# number of cross-file contracts below, compare whitespace-insensitive source
# fragments while still requiring the complete expression which carries the
# policy (not just an easy-to-preserve identifier or comment).
check_compact_source_fragment() {
  local label="$1"
  local file="$2"
  local fragment="$3"
  local compact_source

  if [[ ! -f "$file" ]]; then
    fail "$label: source file '$file' does not exist"
    return
  fi
  compact_source="$(tr -d '[:space:]' < "$file")"
  if ! grep -Fq -- "$fragment" <<< "$compact_source"; then
    fail "$label is missing from $file"
  fi
}

# Verifies the shared setup step structurally, rather than merely finding these
# strings somewhere in the workflow. Both build and Miri jobs must translate
# their semantic profile and compose the nightly-only flags before later steps
# run inside Docker.
check_configure_step() {
  local job="$1"
  local label="$2"
  local count profile_env toolchain_env run

  count="$(jq --arg job "$job" \
    '[.jobs[$job].steps[] | select(.name == "Configure environment variables")] | length' \
    <<< "$workflow_json")"
  check_value "$label Configure-step count" "$count" "1"
  if [[ "$count" != "1" ]]; then
    return
  fi

  profile_env="$(jq -r --arg job "$job" '
    .jobs[$job].steps[]
    | select(.name == "Configure environment variables")
    | .env.FEATURE_PROFILE
  ' <<< "$workflow_json")"
  toolchain_env="$(jq -r --arg job "$job" '
    .jobs[$job].steps[]
    | select(.name == "Configure environment variables")
    | .env.TOOLCHAIN
  ' <<< "$workflow_json")"
  run="$(jq -r --arg job "$job" '
    .jobs[$job].steps[]
    | select(.name == "Configure environment variables")
    | .run
  ' <<< "$workflow_json")"

  check_value "$label Configure-step FEATURE_PROFILE" "$profile_env" '${{ matrix.feature_profile }}'
  check_value "$label Configure-step TOOLCHAIN" "$toolchain_env" '${{ matrix.toolchain }}'

  local required_line
  for required_line in \
    'FEATURES="$(./ci/feature_profile.sh "$FEATURE_PROFILE")"' \
    'echo "FEATURES=$FEATURES" >> $GITHUB_ENV' \
    'RUSTFLAGS="$RUSTFLAGS $ZC_NIGHTLY_RUSTFLAGS"' \
    'MIRIFLAGS="$MIRIFLAGS $ZC_NIGHTLY_MIRIFLAGS"' \
    'echo "RUSTFLAGS=$RUSTFLAGS" >> $GITHUB_ENV' \
    'echo "MIRIFLAGS=$MIRIFLAGS" >> $GITHUB_ENV'; do
    if ! grep -Fq "$required_line" <<< "$run"; then
      fail "$label Configure step is missing: $required_line"
    fi
  done
}

for command in cargo comm find grep jq sed sort tr uniq wc yq; do
  command -v "$command" >/dev/null || fail "required command '$command' was not found"
done
if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

# Exercise feature syntaxes which the current manifest does not use. Keep this
# before the repository-specific checks so the policy implementation cannot
# silently lose forward compatibility while today's feature graph still passes.
if ! ./ci/test_feature_policy.sh; then
  fail "feature-policy regression tests failed"
  exit 1
fi

# Python yq and Go yq intentionally have different expression languages. Use
# each only as a YAML-to-JSON adapter, then apply all policy queries with jq so
# this guard behaves identically in developer environments and CI.
if yq --version 2>&1 | grep -qi mikefarah; then
  YQ_IMPLEMENTATION=go
  if ! workflow_json="$(yq -o=json -I=0 '.' "$WORKFLOW")"; then
    fail "could not parse $WORKFLOW with Go yq"
    exit 1
  fi
else
  YQ_IMPLEMENTATION=python
  if ! workflow_json="$(yq -c '.' "$WORKFLOW")"; then
    fail "could not parse $WORKFLOW with Python yq"
    exit 1
  fi
  if ! command -v tomlq >/dev/null; then
    fail "Python yq is installed without its tomlq companion"
    exit 1
  fi
fi
readonly YQ_IMPLEMENTATION
if ! jq -e . >/dev/null <<< "$workflow_json"; then
  fail "$WORKFLOW did not convert to valid JSON"
  exit 1
fi

# Use the matching yq distribution as a TOML-to-JSON adapter too. Parsing is
# important here: TOML permits quoted keys, dotted keys, inline tables, and
# whitespace variants which a source grep cannot soundly recognize.
toml_to_json() {
  if [[ "$YQ_IMPLEMENTATION" == "go" ]]; then
    yq -p=toml -o=json -I=0 '.' "$1"
  else
    tomlq -c '.' "$1"
  fi
}

# Use the same stable Cargo wrapper as the rest of CI. In particular, do not
# inspect `resolve.nodes[].features`: workspace feature unification can make
# that report features enabled by another workspace member. The per-package
# `features` tables below describe the manifest feature graphs themselves.
if ! metadata="$(./cargo.sh +stable metadata --quiet --locked --offline --no-deps --format-version 1)"; then
  fail "cargo metadata failed"
  exit 1
fi

zerocopy_count="$(jq '[.packages[] | select(.name == "zerocopy")] | length' <<< "$metadata")"
derive_count="$(jq '[.packages[] | select(.name == "zerocopy-derive")] | length' <<< "$metadata")"
check_value "zerocopy package count" "$zerocopy_count" "1"
check_value "zerocopy-derive package count" "$derive_count" "1"
if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

zerocopy_package="$(jq -c '.packages[] | select(.name == "zerocopy")' <<< "$metadata")"
derive_package="$(jq -c '.packages[] | select(.name == "zerocopy-derive")' <<< "$metadata")"
feature_graph="$(jq -c '.features' <<< "$zerocopy_package")"
derive_feature_graph="$(jq -c '.features' <<< "$derive_package")"
optional_dependencies_json="$(jq -c \
  '[.dependencies[] | select(.optional) | (.rename // .name)] | unique' \
  <<< "$zerocopy_package")"

nightly_type="$(jq -r '.metadata.ci["nightly-features"] | type' <<< "$zerocopy_package")"
unsupported_type="$(jq -r '.metadata.ci["miri-unsupported-targets"] | type' <<< "$zerocopy_package")"
check_value "package.metadata.ci.nightly-features type" "$nightly_type" "array"
check_value "package.metadata.ci.miri-unsupported-targets type" "$unsupported_type" "array"
if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

nightly_features_json="$(jq -c '.metadata.ci["nightly-features"]' <<< "$zerocopy_package")"
unsupported_targets_json="$(jq -c '.metadata.ci["miri-unsupported-targets"]' <<< "$zerocopy_package")"
nightly_features="$(jq -r '.[]' <<< "$nightly_features_json")"
unsupported_targets="$(jq -r '.[]' <<< "$unsupported_targets_json")"
check_set "nightly feature exceptions" "$nightly_features" "$nightly_features"
check_set "Miri-unsupported targets" "$unsupported_targets" "$unsupported_targets"

# Keep the feature-closure semantics in one executable policy so synthetic
# regression tests exercise the exact logic used here. In particular, the
# policy tracks dependency activations and forwarded dependency features in
# addition to local feature names; see feature_policy.jq for why those effects
# are part of the stable-vs-default contract.
if ! feature_policy="$(jq -cn \
  --arg stable_feature "$STABLE_FEATURE" \
  --argjson graph "$feature_graph" \
  --argjson optional_dependencies "$optional_dependencies_json" \
  --argjson nightly "$nightly_features_json" '
    {
      stable_feature: $stable_feature,
      graph: $graph,
      optional_dependencies: $optional_dependencies,
      nightly: $nightly
    }
  ' | jq -c -f ./ci/feature_policy.jq)"; then
  fail "could not derive the Cargo feature policy"
  exit 1
fi

if [[ "$(jq -r '.stable_feature_exists' <<< "$feature_policy")" != "true" ]]; then
  fail "Cargo.toml does not define the '$STABLE_FEATURE' feature"
fi
nightly_unknown="$(jq -r '.nightly_unknown[]' <<< "$feature_policy")"
if [[ -n "$nightly_unknown" ]]; then
  fail "nightly-features names features which Cargo.toml does not define:"
  sed 's/^/  /' <<< "$nightly_unknown" >&2
fi
if [[ "$(jq -r '.nightly_default_entry' <<< "$feature_policy")" == "true" ]]; then
  fail "the special Cargo 'default' feature cannot be a nightly feature exception"
fi

stable_actual="$(jq -r '.stable_actual[]' <<< "$feature_policy")"
stable_expected="$(jq -r '.stable_expected[]' <<< "$feature_policy")"
check_set "stable feature closure" "$stable_actual" "$stable_expected"

default_nightly="$(jq -r '.default_nightly[]' <<< "$feature_policy")"
if [[ -n "$default_nightly" ]]; then
  fail "Cargo default features transitively enable nightly-only features:"
  sed 's/^/  /' <<< "$default_nightly" >&2
fi
default_outside_stable="$(jq -r '.default_outside_stable[]' <<< "$feature_policy")"
if [[ -n "$default_outside_stable" ]]; then
  fail "Cargo default feature closure is not a subset of the stable feature closure:"
  sed 's/^/  /' <<< "$default_outside_stable" >&2
fi

# The cross-workspace UI runner currently forwards the outer CLI feature
# selection directly to its nested zerocopy artifact build. That is exact while
# zerocopy-derive has no feature axis. A future derive feature needs an explicit
# mapping policy here and in that protocol, not merely another matrix exclusion.
derive_features="$(jq -r 'keys[]' <<< "$derive_feature_graph")"
if [[ -n "$derive_features" ]]; then
  fail "zerocopy-derive now defines features; update the matrix and cross-workspace UI feature-forwarding policies:"
  sed 's/^/  /' <<< "$derive_features" >&2
fi

expected_profiles=$'default\nstable\nall'
if [[ "$(jq -r '.default_feature_exists' <<< "$feature_policy")" == "true" ]]; then
  expected_profiles+=$'\nno-default'
fi
# Target policy needs to know which semantic profiles transitively enable std,
# not merely today's profile names. Keep that answer derived from the same
# Cargo feature closure which defines the profiles above, so a future default
# or stable feature change automatically updates both the exclusion audit and
# the exact matrix-cell specification below.
std_profiles_json="$(jq -cn --argjson policy "$feature_policy" '[
  if $policy.default_enables_std then "default" else empty end,
  if $policy.stable_enables_std then "stable" else empty end,
  if $policy.std_feature_exists then "all" else empty end
]')"

# A runnable matrix cell relies on Cargo's *default* `cargo test` selection to
# replace three formerly-separate passes. Keep the Cargo-side half of that
# contract fail-closed. In particular:
#
# - library unit tests and doctests must remain enabled;
# - each matrix-owned package must retain a default-selected integration test,
#   which links the ordinary non-cfg(test) library in every native profile;
# - every integration-test source which Cargo would conventionally discover
#   must actually appear in metadata (this catches `autotests = false` and
#   accidental target-path changes); and
# - opting a target out with `test = false` is an ownership transfer, not a way
#   to silently lose it. The dedicated codegen job is currently the sole such
#   owner and is checked against the workflow below.
for package_name in zerocopy zerocopy-derive; do
  package="$(jq -c --arg package "$package_name" \
    '.packages[] | select(.name == $package)' <<< "$metadata")"
  library_count="$(jq '[
    .targets[]
    | select(
        (.kind | index("lib")) != null
        or (.kind | index("proc-macro")) != null
      )
  ] | length' <<< "$package")"
  check_value "$package_name library-target count" "$library_count" "1"

  disabled_library_tests="$(jq -r '
    .targets[]
    | select(
        (.kind | index("lib")) != null
        or (.kind | index("proc-macro")) != null
      )
    | select(.test != true)
    | .name
  ' <<< "$package")"
  if [[ -n "$disabled_library_tests" ]]; then
    fail "$package_name disables its library test harness:"
    sed 's/^/  /' <<< "$disabled_library_tests" >&2
  fi

  disabled_doctests="$(jq -r '
    .targets[]
    | select(
        (.kind | index("lib")) != null
        or (.kind | index("proc-macro")) != null
      )
    | select(.doctest != true)
    | .name
  ' <<< "$package")"
  if [[ -n "$disabled_doctests" ]]; then
    fail "$package_name disables library doctests:"
    sed 's/^/  /' <<< "$disabled_doctests" >&2
  fi

  always_selected_integration_test_count="$(jq '[
    .targets[]
    | select(
        (.kind | index("test")) != null
        and .test == true
        and ((.["required-features"] // []) | length) == 0
      )
  ] | length' <<< "$package")"
  if [[ "$always_selected_integration_test_count" -eq 0 ]]; then
    fail "$package_name has no default-selected integration test to link its ordinary library"
  fi
done

disabled_integration_tests="$(jq -r '
  .packages[]
  | select(.name == "zerocopy" or .name == "zerocopy-derive")
  | .name as $package
  | .targets[]
  | select((.kind | index("test")) != null and .test != true)
  | "\($package)/\(.name)"
' <<< "$metadata")"
check_set "dedicated integration-test targets" \
  "$disabled_integration_tests" "zerocopy/codegen"

# Cargo auto-discovers `tests/foo.rs` and `tests/foo/main.rs`. Comparing those
# paths with metadata is stronger than merely checking today's target names: a
# new conventional test is covered automatically, while disabling discovery
# or redirecting an explicit target fails here until CI ownership is revisited.
filesystem_test_sources="$({
  find tests -mindepth 1 -maxdepth 1 -type f -name '*.rs' -print
  find tests -mindepth 2 -maxdepth 2 -type f -name main.rs -print
  find zerocopy-derive/tests -mindepth 1 -maxdepth 1 -type f -name '*.rs' -print
  find zerocopy-derive/tests -mindepth 2 -maxdepth 2 -type f -name main.rs -print
} | sed 's#^\./##')"
metadata_test_sources="$(jq -r '
  .packages[]
  | select(.name == "zerocopy" or .name == "zerocopy-derive")
  | .targets[]
  | select((.kind | index("test")) != null)
  | .src_path
' <<< "$metadata" | sed "s#^$PWD/##")"
check_set "Cargo integration-test source discovery" \
  "$metadata_test_sources" "$filesystem_test_sources"

# `cargo test` uses the test profile while the eliminated `cargo build` used
# the dev profile. Cargo's test profile inherits dev in the absence of an
# override, which is the equivalence this optimization relies on. Cargo reads
# both config filenames from the invocation directory and every ancestor. The
# matrix invokes Cargo from this workspace root, so inspect every
# repository-controlled location on that search path, including currently
# absent files. Keep this list coordinated with the `working-directory` in
# ci.yml; moving the invocation changes which Cargo config files are effective.
cargo_profile_sources=(
  Cargo.toml
  .cargo/config
  .cargo/config.toml
  ../.cargo/config
  ../.cargo/config.toml
)
for profile_override_source in "${cargo_profile_sources[@]}"; do
  [[ -f "$profile_override_source" ]] || continue
  if ! profile_source_json="$(toml_to_json "$profile_override_source")"; then
    fail "could not parse $profile_override_source while checking Cargo profiles"
    continue
  fi
  if jq -e '.profile | type == "object" and has("test")' \
      >/dev/null <<< "$profile_source_json"; then
    fail "$profile_override_source overrides profile.test; re-audit the single-pass native test contract"
  fi
done

# Environment variables override both manifests and Cargo config. Check every
# repository-controlled source which can set the matrix process environment:
# the workflow (including its generated Docker wrapper), the image definition,
# and the two wrappers on the path to pinned Cargo. If that launch chain gains
# another layer, add it here in the same change.
for profile_override_source in \
  "$WORKFLOW" \
  ../.github/workflows/Dockerfile \
  cargo.sh \
  "$BUILD_TEST_EXECUTOR" \
  ../tools/cargo-zerocopy/src/main.rs; do
  if [[ -f "$profile_override_source" ]] && \
      grep -Eq 'CARGO_PROFILE_TEST_[A-Z0-9_]+' "$profile_override_source"; then
    fail "$profile_override_source sets a test-profile override; re-audit the single-pass native test contract"
  fi
done

# The Docker image can also acquire a global Cargo config indirectly (for
# example, from its base image or a RUN command). The executor performs the
# final runtime check inside that image. Pin the meaningful source fragments so
# refactoring the helper cannot silently discard either the config-file or
# environment half of this cross-file profile contract.
check_compact_source_fragment \
  "CI Cargo-home config guard" \
  "$BUILD_TEST_EXECUTOR" \
  'forconfigin"$cargo_home/config""$cargo_home/config.toml";do'
check_compact_source_fragment \
  "CI test-profile environment guard" \
  "$BUILD_TEST_EXECUTOR" \
  'case"$environment_name"inCARGO_PROFILE_TEST_*)fail'
check_compact_source_fragment \
  "CI test-profile guard invocation" \
  "$BUILD_TEST_EXECUTOR" \
  'if[["$PLAN_ONLY"-eq0]];thencheck_ci_test_profile_contractfi'

# The semantic profile helper is the single translation point from matrix
# policy to Cargo arguments. Exercise every supported mapping, including the
# currently-redundant no-default profile, and require unknown inputs to fail.
if [[ ! -x ./ci/feature_profile.sh ]]; then
  fail "ci/feature_profile.sh is not executable"
else
  for profile in default no-default stable all; do
    case "$profile" in
      default) expected_args="" ;;
      no-default) expected_args="--no-default-features" ;;
      stable) expected_args="--no-default-features --features $STABLE_FEATURE" ;;
      all) expected_args="--all-features" ;;
    esac
    if ! actual_args="$(./ci/feature_profile.sh "$profile")"; then
      fail "ci/feature_profile.sh rejected the supported '$profile' profile"
    else
      check_value "arguments for feature profile '$profile'" "$actual_args" "$expected_args"
    fi
  done
  if ./ci/feature_profile.sh __invalid_ci_profile__ >/dev/null 2>&1; then
    fail "ci/feature_profile.sh accepted an unknown profile"
  fi
fi

# Retain the original toolchain guard: every build.rs threshold toolchain must
# be present in the build matrix, and there must be no stale matrix entries.
build_toolchains="$(jq -r '.jobs.build_test.strategy.matrix.toolchain[]' <<< "$workflow_json")"
threshold_toolchains="$(printf '%s\n' "$build_toolchains" | grep -v -E '^(msrv|stable|nightly)$' || true)"
metadata_toolchains="$(jq -r '.metadata["build-rs"] | keys[]' <<< "$zerocopy_package")"
expected_build_toolchains=$'msrv\nstable\nnightly'
if [[ -n "$metadata_toolchains" ]]; then
  expected_build_toolchains+=$'\n'"$metadata_toolchains"
fi
check_set "build toolchains" "$build_toolchains" "$expected_build_toolchains"
check_set "build.rs threshold toolchains" "$threshold_toolchains" "$metadata_toolchains"

# The two build crates share semantic feature profiles. zerocopy-derive has no
# features, so every non-default profile must be excluded for that crate.
build_matrix_keys="$(jq -r '.jobs.build_test.strategy.matrix | keys[]' <<< "$workflow_json")"
check_set "build matrix axes" "$build_matrix_keys" $'crate\nevent_name\nexclude\nfeature_profile\ntarget\ntoolchain'

build_profiles="$(jq -r '.jobs.build_test.strategy.matrix.feature_profile[]' <<< "$workflow_json")"
build_crates="$(jq -r '.jobs.build_test.strategy.matrix.crate[]' <<< "$workflow_json")"
build_targets="$(jq -r '.jobs.build_test.strategy.matrix.target[]' <<< "$workflow_json")"
build_event_names="$(jq -r '.jobs.build_test.strategy.matrix.event_name[]' <<< "$workflow_json")"
workflow_events="$(jq -r '.on | keys[]' <<< "$workflow_json")"
check_set "build feature profiles" "$build_profiles" "$expected_profiles"
check_set "build crates" "$build_crates" $'zerocopy\nzerocopy-derive'
# The exact-cell audit below expands every workflow trigger. Assert that set
# independently first: deriving both actual and expected cells from `.on`
# without this boundary would let deletion of merge_group silently delete all
# merge-queue coverage from both sides of the comparison.
check_set "workflow triggers" "$workflow_events" \
  $'merge_group\npull_request\npush\nworkflow_dispatch'
if jq -e '.jobs.build_test | has("if") or has("continue-on-error")' \
    >/dev/null <<< "$workflow_json"; then
  fail "the build_test job must run and propagate failures for every workflow event"
fi

# An exclusion with an unknown key or value is accepted by GitHub but matches
# no cells, which makes a typo look like policy. Validate each exclusion against
# the real matrix axes and workflow trigger names before evaluating it. The
# sorted JSON self-comparison separately rejects duplicate exclusions.
invalid_build_exclusions="$(jq -c --argjson workflow "$workflow_json" '
  def value_is_on_axis($matrix; $events):
    .key as $key
    | .value as $value
    | if $key == "event_name"
      then ($events | index($value)) != null
      else ($matrix[$key] | index($value)) != null
      end;
  $workflow.jobs.build_test.strategy.matrix as $matrix
  | ($workflow.on | keys) as $events
  | $matrix.exclude[]
  | select(
      (type != "object")
      or length == 0
      or ((keys - [
        "crate", "event_name", "feature_profile", "target", "toolchain"
      ]) | length) != 0
      or any(to_entries[];
        (.value | type) != "string"
        or (value_is_on_axis($matrix; $events) | not)
      )
    )
' <<< '{}')"
if [[ -n "$invalid_build_exclusions" ]]; then
  fail "build matrix has exclusions with unknown keys or values:"
  sed 's/^/  /' <<< "$invalid_build_exclusions" >&2
fi
build_exclusions="$(jq -cS \
  '.jobs.build_test.strategy.matrix.exclude[]' <<< "$workflow_json")"
check_set "build matrix exclusions" "$build_exclusions" "$build_exclusions"

# Every workspace package needs an explicit CI owner. The build matrix owns the
# two publishable packages. `testutil` is a dev-only harness exercised through
# those packages and directly by the support-code step checked below, so its
# exemption from the cross-target matrix is intentional. A new workspace
# member fails until its owner is recorded.
workspace_packages="$(jq -r '
  .workspace_members[] as $id
  | .packages[]
  | select(.id == $id)
  | .name
' <<< "$metadata")"
expected_workspace_packages="$build_crates"$'\n'"testutil"
check_set "workspace package CI ownership" \
  "$workspace_packages" "$expected_workspace_packages"

# The feature-forwarding protocol crosses Cargo workspaces, so compiling the
# publishable packages does not execute either side's unit tests. Keep the two
# cheap suites immediately after this invariant checker in the same job: the
# checker proves the ownership exists, then CI exercises the implementation.
support_test_step_count="$(jq '[
  .jobs["check-all-toolchains-tested"].steps[]
  | select(.name == "Test CI support code")
] | length' <<< "$workflow_json")"
check_value "CI support-code test-step count" "$support_test_step_count" "1"
if [[ "$support_test_step_count" == "1" ]]; then
  support_test_step="$(jq -c '
    .jobs["check-all-toolchains-tested"].steps[]
    | select(.name == "Test CI support code")
  ' <<< "$workflow_json")"
  check_set "CI support-code test-step keys" \
    "$(jq -r 'keys[]' <<< "$support_test_step")" $'name\nrun'
  check_value "CI support-code test commands" \
    "$(jq -r '.run' <<< "$support_test_step")" \
    $'(cd zerocopy && ./cargo.sh +stable test --package testutil)\n# cargo.sh delegates from zerocopy/, whose vendor excludes the tools\n# workspace.\nTOOLS_STABLE="$(zerocopy/cargo.sh --version stable)"\ncargo +"$TOOLS_STABLE" test --locked --manifest-path tools/cargo-zerocopy/Cargo.toml\n(cd zerocopy && ./ci/test_check_all_toolchains_tested.sh)'

  support_test_previous_step="$(jq -r '
    .jobs["check-all-toolchains-tested"].steps
    | (map(.name) | index("Test CI support code")) as $index
    | if $index == null or $index == 0
      then ""
      else .[$index - 1].name
      end
  ' <<< "$workflow_json")"
  check_value "step before CI support-code tests" \
    "$support_test_previous_step" "Run check"
fi

# Cargo silently omits a target whose `required-features` are not enabled.
# Prove from manifest metadata that every integration test can be selected by
# at least one semantically-owned feature profile. The post-exclusion expansion
# below independently proves that every such profile has native execution
# cells. Together, those checks prevent either required-feature drift or matrix
# exclusions from making a test unreachable. Derive's only owned profile is
# `default`; zerocopy's sets use the feature graph audited above.
zerocopy_profile_features="$(jq -c '.profile_features' <<< "$feature_policy")"
derive_profile_features='{"default":[]}'

while IFS=$'\t' read -r package_name target_name required_features_json; do
  [[ -n "$package_name" ]] || continue
  case "$package_name" in
    zerocopy)
      package_feature_graph="$feature_graph"
      package_profile_features="$zerocopy_profile_features"
      package_profiles="$build_profiles"
      ;;
    zerocopy-derive)
      package_feature_graph="$derive_feature_graph"
      package_profile_features="$derive_profile_features"
      package_profiles="default"
      ;;
  esac

  unknown_required_features="$(jq -r \
    --argjson required "$required_features_json" \
    --argjson graph "$package_feature_graph" '
      ($required - ($graph | keys) | unique)[]
    ' <<< '{}')"
  if [[ -n "$unknown_required_features" ]]; then
    fail "$package_name/$target_name requires unknown Cargo features:"
    sed 's/^/  /' <<< "$unknown_required_features" >&2
  fi

  reachable_profile=""
  while IFS= read -r profile; do
    [[ -n "$profile" ]] || continue
    enabled_features="$(jq -c --arg profile "$profile" \
      '.[$profile] // []' <<< "$package_profile_features")"
    if jq -en \
        --argjson required "$required_features_json" \
        --argjson enabled "$enabled_features" \
        '($required - $enabled | length) == 0' >/dev/null; then
      reachable_profile="$profile"
      break
    fi
  done <<< "$package_profiles"
  if [[ -z "$reachable_profile" ]]; then
    fail "$package_name/$target_name is unreachable from every runnable feature profile (requires $required_features_json)"
  fi
done < <(jq -r '
  .packages[]
  | select(.name == "zerocopy" or .name == "zerocopy-derive")
  | .name as $package
  | .targets[]
  | select((.kind | index("test")) != null)
  | [$package, .name, ((.["required-features"] // []) | tojson)]
  | @tsv
' <<< "$metadata")

# Cargo owns UI-target selection through `required-features`. Pin the exact
# requirement here so deleting or changing it cannot compile an empty target
# or silently remove the harness from every semantic profile.
zerocopy_ui_required_features="$(jq -r '
  .packages[]
  | select(.name == "zerocopy")
  | .targets[]
  | select((.kind | index("test")) != null and .name == "ui")
  | (.["required-features"] // [])[]
' <<< "$metadata")"
check_set "zerocopy UI-test required features" \
  "$zerocopy_ui_required_features" "derive"

# Self-comparison intentionally checks for duplicate targets while allowing the
# build matrix itself to remain the source of truth for the supported set.
check_set "build targets" "$build_targets" "$build_targets"
check_set "build event-name axis" "$build_event_names" '${{ github.event_name }}'
check_configure_step "build_test" "build"

# The workflow deliberately delegates every build-matrix cell to one executor.
# Its machine-readable description is the source used by the executor itself,
# while this checker supplies an independent audit boundary: every workflow
# target must be classified exactly once, and changing the strength assigned to
# any existing target requires updating this explicit policy review point.
executor_ready=1
if [[ ! -x "$BUILD_TEST_EXECUTOR" ]]; then
  fail "$BUILD_TEST_EXECUTOR is not executable"
  executor_ready=0
elif ! executor_description="$($BUILD_TEST_EXECUTOR --describe)"; then
  fail "$BUILD_TEST_EXECUTOR --describe failed"
  executor_ready=0
elif ! jq -e '
  (keys | sort) == ["schema_version", "targets"]
  and .schema_version == 1
  and (.targets | type) == "array"
  and all(.targets[];
    (keys | sort) == ["mode", "target"]
    and (.target | type) == "string"
    and (.target | length) > 0
    and (.mode | type) == "string"
  )
' >/dev/null <<< "$executor_description"; then
  fail "$BUILD_TEST_EXECUTOR --describe returned an invalid schema"
  executor_ready=0
fi

if [[ "$executor_ready" -eq 1 ]]; then
  described_targets="$(jq -r '.targets[].target' <<< "$executor_description")"
  described_modes="$(jq -r '.targets[].mode' <<< "$executor_description")"
  check_set "build/test executor targets" "$described_targets" "$build_targets"
  check_set "build/test executor modes" \
    "$(sort -u <<< "$described_modes")" \
    $'run\ncompile-tests\nlibrary-only'

  run_targets="$(jq -r '.targets[] | select(.mode == "run") | .target' \
    <<< "$executor_description")"
  compile_test_targets="$(jq -r '
    .targets[] | select(.mode == "compile-tests") | .target
  ' <<< "$executor_description")"
  library_only_targets="$(jq -r '
    .targets[] | select(.mode == "library-only") | .target
  ' <<< "$executor_description")"
  check_set "natively runnable targets" "$run_targets" \
    $'i686-unknown-linux-gnu\nx86_64-unknown-linux-gnu'
  check_set "cross-compiled test targets" "$compile_test_targets" \
    $'arm-unknown-linux-gnueabi\naarch64-unknown-linux-gnu\npowerpc-unknown-linux-gnu\npowerpc64-unknown-linux-gnu\nriscv64gc-unknown-linux-gnu\ns390x-unknown-linux-gnu\nx86_64-pc-windows-msvc\nwasm32-unknown-unknown'
  check_set "library-only targets" "$library_only_targets" \
    "thumbv6m-none-eabi"

  # Expand the matrix exactly as GitHub does, once for every event which can
  # trigger this workflow, and apply *every* exclusion key. Axis membership is
  # not enough: two target-only exclusions could otherwise leave all profiles
  # visible in YAML while silently removing every executable test cell.
  #
  # The executor description supplies the target mode. This is a deliberate
  # three-file contract among ci.yml, run_build_test_cell.sh, and this checker:
  # changing an axis, exclusion, or target classification changes this final
  # cell set and must continue to satisfy the coverage assertions below.
  final_build_cells="$(jq -cn \
    --argjson workflow "$workflow_json" \
    --argjson executor "$executor_description" '
      def excluded($cell; $exclusion):
        all($exclusion | to_entries[];
          . as $entry | $cell[$entry.key] == $entry.value);

      $workflow.jobs.build_test.strategy.matrix as $matrix
      | ($workflow.on | keys) as $events
      | [
          $events[] as $event_name
          | $matrix.toolchain[] as $toolchain
          | $matrix.target[] as $target
          | $matrix.feature_profile[] as $feature_profile
          | $matrix.crate[] as $crate
          | {
              event_name: $event_name,
              toolchain: $toolchain,
              target: $target,
              feature_profile: $feature_profile,
              crate: $crate
            } as $cell
          | select(any($matrix.exclude[]; excluded($cell; .)) | not)
          | $cell + {
              mode: (
                $executor.targets[]
                | select(.target == $target)
                | .mode
              )
            }
        ]
    ')"

  # Most threshold toolchains describe language/library behavior which can be
  # exercised on a native runner. These two specifically describe AArch64 SIMD
  # behavior, so they are the only reviewed cross-only exceptions. Three other
  # thresholds are deliberately native-only because their behavior is target
  # independent. Every other current or future threshold is full-target by
  # default. Changing either exception list is therefore an explicit review of
  # less-than-full target coverage, rather than an exclusion which can silently
  # weaken CI.
  cross_only_toolchains=$'no-zerocopy-aarch64-simd-1-59-0\nno-zerocopy-aarch64-simd-be-1-87-0'
  native_only_toolchains=$'no-zerocopy-core-error-1-81-0\nno-zerocopy-diagnostic-on-unimplemented-1-78-0\nno-zerocopy-generic-bounds-in-const-fn-1-61-0'
  target_exception_toolchains="$cross_only_toolchains"$'\n'"$native_only_toolchains"
  # These lists must be duplicate-free, mutually disjoint, and drawn from the
  # live Cargo-derived build toolchains. Otherwise a renamed/removed threshold
  # could leave behind a stale exception which appears to document policy but
  # no longer constrains any matrix cell.
  check_set "target-coverage exception toolchains" \
    "$target_exception_toolchains" "$target_exception_toolchains"
  unknown_target_exception_toolchains="$(comm -13 \
    <(printf '%s\n' "$build_toolchains" | sed '/^$/d' | sort -u) \
    <(printf '%s\n' "$target_exception_toolchains" | sed '/^$/d' | sort -u))"
  if [[ -n "$unknown_target_exception_toolchains" ]]; then
    fail "target-coverage exceptions name unknown build toolchains:"
    sed 's/^/  /' <<< "$unknown_target_exception_toolchains" >&2
  fi
  for cross_only_toolchain in $cross_only_toolchains; do
    # These descriptors bracket AArch64-specific compiler behavior. Merely
    # retaining some cross target is insufficient: an exclusion typo could
    # leave ARM32 or x86 coverage while dropping the AArch64 configuration the
    # descriptor exists to test. PRs deliberately omit this expensive target;
    # every full event must retain exactly AArch64.
    while IFS= read -r workflow_event; do
      [[ "$workflow_event" == "pull_request" ]] && continue
      cross_only_targets="$(jq -r \
        --arg event "$workflow_event" \
        --arg toolchain "$cross_only_toolchain" '[
          .[]
          | select(
              .event_name == $event
              and .toolchain == $toolchain
            )
          | .target
        ] | unique[]' <<< "$final_build_cells")"
      check_set \
        "$workflow_event targets for cross-only toolchain '$cross_only_toolchain'" \
        "$cross_only_targets" \
        "aarch64-unknown-linux-gnu"
    done < <(jq -r '.on | keys[]' <<< "$workflow_json")
  done

  # Require the complete reviewed event x crate x toolchain x profile x target
  # product after exclusions. Derive owns only its default profile on the three
  # general toolchains. Zerocopy owns every semantic profile, except that a
  # non-empty nightly feature set restricts `all` to nightly. Full events cover
  # every target by default; PRs retain the two native targets plus the cheap
  # Windows cross-check. The explicit exceptions below mirror reasons which
  # cannot be inferred mechanically: unavailable stable wasm, thumb's lack of
  # std, and the reviewed native-only/cross-only threshold classes above.
  #
  # This is intentionally independent of ci.yml's exclusion list. That file is
  # the mechanism which realizes the policy, while this block is the fail-closed
  # specification which reviews it. A future exclusion, toolchain, target,
  # feature profile, or default-feature change must either preserve this full
  # product or update the relevant exception here with an explanation.
  workflow_events_json="$(jq -c '.on | keys' <<< "$workflow_json")"
  cross_only_toolchains_json="$(printf '%s\n' "$cross_only_toolchains" | \
    jq -Rsc 'split("\n") | map(select(length != 0))')"
  native_only_toolchains_json="$(printf '%s\n' "$native_only_toolchains" | \
    jq -Rsc 'split("\n") | map(select(length != 0))')"
  run_targets_json="$(printf '%s\n' "$run_targets" | \
    jq -Rsc 'split("\n") | map(select(length != 0))')"
  build_profiles_json="$(printf '%s\n' "$expected_profiles" | \
    jq -Rsc 'split("\n") | map(select(length != 0))')"
  build_toolchains_json="$(printf '%s\n' "$build_toolchains" | \
    jq -Rsc 'split("\n") | map(select(length != 0))')"
  build_targets_json="$(printf '%s\n' "$build_targets" | \
    jq -Rsc 'split("\n") | map(select(length != 0))')"
  expected_build_cells="$(jq -rn \
    --argjson events "$workflow_events_json" \
    --argjson toolchains "$build_toolchains_json" \
    --argjson run_targets "$run_targets_json" \
    --argjson all_targets "$build_targets_json" \
    --argjson profiles "$build_profiles_json" \
    --argjson cross_only "$cross_only_toolchains_json" \
    --argjson native_only "$native_only_toolchains_json" \
    --argjson std_profiles "$std_profiles_json" \
    --argjson nightly_features "$nightly_features_json" '
      [
        $events[] as $event
        | $toolchains[] as $toolchain
        | $all_targets[] as $target
        | $profiles[] as $profile
        | ["zerocopy", "zerocopy-derive"][] as $crate
        | select(
            if ($cross_only | index($toolchain)) != null then
              $target == "aarch64-unknown-linux-gnu"
            elif ($native_only | index($toolchain)) != null then
              ($run_targets | index($target)) != null
            else
              true
            end
          )
        | select(
            $event != "pull_request"
            or (($run_targets + ["x86_64-pc-windows-msvc"]) | index($target)) != null
          )
        | select(
            $toolchain != "stable"
            or $target != "wasm32-unknown-unknown"
          )
        | select(
            if $crate == "zerocopy-derive" then
              $profile == "default"
              and (["msrv", "stable", "nightly"] | index($toolchain)) != null
            else
              $profile != "all"
              or ($nightly_features | length) == 0
              or $toolchain == "nightly"
            end
          )
        | select(
            $target != "thumbv6m-none-eabi"
            or $crate != "zerocopy"
            or ($std_profiles | index($profile)) == null
          )
        | [$event, $crate, $toolchain, $profile, $target]
        | @tsv
      ]
      | unique[]
    ')"
  actual_build_cells="$(jq -r '[
    .[]
    | [
        .event_name,
        .crate,
        .toolchain,
        .feature_profile,
        .target
      ]
    | @tsv
  ] | unique[]' <<< "$final_build_cells")"
  check_set "post-exclusion build-matrix cells" \
    "$actual_build_cells" "$expected_build_cells"

  # `--plan` records the exact argv arrays assembled by the real execution
  # path. Compare the whole JSON object, not substrings: this proves that native
  # cells use Cargo's unfiltered default target selection, cross cells retain
  # `check --tests` plus code generation, and thumb retains its narrower check.
  # It also forbids a future positional test-name filter, `--skip`, `--lib`, or
  # another target selector from hiding newly-added tests.
  while IFS= read -r target; do
    mode="$(jq -r --arg target "$target" '
      .targets[] | select(.target == $target) | .mode
    ' <<< "$executor_description")"
    for crate in zerocopy zerocopy-derive; do
      if [[ "$crate" == "zerocopy-derive" ]]; then
        plan_profiles="default"
      else
        plan_profiles="$expected_profiles"
      fi
      while IFS= read -r profile; do
        [[ -n "$profile" ]] || continue
        if [[ "$profile" == "all" ]]; then
          plan_toolchain="nightly"
        else
          plan_toolchain="msrv"
        fi

        feature_output="$(./ci/feature_profile.sh "$profile")"
        feature_args_json='[]'
        if [[ -n "$feature_output" ]]; then
          read -r -a feature_args <<< "$feature_output"
          feature_args_json="$(jq -cn --args '$ARGS.positional' -- \
            "${feature_args[@]}")"
        fi

        case "$mode" in
          run)
            expected_commands="$(jq -cn \
              --arg toolchain "+$plan_toolchain" \
              --arg crate "$crate" \
              --arg target "$target" \
              --argjson features "$feature_args_json" '
                [["./cargo.sh", $toolchain, "test",
                  "--package", $crate, "--target", $target]
                  + $features + ["--verbose"]]
              ')"
            ;;
          compile-tests)
            expected_commands="$(jq -cn \
              --arg toolchain "+$plan_toolchain" \
              --arg crate "$crate" \
              --arg target "$target" \
              --argjson features "$feature_args_json" '
                [
                  (["./cargo.sh", $toolchain, "check", "--tests",
                    "--package", $crate, "--target", $target]
                    + $features + ["--verbose"]),
                  (["./cargo.sh", $toolchain, "build",
                    "--package", $crate, "--target", $target]
                    + $features + ["--verbose"])
                ]
              ')"
            ;;
          library-only)
            expected_commands="$(jq -cn \
              --arg toolchain "+$plan_toolchain" \
              --arg crate "$crate" \
              --arg target "$target" \
              --argjson features "$feature_args_json" '
                [["./cargo.sh", $toolchain, "check",
                  "--package", $crate, "--target", $target]
                  + $features + ["--verbose"]]
              ')"
            ;;
        esac

        expected_plan="$(jq -cn \
          --arg toolchain "$plan_toolchain" \
          --arg crate "$crate" \
          --arg target "$target" \
          --arg profile "$profile" \
          --arg mode "$mode" \
          --argjson features "$feature_args_json" \
          --argjson commands "$expected_commands" '
            {
              schema_version: 1,
              toolchain: $toolchain,
              crate: $crate,
              target: $target,
              feature_profile: $profile,
              mode: $mode,
              feature_args: $features,
              commands: $commands
            }
          ')"
        if ! actual_plan="$($BUILD_TEST_EXECUTOR --plan \
            "$plan_toolchain" "$crate" "$target" "$profile")"; then
          fail "$BUILD_TEST_EXECUTOR --plan failed for $crate/$plan_toolchain/$profile/$target"
        elif ! jq -e . >/dev/null <<< "$actual_plan"; then
          fail "$BUILD_TEST_EXECUTOR --plan returned invalid JSON for $crate/$plan_toolchain/$profile/$target"
        else
          check_value \
            "build/test plan for $crate/$plan_toolchain/$profile/$target" \
            "$(jq -cS . <<< "$actual_plan")" \
            "$(jq -cS . <<< "$expected_plan")"
        fi
      done <<< "$plan_profiles"
    done
  done <<< "$described_targets"

  if $BUILD_TEST_EXECUTOR --plan msrv zerocopy \
      __unclassified_ci_target__ default >/dev/null 2>&1; then
    fail "$BUILD_TEST_EXECUTOR accepts an unclassified target"
  fi
fi

# There is exactly one unconditional workflow bridge into the executor. Target
# selection belongs in its exhaustively-checked policy, not in duplicated YAML
# `if` expressions. These structural checks also prevent the old Check / Build /
# Run tests / Run UI tests steps from being reintroduced alongside the helper.
executor_step_count="$(jq '[
  .jobs.build_test.steps[]
  | select((.run // "") | contains("run_build_test_cell.sh"))
] | length' <<< "$workflow_json")"
check_value "build/test executor-step count" "$executor_step_count" "1"
all_executor_invocations="$(jq '[
  .jobs[].steps[]?
  | select((.run // "") | contains("run_build_test_cell.sh"))
] | length' <<< "$workflow_json")"
check_value "workflow build/test executor invocation count" \
  "$all_executor_invocations" "1"
if [[ "$executor_step_count" == "1" ]]; then
  executor_step="$(jq -c '
    .jobs.build_test.steps[]
    | select((.run // "") | contains("run_build_test_cell.sh"))
  ' <<< "$workflow_json")"
  check_value "build/test executor-step name" \
    "$(jq -r '.name' <<< "$executor_step")" "Build and test"
  check_value "build/test executor-step command" \
    "$(jq -r '.run' <<< "$executor_step")" \
    './ci/run_build_test_cell.sh "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURE_PROFILE"'
  check_set "build/test executor-step environment" \
    "$(jq -r '.env | keys[]' <<< "$executor_step")" \
    $'CRATE\nFEATURE_PROFILE\nTARGET\nTOOLCHAIN'
  check_value "build/test executor TOOLCHAIN" \
    "$(jq -r '.env.TOOLCHAIN' <<< "$executor_step")" \
    '${{ matrix.toolchain }}'
  check_value "build/test executor CRATE" \
    "$(jq -r '.env.CRATE' <<< "$executor_step")" \
    '${{ matrix.crate }}'
  check_value "build/test executor TARGET" \
    "$(jq -r '.env.TARGET' <<< "$executor_step")" \
    '${{ matrix.target }}'
  check_value "build/test executor FEATURE_PROFILE" \
    "$(jq -r '.env.FEATURE_PROFILE' <<< "$executor_step")" \
    '${{ matrix.feature_profile }}'
  if jq -e 'has("if")' >/dev/null <<< "$executor_step"; then
    fail "the build/test executor step must be unconditional"
  fi
fi

legacy_build_step_count="$(jq '[
  .jobs.build_test.steps[]
  | select(.name == "Check"
      or .name == "Check tests"
      or .name == "Build"
      or .name == "Run tests"
      or .name == "Run UI tests")
] | length' <<< "$workflow_json")"
check_value "legacy build/test step count" "$legacy_build_step_count" "0"

relevant_test_scripts="$(jq -r '
  [.jobs[].steps[]?.run // empty] | join("\n")
' <<< "$workflow_json")"$'\n'"$(< "$BUILD_TEST_EXECUTOR")"
if tr '\n' ' ' <<< "$relevant_test_scripts" | \
    grep -Eq -- '--skip([=[:space:]]+)(ui|codegen)([^[:alnum:]_-]|$)'; then
  fail "CI must classify UI/codegen structurally rather than using a libtest --skip filter"
fi

build_profile_exclusions="$(jq -r '
  .jobs.build_test.strategy.matrix.exclude[]
  | select(has("feature_profile"))
  | if (has("toolchain") and (keys | length) == 2) then
      ["toolchain", .toolchain, .feature_profile] | @tsv
    elif (has("crate") and (keys | length) == 2) then
      ["crate", .crate, .feature_profile] | @tsv
    elif (has("target") and .crate == "zerocopy" and (keys | length) == 3) then
      ["target", .target, .crate, .feature_profile] | @tsv
    else
      ["unexpected", (tojson)] | @tsv
    end
  ' <<< "$workflow_json")"
expected_build_profile_exclusions=""
nightly_feature_count="$(jq 'length' <<< "$nightly_features_json")"
while IFS= read -r toolchain; do
  if [[ "$toolchain" != "nightly" && "$nightly_feature_count" -ne 0 ]]; then
    expected_build_profile_exclusions+="toolchain"$'\t'"$toolchain"$'\t'"all"$'\n'
  fi
done <<< "$build_toolchains"
while IFS= read -r profile; do
  if [[ "$profile" != "default" ]]; then
    expected_build_profile_exclusions+="crate"$'\t'"zerocopy-derive"$'\t'"$profile"$'\n'
  fi
  if jq -e --arg profile "$profile" \
      'index($profile) != null' >/dev/null <<< "$std_profiles_json"; then
    expected_build_profile_exclusions+="target"$'\t'"thumbv6m-none-eabi"$'\t'"zerocopy"$'\t'"$profile"$'\n'
  fi
done <<< "$expected_profiles"
expected_build_profile_exclusions="${expected_build_profile_exclusions%$'\n'}"
check_set "build feature-profile exclusions" "$build_profile_exclusions" "$expected_build_profile_exclusions"

nightly_miri_flags="$(jq -r '.env.ZC_NIGHTLY_MIRIFLAGS' <<< "$workflow_json")"
nightly_miri_flag_tokens="$(tr -s '[:space:]' '\n' <<< "$nightly_miri_flags" | sed '/^$/d')"
for required_flag in -Zmiri-strict-provenance -Zmiri-backtrace=full; do
  if ! grep -Fxq -- "$required_flag" <<< "$nightly_miri_flag_tokens"; then
    fail "ZC_NIGHTLY_MIRIFLAGS does not contain '$required_flag'"
  fi
done

# Miri deliberately uses the full build target axis, then explicitly excludes
# the manifest-classified unsupported targets. Its remaining axes form the
# complete target x crate/profile x borrow-model product.
if ! jq -e '.jobs | has("miri")' >/dev/null <<< "$workflow_json"; then
  fail "workflow does not define the standalone miri job"
else
  miri_matrix_keys="$(jq -r '.jobs.miri.strategy.matrix | keys[]' <<< "$workflow_json")"
  check_set "Miri matrix axes" "$miri_matrix_keys" $'crate\nexclude\nfeature_profile\nmiri_model\ntarget\ntoolchain'

  miri_toolchains="$(jq -r '.jobs.miri.strategy.matrix.toolchain[]' <<< "$workflow_json")"
  miri_targets="$(jq -r '.jobs.miri.strategy.matrix.target[]' <<< "$workflow_json")"
  miri_profiles="$(jq -r '.jobs.miri.strategy.matrix.feature_profile[]' <<< "$workflow_json")"
  miri_crates="$(jq -r '.jobs.miri.strategy.matrix.crate[]' <<< "$workflow_json")"
  miri_models="$(jq -r '.jobs.miri.strategy.matrix.miri_model[] | [(keys | sort | join(",")), .name, .flags] | @tsv' <<< "$workflow_json")"
  check_set "Miri toolchains" "$miri_toolchains" "nightly"
  check_set "Miri targets" "$miri_targets" "$build_targets"
  check_set "Miri feature profiles" "$miri_profiles" "$expected_profiles"
  check_set "Miri crates" "$miri_crates" $'zerocopy\nzerocopy-derive'
  check_set "Miri borrow models" "$miri_models" $'flags,name\tstacked\t\nflags,name\ttree\t-Zmiri-tree-borrows'
  check_configure_step "miri" "Miri"

  unknown_unsupported_targets="$(comm -23 \
    <(printf '%s\n' "$unsupported_targets" | sed '/^$/d' | sort -u) \
    <(printf '%s\n' "$build_targets" | sed '/^$/d' | sort -u))"
  if [[ -n "$unknown_unsupported_targets" ]]; then
    fail "miri-unsupported-targets contains targets absent from the build matrix:"
    sed 's/^/  /' <<< "$unknown_unsupported_targets" >&2
  fi

  miri_exclusions="$(jq -r '
    .jobs.miri.strategy.matrix.exclude[]
    | if (has("target") and (keys | length) == 1) then
        ["target", .target] | @tsv
      elif (has("crate") and has("feature_profile") and (keys | length) == 2) then
        ["crate", .crate, .feature_profile] | @tsv
      else
        ["unexpected", (tojson)] | @tsv
      end
    ' <<< "$workflow_json")"
  expected_miri_exclusions=""
  while IFS= read -r target; do
    [[ -z "$target" ]] || expected_miri_exclusions+="target"$'\t'"$target"$'\n'
  done <<< "$unsupported_targets"
  while IFS= read -r profile; do
    if [[ "$profile" != "default" ]]; then
      expected_miri_exclusions+="crate"$'\t'"zerocopy-derive"$'\t'"$profile"$'\n'
    fi
  done <<< "$expected_profiles"
  expected_miri_exclusions="${expected_miri_exclusions%$'\n'}"
  check_set "Miri exclusions" "$miri_exclusions" "$expected_miri_exclusions"

  supported_target_count="$(comm -23 \
    <(printf '%s\n' "$build_targets" | sed '/^$/d' | sort -u) \
    <(printf '%s\n' "$unsupported_targets" | sed '/^$/d' | sort -u) | wc -l)"
  profile_count="$(printf '%s\n' "$expected_profiles" | sed '/^$/d' | sort -u | wc -l)"
  model_count="$(printf '%s\n' "$miri_models" | sed '/^$/d' | sort -u | wc -l)"
  miri_job_count=$((supported_target_count * (profile_count + 1) * model_count))
  if [[ "$miri_job_count" -gt 256 ]]; then
    fail "Miri matrix expands to $miri_job_count jobs, exceeding GitHub's 256-job limit"
  fi

  miri_needs="$(jq -r '.jobs.miri.needs | if type == "array" then .[] else . end' <<< "$workflow_json")"
  miri_condition="$(jq -r '.jobs.miri.if' <<< "$workflow_json")"
  check_set "Miri job dependencies" "$miri_needs" "build_docker_env"
  check_value "Miri job condition" "$miri_condition" "github.event_name != 'pull_request'"

  miri_step_count="$(jq '[.jobs.miri.steps[] | select(.name == "Run tests under Miri")] | length' <<< "$workflow_json")"
  build_miri_step_count="$(jq '[.jobs.build_test.steps[] | select(.name == "Run tests under Miri")] | length' <<< "$workflow_json")"
  check_value "standalone Miri run-step count" "$miri_step_count" "1"
  check_value "build-matrix Miri run-step count" "$build_miri_step_count" "0"

  miri_model_flags_env="$(jq -r '.jobs.miri.steps[] | select(.name == "Run tests under Miri") | .env.MIRI_MODEL_FLAGS' <<< "$workflow_json")"
  check_value "Miri model flag wiring" "$miri_model_flags_env" '${{ matrix.miri_model.flags }}'

  miri_run_script="$(jq -r '.jobs.miri.steps[] | select(.name == "Run tests under Miri") | .run' <<< "$workflow_json")"
  if ! grep -Fq 'MIRIFLAGS="$MIRIFLAGS $MIRI_MODEL_FLAGS"' <<< "$miri_run_script"; then
    fail "Miri run step does not compose MIRI_MODEL_FLAGS into MIRIFLAGS"
  fi
  miri_command_count="$(grep -Fc 'miri nextest run' <<< "$miri_run_script" || true)"
  check_value "Miri command count per matrix job" "$miri_command_count" "1"
  if grep -Eq '^[[:space:]]*(for|while|until)[[:space:]]' <<< "$miri_run_script"; then
    fail "Miri run step contains a sequential shell loop; use the miri_model matrix axis"
  fi

  sentinel_needs="$(jq -r '.jobs["all-jobs-succeed"].needs[]' <<< "$workflow_json")"
  if ! grep -Fxq miri <<< "$sentinel_needs"; then
    fail "all-jobs-succeed does not depend on the miri job"
  fi
fi

# A `test = false` integration target is invisible to unfiltered `cargo test`.
# The manifest audit above permits only codegen, and this job must explicitly
# lint and execute that exact target. Keeping both commands target-specific
# makes the ownership transfer visible and prevents an apparently successful
# generic Cargo invocation from masking its omission.
if ! jq -e '.jobs | has("codegen")' >/dev/null <<< "$workflow_json"; then
  fail "workflow does not define the dedicated codegen job"
else
  codegen_clippy_step_count="$(jq '[
    .jobs.codegen.steps[] | select(.name == "Clippy")
  ] | length' <<< "$workflow_json")"
  codegen_test_step_count="$(jq '[
    .jobs.codegen.steps[] | select(.name == "Run tests")
  ] | length' <<< "$workflow_json")"
  check_value "codegen Clippy-step count" "$codegen_clippy_step_count" "1"
  check_value "codegen test-step count" "$codegen_test_step_count" "1"

  if [[ "$codegen_clippy_step_count" == "1" ]]; then
    codegen_clippy_run="$(jq -r '
      .jobs.codegen.steps[] | select(.name == "Clippy") | .run
    ' <<< "$workflow_json")"
    codegen_clippy_run="$(tr '\n' ' ' <<< "$codegen_clippy_run" \
      | sed -E 's/\\[[:space:]]+/ /g; s/[[:space:]]+/ /g')"
    for fragment in \
      './cargo.sh +nightly clippy' \
      '--locked' \
      '--package zerocopy' \
      '--target x86_64-unknown-linux-gnu' \
      '--all-features' \
      '--test codegen' \
      '--verbose'; do
      if ! grep -Fq -- "$fragment" <<< "$codegen_clippy_run"; then
        fail "codegen Clippy step is missing '$fragment'"
      fi
    done
    codegen_clippy_selector_count="$(grep -Fo -- '--test codegen' \
      <<< "$codegen_clippy_run" | wc -l)"
    check_value "codegen Clippy target-selector count" \
      "$codegen_clippy_selector_count" "1"
  fi

  if [[ "$codegen_test_step_count" == "1" ]]; then
    codegen_test_run="$(jq -r '
      .jobs.codegen.steps[] | select(.name == "Run tests") | .run
    ' <<< "$workflow_json")"
    codegen_test_run="$(tr '\n' ' ' <<< "$codegen_test_run" \
      | sed -E 's/\\[[:space:]]+/ /g; s/[[:space:]]+/ /g')"
    for fragment in \
      './cargo.sh +nightly test' \
      '--package zerocopy' \
      '--target x86_64-unknown-linux-gnu' \
      '--all-features' \
      '--test codegen' \
      '--verbose'; do
      if ! grep -Fq -- "$fragment" <<< "$codegen_test_run"; then
        fail "codegen test step is missing '$fragment'"
      fi
    done
    codegen_test_selector_count="$(grep -Fo -- '--test codegen' \
      <<< "$codegen_test_run" | wc -l)"
    check_value "codegen test target-selector count" \
      "$codegen_test_selector_count" "1"
  fi
fi

# UI tests now belong to Cargo's unfiltered native test selection. There must
# be no legacy workflow step which reruns them. Instead, cargo-zerocopy emits a
# capability cfg for exactly the semantic toolchains with checked-in snapshots,
# and both UI entry points ignore themselves on all other toolchains, under
# Miri, and under source coverage. The declarations below are deliberately
# coordinated by this fail-closed guard because they live in separate Cargo
# workspaces and cannot share a Rust constant directly.
ui_step_count="$(jq '[
  .jobs[].steps[]? | select(.name == "Run UI tests")
] | length' <<< "$workflow_json")"
check_value "legacy UI-test step count" "$ui_step_count" "0"

cargo_zerocopy_source="../tools/cargo-zerocopy/src/main.rs"
testutil_source="testutil/src/lib.rs"
root_ui_source="tests/ui.rs"
derive_ui_source="zerocopy-derive/tests/ui.rs"

check_compact_source_fragment \
  "UI-test toolchain capability list" "$cargo_zerocopy_source" \
  'constUI_TEST_TOOLCHAINS:[&str;3]=["msrv","stable","nightly"];'
check_compact_source_fragment \
  "UI-test capability cfg declaration" "$cargo_zerocopy_source" \
  'constUI_TEST_TOOLCHAIN_CFG:&str="__ZEROCOPY_INTERNAL_USE_ONLY_UI_TEST_TOOLCHAIN";'
check_compact_source_fragment \
  "UI-test toolchain classifier" "$cargo_zerocopy_source" \
  'fnis_ui_test_toolchain(name:&str)->bool{UI_TEST_TOOLCHAINS.contains(&name)}'
check_compact_source_fragment \
  "conditional UI-test cfg emission" "$cargo_zerocopy_source" \
  'ifis_ui_test_toolchain(name){flags+=&format!("--cfg{UI_TEST_TOOLCHAIN_CFG}");}'

# The test harness must decode the same three semantic descriptors and map
# each one to the matching snapshot suffix. `check_set` makes either additions
# or omissions fail; the variant/name pairs prevent a silent transposition.
testutil_cfg_toolchains="$(grep -oE \
  '__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN[[:space:]]*=[[:space:]]*"[^"]+"' \
  "$testutil_source" | sed -E 's/.*"([^"]+)"/\1/')"
check_set "testutil UI-test cfg toolchains" "$testutil_cfg_toolchains" \
  $'msrv\nstable\nnightly'
testutil_toolchain_names="$(sed -nE \
  's/.*ToolchainVersion::([^[:space:]]+)[[:space:]]*=>[[:space:]]*"([^"]+)".*/\1\t\2/p' \
  "$testutil_source")"
check_set "testutil UI-test snapshot-name mappings" \
  "$testutil_toolchain_names" \
  $'PinnedMsrv\tmsrv\nPinnedStable\tstable\nPinnedNightly\tnightly'

expected_ui_attr="#[cfg_attr(any(miri,coverage_nightly,not($UI_TEST_CFG)),ignore)]"
check_compact_source_fragment "zerocopy UI-test capability predicate" \
  "$root_ui_source" "${expected_ui_attr}fntest_ui()"
check_compact_source_fragment "zerocopy-derive UI-test capability predicate" \
  "$derive_ui_source" "${expected_ui_attr}fnui()"
for ui_source in "$root_ui_source" "$derive_ui_source"; do
  compact_ui_source="$(tr -d '[:space:]' < "$ui_source")"
  ui_attr_count="$(grep -Fo -- "$expected_ui_attr" \
    <<< "$compact_ui_source" | wc -l)"
  check_value "$ui_source UI-test capability-predicate count" \
    "$ui_attr_count" "1"
  if grep -Fq -- '--cfg=feature=' "$ui_source"; then
    fail "$ui_source hard-codes a feature cfg instead of using Cargo's resolved feature set"
  fi
done

# Register the internal cfg with both packages' unexpected-cfg machinery.
# Otherwise a supported UI cell can turn into a warning/failure independently
# of the capability predicate itself.
check_value "zerocopy UI-test check-cfg registration count" \
  "$(grep -Fc "cargo:rustc-check-cfg=cfg($UI_TEST_CFG)" build.rs)" "1"
check_value "zerocopy-derive UI-test check-cfg registration count" \
  "$(grep -Fc "'cfg($UI_TEST_CFG)'" zerocopy-derive/Cargo.toml)" "1"

# UI fixtures recursively ask Cargo for artifacts. Keep that build on the
# outer matrix cell's feature selection, and pass Cargo's resolved feature
# closure to rustc rather than maintaining another manually curated list.
check_compact_source_fragment \
  "cargo-zerocopy UI feature-protocol declaration" "$cargo_zerocopy_source" \
  'constUI_TEST_FEATURE_ARGS_ENV:&str="ZEROCOPY_UI_TEST_FEATURE_ARGS";'
check_compact_source_fragment \
  "cargo-zerocopy UI feature capture" "$cargo_zerocopy_source" \
  'letfeature_selection_args=capture_feature_selection_args(&args_vec);'
check_compact_source_fragment \
  "cargo-zerocopy UI feature forwarding" "$cargo_zerocopy_source" \
  'cmd.env(UI_TEST_FEATURE_ARGS_ENV,encode_feature_selection_args(&feature_selection_args),);'
check_compact_source_fragment \
  "testutil UI feature-protocol declaration" "$testutil_source" \
  'constUI_TEST_FEATURE_ARGS_ENV:&str="ZEROCOPY_UI_TEST_FEATURE_ARGS";'
check_compact_source_fragment \
  "testutil outer feature reuse" "$testutil_source" \
  'letfeature_selection_args=outer_feature_selection_args();command.args(&feature_selection_args);'
check_compact_source_fragment \
  "testutil resolved feature forwarding" "$testutil_source" \
  'forfeaturein&zerocopy_features{command.arg(format!("--rustc-arg=--cfg=feature={:?}",feature));}'

# Semver checks intentionally select the stable semantic profile rather than
# coupling their condition to Cargo argument spelling.
semver_step_count="$(jq '[.jobs.build_test.steps[] | select(.name == "Check semver compatibility")] | length' <<< "$workflow_json")"
check_value "semver step count" "$semver_step_count" "1"
semver_condition="$(jq -r '.jobs.build_test.steps[] | select(.name == "Check semver compatibility") | .if' <<< "$workflow_json")"
if ! grep -Fq "matrix.feature_profile == 'stable'" <<< "$semver_condition"; then
  fail "the semver condition does not select the stable semantic feature profile"
fi

root_ui_compact="$(tr -d '[:space:]' < "$root_ui_source")"
if grep -Fq '#![cfg(feature=' <<< "$root_ui_compact"; then
  fail "$root_ui_source duplicates Cargo.toml's whole-target feature gate"
fi
if grep -q 'matrix\.features' "$WORKFLOW"; then
  fail "workflow still refers to the removed matrix.features axis"
fi
for forwarded_variable in \
  FEATURE_PROFILE FEATURES \
  RUSTFLAGS RUSTDOCFLAGS MIRIFLAGS MIRI_MODEL_FLAGS \
  ZC_NIGHTLY_RUSTFLAGS ZC_NIGHTLY_MIRIFLAGS; do
  if ! grep -Eq -- "-e ${forwarded_variable}([^A-Z_]|$)" "$WORKFLOW"; then
    fail "Docker wrapper does not forward $forwarded_variable"
  fi
done

if [[ "$failed" -ne 0 ]]; then
  exit 1
fi
