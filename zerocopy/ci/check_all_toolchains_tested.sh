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

for command in cargo comm grep jq sed sort tr uniq wc yq; do
  command -v "$command" >/dev/null || fail "required command '$command' was not found"
done
if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

# Python yq and Go yq intentionally have different expression languages. Use
# each only as a YAML-to-JSON adapter, then apply all policy queries with jq so
# this guard behaves identically in developer environments and CI.
if yq --version 2>&1 | grep -qi mikefarah; then
  if ! workflow_json="$(yq -o=json -I=0 '.' "$WORKFLOW")"; then
    fail "could not parse $WORKFLOW with Go yq"
    exit 1
  fi
else
  if ! workflow_json="$(yq -c '.' "$WORKFLOW")"; then
    fail "could not parse $WORKFLOW with Python yq"
    exit 1
  fi
fi
if ! jq -e . >/dev/null <<< "$workflow_json"; then
  fail "$WORKFLOW did not convert to valid JSON"
  exit 1
fi

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

derive_features="$(jq -r 'keys[]' <<< "$derive_feature_graph")"
if [[ -n "$derive_features" ]]; then
  fail "zerocopy-derive now defines features; update the CI profile policy before adding them:"
  sed 's/^/  /' <<< "$derive_features" >&2
fi

expected_profiles=$'default\nstable\nall'
if [[ "$(jq -r '.default_is_nonempty' <<< "$feature_policy")" == "true" ]]; then
  expected_profiles+=$'\nno-default'
fi

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
check_set "build feature profiles" "$build_profiles" "$expected_profiles"
check_set "build crates" "$build_crates" $'zerocopy\nzerocopy-derive'
# Self-comparison intentionally checks for duplicate targets while allowing the
# build matrix itself to remain the source of truth for the supported set.
check_set "build targets" "$build_targets" "$build_targets"
check_set "build event-name axis" "$build_event_names" '${{ github.event_name }}'
check_configure_step "build_test" "build"

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
  case "$profile" in
    default) profile_enables_std="$(jq -r '.default_enables_std' <<< "$feature_policy")" ;;
    no-default) profile_enables_std="false" ;;
    stable) profile_enables_std="$(jq -r '.stable_enables_std' <<< "$feature_policy")" ;;
    all) profile_enables_std="$(jq -r '.std_feature_exists' <<< "$feature_policy")" ;;
  esac
  if [[ "$profile_enables_std" == "true" ]]; then
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

# Semver checks intentionally select the stable semantic profile rather than
# coupling their condition to Cargo argument spelling. UI tests have no
# crate/profile filter so that a future default feature cannot silently miss UI
# coverage.
ui_step_count="$(jq '[.jobs.build_test.steps[] | select(.name == "Run UI tests")] | length' <<< "$workflow_json")"
semver_step_count="$(jq '[.jobs.build_test.steps[] | select(.name == "Check semver compatibility")] | length' <<< "$workflow_json")"
check_value "UI-test step count" "$ui_step_count" "1"
check_value "semver step count" "$semver_step_count" "1"
ui_condition="$(jq -r '.jobs.build_test.steps[] | select(.name == "Run UI tests") | .if' <<< "$workflow_json")"
semver_condition="$(jq -r '.jobs.build_test.steps[] | select(.name == "Check semver compatibility") | .if' <<< "$workflow_json")"
if grep -Eq 'matrix\.(crate|feature_profile)' <<< "$ui_condition"; then
  fail "the UI-test condition must not filter by crate or feature profile"
fi
if ! grep -Fq "matrix.feature_profile == 'stable'" <<< "$semver_condition"; then
  fail "the semver condition does not select the stable semantic feature profile"
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
