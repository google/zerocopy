#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

readonly WORKFLOW="${ZEROCOPY_CI_WORKFLOW:-../.github/workflows/ci.yml}"
readonly STABLE_FEATURE="__internal_use_only_features_that_work_on_stable"

fail() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

contains() {
  local needle="$1"
  shift
  [[ " $* " == *" $needle "* ]]
}

compare_sets() {
  if ! diff -u \
      <(LC_ALL=C sort -u "$2") \
      <(LC_ALL=C sort -u "$3") >&2; then
    fail "$1 differs"
  fi
}

require_fragment() {
  grep -Fq -- "$2" <<< "$1" || fail "$3"
}

reject_fragment() {
  ! grep -Fq -- "$2" <<< "$1" || fail "$3"
}

normalize_run() {
  tr '\n' ' ' | sed 's/\\//g; s/[[:space:]][[:space:]]*/ /g; s/^ //; s/ $//'
}

json_array() {
  printf '%s\n' "$@" | jq -R . | jq -s .
}

step_field() {
  jq -er --arg job "$1" --arg name "$2" --arg field "$3" '
    [.jobs[$job].steps[] | select(.name == $name)] as $steps
    | if ($steps | length) == 1 then $steps[0][$field] // ""
      else error("expected exactly one named step")
      end
  ' "$workflow_json"
}

tmp_dir="$(mktemp -d)"
trap 'rm -rf -- "$tmp_dir"' EXIT
workflow_json="$tmp_dir/workflow.json"
metadata_json="$tmp_dir/metadata.json"
root_package_json="$tmp_dir/root-package.json"
derive_package_json="$tmp_dir/derive-package.json"
feature_policy_json="$tmp_dir/feature-policy.json"

if ! yq -o=json '.' "$WORKFLOW" > "$workflow_json" 2>/dev/null; then
  # Debian's Python yq already emits JSON and does not accept mikefarah/yq's
  # output-format option.
  yq '.' "$WORKFLOW" > "$workflow_json"
fi
jq empty "$workflow_json"

./cargo.sh +stable metadata -q --locked --offline --no-deps --format-version 1 \
  > "$metadata_json"

jq '
  [.packages[]
   | select((.name == "zerocopy") and
            (.manifest_path | endswith("/zerocopy/Cargo.toml")))]
  | if length == 1 then .[0] else error("expected one zerocopy package") end
' "$metadata_json" > "$root_package_json"
jq '
  [.packages[]
   | select((.name == "zerocopy-derive") and
            (.manifest_path | endswith("/zerocopy-derive/Cargo.toml")))]
  | if length == 1 then .[0] else error("expected one zerocopy-derive package") end
' "$metadata_json" > "$derive_package_json"

if ! jq -e --arg stable "$STABLE_FEATURE" '
  .features as $features
  | .metadata.ci["nightly-features"] as $nightly
  | ($nightly | type == "array") and
    (($nightly | length) == ($nightly | unique | length)) and
    all($nightly[]; . as $feature | $features | has($feature)) and
    (($nightly | index("default")) == null) and
    (($nightly | index($stable)) == null) and
    ($features | has($stable)) and
    ($features | has("derive"))
' "$root_package_json" >/dev/null; then
  fail "Cargo feature and package.metadata.ci.nightly-features policy is invalid"
fi

# Cargo metadata supplies the canonical local feature graph. Compute each
# profile's transitive local closure without duplicating that graph here.
jq --arg stable "$STABLE_FEATURE" '
  def closure($features; $active):
    ($active | unique) as $active
    | ([ $active[] as $name
         | ($features[$name] // [])[]
         | select(. as $candidate | $features | has($candidate))
       ] + $active | unique) as $next
    | if $next == $active then $active else closure($features; $next) end;

  .features as $features
  | ($features | keys) as $all
  | .metadata.ci["nightly-features"] as $nightly
  | {
      has_default: ($features | has("default")),
      default: closure(
        $features;
        if ($features | has("default")) then ["default"] else [] end
      ),
      no_default: [],
      stable: closure($features; [$stable]),
      all: closure($features; $all),
      expected_stable: ($all - ($nightly + ["default"])),
      nightly: $nightly
    }
' "$root_package_json" > "$feature_policy_json"

if ! jq -e '
  (.stable == .expected_stable) and
  (.stable | index("derive") != null) and
  (. as $policy
   | all($policy.default[];
         . as $feature | $policy.nightly | index($feature) == null))
' "$feature_policy_json" >/dev/null; then
  fail "the stable aggregate must cover every non-default, non-nightly feature, including derive"
fi
if ! jq -e '.features | keys | length == 0' "$derive_package_json" >/dev/null; then
  fail "zerocopy-derive gained features; classify them in the CI profile policy"
fi

if ! events_json="$(jq -ce '
  .on
  | if type == "object" and length > 0 then keys | sort
    else error("workflow triggers must be a nonempty object")
    end
' "$workflow_json")"; then
  fail "workflow triggers must be a nonempty object"
fi
mapfile -t events < <(jq -r '.[]' <<< "$events_json")
if ! contains pull_request "${events[@]}" || ! contains merge_group "${events[@]}"; then
  fail "CI must run for pull requests and merge groups"
fi
targets=(
  i686-unknown-linux-gnu x86_64-unknown-linux-gnu
  arm-unknown-linux-gnueabi aarch64-unknown-linux-gnu
  powerpc-unknown-linux-gnu powerpc64-unknown-linux-gnu
  riscv64gc-unknown-linux-gnu s390x-unknown-linux-gnu
  x86_64-pc-windows-msvc thumbv6m-none-eabi wasm32-unknown-unknown
)
crates=(zerocopy zerocopy-derive)
profiles=(default)
if [[ "$(jq -r '.has_default' "$feature_policy_json")" == true ]]; then
  profiles+=(no-default)
fi
profiles+=(stable all)

aarch64_only_toolchains=(
  no-zerocopy-aarch64-simd-1-59-0 no-zerocopy-aarch64-simd-be-1-87-0
)
native_only_toolchains=(
  no-zerocopy-core-error-1-81-0 no-zerocopy-diagnostic-on-unimplemented-1-78-0
  no-zerocopy-generic-bounds-in-const-fn-1-61-0
)
full_target_toolchains=(
  no-zerocopy-simd-x86-avx12-1-89-0 no-zerocopy-target-has-atomics-1-60-0
  no-zerocopy-panic-in-const-and-vec-try-reserve-1-57-0
)
classified_toolchains=(
  "${aarch64_only_toolchains[@]}"
  "${native_only_toolchains[@]}"
  "${full_target_toolchains[@]}"
)

printf '%s\n' "${classified_toolchains[@]}" > "$tmp_dir/expected-build-rs"
jq -r '.metadata["build-rs"] | keys[]' "$root_package_json" \
  > "$tmp_dir/actual-build-rs"
compare_sets "classified build.rs toolchains" \
  "$tmp_dir/expected-build-rs" "$tmp_dir/actual-build-rs"

toolchains=(msrv stable nightly "${classified_toolchains[@]}")

toolchains_json="$(json_array "${toolchains[@]}")"
targets_json="$(json_array "${targets[@]}")"
profiles_json="$(json_array "${profiles[@]}")"
crates_json="$(json_array "${crates[@]}")"
if ! jq -e \
    --argjson toolchains "$toolchains_json" \
    --argjson targets "$targets_json" \
    --argjson profiles "$profiles_json" \
    --argjson crates "$crates_json" '
  .jobs.build_test.strategy.matrix as $matrix
  | ($matrix | keys | sort) ==
      (["toolchain", "target", "feature_profile", "crate", "event_name", "exclude"] | sort) and
    ($matrix.event_name == ["${{ github.event_name }}"]) and
    all([
      [$matrix.toolchain, $toolchains],
      [$matrix.target, $targets],
      [$matrix.feature_profile, $profiles],
      [$matrix.crate, $crates]
    ][];
      (.[0] | length == (unique | length)) and
      ((.[0] | sort) == (.[1] | sort)))
' "$workflow_json" >/dev/null; then
  fail "build matrix axes do not match the independently classified policy"
fi

configure_run="$(step_field build_test 'Configure environment variables' run | normalize_run)"
expected_feature_mapping="case \"\$FEATURE_PROFILE\" in default) FEATURES='' ;;"
if contains no-default "${profiles[@]}"; then
  expected_feature_mapping+=" no-default) FEATURES='--no-default-features' ;;"
fi
expected_feature_mapping+=" stable) FEATURES='--no-default-features --features $STABLE_FEATURE' ;;"
expected_feature_mapping+=" all) FEATURES='--all-features' ;;"
expected_feature_mapping+=' *) echo "unknown feature profile: $FEATURE_PROFILE" >&2; exit 1 ;; esac echo "FEATURES=$FEATURES" >> "$GITHUB_ENV"'
require_fragment "$configure_run" "$expected_feature_mapping" \
  "feature profiles must use the complete fail-closed mapping and export"
expected_feature_assignments=$((${#profiles[@]} + 1))
if [[ "$(grep -Fo 'FEATURES=' <<< "$configure_run" | wc -l)" \
      != "$expected_feature_assignments" ]]; then
  fail "feature profile mapping must not contain extra assignments or exports"
fi
require_fragment "$configure_run" 'MIRIFLAGS="${MIRIFLAGS:-}"' \
  "strict shell mode must initialize optional MIRIFLAGS"

declare -A profile_has_std=()
for profile in "${profiles[@]}"; do
  policy_key="${profile//-/_}"
  profile_has_std[$profile]="$(jq -r --arg key "$policy_key" \
    '.[$key] | index("std") != null' "$feature_policy_json")"
done
nightly_feature_count="$(jq '.nightly | length' "$feature_policy_json")"

cell_is_expected() {
  local event="$1" crate="$2" toolchain="$3" profile="$4" target="$5"
  if [[ "$profile" == all && "$nightly_feature_count" != 0 && "$toolchain" != nightly ]]; then
    return 1
  fi
  if [[ "$crate" == zerocopy-derive ]]; then
    [[ "$profile" == default ]] || return 1
    contains "$toolchain" msrv stable nightly || return 1
  fi
  if [[ "$toolchain" == stable && "$target" == wasm32-unknown-unknown ]]; then
    return 1
  fi
  if [[ "$crate" == zerocopy && "$target" == thumbv6m-none-eabi && \
        "${profile_has_std[$profile]}" == true ]]; then
    return 1
  fi
  if [[ "$event" == pull_request ]] && ! contains "$target" \
      i686-unknown-linux-gnu x86_64-unknown-linux-gnu x86_64-pc-windows-msvc; then
    return 1
  fi
  if contains "$toolchain" "${aarch64_only_toolchains[@]}" && \
      [[ "$target" != aarch64-unknown-linux-gnu ]]; then
    return 1
  fi
  if contains "$toolchain" "${native_only_toolchains[@]}" && ! contains "$target" \
      i686-unknown-linux-gnu x86_64-unknown-linux-gnu; then
    return 1
  fi
  return 0
}

expected_build_cells="$tmp_dir/expected-build-cells"
for event in "${events[@]}"; do
  for crate in "${crates[@]}"; do
    for toolchain in "${toolchains[@]}"; do
      for profile in "${profiles[@]}"; do
        for target in "${targets[@]}"; do
          if cell_is_expected "$event" "$crate" "$toolchain" "$profile" "$target"; then
            printf '%s\t%s\t%s\t%s\t%s\n' \
              "$event" "$crate" "$toolchain" "$profile" "$target"
          fi
        done
      done
    done
  done
done > "$expected_build_cells"

actual_build_cells="$tmp_dir/actual-build-cells"
jq -r --argjson events "$events_json" '
  def matches($cell): all(to_entries[]; $cell[.key] == .value);
  .jobs.build_test.strategy.matrix as $matrix
  | $events[] as $event
  | $matrix.crate[] as $crate
  | $matrix.toolchain[] as $toolchain
  | $matrix.feature_profile[] as $profile
  | $matrix.target[] as $target
  | {event_name: $event, crate: $crate, toolchain: $toolchain,
     feature_profile: $profile, target: $target} as $cell
  | select(any($matrix.exclude[]?; matches($cell)) | not)
  | [$event, $crate, $toolchain, $profile, $target] | @tsv
' "$workflow_json" > "$actual_build_cells"
compare_sets "post-exclusion build matrix" "$expected_build_cells" "$actual_build_cells"

native_condition="matrix.target == 'x86_64-unknown-linux-gnu' || matrix.target == 'i686-unknown-linux-gnu'"
cross_condition="matrix.target != 'thumbv6m-none-eabi' && matrix.target != 'x86_64-unknown-linux-gnu' && matrix.target != 'i686-unknown-linux-gnu'"
thumb_condition="matrix.target == 'thumbv6m-none-eabi'"

if ! jq -e '
  .jobs.build_test.steps as $steps
  | def one($name):
      [$steps[] | select(.name == $name)]
      | if length == 1 then .[0] else error("expected exactly one named step") end;
    (one("Configure environment variables").env == {
      "TOOLCHAIN": "${{ matrix.toolchain }}",
      "FEATURE_PROFILE": "${{ matrix.feature_profile }}"
    }) and
    all(["Test native target", "Check cross target", "Check thumb library"][];
      one(.).env == {
        "TOOLCHAIN": "${{ matrix.toolchain }}",
        "CRATE": "${{ matrix.crate }}",
        "TARGET": "${{ matrix.target }}"
      })
' "$workflow_json" >/dev/null; then
  fail "matrix execution steps must receive their exact matrix values"
fi

native_run="$(step_field build_test 'Test native target' run | normalize_run)"
native_if="$(step_field build_test 'Test native target' if)"
[[ "$native_if" == "$native_condition" ]] || fail "native test step has the wrong target condition"
[[ "$native_run" == \
  './cargo.sh +$TOOLCHAIN test --package $CRATE --target $TARGET $FEATURES --verbose' ]] || \
  fail "native cells must run exactly one unfiltered cargo test"

cross_run="$(step_field build_test 'Check cross target' run | normalize_run)"
cross_if="$(step_field build_test 'Check cross target' if)"
[[ "$cross_if" == "$cross_condition" ]] || fail "cross-target step has the wrong target condition"
[[ "$cross_run" == \
  './cargo.sh +$TOOLCHAIN check --tests --package $CRATE --target $TARGET $FEATURES --verbose ./cargo.sh +$TOOLCHAIN build --package $CRATE --target $TARGET $FEATURES --verbose' ]] || \
  fail "cross cells must check tests and build the library exactly once"

thumb_run="$(step_field build_test 'Check thumb library' run | normalize_run)"
thumb_if="$(step_field build_test 'Check thumb library' if)"
[[ "$thumb_if" == "$thumb_condition" ]] || fail "thumb step has the wrong target condition"
[[ "$thumb_run" == \
  './cargo.sh +$TOOLCHAIN check --package $CRATE --target $TARGET $FEATURES --verbose' ]] || \
  fail "thumb cells must check exactly the library"

if ! jq -e '
  ([.targets[] | select(.name == "ui" and (.kind | index("test") != null))] | length == 1) and
  ([.targets[] | select(.name == "ui")][0]["required-features"] == ["derive"]) and
  ([.targets[] | select(.name == "ui")][0].test == true) and
  ([.targets[] | select(.name == "codegen" and (.kind | index("test") != null))] | length == 1) and
  ([.targets[] | select(.name == "codegen")][0].test == false)
' "$root_package_json" >/dev/null; then
  fail "Cargo must own UI eligibility and exclude codegen from ordinary test selection"
fi

codegen_clippy="$(step_field codegen Clippy run | normalize_run)"
codegen_test="$(step_field codegen 'Run tests' run | normalize_run)"
[[ "$codegen_clippy" == \
  './cargo.sh +nightly clippy --locked --package zerocopy --target x86_64-unknown-linux-gnu --all-features --test codegen --verbose' ]] || \
  fail "codegen job must lint its exact all-feature target with warnings enabled"
[[ "$codegen_test" == \
  'RUSTFLAGS="$RUSTFLAGS -Awarnings" ./cargo.sh +nightly test --locked --package zerocopy --target x86_64-unknown-linux-gnu --all-features --verbose --test codegen' ]] || \
  fail "codegen job must execute its exact all-feature test target"

coverage_run="$(step_field coverage 'Generate code coverage' run | normalize_run)"
[[ "$coverage_run" == \
  'set -eo pipefail ./cargo.sh +nightly install --version 0.8.0 cargo-llvm-cov ./cargo.sh +nightly llvm-cov --package zerocopy --target x86_64-unknown-linux-gnu --all-features --doctests --lcov --output-path lcov.info --verbose' ]] || \
  fail "coverage must execute the exact unfiltered all-feature command"

if ! jq -e '
  .jobs.miri as $miri
  | ($miri.strategy.matrix | keys | sort) ==
      (["toolchain", "target", "feature_profile", "crate", "miri_model", "exclude"] | sort) and
    all([
      $miri.strategy.matrix.toolchain,
      $miri.strategy.matrix.target,
      $miri.strategy.matrix.feature_profile,
      $miri.strategy.matrix.crate,
      $miri.strategy.matrix.miri_model
    ][]; type == "array" and length == (unique | length)) and
    $miri.if == "github.event_name != '\''pull_request'\''" and
    $miri.needs == "build_docker_env" and
    $miri.strategy.matrix.toolchain == ["nightly"] and
    $miri.strategy.matrix.miri_model == [
    {"name":"stacked", "flags":""},
    {"name":"tree", "flags":"-Zmiri-tree-borrows"}
  ] and
    ([$miri.steps[] | select(.name == "Configure environment variables")] as $configure
     | [$miri.steps[] | select(.name == "Run tests under Miri")] as $run
     | ($configure | length) == 1 and ($run | length) == 1 and
       $configure[0].env.TOOLCHAIN == "${{ matrix.toolchain }}" and
       $configure[0].env.FEATURE_PROFILE == "${{ matrix.feature_profile }}" and
       $run[0].env.TOOLCHAIN == "${{ matrix.toolchain }}" and
       $run[0].env.CRATE == "${{ matrix.crate }}" and
       $run[0].env.TARGET == "${{ matrix.target }}" and
       $run[0].env.MIRI_MODEL_FLAGS == "${{ matrix.miri_model.flags }}")
' "$workflow_json" >/dev/null; then
  fail "Miri matrix axes and execution wiring are invalid"
fi

unsupported_miri_targets=(riscv64gc-unknown-linux-gnu thumbv6m-none-eabi wasm32-unknown-unknown)
expected_miri_cells="$tmp_dir/expected-miri-cells"
for crate in "${crates[@]}"; do
  for profile in "${profiles[@]}"; do
    if [[ "$crate" == zerocopy-derive && "$profile" != default ]]; then
      continue
    fi
    for target in "${targets[@]}"; do
      contains "$target" "${unsupported_miri_targets[@]}" && continue
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$crate" nightly "$profile" "$target" stacked ''
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$crate" nightly "$profile" "$target" tree '-Zmiri-tree-borrows'
    done
  done
done > "$expected_miri_cells"

actual_miri_cells="$tmp_dir/actual-miri-cells"
jq -r '
  def matches($cell): all(to_entries[]; $cell[.key] == .value);
  .jobs.miri.strategy.matrix as $matrix
  | $matrix.crate[] as $crate
  | $matrix.toolchain[] as $toolchain
  | $matrix.feature_profile[] as $profile
  | $matrix.target[] as $target
  | $matrix.miri_model[] as $model
  | {crate: $crate, toolchain: $toolchain, feature_profile: $profile,
     target: $target, miri_model: $model} as $cell
  | select(any($matrix.exclude[]?; matches($cell)) | not)
  | [$crate, $toolchain, $profile, $target, $model.name, $model.flags] | @tsv
' "$workflow_json" > "$actual_miri_cells"
compare_sets "post-exclusion Miri matrix" "$expected_miri_cells" "$actual_miri_cells"

miri_run="$(step_field miri 'Run tests under Miri' run | normalize_run)"
require_fragment "$miri_run" 'trap '\''mv .cargo/config.toml.bak .cargo/config.toml'\'' EXIT' \
  "Miri must restore the Cargo configuration on every exit path"
miri_command='MIRIFLAGS="$MIRIFLAGS $MIRI_MODEL_FLAGS" ./cargo.sh +$TOOLCHAIN miri nextest run --locked --test-threads "$THREADS" --package $CRATE --target $TARGET $FEATURES'
[[ "$miri_run" == *"$miri_command" ]] || \
  fail "Miri must end by running the selected model, crate, target, and feature profile"
if [[ "$(grep -Fo 'miri nextest run' <<< "$miri_run" | wc -l)" != 1 ]]; then
  fail "Miri must contain exactly one test invocation per matrix cell"
fi

docker_shell_run="$(step_field build_test 'Create Docker Shell Wrapper' run | normalize_run)"
require_fragment "$docker_shell_run" '-e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e FEATURES' \
  "Docker shell must forward matrix profile variables"
require_fragment "$docker_shell_run" '-e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS -e MIRI_MODEL_FLAGS' \
  "Docker shell must forward Miri model flags"
require_fragment "$docker_shell_run" 'exec bash -e -o pipefail "$1"' \
  "Docker shell must preserve GitHub Actions fail-fast and pipeline semantics"

if ! jq -e '
  .jobs as $jobs
  | $jobs["all-jobs-succeed"] as $sentinel
  | ($sentinel.if == "${{ always() }}") and
    (($sentinel["continue-on-error"] // false) == false) and
    (($sentinel.needs | type) == "array") and
    (($sentinel.needs | length) == ($sentinel.needs | unique | length)) and
    (($sentinel.needs | sort) ==
      ([$jobs | keys[] | select(. != "all-jobs-succeed")] | sort)) and
    all($sentinel.steps[]; ((.["continue-on-error"] // false) == false)) and
    ($sentinel.steps[0].if == "${{ cancelled() }}" and
     $sentinel.steps[0].run == "exit 1") and
    any($sentinel.steps[];
      .name == "Require every dependency to succeed" and
      (has("if") | not) and
      .env.EVENT_NAME == "${{ github.event_name }}" and
      .env.NEEDS_JSON == "${{ toJSON(needs) }}")
' "$workflow_json" >/dev/null; then
  fail "all-jobs-succeed must depend exactly on every job and fail closed"
fi

sentinel_run="$(
  step_field all-jobs-succeed 'Require every dependency to succeed' run | normalize_run
)"
expected_sentinel_run="$(normalize_run <<'EOF'
set -euo pipefail
jq -e --arg event "$EVENT_NAME" '
  type == "object" and length > 0 and
  all(
    to_entries[];
    if .key == "miri" and $event == "pull_request"
    then .value.result == "skipped"
    else .value.result == "success"
    end
  )
' <<< "$NEEDS_JSON"
EOF
)"
[[ "$sentinel_run" == "$expected_sentinel_run" ]] || \
  fail "all-jobs-succeed must use the complete fail-closed dependency predicate"

# A single native test pass is sufficient only while the test profile inherits
# the dev profile. Audit only repository-owned inputs that can affect Cargo
# when the build matrix invokes it from the zerocopy workspace.
profile_overrides="$(
  git -C .. grep -nE '\[profile\.test(\]|\.)|CARGO_PROFILE_TEST_' -- \
    'zerocopy/Cargo.toml' '.cargo/**' 'zerocopy/.cargo/**' \
    '.github/workflows/ci.yml' '.github/workflows/Dockerfile' \
    'zerocopy/cargo.sh' 'tools/cargo-zerocopy/src/**' \
    || true
)"
if [[ -n "$profile_overrides" ]]; then
  printf 'test-profile overrides invalidate single-pass native testing:\n%s\n' \
    "$profile_overrides" >&2
  exit 1
fi
