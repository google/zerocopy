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

if [[ "${GITHUB_ACTIONS:-}" == true ]]; then
  readonly WORKFLOW="../.github/workflows/ci.yml"
else
  readonly WORKFLOW="${ZEROCOPY_CI_WORKFLOW:-../.github/workflows/ci.yml}"
fi
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

normalize_run() {
  awk '
    /\\$/ { sub(/\\$/, ""); printf "%s ", $0; next }
    { print }
  ' | sed 's/[[:space:]][[:space:]]*/ /g; s/^ //; s/ $//; /^$/d'
}

parse_toml() {
  if yq -p=toml -o=json '.' "$1" > "$2" 2>/dev/null; then
    return
  fi
  command -v tomlq >/dev/null || return 1
  tomlq '.' "$1" > "$2"
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

if ! jq -e '
  . as $workflow
  | ($workflow.env == {
      "CARGO_TERM_COLOR": "always",
      "CARGO_NET_RETRY": "10",
      "RUSTUP_MAX_RETRIES": "10",
      "ZC_CI_IMAGE": "zerocopy-ci:local",
      "ZC_CI_IMAGE_ARCHIVE": "zerocopy-ci.tar",
      "RUSTFLAGS": "-Dwarnings",
      "RUSTDOCFLAGS": "-Dwarnings --cfg=zerocopy_unstable_ptr",
      "ZC_NIGHTLY_RUSTFLAGS": "-Zrandomize-layout",
      "ZC_NIGHTLY_MIRIFLAGS": "-Zmiri-strict-provenance -Zmiri-backtrace=full",
      "CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN": 1
    }) and
    all([$workflow.jobs.build_test, $workflow.jobs.miri][];
      has("env") | not)
' "$workflow_json" >/dev/null; then
  fail "workflow and matrix-job environments must match the audited policy"
fi

if ! jq -e '
  . as $workflow
  | def one($job; $name):
      [$workflow.jobs[$job].steps[] | select(.name == $name)]
      | if length == 1 then .[0] else error("expected exactly one named step") end;
    all($workflow.jobs[];
      ((.["continue-on-error"] // false) == false) and
      all(.steps[]?; ((.["continue-on-error"] // false) == false))) and
    all([
      ["build_test", "Configure environment variables"],
      ["miri", "Configure environment variables"],
      ["miri", "Run tests under Miri"],
      ["codegen", "Clippy"],
      ["codegen", "Run tests"],
      ["coverage", "Generate code coverage"]
    ][]; . as $step | (one($step[0]; $step[1]) | has("if") | not))
' "$workflow_json" >/dev/null; then
  fail "audited jobs and steps must not skip execution or ignore failures"
fi
if ! jq -e '
  .jobs as $jobs
  | all([
      ["build_test", {"fetch-depth": 2, "persist-credentials": false}],
      ["miri", {"fetch-depth": 2, "persist-credentials": false}],
      ["codegen", {"persist-credentials": false}],
      ["coverage", {"persist-credentials": false}]
    ][]; . as $expected
    | [$jobs[$expected[0]].steps[] | select(
        ((.uses? // "") | startswith("actions/checkout@"))
      )] == [{
        "uses": "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
        "with": $expected[1]
      }])
' "$workflow_json" >/dev/null; then
  fail "audited test jobs must check out the exact triggering revision"
fi
if ! jq -e '
  .jobs["check-all-toolchains-tested"] == {
    "runs-on": "ubuntu-latest",
    "name": "Check that all toolchains listed in Cargo.toml are tested in CI",
    "steps": [
      {
        "name": "Install yq (for YAML parsing)",
        "run": "GONOSUMDB=github.com/mikefarah/yq/v4 go install github.com/mikefarah/yq/v4@v4.44.1"
      },
      {
        "uses": "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
        "with": {"persist-credentials": false}
      },
      {
        "name": "Run check",
        "run": "cd zerocopy && ./ci/check_all_toolchains_tested.sh"
      }
    ]
  }
' "$workflow_json" >/dev/null; then
  fail "the policy checker job must use its exact audited invocation"
fi

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
for manifest in Cargo.toml zerocopy-derive/Cargo.toml; do
  manifest_json="$tmp_dir/package-manifest.json"
  if ! parse_toml "$manifest" "$manifest_json" ||
      ! jq -e '
      .package as $package
      | (($package | has("autotests") | not) or ($package.autotests == true))
    ' "$manifest_json" >/dev/null; then
    fail "$manifest must keep automatic integration-test discovery enabled"
  fi
done

if ! jq -e --arg stable "$STABLE_FEATURE" '
  .features as $features
  | .metadata.ci as $ci
  | $ci["nightly-features"] as $nightly
  | ($nightly | type == "array") and
    (($nightly | length) == ($nightly | unique | length)) and
    all($nightly[]; . as $feature | $features | has($feature)) and
    (($nightly | index("default")) == null) and
    (($nightly | index($stable)) == null) and
    ($features | has($stable)) and
    ($features | has("derive")) and
    (($ci["pinned-stable"] | type) == "string") and
    ($ci["pinned-stable"] | test("^[0-9]+\\.[0-9]+\\.[0-9]+$")) and
    (($ci["pinned-nightly"] | type) == "string") and
    ($ci["pinned-nightly"] |
      test("^nightly-[0-9]{4}-[0-9]{2}-[0-9]{2}$"))
' "$root_package_json" >/dev/null; then
  fail "Cargo feature and package.metadata.ci policy is invalid"
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
events=()
while IFS= read -r event; do
  events+=("$event")
done < <(jq -r '.[]' <<< "$events_json")
if ! contains pull_request "${events[@]}" ||
    ! contains merge_group "${events[@]}" ||
    ! jq -e '.on.pull_request == null and .on.merge_group == null' \
      "$workflow_json" >/dev/null; then
  fail "CI must run unfiltered for pull requests and merge groups"
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
if ! jq -e '
  .metadata["build-rs"] as $versions
  | ($versions | type) == "object" and
    all($versions | to_entries[]; . as $entry
      | ($entry.value | type) == "string" and
        ($entry.key | endswith("-" + ($entry.value | gsub("\\."; "-")))))
' "$root_package_json" >/dev/null; then
  fail "build.rs toolchain names must end in their configured versions"
fi

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

configure_run="$(
  step_field build_test 'Configure environment variables' run |
    sed '/^[[:space:]]*#/d' |
    normalize_run
)"
miri_configure_run="$(
  step_field miri 'Configure environment variables' run |
    sed '/^[[:space:]]*#/d' |
    normalize_run
)"
expected_feature_mapping='case "$FEATURE_PROFILE" in'
expected_feature_mapping+=$'\n'"default) FEATURES='' ;;"
if contains no-default "${profiles[@]}"; then
  expected_feature_mapping+=$'\n'"no-default) FEATURES='--no-default-features' ;;"
fi
expected_feature_mapping+=$'\n''stable)'
expected_feature_mapping+=$'\n'"FEATURES='--no-default-features --features $STABLE_FEATURE'"
expected_feature_mapping+=$'\n'';;'
expected_feature_mapping+=$'\n'"all) FEATURES='--all-features' ;;"
expected_feature_mapping+=$'\n''*) echo "unknown feature profile: $FEATURE_PROFILE" >&2; exit 1 ;;'
expected_feature_mapping+=$'\n''esac'
expected_configure_suffix="$(normalize_run <<'EOF'
ZC_TOOLCHAIN="$(./cargo.sh --version $TOOLCHAIN)"
echo "Found that the '$TOOLCHAIN' toolchain is $ZC_TOOLCHAIN" | tee -a $GITHUB_STEP_SUMMARY
echo "ZC_TOOLCHAIN=$ZC_TOOLCHAIN" >> $GITHUB_ENV
if [[ "$TOOLCHAIN" == 'nightly' ]]; then
  RUSTFLAGS="$RUSTFLAGS $ZC_NIGHTLY_RUSTFLAGS"
  MIRIFLAGS="$MIRIFLAGS $ZC_NIGHTLY_MIRIFLAGS"
  echo "Using nightly toolchain; setting RUSTFLAGS='$RUSTFLAGS' and MIRIFLAGS='$MIRIFLAGS'" | tee -a $GITHUB_STEP_SUMMARY
  echo "RUSTFLAGS=$RUSTFLAGS" >> $GITHUB_ENV
  echo "MIRIFLAGS=$MIRIFLAGS" >> $GITHUB_ENV
else
  echo "Using non-nightly toolchain; not modifying RUSTFLAGS='$RUSTFLAGS' or MIRIFLAGS='$MIRIFLAGS'" | tee -a $GITHUB_STEP_SUMMARY
fi
EOF
)"
expected_configure_run=$'set -euo pipefail\nMIRIFLAGS="${MIRIFLAGS:-}"\n'
expected_configure_run+="$expected_feature_mapping"
expected_configure_run+=$'\n''echo "FEATURES=$FEATURES" >> "$GITHUB_ENV"'
expected_configure_run+=$'\n'"$expected_configure_suffix"
[[ "$configure_run" == "$expected_configure_run" &&
   "$miri_configure_run" == "$expected_configure_run" ]] || \
  fail "matrix environment configuration must use the exact fail-closed program"
if ! jq -e '
  def step_ids: [.steps[] | (.name // .uses)];
  (.jobs.build_test | step_ids) == [
    "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
    "Download prebuilt Docker image",
    "Load prebuilt Docker image",
    "Create Docker Shell Wrapper",
    "Configure environment variables",
    "Test native target",
    "Check cross target",
    "Check thumb library",
    "Clippy",
    "Clippy tests",
    "Cargo doc",
    "Check whether to skip cargo-semver-checks",
    "Remove Cargo config and vendored dependencies",
    "Check semver compatibility"
  ] and
  (.jobs.miri | step_ids) == [
    "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
    "Download prebuilt Docker image",
    "Load prebuilt Docker image",
    "Create Docker Shell Wrapper",
    "Configure environment variables",
    "Run tests under Miri"
  ] and
  (.jobs.codegen | step_ids) == [
    "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
    "Install dependencies",
    "Clippy",
    "Run tests"
  ] and
  (.jobs.coverage | step_ids) == [
    "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
    "Generate code coverage",
    "Upload coverage to Codecov"
  ]
' "$workflow_json" >/dev/null; then
  fail "audited test jobs must preserve their exact step order"
fi
if ! jq -e '
  .jobs as $jobs
  | {"name": "Download prebuilt Docker image",
     "uses": "./.github/actions/download-artifact-with-retry",
     "with": {"artifact-id": "${{ needs.build_docker_env.outputs.image_artifact_id }}",
              "path": "${{ runner.temp }}",
              "expected-file": "${{ env.ZC_CI_IMAGE_ARCHIVE }}"}} as $download
  | {"name": "Load prebuilt Docker image", "shell": "bash",
     "env": {"IMAGE_ARCHIVE": "${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }}",
             "IMAGE_NAME": "${{ env.ZC_CI_IMAGE }}"}} as $load
  | {"name": "Create Docker Shell Wrapper", "shell": "bash"} as $wrapper
  | (($jobs.codegen | del(.steps)) == {
      "runs-on": "ubuntu-latest",
      "name": "Run codegen tests",
      "defaults": {"run": {"working-directory": "zerocopy"}}
    }) and
    (($jobs.coverage | del(.steps)) == {
      "runs-on": "ubuntu-latest",
      "name": "Generate code coverage",
      "defaults": {"run": {"working-directory": "zerocopy"}}
    }) and
    all([$jobs.build_test, $jobs.miri][];
      [.steps[] | select(.name == $download.name)] == [$download] and
      [.steps[] | select(.name == $load.name) | del(.run)] == [$load] and
      [.steps[] | select(.name == $wrapper.name) | del(.run)] == [$wrapper]) and
    all($jobs.codegen.steps[1:][]; (keys | sort) == ["name", "run"]) and
    (($jobs.coverage.steps[1] | keys | sort) == ["name", "run"])
' "$workflow_json" >/dev/null; then
  fail "audited setup steps must have their exact configuration"
fi

expected_load_image_run="$(normalize_run <<'EOF'
set -euo pipefail
trap 'rm -f -- "$IMAGE_ARCHIVE"' EXIT
docker load --input "$IMAGE_ARCHIVE"
docker image inspect "$IMAGE_NAME" >/dev/null
docker run --rm --entrypoint /bin/bash \
  --env BASH_ENV= --env SHELLOPTS= \
  "$IMAGE_NAME" -p -euo pipefail -c '
  cargo_home="${CARGO_HOME:-${HOME:-/root}/.cargo}"
  [[ "$cargo_home" == /root/.cargo ]]
  [[ -d /root && ! -L /root && -d "$cargo_home" && ! -L "$cargo_home" ]]
  [[ ! -L /home && ! -L /home/runner ]]
  for config_dir in "$cargo_home" /home/runner/.cargo /home/.cargo /.cargo; do
    [[ ! -L "$config_dir" ]]
    for config_name in config config.toml; do
      config_path="$config_dir/$config_name"
      [[ ! -e "$config_path" && ! -L "$config_path" ]]
    done
  done
'
EOF
)"
for job in build_test miri; do
  load_image_run="$(
    step_field "$job" 'Load prebuilt Docker image' run |
      sed '/^[[:space:]]*#/d' |
      normalize_run
  )"
  [[ "$load_image_run" == "$expected_load_image_run" ]] ||
    fail "$job must use the exact Docker image loading program"
done

profiles_with_std=()
for profile in "${profiles[@]}"; do
  policy_key="${profile//-/_}"
  if jq -e --arg key "$policy_key" \
      '.[$key] | index("std") != null' "$feature_policy_json" >/dev/null; then
    profiles_with_std+=("$profile")
  fi
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
  if [[ "$crate" == zerocopy && "$target" == thumbv6m-none-eabi ]] && \
      contains "$profile" "${profiles_with_std[@]}"; then
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
expected_cross_run="$(normalize_run <<'EOF'
./cargo.sh +$TOOLCHAIN check --tests --package $CRATE --target $TARGET $FEATURES --verbose
./cargo.sh +$TOOLCHAIN build --package $CRATE --target $TARGET $FEATURES --verbose
EOF
)"
[[ "$cross_run" == "$expected_cross_run" ]] || \
  fail "cross cells must check tests and build the library exactly once"

thumb_run="$(step_field build_test 'Check thumb library' run | normalize_run)"
thumb_if="$(step_field build_test 'Check thumb library' if)"
[[ "$thumb_if" == "$thumb_condition" ]] || fail "thumb step has the wrong target condition"
[[ "$thumb_run" == \
  './cargo.sh +$TOOLCHAIN check --package $CRATE --target $TARGET $FEATURES --verbose' ]] || \
  fail "thumb cells must check exactly the library"

if ! jq -e '
  (.manifest_path | sub("/Cargo.toml$"; "")) as $package_root
  | ([.targets[] | select(.name == "ui" and (.kind | index("test") != null))] | length == 1) and
  ([.targets[] | select(.name == "ui")][0]["required-features"] == ["derive"]) and
  ([.targets[] | select(.name == "ui")][0].test == true) and
  ([.targets[] | select(.name == "codegen" and (.kind | index("test") != null))] | length == 1) and
  ([.targets[] | select(.name == "codegen")][0].test == false) and
  ([.targets[] | select(.name == "zerocopy" and (.kind | index("lib") != null))]
   as $library
   | ($library | length == 1) and
     ($library[0].test == true) and
     ($library[0].doctest == true)) and
  all(.targets[] | select(
    (.kind | index("test") != null) and .name != "codegen"
  ); .test == true) and
  all(.targets[] | select(.kind | index("test") != null);
    .src_path == ($package_root + "/tests/" + .name + ".rs")) and
  all(.targets[] | select(
    (.kind | index("test") != null) and .name != "ui"
  ); ((.["required-features"] // []) == []))
' "$root_package_json" >/dev/null ||
    ! jq -e '
      (.manifest_path | sub("/Cargo.toml$"; "")) as $package_root
      | ([.targets[] | select(.name == "ui" and (.kind | index("test") != null))]
       | length == 1) and
      all(.targets[] | select(.kind | index("test") != null);
        (.test == true) and
        ((.["required-features"] // []) == []) and
        (.src_path == ($package_root + "/tests/" + .name + ".rs"))) and
      ([.targets[] | select(
        .name == "zerocopy_derive" and (.kind | index("proc-macro") != null)
      )] as $library
       | ($library | length == 1) and
         ($library[0].test == true) and
         ($library[0].doctest == true))
    ' "$derive_package_json" >/dev/null; then
  fail "Cargo must own UI/codegen eligibility and package test discovery"
fi

codegen_install="$(
  step_field codegen 'Install dependencies' run |
    sed '/^[[:space:]]*#/d' |
    normalize_run
)"
expected_codegen_install="$(normalize_run <<'EOF'
set -eo pipefail
sudo apt install -qq llvm
bash ../tools/install-cargo-show-asm.sh
EOF
)"
[[ "$codegen_install" == "$expected_codegen_install" ]] ||
  fail "codegen must install its exact audited dependencies"

codegen_clippy="$(step_field codegen Clippy run | normalize_run)"
codegen_test="$(step_field codegen 'Run tests' run | normalize_run)"
[[ "$codegen_clippy" == \
  './cargo.sh +nightly clippy --locked --package zerocopy --target x86_64-unknown-linux-gnu --all-features --test codegen --verbose -- -Dwarnings' ]] || \
  fail "codegen job must lint its exact all-feature target with warnings enabled"
[[ "$codegen_test" == \
  'RUSTFLAGS="$RUSTFLAGS -Awarnings" ./cargo.sh +nightly test --locked --package zerocopy --target x86_64-unknown-linux-gnu --all-features --verbose --test codegen' ]] || \
  fail "codegen job must execute its exact all-feature test target"

coverage_run="$(step_field coverage 'Generate code coverage' run | normalize_run)"
expected_coverage_run="$(normalize_run <<'EOF'
set -eo pipefail
./cargo.sh +nightly install --version 0.8.0 cargo-llvm-cov
./cargo.sh +nightly llvm-cov \
  --package zerocopy \
  --target x86_64-unknown-linux-gnu \
  --all-features \
  --doctests \
  --lcov \
  --output-path lcov.info \
  --verbose
EOF
)"
[[ "$coverage_run" == "$expected_coverage_run" ]] || \
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
       $configure[0].env == {
         "TOOLCHAIN": "${{ matrix.toolchain }}",
         "FEATURE_PROFILE": "${{ matrix.feature_profile }}"
       } and
       $run[0].env == {
         "TOOLCHAIN": "${{ matrix.toolchain }}",
         "CRATE": "${{ matrix.crate }}",
         "TARGET": "${{ matrix.target }}",
         "MIRI_MODEL_FLAGS": "${{ matrix.miri_model.flags }}"
       })
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

miri_run="$(
  step_field miri 'Run tests under Miri' run |
    sed '/^[[:space:]]*#/d' |
    normalize_run
)"
expected_miri_run="$(normalize_run <<'EOF'
set -euo pipefail
mv .cargo/config.toml .cargo/config.toml.bak
trap 'mv .cargo/config.toml.bak .cargo/config.toml' EXIT
[ "$TARGET" == "aarch64-unknown-linux-gnu" ] && cargo clean
THREADS=$(echo "$(nproc) * 2" | bc)
echo "Running Miri tests with $THREADS threads" | tee -a "$GITHUB_STEP_SUMMARY"
MIRIFLAGS="$MIRIFLAGS $MIRI_MODEL_FLAGS" ./cargo.sh +$TOOLCHAIN \
  miri nextest run --locked \
  --ignore-default-filter \
  --test-threads "$THREADS" \
  --package $CRATE \
  --target $TARGET \
  $FEATURES
EOF
)"
[[ "$miri_run" == "$expected_miri_run" ]] || \
  fail "Miri must use the exact fail-fast setup and terminal test invocation"

docker_shell_run="$(
  step_field build_test 'Create Docker Shell Wrapper' run |
    sed '/^[[:space:]]*# /d' |
    normalize_run
)"
miri_docker_shell_run="$(
  step_field miri 'Create Docker Shell Wrapper' run |
    sed '/^[[:space:]]*# /d' |
    normalize_run
)"
expected_docker_shell_run="$(normalize_run <<'EXPECTED_DOCKER'
set -eo pipefail
mkdir -p /home/runner/.docker-cargo/registry /home/runner/.docker-cargo/git
cat << 'EOF' > /tmp/docker-shell.sh
#!/bin/bash
docker run --rm -i \
  --entrypoint /bin/bash \
  --workdir "$PWD" \
  -v /home/runner/work:/home/runner/work \
  -v /home/runner/.docker-cargo/registry:/root/.cargo/registry \
  -v /home/runner/.docker-cargo/git:/root/.cargo/git \
  -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \
  -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \
  -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e FEATURES -e ZC_TOOLCHAIN \
  -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS -e MIRI_MODEL_FLAGS \
  -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \
  -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \
  -e ZC_SKIP_CARGO_SEMVER_CHECKS \
  -e BASH_ENV= -e SHELLOPTS= \
  "$ZC_CI_IMAGE" -p -c "git config --global --add safe.directory '*' && exec /bin/bash -p -e -o pipefail \"\$1\"" -- "$1"
EOF
chmod +x /tmp/docker-shell.sh
EXPECTED_DOCKER
)"
[[ "$docker_shell_run" == "$expected_docker_shell_run" &&
   "$miri_docker_shell_run" == "$expected_docker_shell_run" ]] || \
  fail "Docker shell wrapper must use the exact fail-fast container invocation"
if ! jq -e '
  . as $workflow
  | .jobs as $jobs
  | def expected_explicit_shell($job; $step):
      ($step.shell == "bash") and
      ((($job == "build_test" or $job == "miri") and
        ($step.name == "Load prebuilt Docker image" or
         $step.name == "Create Docker Shell Wrapper")) or
       ($job == "build_docker_env" and
        $step.name == "Generate sanitized Docker tag"));
    ($workflow | has("defaults") | not) and
    all($jobs | to_entries[];
      if (.key == "build_test" or .key == "miri")
      then .value.defaults == {"run": {
        "shell": "/tmp/docker-shell.sh {0}",
        "working-directory": "zerocopy"
      }}
      else ((.value.defaults.run? // {}) | has("shell") | not)
      end) and
    all([$jobs.build_test, $jobs.miri][] | .steps[];
      has("working-directory") | not) and
    all($jobs | to_entries[] as $job
        | $job.value.steps[]?
        | select(has("shell"))
        | [$job.key, .];
      . as $entry | expected_explicit_shell($entry[0]; $entry[1]))
' "$workflow_json" >/dev/null; then
  fail "workflow defaults and shells must match the audited policy"
fi

if ! jq -e '
  .jobs as $jobs
  | $jobs["all-jobs-succeed"] as $sentinel
  | (($sentinel | del(.needs, .steps)) == {
      "name": "All checks succeeded (ci.yml)",
      "if": "${{ always() }}",
      "runs-on": "ubuntu-latest"
    }) and
    (($sentinel.steps | map(.name // .uses)) == [
      "Reject workflow cancellation",
      "Require every dependency to succeed"
    ]) and
    (($sentinel.needs | type) == "array") and
    (($sentinel.needs | length) == ($sentinel.needs | unique | length)) and
    (($sentinel.needs | sort) ==
      ([$jobs | keys[] | select(. != "all-jobs-succeed")] | sort)) and
    ($sentinel.steps[0] == {
      "name": "Reject workflow cancellation",
      "if": "${{ cancelled() }}",
      "run": "exit 1"
    }) and
    (($sentinel.steps[1] | del(.run)) == {
      "name": "Require every dependency to succeed",
      "env": {
        "EVENT_NAME": "${{ github.event_name }}",
        "NEEDS_JSON": "${{ toJSON(needs) }}"
      }
    })
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
# the dev profile. Parse only manifests and Cargo configuration that can affect
# commands launched from the standalone zerocopy workspace.
profile_toml_files=()
while IFS= read -r profile_toml_file; do
  profile_toml_files+=("$profile_toml_file")
done < <(
  git -C .. ls-files -- \
    'zerocopy/Cargo.toml' \
    '.cargo/config' '.cargo/config.toml' \
    'zerocopy/.cargo/config' 'zerocopy/.cargo/config.toml'
)
for profile_toml_file in "${profile_toml_files[@]}"; do
  profile_toml_json="$tmp_dir/profile-input.json"
  if ! parse_toml "../$profile_toml_file" "$profile_toml_json"; then
    fail "could not parse $profile_toml_file as TOML"
  fi
  if jq -e '
    (.profile? // {}) as $profile
    | if ($profile | type) == "object"
      then ($profile | has("test"))
      else true
      end
  ' "$profile_toml_json" >/dev/null; then
    fail "$profile_toml_file defines a test-profile override"
  fi
  if jq -e 'has("include")' "$profile_toml_json" >/dev/null; then
    fail "$profile_toml_file includes Cargo configuration outside this audit"
  fi
  if jq -e '
    (.target? // {})
    | if type == "object"
      then any(.[]; type == "object" and has("runner"))
      else true
      end
  ' "$profile_toml_json" >/dev/null; then
    fail "$profile_toml_file defines a Cargo target runner"
  fi
done

cargo_env_overrides="$(
  git -C .. grep -nE 'CARGO_PROFILE_TEST_|CARGO_TARGET_[A-Z0-9_]+_RUNNER' -- \
    'zerocopy/Cargo.toml' '.cargo/**' 'zerocopy/.cargo/**' \
    '.github/workflows/ci.yml' '.github/workflows/Dockerfile' \
    'zerocopy/cargo.sh' 'tools/cargo-zerocopy/src/**' \
    || true
)"
if [[ -n "$cargo_env_overrides" ]]; then
  printf 'Cargo environment overrides invalidate single-pass native testing:\n%s\n' \
    "$cargo_env_overrides" >&2
  exit 1
fi
