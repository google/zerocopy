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

readonly SCRIPT_NAME="ci/run_build_test_cell.sh"

# This is the single source of truth for how the build matrix can exercise a
# target on an x86_64 Linux GitHub Actions runner. Keep this table exhaustive:
# an unclassified target is an error rather than silently receiving weaker
# coverage. `ci/check_all_toolchains_tested.sh` compares `--describe` with the
# workflow matrix and exercises `--plan` for every supported feature profile.
#
# The three modes are:
#
# - run: compile and run every default-selected test target;
# - compile-tests: type-check tests, then code-generate the library; and
# - library-only: type-check the library without its incompatible dev-deps.
readonly TARGET_SPECS=(
  "i686-unknown-linux-gnu|run"
  "x86_64-unknown-linux-gnu|run"
  "arm-unknown-linux-gnueabi|compile-tests"
  "aarch64-unknown-linux-gnu|compile-tests"
  "powerpc-unknown-linux-gnu|compile-tests"
  "powerpc64-unknown-linux-gnu|compile-tests"
  "riscv64gc-unknown-linux-gnu|compile-tests"
  "s390x-unknown-linux-gnu|compile-tests"
  "x86_64-pc-windows-msvc|compile-tests"
  "thumbv6m-none-eabi|library-only"
  "wasm32-unknown-unknown|compile-tests"
)

usage() {
  cat >&2 <<EOF
usage: $SCRIPT_NAME <toolchain> <crate> <target> <feature-profile>
       $SCRIPT_NAME --plan <toolchain> <crate> <target> <feature-profile>
       $SCRIPT_NAME --describe
EOF
}

fail() {
  echo "$SCRIPT_NAME: $*" >&2
  exit 1
}

target_mode() {
  local requested="$1"
  local spec target mode

  for spec in "${TARGET_SPECS[@]}"; do
    target="${spec%%|*}"
    mode="${spec#*|}"
    if [[ "$requested" == "$target" ]]; then
      echo "$mode"
      return
    fi
  done

  fail "target '$requested' has no build/test mode"
}

describe() {
  # JSON keeps the checker independent of shell parsing details. Generate it
  # from TARGET_SPECS so execution and validation cannot drift apart.
  local spec target mode separator=""

  printf '{"schema_version":1,"targets":['
  for spec in "${TARGET_SPECS[@]}"; do
    target="${spec%%|*}"
    mode="${spec#*|}"
    printf '%s{"target":"%s","mode":"%s"}' \
      "$separator" "$target" "$mode"
    separator=,
  done
  printf ']}\n'
}

args_json() {
  if [[ $# -eq 0 ]]; then
    echo '[]'
    return
  fi

  jq -cn --args '$ARGS.positional' -- "$@"
}

emit_plan() {
  local toolchain="$1"
  local crate="$2"
  local target="$3"
  local feature_profile="$4"
  local mode="$5"
  shift 5

  local feature_json
  feature_json="$(args_json "$@")"

  jq -cn \
    --arg toolchain "$toolchain" \
    --arg crate "$crate" \
    --arg target "$target" \
    --arg feature_profile "$feature_profile" \
    --arg mode "$mode" \
    --argjson feature_args "$feature_json" \
    --argjson commands "$COMMANDS_JSON" \
    '{
      schema_version: 1,
      toolchain: $toolchain,
      crate: $crate,
      target: $target,
      feature_profile: $feature_profile,
      mode: $mode,
      feature_args: $feature_args,
      commands: $commands
    }'
}

run_cargo() {
  if [[ "$PLAN_ONLY" -eq 1 ]]; then
    # Capture the exact argv assembled by the execution path. The invariant
    # checker can therefore prove that runnable cells contain no selectors or
    # libtest filters rather than trusting a second, abstract description.
    local command_json
    command_json="$(args_json "$@")"
    COMMANDS_JSON="$(jq -cn \
      --argjson commands "$COMMANDS_JSON" \
      --argjson command "$command_json" \
      '$commands + [$command]')"
    return
  fi

  printf 'Running:'
  printf ' %q' "$@"
  printf '\n'
  "$@"
}

check_ci_test_profile_contract() {
  # The checker parses every repository Cargo config and scans the workflow and
  # Dockerfile for profile environment variables. The running image can still
  # acquire a global Cargo config from its base image or a Docker RUN command,
  # so close that final boundary immediately before executing Cargo in CI.
  #
  # Reject the entire global config rather than trying to parse it here: yq is
  # intentionally not part of the build image, and repository-owned settings
  # belong in `.cargo/config.toml`, where the checker can audit them. Local
  # developer configs remain supported because this guard is CI-only.
  if [[ "${CI:-}" != "true" ]]; then
    return
  fi

  local cargo_home="${CARGO_HOME:-}"
  if [[ -z "$cargo_home" ]]; then
    [[ -n "${HOME:-}" ]] || fail "CI defines neither CARGO_HOME nor HOME"
    cargo_home="$HOME/.cargo"
  fi

  local config
  for config in "$cargo_home/config" "$cargo_home/config.toml"; do
    if [[ -e "$config" ]]; then
      fail "CI Cargo home contains '$config'; re-audit the single-pass native test contract"
    fi
  done

  # Environment variables have higher precedence than manifest/config values.
  # Inspect names rather than a fixed option list so every current or future
  # CARGO_PROFILE_TEST_* setting fails closed.
  local environment_name
  while IFS= read -r environment_name; do
    case "$environment_name" in
      CARGO_PROFILE_TEST_*)
        fail "CI sets '$environment_name'; re-audit the single-pass native test contract"
        ;;
    esac
  done < <(compgen -e)
}

if [[ $# -eq 1 && "$1" == "--describe" ]]; then
  describe
  exit
fi

PLAN_ONLY=0
if [[ $# -gt 0 && "$1" == "--plan" ]]; then
  PLAN_ONLY=1
  shift
fi
COMMANDS_JSON='[]'

if [[ $# -ne 4 ]]; then
  usage
  exit 1
fi

readonly TOOLCHAIN="$1"
readonly CRATE="$2"
readonly TARGET="$3"
readonly FEATURE_PROFILE="$4"
MODE="$(target_mode "$TARGET")"
readonly MODE

# feature_profile.sh emits a deliberately small, shell-like argument string.
# Split it into an array without `eval`: Cargo feature names cannot contain
# whitespace, and every option emitted by that helper is one word. Quoted array
# expansion below prevents pathname expansion and preserves argument bounds.
feature_output="$(./ci/feature_profile.sh "$FEATURE_PROFILE")"
FEATURE_ARGS=()
if [[ -n "$feature_output" ]]; then
  if [[ "$feature_output" == *$'\n'* ]]; then
    fail "feature profile output must be a single line"
  fi
  read -r -a FEATURE_ARGS <<< "$feature_output"
fi
readonly FEATURE_ARGS

if [[ "$PLAN_ONLY" -eq 0 ]]; then
  check_ci_test_profile_contract
fi

# Cargo.toml, rather than a libtest name filter here, owns exceptional test
# targets. The UI target declares the feature it needs; the codegen target is
# excluded from default test selection and is run and linted by its dedicated
# CI job. cargo-zerocopy and the UI harness arrange for unsupported toolchains
# to report the UI test as ignored. This lets every runnable cell use one
# unfiltered default `cargo test`, so future default-selected tests run
# automatically.
case "$MODE" in
  run)
    run_cargo \
      ./cargo.sh "+$TOOLCHAIN" test \
      --package "$CRATE" \
      --target "$TARGET" \
      "${FEATURE_ARGS[@]}" \
      --verbose
    ;;
  compile-tests)
    # These targets cannot execute on the runner. `check --tests` covers their
    # test-only code without linking, while `build` still exercises codegen for
    # the library's ordinary artifact.
    run_cargo \
      ./cargo.sh "+$TOOLCHAIN" check \
      --tests \
      --package "$CRATE" \
      --target "$TARGET" \
      "${FEATURE_ARGS[@]}" \
      --verbose
    run_cargo \
      ./cargo.sh "+$TOOLCHAIN" build \
      --package "$CRATE" \
      --target "$TARGET" \
      "${FEATURE_ARGS[@]}" \
      --verbose
    ;;
  library-only)
    # thumbv6m cannot check tests because memchr, a dev-dependency, does not
    # support the target. Keep this exception explicit and fail closed if the
    # workflow adds another target with the same limitation.
    run_cargo \
      ./cargo.sh "+$TOOLCHAIN" check \
      --package "$CRATE" \
      --target "$TARGET" \
      "${FEATURE_ARGS[@]}" \
      --verbose
    ;;
  *)
    fail "internal error: unknown build/test mode '$MODE'"
    ;;
esac

if [[ "$PLAN_ONLY" -eq 1 ]]; then
  emit_plan \
    "$TOOLCHAIN" \
    "$CRATE" \
    "$TARGET" \
    "$FEATURE_PROFILE" \
    "$MODE" \
    "${FEATURE_ARGS[@]}"
fi
