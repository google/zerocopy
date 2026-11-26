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

if ! command -v yq >/dev/null 2>&1; then
  echo "Error: yq is required on PATH" >&2
  exit 1
fi

failed=0

report_failure() {
  echo "$1" | tee -a "${GITHUB_STEP_SUMMARY:-/dev/null}" >&2
  failed=1
}

# Verify that every local PR or reusable workflow under `.github/workflows/`
# defines an `all-jobs-succeed` gate whose `needs` lists every other job, and
# that any `../.github/workflows/` workflow defining `all-jobs-succeed` lists
# every other job in `needs` (thin `ci-core` caller workflows in
# `../.github/workflows/` are statically validated by `ci-core verify-repo`).
shopt -s nullglob
workflows=(
  ../.github/workflows/*.yml
  ../.github/workflows/*.yaml
  .github/workflows/*.yml
  .github/workflows/*.yaml
)

for i in "${workflows[@]}"; do
  # Explicitly validate YAML parseability before inspecting `.on` so malformed
  # or empty workflow files never silently skip the dependency check.
  if ! yq -e '.' "$i" >/dev/null; then
    report_failure "$i: failed to parse workflow YAML"
    continue
  fi

  # Handle both `kislyuk/yq` (`string`/`array`/`object`/`null`) and
  # `mikefarah/yq` v4 (`!!str`/`!!seq`/`!!map`/`!!null`) type names.
  on_type=$(yq -r '.on | type' "$i")
  triggers_pr_or_call=0
  case "$on_type" in
    string|'!!str')
      on_val=$(yq -r '.on' "$i")
      if [ "$on_val" = "pull_request" ] || [ "$on_val" = "workflow_call" ]; then
        triggers_pr_or_call=1
      fi
      ;;
    array|'!!seq')
      on_entries=$(yq -r '.on[]' "$i")
      if [ -n "$on_entries" ] && grep -Fxq -e 'pull_request' -e 'workflow_call' <<< "$on_entries"; then
        triggers_pr_or_call=1
      fi
      ;;
    object|'!!map')
      on_keys=$(yq -r '.on | keys | .[]' "$i")
      if [ -n "$on_keys" ] && grep -Fxq -e 'pull_request' -e 'workflow_call' <<< "$on_keys"; then
        triggers_pr_or_call=1
      fi
      ;;
    *)
      report_failure "$i: missing or unsupported 'on' trigger type: $on_type"
      continue
      ;;
  esac

  if [ "$triggers_pr_or_call" -eq 0 ]; then
    continue
  fi

  jobs_type=$(yq -r '.jobs | type' "$i")
  if [ "$jobs_type" != "object" ] && [ "$jobs_type" != "!!map" ]; then
    report_failure "$i: missing or invalid 'jobs' mapping (got $jobs_type)"
    continue
  fi

  all_jobs=$(yq -r '.jobs | keys | .[]' "$i")
  if [ -z "$all_jobs" ] || ! grep -Fxq 'all-jobs-succeed' <<< "$all_jobs"; then
    if [[ "$i" == .github/workflows/* ]]; then
      report_failure "$i: missing required all-jobs-succeed job"
    fi
    continue
  fi

  needs_type=$(yq -r '.jobs["all-jobs-succeed"].needs | type' "$i")
  needs_jobs=""
  case "$needs_type" in
    array|'!!seq')
      needs_jobs=$(yq -r '.jobs["all-jobs-succeed"].needs[]' "$i")
      ;;
    null|'!!null')
      needs_jobs=""
      ;;
    *)
      report_failure "$i: all-jobs-succeed.needs must be a YAML sequence (got $needs_type)"
      continue
      ;;
  esac

  other_jobs=$(printf '%s\n' "$all_jobs" | awk 'NF && $0 != "all-jobs-succeed"' | LC_ALL=C sort -u)
  sorted_needs=$(printf '%s\n' "$needs_jobs" | awk 'NF' | LC_ALL=C sort -u)

  missing=$(comm -23 \
    <(if [ -n "$other_jobs" ]; then printf '%s\n' "$other_jobs"; fi) \
    <(if [ -n "$sorted_needs" ]; then printf '%s\n' "$sorted_needs"; fi))

  if [ -n "$missing" ]; then
    missing_jobs=$(printf '%s\n' "$missing" | tr '\n' ' ')
    report_failure "$i: all-jobs-succeed missing dependencies on some jobs: $missing_jobs"
  fi
done

exit "$failed"
