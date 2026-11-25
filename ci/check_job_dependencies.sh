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

if [ ! -d .github ]; then
  echo "Error: .github directory not found" >&2
  exit 1
fi

failed=0

report_failure() {
  local msg="$1"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    echo "$msg" | tee -a "$GITHUB_STEP_SUMMARY" >&2
  else
    echo "$msg" >&2
  fi
  failed=1
}

has_line() {
  local needle="$1"
  local haystack="$2"
  local line=""
  while IFS= read -r line; do
    if [ "$line" = "$needle" ]; then
      return 0
    fi
  done <<< "$haystack"
  return 1
}

seen_workflow=0

while IFS= read -r -d '' i; do
  # Validate every YAML file under `.github/` before trigger inspection so
  # malformed or empty files fail closed rather than silently skipping checks.
  if ! yq -e '.' "$i" >/dev/null; then
    report_failure "$i: failed to parse YAML"
    continue
  fi

  # Non-workflow YAML files (actions, dependabot, issue templates) do not carry
  # workflow `.on` or `.jobs` definitions.
  case "$i" in
    .github/workflows/*)
      if [[ "$i" == .github/workflows/*/* ]]; then
        continue
      fi
      ;;
    *)
      continue
      ;;
  esac

  seen_workflow=1

  # Support both `kislyuk/yq` (`string`/`array`/`object`/`null`) and
  # `mikefarah/yq` v4 (`!!str`/`!!seq`/`!!map`/`!!null`) type names.
  on_type=$(yq -r '.on | type' "$i")
  is_pr=0
  case "$on_type" in
    string|'!!str')
      on_val=$(yq -r '.on' "$i")
      if [ "$on_val" = "pull_request" ]; then
        is_pr=1
      fi
      ;;
    array|'!!seq')
      on_entries=$(yq -r '.on[]' "$i")
      if has_line "pull_request" "$on_entries"; then
        is_pr=1
      fi
      ;;
    object|'!!map')
      on_keys=$(yq -r '.on | keys | .[]' "$i")
      if has_line "pull_request" "$on_keys"; then
        is_pr=1
      fi
      ;;
    *)
      report_failure "$i: missing or unsupported 'on' trigger type: $on_type"
      continue
      ;;
  esac

  jobs_type=$(yq -r '.jobs | type' "$i")
  if [ "$jobs_type" != "object" ] && [ "$jobs_type" != "!!map" ]; then
    report_failure "$i: missing or invalid 'jobs' mapping (got $jobs_type)"
    continue
  fi

  all_jobs=$(yq -r '.jobs | keys | .[]' "$i")
  job_count=$(
    printf '%s\n' "$all_jobs" | awk 'NF { count++ } END { print count + 0 }'
  )
  if [ "$job_count" -eq 0 ]; then
    report_failure "$i: workflow must define at least one job"
    continue
  fi

  has_gate=0
  if has_line "all-jobs-succeed" "$all_jobs"; then
    has_gate=1
  fi

  # Single-job `pull_request` workflows (such as `ci-core-pr.yml` and
  # `dependency-review.yml`) intentionally omit `all-jobs-succeed`.
  if [ "$is_pr" -eq 1 ] && [ "$job_count" -ge 2 ] && [ "$has_gate" -eq 0 ]; then
    report_failure \
      "$i: pull_request workflow with $job_count jobs missing all-jobs-succeed"
    continue
  fi

  if [ "$has_gate" -eq 0 ]; then
    continue
  fi

  needs_type=$(yq -r '.jobs["all-jobs-succeed"].needs | type' "$i")
  needs_jobs=""
  case "$needs_type" in
    array|'!!seq')
      needs_elem_types=$(
        yq -r '.jobs["all-jobs-succeed"].needs[] | type' "$i"
      )
      invalid_elem=$(
        printf '%s\n' "$needs_elem_types" | awk \
          'NF && $0 != "string" && $0 != "!!str" { print; exit }'
      )
      if [ -n "$invalid_elem" ]; then
        report_failure \
          "$i: all-jobs-succeed.needs entries must be strings ($invalid_elem)"
        continue
      fi
      needs_jobs=$(yq -r '.jobs["all-jobs-succeed"].needs[]' "$i")
      elem_count=$(
        printf '%s\n' "$needs_elem_types" |
          awk 'NF { count++ } END { print count + 0 }'
      )
      nonempty_needs=$(
        printf '%s\n' "$needs_jobs" |
          awk 'NF { count++ } END { print count + 0 }'
      )
      if [ "$elem_count" -ne "$nonempty_needs" ] ||
        [ "$nonempty_needs" -eq 0 ]; then
        report_failure \
          "$i: all-jobs-succeed.needs must be a non-empty list of job names"
        continue
      fi
      ;;
    string|'!!str')
      needs_val=$(yq -r '.jobs["all-jobs-succeed"].needs' "$i")
      if [ -z "$needs_val" ]; then
        report_failure "$i: all-jobs-succeed.needs must not be empty"
        continue
      fi
      needs_jobs="$needs_val"
      ;;
    *)
      report_failure \
        "$i: all-jobs-succeed.needs invalid type (got $needs_type)"
      continue
      ;;
  esac

  other_jobs=$(
    printf '%s\n' "$all_jobs" \
      | awk 'NF && $0 != "all-jobs-succeed"' \
      | LC_ALL=C sort -u
  )
  sorted_needs=$(
    printf '%s\n' "$needs_jobs" \
      | awk 'NF' \
      | LC_ALL=C sort -u
  )

  missing=$(LC_ALL=C comm -23 \
    <(if [ -n "$other_jobs" ]; then printf '%s\n' "$other_jobs"; fi) \
    <(if [ -n "$sorted_needs" ]; then printf '%s\n' "$sorted_needs"; fi))

  if [ -n "$missing" ]; then
    missing_jobs=$(printf '%s\n' "$missing" | tr '\n' ' ')
    report_failure \
      "$i: all-jobs-succeed missing dependencies on some jobs: $missing_jobs"
  fi
done < <(
  find .github \( -iname '*.yaml' -o -iname '*.yml' \) -print0 \
    | LC_ALL=C sort -z
)

if [ "$seen_workflow" -eq 0 ] && [ "$failed" -eq 0 ]; then
  report_failure ".github/workflows: no workflow YAML files found"
fi

if [ "$failed" -eq 1 ]; then
  exit 1
fi
