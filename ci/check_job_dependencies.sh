#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/.."
which yq > /dev/null
failed=0

report() {
  echo "$1" >&2
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    echo "$1" >> "$GITHUB_STEP_SUMMARY"
  fi
}

while IFS= read -r -d '' workflow; do
  if ! yq -e '.jobs | has("all-jobs-succeed")' \
      "$workflow" 2>/dev/null >/dev/null; then
    continue
  fi

  all_jobs="$(
    yq -r '.jobs | keys | .[]' "$workflow" \
      | grep -v '^all-jobs-succeed$' \
      | sort -u
  )"
  dependencies="$(
    yq -r '.jobs["all-jobs-succeed"].needs[]?' "$workflow" \
      | sort -u
  )"

  missing="$(comm -23 <(echo "$all_jobs") <(echo "$dependencies"))"
  unexpected="$(comm -13 <(echo "$all_jobs") <(echo "$dependencies"))"
  if [ -n "$missing" ]; then
    report "$workflow: all-jobs-succeed is missing dependencies: $(tr '\n' ' ' <<< "$missing")"
    failed=1
  fi
  if [ -n "$unexpected" ]; then
    report "$workflow: all-jobs-succeed has unknown dependencies: $(tr '\n' ' ' <<< "$unexpected")"
    failed=1
  fi

  dependency_count="$(
    yq -r '.jobs["all-jobs-succeed"].needs | length' "$workflow"
  )"
  unique_dependency_count="$(
    yq -r '.jobs["all-jobs-succeed"].needs | unique | length' "$workflow"
  )"
  if [ "$dependency_count" -ne "$unique_dependency_count" ]; then
    report "$workflow: all-jobs-succeed contains duplicate dependencies"
    failed=1
  fi

  condition="$(yq -r '.jobs["all-jobs-succeed"].if // ""' "$workflow")"
  condition="$(tr -d '[:space:]' <<< "$condition")"
  if [ "$condition" != '${{always()}}' ] && [ "$condition" != 'always()' ]; then
    report "$workflow: all-jobs-succeed must use if: always()"
    failed=1
  fi

  # GitHub only permits the cancelled() status function in job and step `if`
  # expressions. In particular, moving it into an action input makes GitHub
  # reject the workflow before CI can report a failure. Require a fail-closed
  # inline guard as the first step, before checkout or the shared action can be
  # skipped, and reject continue-on-error on either the guard or its job. Keep
  # this exact contract coordinated with the gate jobs in ci.yml and
  # anneal.yml.
  cancellation_guard_count="$(
    yq -r '[.jobs["all-jobs-succeed"].steps[]? | select(.name == "Reject workflow cancellation" and (.if == "${{ cancelled() }}" or .if == "cancelled()") and .run == "exit 1" and ((.["continue-on-error"] // false) == false))] | length' \
      "$workflow"
  )"
  first_step_is_guard="$(
    yq -r '[.jobs["all-jobs-succeed"].steps[0] | select(.name == "Reject workflow cancellation" and (.if == "${{ cancelled() }}" or .if == "cancelled()") and .run == "exit 1" and ((.["continue-on-error"] // false) == false))] | length' \
      "$workflow"
  )"
  gate_continue_on_error="$(
    yq -r '.jobs["all-jobs-succeed"]["continue-on-error"] // false' \
      "$workflow"
  )"
  if [ "$cancellation_guard_count" -ne 1 ] || \
      [ "$first_step_is_guard" -ne 1 ] || \
      [ "$gate_continue_on_error" != false ]; then
    report "$workflow: all-jobs-succeed must reject cancellation in its first, fail-closed step"
    failed=1
  fi

  checker_count="$(
    yq -r '[.jobs["all-jobs-succeed"].steps[]? | select(.uses == "./.github/actions/require-successful-jobs")] | length' \
      "$workflow"
  )"
  if [ "$checker_count" -ne 1 ]; then
    report "$workflow: all-jobs-succeed must invoke the shared result checker exactly once"
    failed=1
  fi
done < <(find .github -type f \( -iname '*.yaml' -o -iname '*.yml' \) -print0)

if [ "$failed" -eq 1 ]; then
  exit 1
fi
