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
which yq > /dev/null
failed=0

# Verify that every PR or reusable workflow defines an `all-jobs-succeed` gate
# whose `needs` lists every other job in that workflow, so branch protection
# cannot miss a job result.
shopt -s nullglob
for i in ../.github/workflows/anneal-current.yml .github/workflows/*.yml .github/workflows/*.yaml; do
  if yq -e '.on | has("pull_request") or has("workflow_call")' "$i" >/dev/null 2>&1; then
    missing=$(comm -23 \
      <(yq -r '.jobs | keys | .[]' "$i" | grep -v '^all-jobs-succeed$' | sort -u) \
      <(yq -r '.jobs["all-jobs-succeed"].needs[]?' "$i" | sort -u))

    if [ -n "$missing" ]; then
      missing_jobs="$(echo "$missing" | tr '\n' ' ')"
      echo "$i: all-jobs-succeed missing dependencies on some jobs: $missing_jobs" | tee -a "${GITHUB_STEP_SUMMARY:-/dev/null}" >&2
      failed=1
    fi
  fi
done

exit "$failed"
