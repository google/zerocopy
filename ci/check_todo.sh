#!/usr/bin/env bash
#
# Copyright 2025 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

# This allows us to leave XODO comments in this file and have them still be
# picked up by this script without having the script itself trigger false
# positives. The alternative would be to exclude this script entirely, which
# would mean that we couldn't use XODO comments in this script.
KEYWORD=$(echo XODO | sed -e 's/X/T/')

# Make sure `rg` is installed (if this fails, `set -e` above will cause the
# script to exit).
rg --version >/dev/null

# -H: Print filename (default for multiple files/recursive)
# -n: Print line number
# -w: Match whole words
# Match TODO, TODO-check-disable, and TODO-check-enable
PATTERN="$KEYWORD|$KEYWORD-check-disable|$KEYWORD-check-enable"
if [ "$#" -eq 0 ]; then
  # The no-argument CI mode enforces Zerocopy's strict TODO policy over
  # Zerocopy and shared repository machinery. Anneal and exocrate have their own
  # project norms and existing TODOs.
  PATHS=(ci githooks tools zerocopy)
else
  PATHS=("$@")
fi

# Discover all commits relative to `main` (falling back to `HEAD` when on `main`
# itself). Do not pass `--no-merges`: on a GitHub `pull_request` checkout,
# `HEAD` is a synthetic merge of `main` (`HEAD^1`) and the PR tip (`HEAD^2`), so
# `origin/main..HEAD` traverses `HEAD^2` and audits every commit in the PR
# (including authored merge commits) as well as the merged tree at `HEAD`.
base_ref=""
if git rev-parse --verify --quiet origin/main >/dev/null 2>&1; then
  base_ref="origin/main"
elif git rev-parse --verify --quiet main >/dev/null 2>&1; then
  base_ref="main"
fi

commits=""
if [ -n "$base_ref" ]; then
  commits=$(git rev-list "${base_ref}..HEAD" 2>/dev/null || true)
fi
if [ -z "$commits" ]; then
  commits=$(git rev-list -n 1 HEAD 2>/dev/null || true)
fi

# Vendored dependencies have their own task-marker norms; enforce this only on
# code we maintain.
output=$({
  if [ "$#" -gt 0 ] || [ -z "$commits" ] || [ -n "$(git status --porcelain 2>/dev/null || true)" ]; then
    rg -H -n -w --glob '!**/vendor/**' "$PATTERN" "${PATHS[@]}" || true
  fi

  for commit in $commits; do
    short_commit=$(git rev-parse --short=12 "$commit")
    git log -1 --pretty=%B "$commit" 2>/dev/null \
      | rg -n -w "$PATTERN" \
      | sed "s/^/COMMIT_MESSAGE(${short_commit}):/" || true
    git grep -I -n -w -E "$PATTERN" "$short_commit" -- "${PATHS[@]}" ':!**/vendor/**' 2>/dev/null \
      | sed "s/^${short_commit}:/${short_commit}@/" || true
  done
})

if [ -z "$output" ]; then
  exit 0
fi

# Track the disabled state for each file. Since we process lines in order for
# each file, we can maintain state. However, rg output might interleave files if
# not sorted, but usually it's grouped. To be safe, we sort the output by
# filename and line number.
sorted_output=$(echo "$output" | LC_ALL=C sort -t: -k1,1 -k2,2n)

exit_code=0
current_file=""
disabled=0

while IFS= read -r line; do
  if [[ "$line" =~ ^([^:]+):([0-9]+):(.*)$ ]]; then
    file="${BASH_REMATCH[1]}"
    content="${BASH_REMATCH[3]}"
  else
    echo "Error: could not parse rg output line: $line" >&2
    exit 1
  fi

  if [ "$file" != "$current_file" ]; then
    current_file="$file"
    disabled=0
  fi

  if [[ "$content" == *"$KEYWORD-check-disable"* ]]; then
    disabled=1
  elif [[ "$content" == *"$KEYWORD-check-enable"* ]]; then
    disabled=0
  elif [[ "$content" == *"$KEYWORD"* ]]; then
    if [ "$disabled" -eq 0 ]; then
      if [ "$exit_code" -eq 0 ]; then
        echo "Found $KEYWORD markers in the codebase." >&2
        echo "$KEYWORD is used for tasks that should be done before merging a PR; if you want to leave a message in the codebase, use FIXME." >&2
        echo "If you need to allow a $KEYWORD, wrap it in $KEYWORD-check-disable and $KEYWORD-check-enable." >&2
        echo "" >&2
        exit_code=1
      fi
      echo "$line" >&2
    fi
  fi
done <<< "$sorted_output"

exit $exit_code
