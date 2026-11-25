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

# Resolve explicit relative path arguments against the caller's working
# directory before switching to the repository root.
caller_pwd=$(pwd -P)
resolved_paths=()
for arg in "$@"; do
  if [ -z "$arg" ]; then
    echo "Error: path argument must not be empty" >&2
    exit 1
  fi
  if [[ "$arg" == /* ]]; then
    resolved_paths+=("$arg")
  else
    resolved_paths+=("$caller_pwd/$arg")
  fi
done

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
# Match the keyword and its check-disable / check-enable directives.
PATTERN="$KEYWORD|$KEYWORD-check-disable|$KEYWORD-check-enable"
if [ "${#resolved_paths[@]}" -gt 0 ]; then
  SEARCH_PATHS=("${resolved_paths[@]}")
else
  # The no-argument CI mode enforces Zerocopy's strict task-marker policy
  # over Zerocopy and shared repository machinery. Anneal and exocrate have
  # their own project norms and existing markers.
  SEARCH_PATHS=(ci githooks tools zerocopy)
fi

# Run a search command (`rg` or `git grep`) whose exit status is:
#   0: matches found
#   1: no matches found (allowed)
#   >=2: operational error (fail closed)
run_search_allow_nomatch() {
  local rc=0
  "$@" || rc=$?
  if [ "$rc" -ne 0 ] && [ "$rc" -ne 1 ]; then
    return "$rc"
  fi
  return 0
}

# Detect whether we are inside a Git work tree (`meta-todo` in `ci/checks.toml`
# runs in a `.git`-less sandbox, so Git discovery must be skipped there).
in_git_repo=0
if [ -e .git ]; then
  git rev-parse --is-inside-work-tree >/dev/null
  in_git_repo=1
fi

# Discover all commits relative to `main` (falling back to `HEAD` when on
# `main` itself). Do not pass `--no-merges`: on a GitHub `pull_request`
# checkout, `HEAD` is a synthetic merge of `main` (`HEAD^1`) and the PR tip
# (`HEAD^2`), so `origin/main..HEAD` traverses `HEAD^2` and audits every
# commit in the PR (including authored merge commits) as well as the merged
# tree at `HEAD`.
commits=""
if [ "$in_git_repo" -eq 1 ]; then
  base_ref=""
  if git rev-parse --verify --quiet origin/main >/dev/null 2>&1; then
    base_ref="origin/main"
  elif git rev-parse --verify --quiet main >/dev/null 2>&1; then
    base_ref="main"
  fi

  if [ -n "$base_ref" ]; then
    commits=$(git rev-list "${base_ref}..HEAD")
  fi
  if [ -z "$commits" ] &&
    git rev-parse --verify --quiet HEAD >/dev/null 2>&1; then
    commits=$(git rev-list -n 1 HEAD)
  fi
fi

exit_code=0

report_marker() {
  local line="$1"
  if [ "$exit_code" -eq 0 ]; then
    echo "Found $KEYWORD markers in the codebase." >&2
    echo "$KEYWORD is used for tasks that should be done before merging" \
      "a PR; if you want to leave a message in the codebase, use FIXME." >&2
    echo "If you need to allow a $KEYWORD in source or docs, wrap it in" \
      "$KEYWORD-check-disable and $KEYWORD-check-enable (commit messages" \
      "may not use disable directives)." >&2
    echo "" >&2
    exit_code=1
  fi
  echo "$line" >&2
}

# Audit commit messages separately from source/doc files so check-disable
# directives in commit messages can never suppress task markers.
for commit in $commits; do
  short_commit=$(git rev-parse --short=12 "$commit")
  commit_msg=$(git log -1 --pretty=%B "$commit")
  msg_matches=$(
    run_search_allow_nomatch rg -n -w "$PATTERN" <<< "$commit_msg"
  )
  if [ -n "$msg_matches" ]; then
    while IFS= read -r m; do
      [ -z "$m" ] && continue
      report_marker "COMMIT_MESSAGE(${short_commit}):${m}"
    done <<< "$msg_matches"
  fi
done

worktree_dirty=0
if [ "$in_git_repo" -eq 1 ]; then
  status_out=$(git status --porcelain)
  if [ -n "$status_out" ]; then
    worktree_dirty=1
  fi
fi

# Vendored dependencies have their own task-marker norms; enforce this only on
# code we maintain. Run each search at top level rather than inside a compound
# `$(...)` subshell so `set -e` never drops an intermediate non-zero exit code.
output=""
append_output() {
  local chunk="$1"
  if [ -n "$chunk" ]; then
    if [ -n "$output" ]; then
      output+=$'\n'"$chunk"
    else
      output="$chunk"
    fi
  fi
}

if [ "${#resolved_paths[@]}" -gt 0 ] || [ -z "$commits" ] ||
  [ "$worktree_dirty" -eq 1 ]; then
  wt_matches=$(
    run_search_allow_nomatch rg --no-heading -H -n -w \
      --glob '!**/vendor/**' "$PATTERN" -- "${SEARCH_PATHS[@]}"
  )
  append_output "$wt_matches"
fi

for commit in $commits; do
  short_commit=$(git rev-parse --short=12 "$commit")
  tree_matches=$(
    run_search_allow_nomatch git grep -I -n -w -E "$PATTERN" \
      "$short_commit" -- "${SEARCH_PATHS[@]}" ':!**/vendor/**'
  )
  if [ -n "$tree_matches" ]; then
    while IFS= read -r m; do
      [ -z "$m" ] && continue
      append_output "${m/#${short_commit}:/${short_commit}@}"
    done <<< "$tree_matches"
  fi
done

if [ -z "$output" ]; then
  exit "$exit_code"
fi

# Track the disabled state for each file. Because `rg` output can interleave
# files or lines across scans, sort by filename and line number first.
sorted_output=$(printf '%s\n' "$output" | LC_ALL=C sort -t: -k1,1 -k2,2n)

current_file=""
disabled=0

while IFS= read -r line; do
  [ -z "$line" ] && continue
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
      report_marker "$line"
    fi
  fi
done <<< "$sorted_output"

exit "$exit_code"
