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

# This allows us to leave XODO comments in this file and have them still be
# picked up by this script without having the script itself trigger false
# positives. The alternative would be to exclude this script entirely, which
# would mean that we couldn't use XODO comments in this script.
KEYWORD=$(echo XODO | sed -e 's/X/T/')

# TODO

# Make sure `rg` is installed (if this fails, `set -e` above will cause the
# script to exit).
rg --version >/dev/null

# -H: Print filename (default for multiple files/recursive)
# -n: Print line number
# -w: Match whole words
output=$(rg -H -n -w "$KEYWORD" || true)

if [ -n "$output" ]; then
  echo "Found $KEYWORD markers in the codebase." >&2
  echo "$KEYWORD is used for tasks that should be done before merging a PR; if you want to leave a message in the codebase, use FIXME." >&2
  echo "" >&2
  if [ "${GITHUB_ACTIONS:-false}" == "true" ]; then
    echo "$output" | while IFS= read -r output; do
      # Parse format `file:line: message`
      file=$(echo "$output" | cut -d : -f 1)
      line=$(echo "$output" | cut -d : -f 2)
      message=$(echo "$output" | cut -d : -f 3-)

      # Escape message for workflow command: % -> %25, \r -> %0D, \n -> %0A
      message="${message//'%'/'%25'}"
      message="${message//$'\r'/'%0D'}"
      message="${message//$'\n'/'%0A'}"

      # Output the workflow command for GitHub Actions annotations. Use `::notice`
      # rather than `::error` so that the output is less visually distracting (the
      # `exit 1` below will still ensure that this causes CI to fail).
      echo "::notice file=${file},line=${line},endLine=${line},title=$KEYWORD Found::${message}"
    done
  else
    echo "$output" >&2
  fi

  exit 1
fi
