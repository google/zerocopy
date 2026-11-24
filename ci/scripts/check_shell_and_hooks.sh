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

cd "$(dirname "$0")/../.."

REQUIRE_SHELLCHECK=0
for arg in "$@"; do
  case "$arg" in
    --require-shellcheck)
      REQUIRE_SHELLCHECK=1
      ;;
    *)
      echo "error: unknown argument: $arg" >&2
      exit 2
      ;;
  esac
done

shopt -s nullglob
SHELL_FILES=(
  githooks/pre-push
  ci/*.sh
  ci/scripts/*.sh
  zerocopy/cargo.sh
  zerocopy/ci/*.sh
  anneal/ci/*.sh
  .github/scripts/*.sh
  tools/*.sh
)
shopt -u nullglob

for f in "${SHELL_FILES[@]}"; do
  bash -n "$f"
done

if command -v shellcheck >/dev/null 2>&1; then
  shellcheck -S warning "${SHELL_FILES[@]}"
elif [[ "$REQUIRE_SHELLCHECK" -eq 1 ]]; then
  echo "error: shellcheck is required under --require-shellcheck" >&2
  exit 1
fi

# Verify that `githooks/pre-push` invokes every top-level check script in `ci/`
# and `zerocopy/ci/` (excluding release, formatting-delegate, todo, and heavy
# packaging scripts).
shopt -s extglob nullglob
GLOBIGNORE="./*/@(release_crate_version|check_todo).sh"
for f in ./ci/*.sh ./ci/*.py; do
  if ! grep -F "$f" githooks/pre-push >/dev/null; then
    echo "$f not called from githooks/pre-push" >&2
    exit 1
  fi
done
GLOBIGNORE="./zerocopy/ci/@(release_crate_version|check_fmt|check_packaging).sh"
for f in ./zerocopy/ci/*; do
  if ! grep -F "$f" githooks/pre-push >/dev/null; then
    echo "$f not called from githooks/pre-push" >&2
    exit 1
  fi
done
unset GLOBIGNORE
shopt -u extglob nullglob
