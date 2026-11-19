#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Fetch the two pinned upstream trees examined by REPORT.md into
# <dest>/seL4 and <dest>/l4v using only HTTP GET requests, and confirm that
# each archive is the pinned commit.
#
# Usage: fetch_subjects.sh <dest-dir>

set -euo pipefail

dest=${1:?usage: fetch_subjects.sh <dest-dir>}
mkdir -p "$dest"

fetch() {
  local repo=$1 commit=$2
  local tarball="$dest/$repo.tar.gz"
  curl -sS -L --fail -o "$tarball" \
    "https://codeload.github.com/seL4/$repo/tar.gz/$commit"
  # `git archive` records the commit id in a pax header; GitHub archives
  # keep it, so this checks the archive against the pin. The reader exits
  # after the header, so tolerate the resulting SIGPIPE in `gzip`.
  local got
  got=$( (gzip -dc "$tarball" 2>/dev/null || true) | git get-tar-commit-id)
  if [ "$got" != "$commit" ]; then
    echo "error: $repo archive is commit $got, expected $commit" >&2
    exit 1
  fi
  rm -rf "${dest:?}/$repo"
  mkdir -p "$dest/$repo"
  tar -xzf "$tarball" -C "$dest/$repo" --strip-components=1
  echo "$repo $commit -> $dest/$repo"
}

fetch seL4 08c7e5fddb3111ff377745c8eefb07feb5c4cfb7
fetch l4v b0fe7693ca5943e08c49e038d33fd64dc7dfa72e
