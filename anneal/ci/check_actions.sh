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

export PATH="$HOME/.cargo/bin:$PATH"
if ! command -v action-validator >/dev/null 2>&1; then
  cargo install -q action-validator --version 0.8.0 --locked
fi

shopt -s nullglob
files=(../.github/workflows/ci-*.yml .github/workflows/*.yml .github/workflows/*.yaml)
if [ "${#files[@]}" -eq 0 ]; then
  echo "anneal/ci/check_actions.sh: expected at least one workflow file" >&2
  exit 1
fi
action-validator "${files[@]}"
# Validate `release.yml` from the repository root so `action-validator`
# resolves its `on.push.paths` globs (`zerocopy/Cargo.toml`) accurately.
(cd .. && action-validator .github/workflows/release.yml)
