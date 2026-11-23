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

if ! command -v cargo-readme >/dev/null 2>&1; then
  (
    cd ..
    cargo install -q cargo-readme --version 3.2.0
  )
fi

if [[ -n "${GENERATE_README_BIN:-}" ]]; then
  diff <("$GENERATE_README_BIN") README.md >&2
else
  diff <(cd .. && cargo -q run --locked --manifest-path tools/generate-readme/Cargo.toml) README.md >&2
fi
exit $?
