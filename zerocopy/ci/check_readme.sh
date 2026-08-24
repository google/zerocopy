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

# Install again in case the installation failed during the
# `generate_cache` step. We treat that step as best-effort and
# suppress all errors from it.
../tools/cargo.sh install -q cargo-readme --version 3.2.0 --locked

# `tools/cargo.sh` pins the compiler explicitly, defeating both
# RUSTUP_TOOLCHAIN and rustup directory overrides, and establishes the tools
# workspace as Cargo's discovery directory. Keep this invocation identical to
# the regeneration commands in `../src/lib.rs` and `../AGENTS.md`. The
# generator needs its source directory explicitly because its repository-layout
# auto-detection intentionally starts from the tools workspace.
diff <(
  ZEROCOPY_README_DIR=../zerocopy \
    ../tools/cargo.sh -q run --locked -p generate-readme
) README.md >&2
exit $?
