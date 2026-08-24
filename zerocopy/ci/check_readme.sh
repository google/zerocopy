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

# Run repository tools with the exact compiler recorded by the tools
# workspace. An explicit `+<toolchain>` also defeats RUSTUP_TOOLCHAIN and a
# persisted rustup directory override. Keep this deliberately narrow parser
# coordinated with `../../tools/rust-toolchain.toml`, `../../ci/check_tools.sh`,
# `../cargo.sh`, and `../win-cargo.bat`; a changed or duplicate declaration
# must fail closed rather than silently selecting another compiler.
TOOLS_TOOLCHAIN="$(
  sed -nE 's/^channel = "([0-9]+\.[0-9]+\.[0-9]+)"$/\1/p' \
    ../tools/rust-toolchain.toml
)"
if [[ -z "$TOOLS_TOOLCHAIN" || "$TOOLS_TOOLCHAIN" == *$'\n'* ]]; then
  echo "Expected one exact channel in tools/rust-toolchain.toml" >&2
  exit 1
fi

# Install again in case the installation failed during the
# `generate_cache` step. We treat that step as best-effort and
# suppress all errors from it.
(
  cd ../tools
  cargo "+$TOOLS_TOOLCHAIN" install -q cargo-readme --version 3.2.0 \
    --locked
)

# Cargo discovers rust-toolchain.toml and .cargo configuration from its
# working directory, not from --manifest-path. Run inside `tools` so the
# invocation and the documented regeneration command share the same context.
# The generator then needs its source directory explicitly because its
# repository-layout auto-detection intentionally starts from that context.
diff <(
  cd ../tools
  ZEROCOPY_README_DIR=../zerocopy \
    cargo "+$TOOLS_TOOLCHAIN" -q run --locked -p generate-readme
) README.md >&2
exit $?
