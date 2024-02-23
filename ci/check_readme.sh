#!/usr/bin/env bash
set -eo pipefail

# Install again in case the installation failed during the
# `generate_cache` step. We treat that step as best-effort and
# suppress all errors from it.
cargo install -q cargo-readme --version 3.2.0

diff <(cargo -q run --manifest-path tools/Cargo.toml -p generate-readme) README.md
exit $?
