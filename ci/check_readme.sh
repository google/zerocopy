#!/usr/bin/env bash
set -eo pipefail

# Install again in case the installation failed during the
# `generate_cache` step. We treat that step as best-effort and
# suppress all errors from it.
cargo install cargo-readme --version 3.2.0 -q

diff <(./generate-readme.sh) README.md
exit $?
