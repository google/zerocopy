#!/usr/bin/env bash
set -eo pipefail

# Check whether the set of toolchains tested in this file (other than
# 'msrv', 'stable', and 'nightly') is equal to the set of toolchains
# listed in the 'package.metadata.build-rs' section of Cargo.toml.
#
# If the inputs to `diff` are not identical, `diff` exits with a
# non-zero error code, which causes this script to fail (thanks to
# `set -e`).
diff \
  <(cat .github/workflows/ci.yml | yq '.jobs.build_test.strategy.matrix.toolchain | .[]' | \
    sort -u | grep -v '^\(msrv\|stable\|nightly\)$') \
  <(cargo metadata -q --format-version 1 | \
    jq -r ".packages[] | select(.name == \"zerocopy\").metadata.\"build-rs\" | keys | .[]" | \
    sort -u)
