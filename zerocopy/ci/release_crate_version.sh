#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

if [ $# -ne 1 ]; then
    echo "Usage: $0 <version>" >&2
    exit 1
fi

VERSION="$1"
PREV_VERSION="$(sed -n 's/^version = "\([0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\)"$/\1/p' Cargo.toml | head -n 1)"

sed -i -e "s/^zerocopy-derive = { version = \"=[0-9a-zA-Z\.-]*\"/zerocopy-derive = { version = \"=$VERSION\"/" Cargo.toml
sed -i -e "s/^version = \"[0-9a-zA-Z\.-]*\"/version = \"$VERSION\"/" Cargo.toml zerocopy-derive/Cargo.toml

if [ -n "$PREV_VERSION" ]; then
    # Pin the semver baseline to the version this release supersedes: the new
    # version is not on crates.io until after this PR merges and publishes.
    # The `roll_semver_baseline` job in `roll-pinned-toolchain-versions.yml`
    # then advances the pin to the new release, so after publication the
    # baseline lags until that job's next weekly run or a manual dispatch.
    PIN_FILE="../ci/pins/semver-baseline.toml"
    VER_MATCH="$(grep -Ec '^version = "[0-9]+\.[0-9]+\.[0-9]+"$' "$PIN_FILE" || true)"
    if [ "$VER_MATCH" -ne 1 ]; then
        echo "Expected one version line in $PIN_FILE; found $VER_MATCH" >&2
        exit 1
    fi
    SHA_MATCH="$(grep -Ec '^crate-sha256 = "[0-9a-f]{64}"$' "$PIN_FILE" || true)"
    if [ "$SHA_MATCH" -ne 1 ]; then
        echo "Expected one crate-sha256 line in $PIN_FILE; found $SHA_MATCH" >&2
        exit 1
    fi
    PREV_SHA="$(
        curl -fsSL "https://index.crates.io/ze/ro/zerocopy" \
            | jq -er --arg v "$PREV_VERSION" 'select(.vers == $v) | .cksum' \
            | head -n 1
    )"
    if ! [[ "$PREV_SHA" =~ ^[0-9a-f]{64}$ ]]; then
        echo "Failed to resolve crates.io SHA-256 for zerocopy $PREV_VERSION" >&2
        exit 1
    fi
    sed -i -E -e "s/^version = \"[0-9]+\.[0-9]+\.[0-9]+\"$/version = \"$PREV_VERSION\"/" "$PIN_FILE"
    sed -i -E -e "s/^crate-sha256 = \"[0-9a-f]{64}\"$/crate-sha256 = \"$PREV_SHA\"/" "$PIN_FILE"
    grep -Fx "version = \"$PREV_VERSION\"" "$PIN_FILE" >/dev/null
    grep -Fx "crate-sha256 = \"$PREV_SHA\"" "$PIN_FILE" >/dev/null
fi

# Ensure that `Cargo.lock` is updated.
cargo generate-lockfile
