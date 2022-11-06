#!/bin/bash
#
# Copyright 2023 The Fuchsia Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# Usage: `pkg-meta <crate-name> <selector>`
#
# Extracts metadata from zerocopy's `Cargo.toml` file.
function pkg-meta {
    if [[ $# != 2 ]]; then
        echo "Usage: pkg-meta <crate-name> <selector>" >&2
        return 1
    fi
    cargo metadata --format-version 1 | jq -r ".packages[] | select(.name == \"$1\").$2"
}

# Usage: `msrv <crate-name>`
#
# Extracts the `rust_version` package metadata key.
function msrv {
    if [[ $# != 1 ]]; then
        echo "Usage: msrv <crate-name>" >&2
        return 1
    fi
    pkg-meta $1 rust_version
}

# Usage: `version <crate-name>`
#
# Extracts the `version` mackage metadata key.
function version {
    if [[ $# != 1 ]]; then
        echo "Usage: version <crate-name>" >&2
        return 1
    fi
    pkg-meta $1 version
}

function test_check_fmt {
    ROOT=$(git rev-parse --show-toplevel)                       && \
    cargo fmt --check --package zerocopy                        && \
    cargo fmt --check --package zerocopy-derive                 && \
    rustfmt --check $ROOT/tests/ui-nightly/*.rs                 && \
    rustfmt --check $ROOT/zerocopy-derive/tests/ui-nightly/*.rs
}

function test_check_readme {
    ROOT=$(git rev-parse --show-toplevel)            && \
    cargo install cargo-readme --version 3.2.0       && \
    diff <($ROOT/generate-readme.sh) $ROOT/README.md
}

# Make sure that the MSRV in zerocopy's and zerocopy-derive's `Cargo.toml` files
# are the same.
function test_check_msrvs {
    ver_zerocopy=$(msrv zerocopy)               && \
    ver_zerocopy_derive=$(msrv zerocopy-derive) && \

    if [[ "$ver_zerocopy" == "$ver_zerocopy_derive" ]]; then
        echo "Same MSRV ($ver_zerocopy) found for zerocopy and zerocopy-derive."
        true
    else
        echo "Different MSRVs found for zerocopy ($ver_zerocopy) and zerocopy-derive ($ver_zerocopy_derive)."
        false
    fi
}

# Make sure that both crates are at the same version, and that zerocopy depends
# exactly upon the current version of zerocopy-derive. See `INTERNAL.md` for an
# explanation of why we do this.
function test_check_versions {
    ver_zerocopy=$(version zerocopy)                               && \
    ver_zerocopy_derive=$(version zerocopy-derive)                 && \
    zerocopy_derive_dep_ver=$(pkg-meta zerocopy \
        'dependencies[] | select(.name == "zerocopy-derive").req') && \

    if [[ "$ver_zerocopy" == "$ver_zerocopy_derive" ]]; then
        echo "Same crate version ($ver_zerocopy) found for zerocopy and zerocopy-derive."
    else
        echo "Different crate versions found for zerocopy ($ver_zerocopy) and zerocopy-derive ($ver_zerocopy_derive)."
        false
    fi && \

    # Note the leading `=` sign - the dependency needs to be an exact one.
    if [[ "$zerocopy_derive_dep_ver" == "=$ver_zerocopy_derive" ]]; then
        echo "zerocopy depends upon same version of zerocopy-derive in-tree ($zerocopy_derive_dep_ver)."
    else
        echo "zerocopy depends upon different version of zerocopy-derive ($zerocopy_derive_dep_ver) than the one in-tree ($ver_zerocopy_derive)."
        false
    fi
}

# Usage: `run_test_in_github_action <test-function>`
#
# Runs the named test function, piping the output to the appropriate locations
# and exiting with the return code of the function.
function run_test_in_github_action {
    if [[ $# != 1 ]]; then
        echo "Usage: run_test_in_github_action <test-function>" >&2
        return 1
    fi

    OUTPUT="$($1)"
    RESULT=$?
    echo "$OUTPUT" | tee -a $GITHUB_STEP_SUMMARY >&2
    exit $RESULT
}
