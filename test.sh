#!/bin/bash
#
# Copyright 2023 The Fuchsia Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -e

ROOT=$(git rev-parse --show-toplevel)
. $ROOT/util.sh

# Usage: `run-test <command>...`
#
# Runs the named test, exiting the script on failure.
function run-test {
    if [[ $# == 0 ]]; then
        echo "Usage: run-test <command>..." >&2
        return 1
    fi

    echo "Running test \"$@\" ..."
    "$@" || (RET=$? && echo "Test \"$@\" failed." >&2 && exit $RET)
    echo
}

# TODO: Colorize, baby!

# run-test test-check-fmt
# run-test test-check-readme
# run-test test-check-msrvs
# run-test test-check-versions

# TODO: Consistent strategy around failing early for internal errors

for TOOLCHAIN_NAME in msrv stable nightly; do
    TOOLCHAIN=$(get-toolchain-by-name "$TOOLCHAIN_NAME") || exit $?
    for TARGET in i686-unknown-linux-gnu x86_64-unknown-linux-gnu arm-unknown-linux-gnueabi aarch64-unknown-linux-gnu powerpc-unknown-linux-gnu powerpc64-unknown-linux-gnu wasm32-wasi; do
        for FEATURES in "--no-default-features" "" "--features __internal_use_only_features_that_work_on_stable" "--all-features"; do
            for CRATE in zerocopy zerocopy-derive; do
                if [[
                    ($TOOLCHAIN_NAME == msrv && "$FEATURES" == --all-features) ||
                    ($TOOLCHAIN_NAME == stable && "$FEATURES" == --all-features) ||
                    ($CRATE == zerocopy-derive && "$FEATURES" != "")
                ]]; then
                    echo skipping...
                    continue
                fi

                run-test test-check "$TOOLCHAIN_NAME" "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURES"
                run-test test-build "$TOOLCHAIN_NAME" "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURES"
                run-test test-tests "$TOOLCHAIN_NAME" "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURES"
                run-test test-miri "$TOOLCHAIN_NAME" "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURES"
                run-test test-clippy "$TOOLCHAIN_NAME" "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURES"
                run-test test-doc "$TOOLCHAIN_NAME" "$TOOLCHAIN" "$CRATE" "$TARGET" "$FEATURES"
            done
        done
    done
done

echo "All tests completed successfully!"