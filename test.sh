#!/bin/bash
#
# Copyright 2023 The Fuchsia Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -e

ROOT=$(git rev-parse --show-toplevel)
. $ROOT/util.sh

function run_test {
    if [[ $# != 1 ]]; then
        echo "Usage: run_test <test-function>" >&2
        return 1
    fi

    # Run `$1`, capturing stdout and stderr.
    #
    # https://stackoverflow.com/a/59592881/836390
    {
        IFS=$'\n' read -r -d '' STDERR;
        IFS=$'\n' read -r -d '' STDOUT;
    } < <((printf '\0%s\0' "$($1)" 1>&2) 2>&1)
    RESULT=$?

    if [[ $RESULT != 0 ]]; then
        echo "Test \"$1\" failed with return code $RESULT." >&2
        echo "stdout:"                                      >&2
        echo "$STDOUT" | sed -e 's/^/    /g'                >&2
        echo "stderr:"                                      >&2
        echo "$STDERR" | sed -e 's/^/    /g'                >&2
        echo                                                >&2
    fi

    return $?
}

FAIL=0
run_test test_check_fmt      || FAIL=1
run_test test_check_readme   || FAIL=1
run_test test_check_msrvs    || FAIL=1
run_test test_check_versions || FAIL=1

if [[ $FAIL == 0 ]]; then
    echo "All tests completed successfully!"
    exit 0
else
    exit 1
fi
