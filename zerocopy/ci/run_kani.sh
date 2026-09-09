#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail

ZEROCOPY_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
readonly ZEROCOPY_DIR
KANI_OUTPUT="$(mktemp)"
readonly KANI_OUTPUT
trap 'rm -f "${KANI_OUTPUT}"' EXIT

check_cover_summaries() {
    awk '
        /cover[[:space:]]+properties[[:space:]]+satisfied/ {
            found_cover_candidate = 1
            if (NF != 7 || $1 != "**" || $3 != "of" || $5 != "cover" ||
                    $6 != "properties" || $7 != "satisfied" ||
                    $2 !~ /^(0|[1-9][0-9]*)$/ || $4 !~ /^[1-9][0-9]*$/) {
                print "Malformed Kani cover summary: " $0 > "/dev/stderr"
                malformed_cover_summary = 1
            } else {
                found_cover_summary = 1
                # Canonical decimal strings are numerically equal exactly when
                # their strings are equal; this avoids AWK numeric precision
                # limits for arbitrarily long counts.
                if (("count:" $2) != ("count:" $4)) {
                    print "Kani cover obligation failed: " $0 > "/dev/stderr"
                    failed_cover = 1
                }
            }
        }
        END {
            if (malformed_cover_summary) {
                exit 2
            }
            if (!found_cover_candidate || !found_cover_summary) {
                print "Kani emitted no recognized cover summary" > "/dev/stderr"
                exit 2
            }
            if (failed_cover) {
                exit 1
            }
        }
    ' "$1"
}

expect_parser_result() {
    local expected="$1"
    local fixture="$2"
    local actual
    printf '%s\n' "${fixture}" > "${KANI_OUTPUT}"
    if check_cover_summaries "${KANI_OUTPUT}" >/dev/null 2>&1; then
        actual=success
    else
        actual=failure
    fi
    if [[ "${actual}" != "${expected}" ]]; then
        echo "Kani cover parser self-test expected ${expected}: ${fixture}" >&2
        exit 1
    fi
}

if (( $# == 1 )) && [[ "$1" == "--self-test-cover-parser" ]]; then
    readonly SELF_TEST_VALID_SUMMARY="** 1 of 1 cover properties satisfied"
    expect_parser_result success "** 2 of 2 cover properties satisfied"
    expect_parser_result failure "** 1 of 2 cover properties satisfied"
    expect_parser_result failure "VERIFICATION:- SUCCESSFUL"
    expect_parser_result failure "** x of x cover properties satisfied"
    expect_parser_result failure "** 0 of 0 cover properties satisfied"
    expect_parser_result failure "** 01 of 01 cover properties satisfied"
    expect_parser_result failure "** 1 of 1 cover properties satisfied extra"
    expect_parser_result success \
        "** 9007199254740993 of 9007199254740993 cover properties satisfied"
    expect_parser_result failure \
        "** 9007199254740992 of 9007199254740993 cover properties satisfied"
    expect_parser_result failure \
        "${SELF_TEST_VALID_SUMMARY}"$'\n'"** 1 of 2 cover properties satisfied"
    expect_parser_result failure \
        "${SELF_TEST_VALID_SUMMARY}"$'\n'"* 1 of 1 cover properties satisfied"
    exit 0
fi

cd "${ZEROCOPY_DIR}"

set +e
"${ZEROCOPY_DIR}/cargo.sh" +stable kani "$@" 2>&1 | tee "${KANI_OUTPUT}"
PIPELINE_STATUS=("${PIPESTATUS[@]}")
readonly KANI_STATUS="${PIPELINE_STATUS[0]}"
readonly TEE_STATUS="${PIPELINE_STATUS[1]}"
set -e

if (( KANI_STATUS != 0 )); then
    exit "${KANI_STATUS}"
fi
if (( TEE_STATUS != 0 )); then
    exit "${TEE_STATUS}"
fi

# Kani 0.67 reports unsatisfied `kani::cover!` properties but still exits
# successfully. Its CLI has no `--fail-on-cover` option. Parse the exact output
# format audited in `agent_docs/validation.md` so every emitted non-vacuity
# summary fails closed, and total absence also fails. Re-audit this parser
# whenever the pinned Kani version changes.
check_cover_summaries "${KANI_OUTPUT}"
