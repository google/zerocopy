#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://opensource.org/licenses/Apache-2.0>, or the MIT license
# <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option. This file
# may not be copied, modified, or distributed except according to those terms.

set -eo pipefail

readonly SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly KANI_OUTPUT="$(mktemp)"
trap 'rm -f "${KANI_OUTPUT}"' EXIT

set +e
"${SCRIPT_DIR}/../cargo.sh" +stable kani "$@" 2>&1 | tee "${KANI_OUTPUT}"
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
# format audited in `agent_docs/validation.md` so non-vacuity obligations fail
# closed. Re-audit this parser whenever the pinned Kani version changes.
awk '
    $1 == "**" && $3 == "of" && $5 == "cover" &&
        $6 == "properties" && $7 == "satisfied" {
        found_cover_summary = 1
        if ($2 != $4) {
            print "Kani cover obligation failed: " $0 > "/dev/stderr"
            failed_cover = 1
        }
    }
    END {
        if (!found_cover_summary) {
            print "Kani emitted no recognized cover summary" > "/dev/stderr"
            exit 2
        }
        if (failed_cover) {
            exit 1
        }
    }
' "${KANI_OUTPUT}"
