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

# The metadata/result equality below establishes completeness only for the
# harness set which this invocation asks Kani to compile. CI is intentionally a
# no-filter run; reject the proof/test selection flags most likely to make a
# local invocation look like the full-suite protocol while checking a subset.
for argument in "$@"; do
    case "${argument}" in
        --harness | --harness=* | --exact | --tests)
            echo "run_kani.sh does not support harness-selection argument: ${argument}" >&2
            exit 2
            ;;
    esac
done

ZEROCOPY_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
readonly ZEROCOPY_DIR
REPO_DIR="$(dirname -- "${ZEROCOPY_DIR}")"
readonly REPO_DIR
KANI_SCRATCH="$(mktemp -d)"
readonly KANI_SCRATCH
KANI_OUTPUT="${KANI_SCRATCH}/combined-output.log"
readonly KANI_OUTPUT
KANI_TARGET="${KANI_SCRATCH}/target"
readonly KANI_TARGET
trap 'rm -rf -- "${KANI_SCRATCH}"' EXIT

cd "${ZEROCOPY_DIR}"

set +e
"${ZEROCOPY_DIR}/cargo.sh" +stable kani \
    --target-dir "${KANI_TARGET}" \
    -Zunstable-options \
    --output-into-files \
    "$@" 2>&1 | tee "${KANI_OUTPUT}"
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
# successfully. Its CLI has no `--fail-on-cover` option. The combined output
# above is retained for diagnostics, while the checker validates the complete
# per-harness inventory emitted into the fresh target. Re-audit the checker
# whenever the pinned Kani version changes.
python3 "${REPO_DIR}/ci/check_kani_cover.py" "${KANI_TARGET}"
