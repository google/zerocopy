#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# These producer boundaries have one live extraction subject per invocation.
set -euo pipefail
repo=${AENEAS_CONTROL_REPO:?}
project=${AENEAS_CONTROL_PROJECT:?}
cd "$repo"
source verification/aeneas/toolchain.sh
tools_dir=$AENEAS_TOOLCHAIN_DIR
work=$(mktemp -d "$project/frontend.XXXXXX")
trap 'rm -rf "$work"' EXIT
run() {
    python3 -B verification/aeneas/control_runner.py command \
        "$AENEAS_CONTROL_LOG_DIR/commands" -- "$@"
}
run python3 -B verification/aeneas/tests/provided_method_controls.py \
    "$tools_dir/charon" "$work" "$repo" "$tools_dir/rust/lib"
run python3 -B verification/aeneas/tests/impl_root_controls.py \
    "$tools_dir/charon" "$work/impl-roots" "$repo" "$tools_dir/rust/lib"
run bash verification/aeneas/tests/annotation-origins.sh
# Validate capability observations before interpreting absence as inapplicability.
capabilities=$(python3 - "$project/bindings.json" <<'PY'
import json, sys
from pathlib import Path
manifest = json.loads(Path(sys.argv[1]).read_text())
if manifest.get('version') != 3 or manifest.get('mode') != 'verified-live':
    raise SystemExit('Invalid verified bindings for extraction controls')
functions = {row['raw'] for row in manifest['bindings'].values() if row['kind'] == 'function'}
print('storage' if 'Zerocopy.util.safety_checks.checked_bool' in functions else '')
print('into-bytes' if any(row['rust'] == 'zerocopy::IntoBytes' for row in manifest['trait_laws']) else '')
PY
)
if [[ $capabilities == *into-bytes* ]]; then
    run python3 -B verification/aeneas/tests/trait_const_binding_controls.py "$project"
    run python3 -B verification/aeneas/tests/unemitted_type_controls.py "$project"
fi
if [[ $capabilities == *storage* ]]; then
    run bash verification/aeneas/tests/producer-controls.sh generate "$AENEAS_CONTROL_PRODUCER_DIR"
fi
