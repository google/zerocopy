#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Compile deliberately invalid producers; never execute their Rust code.
set -euo pipefail
[[ $# == 1 && -f "$1/bindings.json" ]] || { echo "Usage: $0 VERIFIED_PROJECT" >&2; exit 1; }
project=$(cd "$1" && pwd)
cd "$(dirname "$0")/../../.."
repo=$PWD
source verification/aeneas/toolchain.sh
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
fixture="$repo/verification/aeneas/tests/producer-controls"
work="$project/producer-controls"
mkdir -p "$work/Controls" "$project/.lake/build/lib/lean/Controls"
roots=aeneas_admission_controls::valid,aeneas_admission_controls::ignored,aeneas_admission_controls::before_divergence
boundary=aeneas_admission_controls::util::transmute_unchecked
(
    cd "$fixture"
    CHARON_ADMISSION_SNAPSHOT="$work/controls.before.ullbc" \
    CARGO_TARGET_DIR="$work/rust" \
        "$tools_dir/charon" cargo --preset=aeneas --sysroot default \
        --mir promoted --no-dedup-serialized-ast --opaque "$boundary" \
        --start-from "$roots" --dest-file "$work/controls.llbc" \
        --abort-on-error --error-on-warnings -- --lib --locked --offline
)
# Exercise the same admission traversal, with the fixture's exact callable
# identity. This does not mint a production binding manifest or certify the
# toy helper body: its opaque interpretation is deliberately a test premise.
python3 - "$repo" "$work" "$roots" "$boundary" <<'PY'
import json, sys
from pathlib import Path
repo, work = map(Path, sys.argv[1:3])
sys.path.insert(0, str(repo / 'verification/aeneas'))
import admission
registry = json.loads((repo / 'verification/aeneas/external.json').read_text())
entry = next(row.copy() for row in registry if row['rust'] == 'zerocopy::util::transmute_unchecked')
entry['rust'] = sys.argv[4]
for filename, before in [('controls.before.ullbc', True), ('controls.llbc', False)]:
    checker = admission.Admission(json.loads((work / filename).read_text()), [entry])
    if checker.before != before:
        raise SystemExit('Producer control has the wrong inspection stage')
    checker.audit(sys.argv[3].split(','))
PY
"$tools_dir/aeneas" -backend lean -namespace Controls \
    -dest "$work/Controls" -split-files -abort-on-error \
    -warnings-as-errors -no-progress-bar -use-tuple-structs false "$work/controls.llbc"
cat > "$work/Controls/TypesExternal.lean" <<'LEAN'
module
public import Aeneas
LEAN
cat > "$work/Controls/FunsExternal.lean" <<'LEAN'
module
public import Controls.Types
public import Zerocopy.FunsExternal
LEAN
(
    cd "$project"
    # Compile every fixture module freshly. A cached caller from another model
    # cannot make a missing or erased unsafe call look forbidden.
    for name in TypesExternal Types FunsExternal Funs; do
        aeneas_lake env lean --root="$work" -DwarningAsError=true \
            "$work/Controls/$name.lean" \
            -o "$project/.lake/build/lib/lean/Controls/$name.olean"
    done
    aeneas_lake env lean -DwarningAsError=true "$fixture/Check.lean"
)
echo 'Confirmed: generated callers retain forbidden production before discard and divergence'
