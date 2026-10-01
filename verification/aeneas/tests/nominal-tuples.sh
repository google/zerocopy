#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
set -euo pipefail
cd "$(dirname "$0")/../../.."
source verification/aeneas/toolchain.sh
repo=$PWD
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
upstream=${AENEAS_UPSTREAM_EXE:-"$tools_dir/aeneas-upstream"}
work="$repo/target/aeneas/nominal-tuples"
mkdir -p "$work"/{nominal,default,explicit}
export RUSTUP_TOOLCHAIN="$AENEAS_RUST_TOOLCHAIN"
(
    cd verification/aeneas/tests/nominal-tuples
    CARGO_TARGET_DIR="$work/rust" "$tools_dir/charon" cargo --preset=aeneas --sysroot default \
        --dest-file "$work/nominal.llbc" --abort-on-error --error-on-warnings \
        -- --lib --locked --offline
)
extract() {
    local executable=$1 destination=$2
    shift 2
    "$executable" -backend lean -namespace NominalTuples -dest "$destination" \
        -abort-on-error -warnings-as-errors -no-progress-bar "$@" "$work/nominal.llbc"
}
extract "$tools_dir/aeneas" "$work/nominal" -use-tuple-structs false
extract "$tools_dir/aeneas" "$work/default"
extract "$tools_dir/aeneas" "$work/explicit" -use-tuple-structs true
diff -u "$work/default/Nominal.lean" "$work/explicit/Nominal.lean"
[[ -x "$upstream" ]] || { echo "Missing upstream comparison binary: $upstream" >&2; exit 1; }
mkdir -p "$work/upstream"
extract "$upstream" "$work/upstream"
diff -u "$work/upstream/Nominal.lean" "$work/default/Nominal.lean"
python3 verification/aeneas/tests/check_nominal_tuples.py "$work"
# Read only the installed backend's compiled imports; all test artifacts live here.
export LEAN_PATH
LEAN_PATH=$(python3 - "$tools_dir/backends/lean" "$work/nominal" <<'PYLEAN'
from pathlib import Path
import os, sys
backend = Path(sys.argv[1])
paths = [str(backend / '.lake/build/lib/lean')]
paths += [str(p) for p in sorted((backend / '.lake/packages').glob('*/.lake/build/lib/lean'))]
print(os.pathsep.join([sys.argv[2], *paths]))
PYLEAN
)
"$tools_dir/lean/bin/lean" -j1 -DwarningAsError=true -o "$work/nominal/Nominal.olean" "$work/nominal/Nominal.lean"
"$tools_dir/lean/bin/lean" -j1 -DwarningAsError=true verification/aeneas/tests/nominal-tuples/Check.lean
LEAN_PATH="$work/default:${LEAN_PATH#*:}"
"$tools_dir/lean/bin/lean" -j1 -DwarningAsError=true -o "$work/default/Nominal.olean" "$work/default/Nominal.lean"
"$tools_dir/lean/bin/lean" -j1 -DwarningAsError=true verification/aeneas/tests/nominal-tuples/Default.lean
echo "Nominal tuple extraction fixtures: $work"
