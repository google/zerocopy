#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Prepare the tracked Lean sources for native editor and incremental Lake use.
set -euo pipefail
check=false
live=false
for arg in "$@"; do
    case "$arg" in
        --check) check=true ;;
        --live) live=true ;;
        *) echo "Usage: $0 [--check] [--live]" >&2; exit 1 ;;
    esac
done
cd "$(dirname "$0")/../.."
repo=$PWD
source verification/aeneas/toolchain.sh
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
backend="$tools_dir/backends/lean"
[[ $(cat "$backend/lean-toolchain") == "$AENEAS_LEAN_TOOLCHAIN" ]]
export PATH="$tools_dir/lean/bin:$PATH"
work="$repo/verification/aeneas/lean"
python3 -B verification/aeneas/workspace.py protect "$work" --root "$repo"
if "$live"; then
    # Refresh the model even when changed Rust invalidates an existing proof.
    bash verification/aeneas/run.sh --extract-only
    model="$repo/target/aeneas/verification/Zerocopy"
else
    model="$repo/verification/aeneas/golden"
fi
CARGO_TARGET_DIR="$repo/target/aeneas/annotation-tool" \
    cargo +"$AENEAS_RUST_TOOLCHAIN" build --locked --jobs 2 \
    --manifest-path tools/Cargo.toml -p aeneas-inline
python3 -B - "$model" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'verification/aeneas')
import golden
golden.files(Path(sys.argv[1]), live=True)
PY
mkdir -p "$work/Zerocopy"
for file in Types.lean Funs.lean TypesExternal_Template.lean FunsExternal_Template.lean; do
    cp "$model/$file" "$work/Zerocopy/$file"
done
cp "$backend/lean-toolchain" "$work/lean-toolchain"
python3 -B verification/aeneas/inline.py dev-assemble --root "$repo" \
    --tool "$repo/target/aeneas/annotation-tool/debug/aeneas-inline" --work "$work"
python3 -B verification/aeneas/prepare.py workspace "$work" --backend "$backend"
echo "Lean development project: $work"
echo "Model: $model; specifications refreshed from current Rust comments."
echo "Development checks do not replace the fresh golden/live CI verification."
if "$check"; then
    python3 -B verification/aeneas/workspace.py check "$work" --root "$repo"
fi
