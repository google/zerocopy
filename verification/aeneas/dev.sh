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
refresh=false
final=false
targets=()
copy_owner=""
dry_run=false
while (($#)); do
    case "$1" in
        --check) check=true ;;
        --live) live=true ;;
        --refresh) refresh=true ;;
        --final) final=true ;;
        --dry-run) dry_run=true ;;
        --copy-back)
            if [[ $# -lt 2 || -n "$copy_owner" || "$2" == --* ]]; then
                echo "--copy-back requires one full Rust owner" >&2; exit 1
            fi
            copy_owner=$2
            shift ;;
        --*) echo "Usage: $0 [--refresh|--live] [--check [MODULE ...]] | --final | --copy-back OWNER [--dry-run]" >&2; exit 1 ;;
        *) targets+=("$1") ;;
    esac
    shift
done
if [[ -n "$copy_owner" ]]; then
    if "$check" || "$live" || "$refresh" || "$final" || ((${#targets[@]})); then
        echo "--copy-back cannot be combined with preparation or checking" >&2; exit 1
    fi
elif "$dry_run"; then
    echo "--dry-run requires --copy-back" >&2; exit 1
fi
if ((${#targets[@]})) && ! "$check"; then
    echo "Module targets require --check" >&2; exit 1
fi
if "$final" && { "$check" || "$live" || "$refresh" || [[ -n "$copy_owner" ]]; }; then
    echo "--final runs the complete CI check and cannot be combined with development options" >&2; exit 1
fi
cd "$(dirname "$0")/../.."
repo=$PWD
if "$final"; then
    exec bash verification/aeneas/run.sh
fi
if [[ -n "$copy_owner" ]]; then
    copy_args=(copy-back "$repo/verification/aeneas/lean" --root "$repo" --owner "$copy_owner")
    if ! "$dry_run"; then copy_args+=(--apply); fi
    python3 -B verification/aeneas/workspace.py "${copy_args[@]}"
    exit
fi
source verification/aeneas/toolchain.sh
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
backend="$tools_dir/backends/lean"
[[ $(cat "$backend/lean-toolchain") == "$AENEAS_LEAN_TOOLCHAIN" ]]
export PATH="$tools_dir/lean/bin:$PATH"
work="$repo/verification/aeneas/lean"
# Rechecking an existing editor project must preserve its in-place Lean edits.
# Refresh is explicit; first use still prepares the golden project automatically.
# A source change can make cached imports stale. Only the separate final command
# claims complete verification of the current Rust and handwritten proof sources.
if "$check" && ! "$refresh" && ! "$live" && [[ -f "$work/lakefile.lean" ]]; then
    develop_args=(develop "$work" --root "$repo")
    if ((${#targets[@]})); then
        for target in "${targets[@]}"; do develop_args+=(--target "$target"); done
    fi
    exec python3 -B verification/aeneas/workspace.py "${develop_args[@]}"
fi
python3 -B verification/aeneas/workspace.py protect "$work" --root "$repo"
# Trait dictionaries and native layout bindings need compiler evidence even
# when the editor uses golden definitions. Extraction does not check proofs.
bash verification/aeneas/run.sh --extract-only
bindings_work="$repo/target/aeneas/verification"
if "$live"; then
    model="$bindings_work/Zerocopy"
else
    model="$repo/verification/aeneas/golden"
fi
# The golden checker owns the generated-file roster. Validate the complete
# producer output before copying those same modules into the editor project;
# handwritten external implementations stay with the authored proof sources.
python3 -B - "$model" "$work/Zerocopy" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'verification/aeneas')
import golden
from output import write_bytes
source, destination = map(Path, sys.argv[1:])
generated = golden.files(source, live=True)
destination.mkdir(parents=True, exist_ok=True)
for name in generated:
    write_bytes(destination / name, (source / name).read_bytes())
PY
python3 -B - "$backend/lean-toolchain" "$work/lean-toolchain" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'verification/aeneas')
from output import write_bytes
source, destination = map(Path, sys.argv[1:])
write_bytes(destination, source.read_bytes())
PY
python3 -B verification/aeneas/inline.py dev-assemble --root "$repo" \
    --tool "$repo/target/aeneas/annotation-tool/debug/aeneas-inline" --work "$work" \
    --bindings-work "$bindings_work"
python3 -B verification/aeneas/prepare.py workspace "$work" --backend "$backend"
echo "Lean development project: $work"
echo "Model: $model; specifications refreshed from current Rust comments."
echo "Development checks do not replace the fresh golden/live CI verification."
if "$check"; then
    develop_args=(develop "$work" --root "$repo")
    if ((${#targets[@]})); then
        for target in "${targets[@]}"; do develop_args+=(--target "$target"); done
    fi
    python3 -B verification/aeneas/workspace.py "${develop_args[@]}"
fi
