#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
update_goldens=false
case "${1:-}" in
    "") [[ $# == 0 ]] ;;
    --update-goldens) [[ $# == 1 ]]; update_goldens=true ;;
    *) echo "Usage: $0 [--update-goldens]" >&2; exit 1 ;;
esac
cd "$(dirname "$0")/../.."
repo=$PWD
source verification/aeneas/toolchain.sh
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
backend="$tools_dir/backends/lean"
[[ $("$tools_dir/aeneas" -version) == "aeneas $AENEAS_RELEASE" ]]
[[ $("$tools_dir/charon" toolchain-version) == "$AENEAS_RUST_TOOLCHAIN" ]]
[[ $("$tools_dir/charon" version) == "$CHARON_VERSION ($CHARON_REV)" ]]
[[ $(cat "$backend/lean-toolchain") == "$AENEAS_LEAN_TOOLCHAIN" ]]
export PATH="$tools_dir/lean/bin:$PATH"
export RUSTUP_TOOLCHAIN="$AENEAS_RUST_TOOLCHAIN"

# Fresh sources AND oleans: a removed declaration cannot survive via a cache.
initialize_workspace() {
    rm -rf "$1"
    mkdir -p "$1/Zerocopy"
    cp verification/aeneas/lean/*.lean "$1/"
    cp verification/aeneas/lean/Zerocopy/*.lean "$1/Zerocopy/"
    cp "$backend/lean-toolchain" "$1/lean-toolchain"
}
check_proofs() (
    cd "$1"
    lake build
    for source in Arithmetic.lean LayoutMath.lean Proofs.lean ContractTests.lean Loops.lean ContractSimps.lean RequiredContracts.lean SupportTests.lean Corollaries.lean Required.lean; do
        lake env lean -DwarningAsError=true "$source"
    done
    # Always run the audit, even if Lake caches its imports.
    lake env lean -DwarningAsError=true Check.lean
)
work="$repo/target/aeneas/verification"
golden_work="$repo/target/aeneas/golden-verification"
rendered="$repo/target/aeneas/rendered-golden"
initialize_workspace "$work"
initialize_workspace "$golden_work"
rm -rf "$rendered"

# Use a Rust parser for body ownership and a lexer for comments/literals.
CARGO_TARGET_DIR="$repo/target/aeneas/annotation-tool" \
    cargo +"$AENEAS_RUST_TOOLCHAIN" build --locked \
    --manifest-path tools/Cargo.toml -p aeneas-inline
inline_tool="$repo/target/aeneas/annotation-tool/debug/aeneas-inline"
inline_cmd=(python3 -B verification/aeneas/inline.py)
inline_args=(--root "$repo" --tool "$inline_tool")
scan=scan
if "$update_goldens"; then scan=scan-update; fi
"${inline_cmd[@]}" "$scan" "${inline_args[@]}" --work "$work"
roots=$(cat "$work/roots.txt")
"${inline_cmd[@]}" assemble "${inline_args[@]}" --work "$work"

# This compiles the actual zerocopy library with its normal build script and
# default features. Start from these private helpers and their dependencies;
# whole-crate unsafe verification is outside the current Aeneas safe subset.
(
    cd zerocopy
    CARGO_TARGET_DIR="$repo/target/aeneas/rust" \
        "$tools_dir/charon" cargo --preset=aeneas --sysroot default \
        --start-from "$roots" \
        --dest-file "$work/zerocopy.llbc" --abort-on-error --error-on-warnings \
        -- --lib --locked --offline
)
python3 verification/aeneas/prepare.py llbc "$work/zerocopy.llbc"
"${inline_cmd[@]}" bindings "${inline_args[@]}" --work "$work"
"$tools_dir/aeneas" -backend lean -namespace Zerocopy -dest "$work/Zerocopy" \
    -split-files -abort-on-error -warnings-as-errors -no-progress-bar \
    "$work/zerocopy.llbc"
python3 verification/aeneas/prepare.py prepare "$work" --backend "$backend"
if "$update_goldens"; then
    # Update explicitly, and only from a fresh extraction that passes proofs.
    echo "Checking live model before updating goldens"
    check_proofs "$work"
    "${inline_cmd[@]}" update "${inline_args[@]}" --work "$work/Zerocopy"
fi
"${inline_cmd[@]}" render "${inline_args[@]}" --work "$rendered"
python3 verification/aeneas/golden.py compare "$work/Zerocopy" "$rendered"
cp "$rendered/"*.lean "$golden_work/Zerocopy/"
"${inline_cmd[@]}" assemble "${inline_args[@]}" --work "$golden_work"
python3 verification/aeneas/prepare.py workspace "$golden_work" --backend "$backend"
echo "Checking proofs and axioms against the checked-in golden model"
check_proofs "$golden_work"
echo "Checking proofs and axioms against the live Aeneas model"
check_proofs "$work"
