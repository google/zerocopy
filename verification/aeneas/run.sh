#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Produce a fresh Rust extraction, compare its generated modules, then check
# the authored proofs against golden and live definitions independently. A text
# match does not establish a proof, and a proof does not establish a text match.
set -euo pipefail
update_goldens=false
extract_only=false
case "${1:-}" in
    "") [[ $# == 0 ]] ;;
    --update-goldens) [[ $# == 1 ]]; update_goldens=true ;;
    --extract-only) [[ $# == 1 ]]; extract_only=true ;;
    *) echo "Usage: $0 [--update-goldens|--extract-only]" >&2; exit 1 ;;
esac
cd "$(dirname "$0")/../.."
repo=$PWD
source verification/aeneas/toolchain.sh
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
backend="$tools_dir/backends/lean"
[[ $("$tools_dir/aeneas" -version) == "aeneas $AENEAS_VERSION" ]]
[[ $("$tools_dir/charon" toolchain-version) == "$AENEAS_RUST_TOOLCHAIN" ]]
[[ $("$tools_dir/charon" version) == "$CHARON_VERSION ($CHARON_REV)" ]]
[[ $(cat "$backend/lean-toolchain") == "$AENEAS_LEAN_TOOLCHAIN" ]]
export PATH="$tools_dir/lean/bin:$PATH"
export RUSTUP_TOOLCHAIN="$AENEAS_RUST_TOOLCHAIN"

workspace_cmd=(python3 -B verification/aeneas/workspace.py)
initialize_workspace() {
    "${workspace_cmd[@]}" initialize "$1" --root "$repo" --backend "$backend"
}
check_proofs() {
    "${workspace_cmd[@]}" check "$1" --root "$repo"
}
work="$repo/target/aeneas/verification"
golden_work="$repo/target/aeneas/golden-verification"
initialize_workspace "$work"
if ! "$extract_only"; then initialize_workspace "$golden_work"; fi

# Use a Rust parser for body ownership and a lexer for comments/literals.
CARGO_TARGET_DIR="$repo/target/aeneas/annotation-tool" \
    cargo build --locked --jobs 2 \
    --manifest-path tools/Cargo.toml -p aeneas-inline
inline_tool="$repo/target/aeneas/annotation-tool/debug/aeneas-inline"
inline_cmd=(python3 -B verification/aeneas/inline.py)
inline_args=(--root "$repo" --tool "$inline_tool")
scan=scan
if "$update_goldens"; then scan=scan-update; fi
"${inline_cmd[@]}" "$scan" "${inline_args[@]}" --work "$work"
roots=$(cat "$work/roots.txt")
# Admission requires controlled compiler inputs and both inspection stages.
# Registry-derived opaque selections cannot hide arbitrary local functions.
python3 -B verification/aeneas/admission.py inputs > "$work/extraction-inputs.json"
opaque_args=()
while IFS= read -r name; do
    [[ -z "$name" ]] || opaque_args+=(--opaque "$name")
done < <(python3 -B verification/aeneas/admission.py opaque)
export CHARON_ADMISSION_SNAPSHOT="$work/zerocopy.before.ullbc"

# This compiles the actual zerocopy library with its normal build script and
# default features. Start from these private helpers and their dependencies;
# whole-crate unsafe verification is outside the current Aeneas safe subset.
(
    cd zerocopy
    CARGO_TARGET_DIR="$repo/target/aeneas/rust" \
        "$tools_dir/charon" cargo --preset=aeneas --sysroot default \
        --start-from "$roots" \
        --mir promoted --no-dedup-serialized-ast \
        "${opaque_args[@]}" \
        --dest-file "$work/zerocopy.llbc" --abort-on-error --error-on-warnings \
        -- --lib --locked --offline
)
# Charon produces LLBC; the inline tool binds Rust owners to that inspected
# extraction. Aeneas then produces the function bodies used by the live proofs.
# Admission inspects the preserved pre-transformation snapshot and final LLBC.
# Their remaining correspondence premises are recorded in LOWERING_AUDIT.md.
# FIXME: Typed copies erase storage events (upstream issue #1405):
# https://github.com/AeneasVerif/aeneas/issues/1405. Neither strict extraction
# errors nor the downstream forbidden tag can detect an already erased effect.
# Promoted MIR precedes drop elaboration: residual Drop terminators reject the
# body rather than relying on destructor desugaring or Aeneas's drop erasure.
python3 verification/aeneas/prepare.py llbc "$work/zerocopy.llbc"
"${inline_cmd[@]}" bindings "${inline_args[@]}" --work "$work"
"$tools_dir/aeneas" -backend lean -namespace Zerocopy -dest "$work/Zerocopy" \
    -split-files -abort-on-error -warnings-as-errors -no-progress-bar \
    -use-tuple-structs false \
    "$work/zerocopy.llbc"
unset CHARON_ADMISSION_SNAPSHOT
python3 verification/aeneas/prepare.py prepare "$work"
"${inline_cmd[@]}" models "${inline_args[@]}" --work "$work"
"${inline_cmd[@]}" assemble "${inline_args[@]}" --work "$work"
python3 verification/aeneas/prepare.py workspace "$work" --backend "$backend"
if "$extract_only"; then
    echo "Development extraction: $work"
    echo "Golden comparison and proof checks have not run."
    exit 0
fi
if "$update_goldens"; then
    # Update explicitly, and only from a fresh extraction that passes proofs.
    echo "Checking live model before updating goldens"
    check_proofs "$work"
    "${inline_cmd[@]}" update "${inline_args[@]}" --work "$work/Zerocopy"
fi
python3 verification/aeneas/golden.py compare "$work/Zerocopy" verification/aeneas/golden
"${inline_cmd[@]}" render "${inline_args[@]}" --work "$golden_work/Zerocopy"
# Reuse the audited Rust-to-Lean owner mapping, but keep the golden function
# definitions. This fixes which function each spec targets without substituting
# live bodies into the golden proof build. Fuzzy documentation cannot select a
# different function; both projects must pass their own proofs and axiom audit.
cp "$work/bindings.json" "$golden_work/bindings.json"
"${inline_cmd[@]}" assemble "${inline_args[@]}" --work "$golden_work"
python3 verification/aeneas/prepare.py workspace "$golden_work" --backend "$backend"
echo "Checking proofs and axioms against the checked-in golden model"
check_proofs "$golden_work"
echo "Checking proofs and axioms against the live Aeneas model"
check_proofs "$work"
