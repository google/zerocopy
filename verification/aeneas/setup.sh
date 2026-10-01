#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/../.."
source verification/aeneas/toolchain.sh
mkdir -p target/aeneas

# This directory is owned by this script. Publish a complete install only.
staging=$(mktemp -d "$PWD/target/aeneas/setup.XXXXXX")
trap 'rm -rf "$staging"' EXIT

fetch() {
    curl --fail --location --silent --show-error --retry 5 "$1" -o "$2"
    python3 - "$2" "$3" <<'PY'
import hashlib
import sys
from pathlib import Path
digest = hashlib.sha256()
with Path(sys.argv[1]).open("rb") as archive:
    for block in iter(lambda: archive.read(1024 * 1024), b""):
        digest.update(block)
actual = digest.hexdigest()
if actual != sys.argv[2]:
    raise SystemExit(f"SHA-256 mismatch for {sys.argv[1]}: {actual}")
PY
}

fetch "https://github.com/AeneasVerif/aeneas/releases/download/$AENEAS_RELEASE/aeneas-$AENEAS_PLATFORM.tar.gz" \
    "$staging/aeneas.tar.gz" "$AENEAS_SHA256"
mkdir "$staging/toolchain"
tar -xzf "$staging/aeneas.tar.gz" -C "$staging/toolchain"
fetch "https://github.com/leanprover/lean4/releases/download/v$AENEAS_LEAN_VERSION/lean-$AENEAS_LEAN_VERSION-$AENEAS_LEAN_PLATFORM.tar.zst" \
    "$staging/lean.tar.zst" "$AENEAS_LEAN_SHA256"
mkdir "$staging/toolchain/lean"
tar --zstd -xf "$staging/lean.tar.zst" -C "$staging/toolchain/lean" --strip-components=1

[[ $("$staging/toolchain/aeneas" -version) == "aeneas $AENEAS_RELEASE" ]]
[[ $("$staging/toolchain/charon" toolchain-version) == "$AENEAS_RUST_TOOLCHAIN" ]]
[[ $("$staging/toolchain/charon" version) == "$CHARON_VERSION ($CHARON_REV)" ]]
[[ $(cat "$staging/toolchain/backends/lean/lean-toolchain") == "$AENEAS_LEAN_TOOLCHAIN" ]]
rustup toolchain install "$AENEAS_RUST_TOOLCHAIN" --profile minimal \
    --component rustc-dev --component rust-src

# Fetch only Mathlib modules imported by this backend, plus their dependencies.
# The bundle contains a manifest with pinned dependency revisions. Lake loads
# it directly; do not run `lake update` and float the dependencies.
export PATH="$staging/toolchain/lean/bin:$PATH"
python3 verification/aeneas/prepare.py mathlib-imports \
    "$staging/toolchain/backends/lean" > "$staging/mathlib-imports.txt"
mathlib_modules=()
while IFS= read -r module; do
    mathlib_modules+=("$module")
done < "$staging/mathlib-imports.txt"
(
    cd "$staging/toolchain/backends/lean"
    lake exe cache get "${mathlib_modules[@]}"
)
rm -rf target/aeneas/toolchain
mv "$staging/toolchain" target/aeneas/toolchain
