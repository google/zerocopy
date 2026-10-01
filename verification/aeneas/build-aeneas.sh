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
[[ $# == 1 && -d "$1" ]] || { echo "Usage: $0 TOOLCHAIN_DIRECTORY" >&2; exit 1; }
tools_dir=$(cd "$1" && pwd)
command -v nix >/dev/null || { echo 'Building the patched Aeneas requires Nix.' >&2; exit 1; }
mkdir -p target/aeneas
staging=$(mktemp -d "$PWD/target/aeneas/build.XXXXXX")
trap 'rm -rf "$staging"' EXIT
# Check both producer inputs before applying the CLI patch. The build record
# below also hashes the resulting executable so inspection can identify it.
check_hash() {
    python3 - "$1" "$2" <<'PY'
import hashlib, sys
from pathlib import Path
actual = hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest()
if actual != sys.argv[2]:
    raise SystemExit(f"SHA-256 mismatch for {sys.argv[1]}: {actual}")
PY
}
curl --fail --location --silent --show-error --retry 5 \
    "https://codeload.github.com/AeneasVerif/aeneas/tar.gz/$AENEAS_REV" \
    -o "$staging/source.tar.gz"
check_hash "$staging/source.tar.gz" "$AENEAS_SOURCE_SHA256"
check_hash verification/aeneas/patches/use-tuple-structs.patch "$AENEAS_PATCH_SHA256"
tar -xzf "$staging/source.tar.gz" -C "$staging"
export AENEAS_SOURCE_DIR="$staging/aeneas-$AENEAS_REV"
export AENEAS_VERSION
(
    cd "$AENEAS_SOURCE_DIR"
    patch -F 0 -p1 < "$OLDPWD/verification/aeneas/patches/use-tuple-structs.patch"
)
# No update/override of flake inputs: the source archive includes flake.lock.
# Limit simultaneous derivations and compiler jobs on small developer machines.
artifact=$(nix --extra-experimental-features "nix-command flakes" build --impure --file verification/aeneas/build-aeneas.nix \
    --no-link --print-out-paths --option max-jobs 1 --option cores 2)
[[ $("$artifact/aeneas" -version) == "aeneas $AENEAS_VERSION" ]]
"$artifact/aeneas" -help | python3 -c 'import sys; assert "-use-tuple-structs" in sys.stdin.read()'
[[ $("$tools_dir/aeneas" -version) == "aeneas $AENEAS_RELEASE" ]]
# Preserve the unpatched release executable as the compatibility oracle for
# nominal-tuples.sh; the patched default must still produce its exact output.
cp "$tools_dir/aeneas" "$tools_dir/aeneas-upstream"
cp "$artifact/aeneas" "$tools_dir/aeneas"
if [[ -d "$artifact/libs" ]]; then
    mkdir -p "$tools_dir/libs"
    cp "$artifact/libs/"* "$tools_dir/libs/"
fi
python3 - "$tools_dir" "$AENEAS_REV" "$AENEAS_SOURCE_SHA256" "$AENEAS_PATCH_SHA256" "$AENEAS_VERSION" <<'PY'
import hashlib, json, sys
from pathlib import Path
root = Path(sys.argv[1])
provenance = dict(zip(("source_rev", "source_sha256", "patch_sha256", "version"), sys.argv[2:]))
provenance["binary_sha256"] = hashlib.sha256((root / "aeneas").read_bytes()).hexdigest()
(root / "aeneas-build.json").write_text(json.dumps(provenance, indent=2) + "\n")
PY
