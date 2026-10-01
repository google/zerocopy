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
[[ $# == 1 && -d "$1" ]] || { echo "Usage: $0 TOOLCHAIN_DIRECTORY" >&2; exit 1; }
tools_dir=$(cd "$1" && pwd)
# Validate the producer archive before applying the consumer's CLI-only patch.
values=$(python3 -B verification/aeneas/toolchain.py shell "$tools_dir" --upstream)
eval "$values"
command -v nix >/dev/null || { echo 'Building the patched Aeneas requires Nix.' >&2; exit 1; }
export ANNEAL_FLAKE_DIR="$PWD/anneal"
mkdir -p target/aeneas
staging=$(mktemp -d "$PWD/target/aeneas/build.XXXXXX")
trap 'rm -rf "$staging"' EXIT
system=$(nix --extra-experimental-features "nix-command flakes" eval --impure --raw --expr builtins.currentSystem)
source_path=$(nix --extra-experimental-features "nix-command flakes" eval --no-write-lock-file --raw \
    "path:$ANNEAL_FLAKE_DIR#packages.$system.aeneas-download.toolchain.aeneas-source")
cp -R "$source_path" "$staging/source"
chmod -R u+w "$staging/source"
export AENEAS_SOURCE_DIR="$staging/source"
export AENEAS_VERSION
(
    cd "$AENEAS_SOURCE_DIR"
    patch -F 0 -p1 < "$OLDPWD/verification/aeneas/patches/use-tuple-structs.patch"
)
artifact=$(nix --extra-experimental-features "nix-command flakes" build --impure --file verification/aeneas/build-aeneas.nix \
    --no-link --print-out-paths --option max-jobs 1 --option cores 2)
[[ $("$artifact/aeneas" -version) == "aeneas $AENEAS_VERSION" ]]
"$artifact/aeneas" -help | python3 -c 'import sys; assert "-use-tuple-structs" in sys.stdin.read()'
# Keep the actual unpatched producer executable for the default-mode oracle.
cp "$tools_dir/aeneas" "$tools_dir/aeneas-upstream"
# Remove only the temporary adapter link: do not overwrite the archive executable.
[[ -L "$tools_dir/aeneas" ]] || { echo 'Expected fresh archive adapter' >&2; exit 1; }
rm "$tools_dir/aeneas"
cp "$artifact/aeneas" "$tools_dir/aeneas"
if [[ -d "$artifact/libs" ]]; then
    mkdir -p "$tools_dir/libs"
    # Replace read-only private copies from the upstream adapter. The frozen
    # archive's libraries stay untouched in bundle/aeneas/bin/libs.
    cp -f "$artifact/libs/"* "$tools_dir/libs/"
fi
python3 -B verification/aeneas/toolchain.py record "$tools_dir"
