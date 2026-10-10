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
repo=$PWD
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
if [[ -e "$tools_dir" || -L "$tools_dir" ]]; then
    python3 -B verification/aeneas/toolchain.py check "$tools_dir"
    echo "Using validated Anneal toolchain: $tools_dir"
    exit
fi
command -v nix >/dev/null || { echo 'Cold Anneal toolchain setup requires Nix.' >&2; exit 1; }
mkdir -p "$(dirname "$tools_dir")"
staging=$(mktemp -d "$(dirname "$tools_dir")/setup.XXXXXX")
# The archive has read-only directories. Make only private staging directories
# writable before removing them; find does not follow the toolchain's symlinks.
trap 'find "$staging" -type d -exec chmod u+w {} +; rm -rf "$staging"' EXIT
nix_cmd=(nix --extra-experimental-features "nix-command flakes")
flake="path:$repo/anneal"
# Both the archive and its layout check use Anneal's existing source of truth.
archive=$("${nix_cmd[@]}" build --no-write-lock-file --no-link --print-out-paths \
    --option max-jobs 1 --option cores 2 "$flake#omnibus-archive-ci")
"${nix_cmd[@]}" build --no-write-lock-file --no-link --option max-jobs 1 --option cores 2 \
    "$flake#omnibus-archive-layout-check"
system=$("${nix_cmd[@]}" eval --impure --raw --expr builtins.currentSystem)
"${nix_cmd[@]}" eval --no-write-lock-file --json \
    "$flake#packages.$system.aeneas-download.toolchain" > "$staging/expected.json"
tar_path=$("${nix_cmd[@]}" build --impure --no-link --print-out-paths --expr \
    "(builtins.getFlake \"$flake\").inputs.nixpkgs.legacyPackages.$system.gnutar")
zstd_path=$("${nix_cmd[@]}" build --impure --no-link --print-out-paths --expr \
    "(builtins.getFlake \"$flake\").inputs.nixpkgs.legacyPackages.$system.zstd.bin")
mkdir -p "$staging/toolchain/bundle"
"$tar_path/bin/tar" --use-compress-program="$zstd_path/bin/zstd" -xf "$archive" \
    -C "$staging/toolchain/bundle"
python3 - "$staging/expected.json" "$staging/toolchain/bundle/aeneas/metadata.json" <<'PYCHECK'
import json, sys
expected, actual = (json.load(open(path)) for path in sys.argv[1:])
for key, value in actual.items():
    if expected.get(key) != value:
        raise SystemExit(f"Anneal archive metadata mismatch: {key}")
PYCHECK
# Keep zerocopy's existing executable/backend paths without copying toolchains.
for name in aeneas charon charon-driver; do
    ln -s "bundle/aeneas/bin/$name" "$staging/toolchain/$name"
done
ln -s bundle/aeneas/backends "$staging/toolchain/backends"
ln -s bundle/lean "$staging/toolchain/lean"
ln -s bundle/rust "$staging/toolchain/rust"
if [[ -d "$staging/toolchain/bundle/aeneas/bin/libs" ]]; then
    mkdir "$staging/toolchain/libs"
    cp "$staging/toolchain/bundle/aeneas/bin/libs/"* "$staging/toolchain/libs/"
fi
bash verification/aeneas/build-aeneas.sh "$staging/toolchain"
python3 -B verification/aeneas/toolchain.py check "$staging/toolchain"
[[ ! -e "$tools_dir" && ! -L "$tools_dir" ]] || { echo "Installation appeared during setup: $tools_dir" >&2; exit 1; }
mv "$staging/toolchain" "$tools_dir"
