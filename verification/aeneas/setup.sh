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
# A shared cache is opt-in. Its key comes from Anneal and the patched builder;
# no upstream versions are independently pinned here.
build_key=$(python3 -B verification/aeneas/toolchain.py cache-key)
install_dir=$tools_dir
cache_lock=
link_cached_installation() {
    # os.symlink treats an existing directory as a collision, never as a parent.
    python3 - "$install_dir" "$tools_dir" <<'PYLINK'
import os, sys
os.symlink(sys.argv[1], sys.argv[2], target_is_directory=True)
PYLINK
}
if [[ -n ${AENEAS_TOOLCHAIN_CACHE_DIR:-} ]]; then
    mkdir -p "$AENEAS_TOOLCHAIN_CACHE_DIR"
    cache_dir=$(cd "$AENEAS_TOOLCHAIN_CACHE_DIR" && pwd)
    install_dir="$cache_dir/$build_key"
    if [[ -e "$install_dir" || -L "$install_dir" ]]; then
        python3 -B verification/aeneas/toolchain.py check --cache "$install_dir"
        mkdir -p "$(dirname "$tools_dir")"
        link_cached_installation
        echo "Using validated cached Anneal toolchain: $install_dir"
        exit
    fi
    cache_lock="$cache_dir/.$build_key.lock"
    mkdir "$cache_lock" || { echo "Toolchain cache is locked: $cache_lock; inspect stale locks before retrying." >&2; exit 1; }
    trap 'rmdir "$cache_lock"' EXIT
    # A producer may have published just before we acquired its lock.
    if [[ -e "$install_dir" || -L "$install_dir" ]]; then
        python3 -B verification/aeneas/toolchain.py check --cache "$install_dir"
        mkdir -p "$(dirname "$tools_dir")"
        link_cached_installation
        echo "Using validated cached Anneal toolchain: $install_dir"
        exit
    fi
fi
command -v nix >/dev/null || { echo 'Cold Anneal toolchain setup requires Nix.' >&2; exit 1; }
mkdir -p "$(dirname "$install_dir")"
staging=$(mktemp -d "$(dirname "$install_dir")/setup.XXXXXX")
staging_retained=0
# The archive has read-only directories. Make only private staging directories
# writable before removing them; find does not follow the toolchain's symlinks.
trap 'if [[ "$staging_retained" != 1 ]]; then find "$staging" -type d -exec chmod u+w {} +; rm -rf "$staging"; fi; if [[ -n "$cache_lock" ]]; then rmdir "$cache_lock"; fi' EXIT
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
python3 -B verification/aeneas/toolchain.py check --cache "$staging/toolchain"
[[ $(python3 -B verification/aeneas/toolchain.py cache-key) == "$build_key" ]] || { echo 'Toolchain build inputs changed during setup; retry from a fresh staging directory.' >&2; exit 1; }
if python3 -B verification/aeneas/toolchain.py publish "$staging/toolchain" "$install_dir"; then
    :
else
    staging_retained=1
    echo "Validated staged toolchain retained at: $staging/toolchain" >&2
    exit 1
fi
if [[ -n "$cache_lock" ]]; then
    mkdir -p "$(dirname "$tools_dir")"
    # Symlink creation fails if an installation appeared; never replace it.
    link_cached_installation
fi
