#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/anneal-release-dry-run.XXXXXXXX")"
WORKTREE="$TMP_ROOT/worktree"
PATCH="$TMP_ROOT/anneal-release-source.patch"

cleanup() {
  git -C "$ROOT" worktree remove --force "$WORKTREE" >/dev/null 2>&1 || rm -rf "$TMP_ROOT"
}
trap cleanup EXIT

VERSION="${ANNEAL_RELEASE_DRY_RUN_VERSION:-999.0.0-alpha.0}"
TAG_NAME="anneal-toolchains-v${VERSION}-dry-run"

git -C "$ROOT" worktree add --detach "$WORKTREE" HEAD >/dev/null
cd "$WORKTREE"

./ci/release_anneal_version.sh "$VERSION"

python3 anneal/tools/check-release-pr-files.py \
  --context "Release dry-run version bump" \
  --include-untracked \
  --allowed anneal/Cargo.lock \
  --allowed anneal/Cargo.toml \
  --allowed anneal/README.md \
  --required anneal/Cargo.toml

git diff --binary > "$PATCH"
if [ ! -s "$PATCH" ]; then
  echo "Release dry-run version bump produced an empty patch." >&2
  exit 1
fi

git reset --hard HEAD >/dev/null
git clean -fdx >/dev/null
git apply --check "$PATCH"
git apply "$PATCH"

python3 anneal/tools/check-release-pr-files.py \
  --context "Release dry-run applied source patch" \
  --include-untracked \
  --allowed anneal/Cargo.lock \
  --allowed anneal/Cargo.toml \
  --allowed anneal/README.md \
  --required anneal/Cargo.toml

mkdir -p anneal/release-metadata
for target in linux-x86_64 linux-aarch64 macos-x86_64 macos-aarch64; do
  case "$target" in
    linux-x86_64)
      cargo_os=linux
      cargo_arch=x86_64
      ;;
    linux-aarch64)
      cargo_os=linux
      cargo_arch=aarch64
      ;;
    macos-x86_64)
      cargo_os=macos
      cargo_arch=x86_64
      ;;
    macos-aarch64)
      cargo_os=macos
      cargo_arch=aarch64
      ;;
    *)
      echo "unexpected release dry-run target: $target" >&2
      exit 1
      ;;
  esac

  sha256="$(python3 -c 'import hashlib, sys; print(hashlib.sha256(sys.argv[1].encode()).hexdigest())' "$target")"
  url="https://github.com/google/zerocopy/releases/download/${TAG_NAME}/anneal-toolchain-${target}.tar.zst"
  cat > "anneal/release-metadata/${target}.json" <<EOF
{
  "arch": "${cargo_arch}",
  "filename": "anneal-toolchain-${target}.tar.zst",
  "os": "${cargo_os}",
  "sha256": "${sha256}",
  "target": "${target}",
  "url": "${url}"
}
EOF
done

python3 anneal/tools/update-exocrate-metadata.py \
  --cargo-toml anneal/Cargo.toml \
  --metadata-dir anneal/release-metadata \
  --expected-release-tag "$TAG_NAME" \
  --require-all

rm -rf anneal/release-metadata

python3 anneal/tools/check-release-pr-files.py \
  --context "Release dry-run metadata update" \
  --include-untracked \
  --allowed anneal/Cargo.lock \
  --allowed anneal/Cargo.toml \
  --allowed anneal/README.md \
  --required anneal/Cargo.toml

python3 - "$TAG_NAME" <<'PY'
import pathlib
import sys
import tomllib

tag = sys.argv[1]
manifest = tomllib.loads(pathlib.Path("anneal/Cargo.toml").read_text(encoding="utf-8"))
exocrate = manifest["package"]["metadata"]["exocrate"]
expected = {
    ("linux", "x86_64"),
    ("linux", "aarch64"),
    ("macos", "x86_64"),
    ("macos", "aarch64"),
}

actual = {(os_name, arch) for os_name, by_arch in exocrate.items() for arch in by_arch}
if actual != expected:
    raise SystemExit(f"unexpected exocrate platforms: expected {expected}, got {actual}")

for os_name, arch in sorted(expected):
    metadata = exocrate[os_name][arch]
    sha256 = metadata.get("sha256")
    url = metadata.get("url")
    if not isinstance(sha256, str) or len(sha256) != 64 or any(c not in "0123456789abcdef" for c in sha256):
        raise SystemExit(f"invalid sha256 for {os_name}.{arch}: {sha256!r}")
    if not isinstance(url, str) or f"/releases/download/{tag}/" not in url:
        raise SystemExit(f"invalid URL for {os_name}.{arch}: {url!r}")
PY

echo "Anneal release dry-run checks passed."
