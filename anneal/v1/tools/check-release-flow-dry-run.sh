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

python3 anneal/v1/tools/check-release-pr-files.py \
  --context "Release dry-run version bump" \
  --include-untracked \
  --allowed anneal/v1/Cargo.lock \
  --allowed anneal/v1/Cargo.toml \
  --allowed anneal/v1/README.md \
  --required anneal/v1/Cargo.toml

git diff --binary > "$PATCH"
if [ ! -s "$PATCH" ]; then
  echo "Release dry-run version bump produced an empty patch." >&2
  exit 1
fi

git reset --hard HEAD >/dev/null
git clean -fdx >/dev/null
git apply --check "$PATCH"
git apply "$PATCH"

python3 anneal/v1/tools/check-release-pr-files.py \
  --context "Release dry-run applied source patch" \
  --include-untracked \
  --allowed anneal/v1/Cargo.lock \
  --allowed anneal/v1/Cargo.toml \
  --allowed anneal/v1/README.md \
  --required anneal/v1/Cargo.toml

mkdir -p anneal/v1/release-metadata
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
  cat > "anneal/v1/release-metadata/${target}.json" <<EOF
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

python3 anneal/v1/tools/validate-release-artifacts.py \
  --metadata-dir anneal/v1/release-metadata \
  --tag "$TAG_NAME" \
  --repository google/zerocopy

python3 anneal/v1/tools/update-exocrate-metadata.py \
  --cargo-toml anneal/v1/Cargo.toml \
  --metadata-dir anneal/v1/release-metadata \
  --expected-release-tag "$TAG_NAME" \
  --require-all

rm -rf anneal/v1/release-metadata

python3 anneal/v1/tools/check-release-pr-files.py \
  --context "Release dry-run metadata update" \
  --include-untracked \
  --allowed anneal/v1/Cargo.lock \
  --allowed anneal/v1/Cargo.toml \
  --allowed anneal/v1/README.md \
  --required anneal/v1/Cargo.toml

python3 - "$TAG_NAME" <<'PY'
import pathlib
import sys
import tomllib

tag = sys.argv[1]
manifest = tomllib.loads(pathlib.Path("anneal/v1/Cargo.toml").read_text(encoding="utf-8"))
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

python3 - <<'PY'
import pathlib

workflow = pathlib.Path(".github/workflows/anneal-release.yml").read_text(encoding="utf-8")

def job(name: str, next_name: str | None) -> str:
    start = workflow.index(f"  {name}:\n")
    end = len(workflow) if next_name is None else workflow.index(f"  {next_name}:\n")
    return workflow[start:end]


resolve = job("resolve-release-source", "prepare-release-source")
prepare = job("prepare-release-source", "build-toolchains")
build = job("build-toolchains", "prepare-release-pr")
prepare_pr = job("prepare-release-pr", "review-release")
review = job("review-release", "publish-release-assets")
publish = job("publish-release-assets", "submit-release-pr")
submit = job("submit-release-pr", None)
prepare_crates = job("prepare-crates-release", "release")
release_crates = job("release", "resolve-release-source")

if "package-release-crates.sh" not in prepare_crates:
    raise SystemExit("crate preparation must run the PR-tested packaging script")
if "./.github/actions/install-pinned-stable" not in prepare_crates:
    raise SystemExit("crate preparation must install the pinned Cargo version")
if "create-crates-release-plan.py" in prepare_crates:
    raise SystemExit("unprivileged crate preparation must not supply commands")
for forbidden in ("contents: write", "id-token: write", "CARGO_REGISTRY_TOKEN"):
    if forbidden in prepare_crates:
        raise SystemExit(f"crate preparation gained a credential: {forbidden}")

if "environment: release" not in release_crates:
    raise SystemExit("crate publisher must use the release environment")
if "id-token: write" not in release_crates:
    raise SystemExit("crate publisher is missing crates.io OIDC permission")
if "create-crates-release-plan.py" not in release_crates:
    raise SystemExit("crate publisher must construct its own trusted plan")
if "./.github/actions/install-pinned-stable" not in release_crates:
    raise SystemExit("crate publisher must install the pinned Cargo version")
if "reconcile-crates-release.py" not in release_crates:
    raise SystemExit("crate publisher must use the resumable reconciler")
for forbidden in (
    "./anneal/v1/tools/package-release-crates.sh",
    "cargo publish",
    "git tag",
):
    if forbidden in release_crates:
        raise SystemExit(f"crate publisher bypasses the release plan: {forbidden}")

if "tools/pre-publish.sh" in workflow:
    raise SystemExit("release workflow still mutates source before publication")
if "git checkout -q HEAD^" in workflow:
    raise SystemExit("release version detection still assumes a one-commit push")

for name, block in {
    "resolve-release-source": resolve,
    "prepare-release-source": prepare,
    "build-toolchains": build,
    "prepare-release-pr": prepare_pr,
    "review-release": review,
}.items():
    if "contents: write" in block or "GOOGLE_PR_CREATION_BOT_TOKEN" in block:
        raise SystemExit(f"unprivileged {name} job gained a repository credential")

if "nix build" not in build or "gh release" in build or "GH_TOKEN" in build:
    raise SystemExit("toolchain builders must build without release credentials")
if "git apply anneal-release-source.patch" in build:
    raise SystemExit("toolchain builders must build the exact selected commit")
if "validate-release-artifacts.py" not in review:
    raise SystemExit("release review must validate matrix-produced metadata")

if "environment: release" not in publish or "contents: write" not in publish:
    raise SystemExit("asset publisher must use the release environment and write token")
for forbidden in (
    "nix build",
    "release_anneal_version.sh",
    "update-exocrate-metadata.py",
    "GOOGLE_PR_CREATION_BOT_TOKEN",
):
    if forbidden in publish:
        raise SystemExit(f"asset publisher executes or receives forbidden input: {forbidden}")
if "validate-release-artifacts.py" not in publish:
    raise SystemExit("asset publisher must validate archives with trusted code")
if '--draft' not in publish or '--draft=false' not in publish:
    raise SystemExit("asset publisher must stage a draft before publishing it")

if "GOOGLE_PR_CREATION_BOT_TOKEN" not in submit:
    raise SystemExit("PR submitter is missing the bot credential")
if "gh release" in submit or "nix build" in submit:
    raise SystemExit("PR submitter must not hold release-asset authority")
if workflow.index("  publish-release-assets:\n") > workflow.index("  submit-release-pr:\n"):
    raise SystemExit("toolchain assets must be public before the release PR is submitted")
PY

echo "Anneal release dry-run checks passed."
