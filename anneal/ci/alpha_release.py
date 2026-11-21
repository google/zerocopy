# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Prepare and validate an Anneal alpha release."""

import argparse
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tomllib


REPO = Path(__file__).resolve().parents[2]
MANIFEST_PATH = "anneal/trusted/cargo-anneal/Cargo.toml"
LOCK_PATH = "anneal/Cargo.lock"
ROOT_HASH_PATH = "anneal/trusted/root-manifest.sha256"
MANIFEST = REPO / MANIFEST_PATH
ASSET = "anneal-toolchain-linux-x86_64.tar.zst"
UNPINNED = "0" * 64
ARCHIVE_INPUTS = (
    ".github/workflows/release.yml",
    "anneal/ci/alpha_release.py",
    LOCK_PATH,
    "anneal/flake.nix",
    "anneal/flake.lock",
    "anneal/trusted/rustc-capture",
    "anneal/trusted/lean",
    "anneal/trusted/audit/TrustedBoundary.lean",
    "anneal/trusted/audit/library-lock.json",
    "anneal/theory",
    "anneal/trusted/cargo-anneal/src/bundled_resources.rs",
)


def alpha_number(version):
    match = re.fullmatch(r"0\.2\.0-alpha\.([1-9][0-9]*)", version)
    if match is None:
        raise ValueError("expected a 0.2.0 alpha version")
    return int(match[1])


def archive_tag(version):
    return f"anneal-toolchain-v{version}"


def archive_url(version):
    return f"https://github.com/google/zerocopy/releases/download/{archive_tag(version)}/{ASSET}"


def release_metadata(text):
    package = tomllib.loads(text)["package"]
    version = package["version"]
    alpha_number(version)
    if package["name"] != "cargo-anneal":
        raise ValueError("expected the cargo-anneal manifest")
    rows = package["metadata"]["exocrate"]
    if len(rows) != 1:
        raise ValueError("expected exactly one alpha archive")
    return version, rows[0]


def archive(text, version):
    current, row = release_metadata(text)
    if current != version:
        raise ValueError("release version must match the current verifier manifest")
    digest = row["sha256"]
    expected = {"os": "linux", "arch": "x86_64", "url": archive_url(version), "sha256": digest}
    if row != expected or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("invalid alpha archive metadata")
    return archive_tag(version), digest


def replace_one(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"expected exactly one {old!r}")
    return text.replace(old, new, 1)


def prepare(repo, version):
    status = subprocess.check_output(["git", "status", "--porcelain"], cwd=repo, text=True)
    if status:
        raise ValueError("prepare the Anneal release from a clean checkout")
    manifest = repo / MANIFEST_PATH
    lockfile = repo / LOCK_PATH
    root_hashes = repo / ROOT_HASH_PATH
    text = manifest.read_text()
    current = tomllib.loads(text)["package"]["version"]
    _, digest = archive(text, current)
    if alpha_number(version) < alpha_number(current) or (
        version == current and digest != UNPINNED
    ):
        raise ValueError("expected a newer alpha or the current unpinned alpha")

    lock_bytes = lockfile.read_bytes()
    lock = lock_bytes.decode("utf-8")
    lock_row = '[[package]]\nname = "cargo-anneal"\nversion = '
    updated_lock = replace_one(lock, f'{lock_row}"{current}"', f'{lock_row}"{version}"')
    new_lock_bytes = updated_lock.encode("utf-8")
    lock_hash = hashlib.sha256(lock_bytes).hexdigest()
    new_lock_hash = hashlib.sha256(new_lock_bytes).hexdigest()
    updated_hashes = replace_one(
        root_hashes.read_text(), f"{lock_hash}  Cargo.lock\n", f"{new_lock_hash}  Cargo.lock\n"
    )
    updated = replace_one(text, f'version = "{current}"', f'version = "{version}"')
    updated = replace_one(updated, archive_url(current), archive_url(version))
    updated = replace_one(updated, f'sha256 = "{digest}"', f'sha256 = "{UNPINNED}"')
    archive(updated, version)

    manifest.write_text(updated)
    lockfile.write_bytes(new_lock_bytes)
    root_hashes.write_text(updated_hashes)
    subprocess.run(
        ["git", "add", "--", MANIFEST_PATH, LOCK_PATH, ROOT_HASH_PATH], cwd=repo, check=True
    )
    tree = subprocess.check_output(["git", "write-tree"], cwd=repo, text=True).strip()
    timestamp = subprocess.check_output(
        ["git", "show", "-s", "--format=%cI", "HEAD"], cwd=repo, text=True
    ).strip()
    # Archive building and hosting run on separate runners. The base commit's
    # timestamp lets both reconstruct the exact commit without sharing a checkout.
    identity = {
        "GIT_AUTHOR_NAME": "Google PR Creation Bot",
        "GIT_AUTHOR_EMAIL": "github-pull-request-creation-bot@google.com",
        "GIT_AUTHOR_DATE": timestamp,
        "GIT_COMMITTER_NAME": "Google PR Creation Bot",
        "GIT_COMMITTER_EMAIL": "github-pull-request-creation-bot@google.com",
        "GIT_COMMITTER_DATE": timestamp,
    }
    return subprocess.check_output(
        ["git", "-c", "commit.gpgsign=false", "commit-tree", tree, "-p", "HEAD", "-m",
         f"Prepare Anneal release {version}"],
        cwd=repo, text=True, env={**os.environ, **identity},
    ).strip()


def read_manifest(repo, revision):
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("expected a Git object ID")
    return subprocess.check_output(
        ["git", "show", f"{revision}:{MANIFEST_PATH}"], cwd=repo, text=True
    )


def version_to_publish(before, after):
    version, _ = release_metadata(after)
    _, digest = archive(after, version)
    previous, previous_row = release_metadata(before)
    previous_digest = previous_row["sha256"]
    if not re.fullmatch(r"[0-9a-f]{64}", previous_digest):
        raise ValueError("invalid previous archive digest")
    if alpha_number(version) < alpha_number(previous):
        raise ValueError("cannot publish an older Anneal version")
    if version == previous and previous_digest != UNPINNED:
        if digest != previous_digest:
            raise ValueError("cannot change the pin for an already pinned Anneal version")
        return ""
    return version if digest != UNPINNED else ""


def pin(text, version, digest):
    if not re.fullmatch(r"[0-9a-f]{64}", digest) or digest == UNPINNED:
        raise ValueError("expected the nonzero SHA-256 of the released archive")
    _, current = archive(text, version)
    if current == digest:
        return text
    if current != UNPINNED:
        raise ValueError("the release already pins a different archive")
    old = f'sha256 = "{UNPINNED}"'
    if text.count(old) != 1:
        raise ValueError("expected one placeholder SHA-256 in the manifest")
    updated = text.replace(old, f'sha256 = "{digest}"', 1)
    if archive(updated, version)[1] != digest:
        raise ValueError("the pinned digest did not reach the alpha archive")
    return updated


def check_archive_base(repo, source, version, tree="HEAD"):
    archive(read_manifest(repo, source), version)
    result = subprocess.run(
        ["git", "diff", "--name-only", source, tree, "--", *ARCHIVE_INPUTS],
        cwd=repo, check=True, text=True, capture_output=True,
    )
    if result.stdout:
        raise ValueError(f"archive inputs changed after the toolchain release:\n{result.stdout}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("version", nargs="?")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--changed-since")
    mode.add_argument("--require-pinned", action="store_true")
    mode.add_argument("--pin")
    parser.add_argument("--archive-base")
    parser.add_argument("--archive-tree", default="HEAD")
    args = parser.parse_args()
    try:
        if args.changed_since:
            if args.version:
                raise ValueError("derive the version from the manifests on a push")
            print(version_to_publish(read_manifest(REPO, args.changed_since), MANIFEST.read_text()))
            return
        if not args.version:
            raise ValueError("expected an Anneal release version")
        if args.prepare:
            print(prepare(REPO, args.version))
            return
        if args.archive_tree != "HEAD" and not re.fullmatch(r"[0-9a-f]{40}", args.archive_tree):
            raise ValueError("expected a prepared Git object ID")
        text = MANIFEST.read_text()
        tag, digest = archive(text, args.version)
        if args.archive_base:
            check_archive_base(REPO, args.archive_base, args.version, args.archive_tree)
        if args.pin:
            updated = pin(text, args.version, args.pin)
            if updated != text:
                MANIFEST.write_text(updated)
        if args.require_pinned and digest == UNPINNED:
            raise ValueError("prepare and merge the archive pin before publishing")
    except (ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"{error}\n")
    print(tag)


if __name__ == "__main__":
    main()
