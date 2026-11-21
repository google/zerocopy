# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate the MIR alpha manifest or pin its released toolchain digest."""

import argparse
from pathlib import Path
import re
import subprocess
import tomllib


MANIFEST = Path(__file__).resolve().parents[1] / "trusted/cargo-anneal/Cargo.toml"
ASSET = "anneal-toolchain-linux-x86_64.tar.zst"
UNPINNED = "0" * 64
ARCHIVE_INPUTS = (
    ".github/workflows/release.yml",
    "anneal/Cargo.lock",
    "anneal/flake.nix",
    "anneal/flake.lock",
    "anneal/trusted/rustc-capture",
    "anneal/trusted/lean",
    "anneal/trusted/audit/TrustedBoundary.lean",
    "anneal/trusted/audit/library-lock.json",
    "anneal/theory",
    "anneal/trusted/cargo-anneal/src/bundled_resources.rs",
)


def archive(text, version):
    package = tomllib.loads(text)["package"]
    if not re.fullmatch(r"0\.2\.0-alpha\.[1-9][0-9]*", version):
        raise ValueError("expected a 0.2.0 alpha version")
    if package["name"] != "cargo-anneal" or package["version"] != version:
        raise ValueError("release version must match the current verifier manifest")
    tag = f"anneal-mir-toolchain-v{version}"
    url = f"https://github.com/google/zerocopy/releases/download/{tag}/{ASSET}"
    rows = package["metadata"]["exocrate"]
    if len(rows) != 1:
        raise ValueError("expected exactly one alpha archive")
    row = rows[0]
    digest = row["sha256"]
    expected = {"os": "linux", "arch": "x86_64", "url": url, "sha256": digest}
    if row != expected or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("invalid alpha archive metadata")
    return tag, digest


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


def check_archive_base(repo, source, version):
    if not re.fullmatch(r"[0-9a-f]{40}", source):
        raise ValueError("expected the archive release's source commit")
    metadata = "anneal/trusted/cargo-anneal/Cargo.toml"
    original = subprocess.check_output(
        ["git", "show", f"{source}:{metadata}"], cwd=repo, text=True
    )
    archive(original, version)
    result = subprocess.run(
        ["git", "diff", "--name-only", source, "HEAD", "--", *ARCHIVE_INPUTS],
        cwd=repo, check=True, text=True, capture_output=True,
    )
    if result.stdout:
        raise ValueError(f"archive inputs changed after the toolchain release:\n{result.stdout}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("version")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--require-pinned", action="store_true")
    mode.add_argument("--pin")
    parser.add_argument("--archive-base")
    args = parser.parse_args()
    try:
        text = MANIFEST.read_text()
        tag, digest = archive(text, args.version)
        if args.archive_base:
            check_archive_base(MANIFEST.parents[3], args.archive_base, args.version)
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
