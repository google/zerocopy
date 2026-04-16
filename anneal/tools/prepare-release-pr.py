#!/usr/bin/env python3
"""Updates Cargo.toml with artifact hashes.

This script is used in the manual release workflow to close the loop: it
downloads the artifacts published to a unique release, computes their
hashes, and updates Cargo.toml with these hashes and URLs.
"""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tomlkit

CARGO_TOML_PATH = (Path(__file__).parent.parent / "Cargo.toml").resolve()

def get_file_sha256(path):
    """Computes the SHA256 hash of a file.

    This is used to verify the integrity of artifacts downloaded by users.
    """
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while chunk := f.read(8192):
            h.update(chunk)
    return h.hexdigest()

def main():
    parser = argparse.ArgumentParser(description="Update Cargo.toml with artifact hashes")
    parser.add_argument("--tag", required=True, help="Release tag")
    parser.add_argument("--aeneas-version", required=True, help="Aeneas version")
    parser.add_argument("--crate-version", help="New crate version")
    args = parser.parse_args()

    # 1. Download artifacts.
    # We download the artifacts from the unique release tag generated in the
    # previous step of the workflow. This ensures we are getting the exact
    # binaries built by that run.
    print(f"Downloading artifacts from release {args.tag}...")
    try:
        # Ensure output directory exists
        os.makedirs("dist_download", exist_ok=True)
        subprocess.run([
            "gh", "release", "download", args.tag,
            "-D", "dist_download",
            "-R", "google/zerocopy",
            "--clobber"
        ], check=True)
    except subprocess.CalledProcessError as e:
        print(f"ERROR: Failed to download artifacts: {e}")
        sys.exit(1)

    # 2. Compute hashes.
    # We compute hashes for all downloaded artifacts to bake them into
    # Cargo.toml. This allows `cargo anneal setup` to verify integrity.
    checksums = {}
    dist_dir = Path("dist_download")
    for path in dist_dir.glob("*.tar.zst"):
        name = path.name
        target = name.replace("anneal-toolchain-", "").replace(".tar.zst", "")
        checksums[target] = get_file_sha256(path)
        print(f"Hash for {target}: {checksums[target]}")

    # 3. Update Cargo.toml.
    # We use tomlkit to parse and modify the document, which ensures
    # that all existing comments and formatting in the original file are
    # preserved.
    print(f"Updating {CARGO_TOML_PATH}...")
    try:
        content = CARGO_TOML_PATH.read_text()
        doc = tomlkit.parse(content)
    except Exception as e:
        print(f"ERROR: Failed to parse Cargo.toml: {e}")
        sys.exit(1)

    try:
        metadata = doc["package"]["metadata"]
        deps = metadata["anneal"]["dependencies"]

        deps["aeneas"]["tag"] = args.tag
        deps["aeneas"]["checksums"] = tomlkit.table()
        for k, v in sorted(checksums.items()):
            deps["aeneas"]["checksums"][k] = v

        metadata["build_rs"]["aeneas_rev"] = args.aeneas_version

        if args.crate_version and args.crate_version != "PROMPT: Enter Cargo version":
            doc["package"]["version"] = args.crate_version
            
    except KeyError as e:
        print(f"ERROR: Cargo.toml missing expected metadata section: {e}")
        sys.exit(1)

    try:
        CARGO_TOML_PATH.write_text(tomlkit.dumps(doc))
    except Exception as e:
        print(f"ERROR: Failed to write to Cargo.toml: {e}")
        sys.exit(1)

    print("Cargo.toml updated successfully.")

if __name__ == "__main__":
    main()
